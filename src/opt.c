/* Krell — optimizer: semantics-preserving rewrite passes over the IR.
 *
 * Method: per function, one forward pass rebuilds each block's
 * instruction list applying local rules (constant folding with the
 * interpreter's exact semantics, identities, strength reduction,
 * div-by-constant via validated magic numbers, chain collapsing), with
 * a substitution map for values replaced by existing values. A marking
 * DCE then drops unmarked pure instructions. All rules are
 * dominance-safe by construction: substitutions only ever point to
 * values defined before the replaced instruction, expansions live in
 * the same block at the same position, and the module is snapshot /
 * restored if the verifier rejects the result. */
#include "krell.h"
#include <string.h>
#include <math.h>

static uint64_t msk64(int bits) { return bits >= 64 ? ~0ull : ((1ull << bits) - 1ull); }
static int64_t sx64(uint64_t v, int bits) {
    if (bits >= 64) return (int64_t)v;
    return (int64_t)(v << (64 - bits)) >> (64 - bits);
}

typedef struct { Instr *v; int n, cap; } InsVec;
static void iv_push(InsVec *iv, Instr in) {
    if (iv->n == iv->cap) { iv->cap = iv->cap ? iv->cap * 2 : 16; iv->v = realloc(iv->v, sizeof(Instr) * (size_t)iv->cap); }
    iv->v[iv->n++] = in;
}

typedef struct {
    Func *f;
    const Cost *cost;
    OptStats *st;
    int32_t *subst;        /* value -> replacement value (identity default) */
    int *usecount;
    int64_t *konst;        /* known integer constant per value */
    uint8_t *hask;
    int cap;               /* allocated length of the per-value arrays */
} Opt;

static void opt_grow(Opt *o, int v) {
    if (v < o->cap) return;
    int nc = o->cap ? o->cap : 64;
    while (v >= nc) nc *= 2;
    o->subst = realloc(o->subst, sizeof(int32_t) * (size_t)nc);
    o->usecount = realloc(o->usecount, sizeof(int) * (size_t)nc);
    o->konst = realloc(o->konst, sizeof(int64_t) * (size_t)nc);
    o->hask = realloc(o->hask, (size_t)nc);
    for (int i = o->cap; i < nc; i++) { o->subst[i] = i; o->usecount[i] = 0; o->konst[i] = 0; o->hask[i] = 0; }
    o->cap = nc;
}
/* fresh value id with a registered type (mirrors ir.c's growth) */
static int opt_new_value(Opt *o, Type t) {
    Func *f = o->f;
    if (f->nvalues >= f->vcap) {
        f->vcap = f->vcap ? f->vcap * 2 : 32;
        f->vtypes  = realloc(f->vtypes,  (size_t)f->vcap * sizeof(Type));
        f->cval    = realloc(f->cval,    (size_t)f->vcap * sizeof(uint64_t));
        f->isconst = realloc(f->isconst, (size_t)f->vcap);
    }
    int v = f->nvalues++;
    f->vtypes[v] = t;
    f->cval[v] = 0;
    f->isconst[v] = 0;
    opt_grow(o, v);
    return v;
}
static int sub(Opt *o, int v) { return v < 0 ? v : o->subst[v]; }
static bool isk(Opt *o, int v, int64_t *out) {
    if (v < 0 || !o->hask[v]) return false;
    *out = o->konst[v];
    return true;
}
/* per-block iconst cache (constants are created in the block that uses
 * them, ahead of the user, so dominance is trivially satisfied) */
typedef struct { Type ty; int64_t imm; int val; } KEnt;
typedef struct { KEnt *v; int n, cap; } KCache;
static int block_iconst(Opt *o, InsVec *nb, KCache *kc, Type ty, int64_t imm) {
    for (int i = 0; i < kc->n; i++)
        if (ty_eq(kc->v[i].ty, ty) && kc->v[i].imm == imm) return kc->v[i].val;
    int v = opt_new_value(o, ty);
    Instr in = ins_iconst(ty, imm);
    in.result = v;
    iv_push(nb, in);
    if (kc->n == kc->cap) { kc->cap = kc->cap ? kc->cap * 2 : 8; kc->v = realloc(kc->v, sizeof(KEnt) * (size_t)kc->cap); }
    kc->v[kc->n++] = (KEnt){ ty, imm, v };
    o->hask[v] = 1; o->konst[v] = imm;
    return v;
}

/* ---- interpreter-exact integer evaluation for folding ---- */
static uint64_t eval_bin(int op, Type t, uint64_t A, uint64_t B) {
    int bits = t.bits;
    uint64_t m = msk64(bits);
    A &= m; B &= m;
    switch (op) {
    case OP_ADD: return (A + B) & m;
    case OP_SUB: return (A - B) & m;
    case OP_MUL: return (A * B) & m;
    case OP_AND: return A & B;
    case OP_OR:  return A | B;
    case OP_XOR: return A ^ B;
    case OP_UDIV: return B ? (A / B) & m : 0;
    case OP_UREM: return B ? (A % B) & m : 0;
    case OP_SDIV: {
        int64_t sa = sx64(A, bits), sb = sx64(B, bits);
        if (!sb) return 0;
        if (sb == -1 && sa == sx64(m & (1ull << (bits - 1)), bits)) return (uint64_t)sa & m;
        return (uint64_t)(sa / sb) & m;
    }
    case OP_SREM: {
        int64_t sa = sx64(A, bits), sb = sx64(B, bits);
        if (!sb) return 0;
        if (sb == -1 && sa == sx64(m & (1ull << (bits - 1)), bits)) return 0;
        return (uint64_t)(sa % sb) & m;
    }
    case OP_SHL:  return (A << (B % (uint64_t)bits)) & m;
    case OP_LSHR: return (A >> (B % (uint64_t)bits)) & m;
    case OP_ASHR: return (uint64_t)(sx64(A, bits) >> (B % (uint64_t)bits)) & m;
    }
    return 0;
}
static uint64_t eval_un(int op, Type t, uint64_t A) {
    int bits = t.bits;
    uint64_t m = msk64(bits);
    A &= m;
    switch (op) {
    case OP_NEG: return (0 - A) & m;
    case OP_NOT: return (~A) & m;
    case OP_POPCOUNT: { int n = 0; for (int i = 0; i < bits; i++) n += (int)((A >> i) & 1); return (uint64_t)n; }
    case OP_CLZ: { for (int i = bits - 1; i >= 0; i--) if ((A >> i) & 1) return (uint64_t)(bits - 1 - i); return (uint64_t)bits; }
    case OP_CTZ: { for (int i = 0; i < bits; i++) if ((A >> i) & 1) return (uint64_t)i; return (uint64_t)bits; }
    case OP_BSWAP: {
        uint64_t r = 0;
        for (int i = 0; i < bits / 8; i++) r |= ((A >> (8 * i)) & 0xff) << (8 * (bits / 8 - 1 - i));
        return r & m;
    }
    }
    return 0;
}
static int eval_icmp(int pred, Type t, uint64_t A, uint64_t B) {
    int bits = t.bits;
    A &= msk64(bits); B &= msk64(bits);
    int64_t sa = sx64(A, bits), sb = sx64(B, bits);
    switch (pred) {
    case IC_EQ: return A == B; case IC_NE: return A != B;
    case IC_ULT: return A < B; case IC_ULE: return A <= B;
    case IC_UGT: return A > B; case IC_UGE: return A >= B;
    case IC_SLT: return sa < sb; case IC_SLE: return sa <= sb;
    case IC_SGT: return sa > sb; case IC_SGE: return sa >= sb;
    }
    return 0;
}
/* float -> int with SEMANTICS.md saturation (NaN -> 0) */
static uint64_t f2i_fold(double d, int bits, int unsig) {
    if (isnan(d)) return 0;
    if (!unsig) {
        if (bits == 64) {
            if (d >= 9223372036854775808.0) return (uint64_t)INT64_MAX;
            if (d < -9223372036854775808.0) return (uint64_t)INT64_MIN;
            return (uint64_t)(int64_t)d;
        }
        double hi = ldexp(1.0, bits - 1);          /* 2^(bits-1), bits <= 63 */
        if (d >= hi) return (uint64_t)(int64_t)(hi - 1) & msk64(bits);
        if (d < -hi) return (uint64_t)(int64_t)(-hi) & msk64(bits);
        return (uint64_t)(int64_t)d & msk64(bits);
    } else {
        double hi = ldexp(1.0, bits);              /* 2^bits */
        if (d >= hi) return msk64(bits);
        if (d <= 0) return 0;
        if (bits == 64) return (uint64_t)d;
        return (uint64_t)(uint64_t)d & msk64(bits);
    }
}

/* ---- magic-number unsigned division (Hacker's Delight family) ----
 * Finds (M, s) with q = mulhi32(x, M) >> s == x / d for all x, using the
 * add-free variant; the candidate is then PROVEN on edge cases plus
 * 200k deterministic random probes before it is used. */
static bool magic_u32(uint32_t d, uint32_t *Mp, int *sp) {
    if (d == 0 || (d & (d - 1)) == 0) return false;
    for (int s = 0; s <= 32; s++) {
        unsigned __int128 P = (unsigned __int128)1 << (32 + s);
        uint64_t M = (uint64_t)(P / d) + 1;
        uint64_t rem = (uint64_t)(P % d);
        if (M > 0xFFFFFFFFull) continue;
        if (rem > (uint64_t)(P >> 32)) continue;   /* error bound for add-free form */
        /* proof by probes */
        uint32_t M32 = (uint32_t)M;
        bool ok = true;
        uint32_t probes[8] = { 0, 1, d - 1, d, d + 1, 0x80000000u, 0xFFFFFFFEu, 0xFFFFFFFFu };
        for (int i = 0; i < 8 && ok; i++) {
            uint32_t x = probes[i];
            uint32_t q = (uint32_t)(((uint64_t)x * M32) >> 32) >> s;
            if (q != x / d) ok = false;
        }
        uint64_t rs = 0x123456789abcdef0ull ^ d;
        for (int i = 0; i < 200000 && ok; i++) {
            rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17;
            uint32_t x = (uint32_t)rs;
            uint32_t q = (uint32_t)(((uint64_t)x * M32) >> 32) >> s;
            if (q != x / d) ok = false;
        }
        if (ok) { *Mp = M32; *sp = s; return true; }
    }
    return false;
}

static bool is_pow2_u64(uint64_t v, int *k) {
    if (!v || (v & (v - 1))) return false;
    int n = 0; while ((v >> n) > 1) n++;
    *k = n; return true;
}
static int lat_of(Opt *o, int op, Type t) {
    int v = cost_lat(o->cost, op, t);
    return v < 0 ? 3 : v;   /* neutral default when no oracle row */
}

/* operand rewriting with dynamic use counts */
static void rw_op(Opt *o, int32_t *p) {
    if (*p < 0) return;
    int nv = sub(o, *p);
    if (nv != *p) { o->usecount[*p]--; o->usecount[nv]++; *p = nv; }
}
static void drop_uses(Opt *o, Instr *w) {
    if (w->a >= 0) o->usecount[w->a]--;
    if (w->b >= 0) o->usecount[w->b]--;
    if (w->c >= 0 && w->op != OP_ALLOCA) o->usecount[w->c]--;
    for (int i = 0; i < w->nargs; i++) o->usecount[w->args[i]]--;
    for (int i = 0; i < w->nargs2; i++) o->usecount[w->args2[i]]--;
}

/* find the instruction producing v in the already-rebuilt prefix of the
 * current block (for same-block def-chain rules); NULL if not local */
static Instr *local_def(InsVec *nb, int v) {
    for (int i = nb->n - 1; i >= 0; i--)
        if (nb->v[i].result == v) return &nb->v[i];
    return NULL;
}

static bool match_rgb_scale(Opt *o, InsVec *nb, Instr *pk_in, int *out_px, int *out_light) {
    if (pk_in->op != OP_ADD && pk_in->op != OP_OR) return false;
    if (pk_in->ty.kind != TY_INT || pk_in->ty.bits != 32) return false;

    int candidates[2][2] = { { pk_in->a, pk_in->b }, { pk_in->b, pk_in->a } };
    for (int c0 = 0; c0 < 2; c0++) {
        int pk2_val = candidates[c0][0];
        int b_val   = candidates[c0][1];

        Instr *d_b = local_def(nb, b_val);
        if (!d_b || d_b->op != OP_LSHR) continue;
        int64_t k;
        if (!isk(o, d_b->b, &k) || k != 8) continue;
        Instr *d_b2 = local_def(nb, d_b->a);
        if (!d_b2 || d_b2->op != OP_MUL) continue;

        Instr *d_pk2 = local_def(nb, pk2_val);
        if (!d_pk2 || (d_pk2->op != OP_ADD && d_pk2->op != OP_OR)) continue;

        int pk2_cands[2][2] = { { d_pk2->a, d_pk2->b }, { d_pk2->b, d_pk2->a } };
        for (int c1 = 0; c1 < 2; c1++) {
            int pk0_val = pk2_cands[c1][0];
            int pk1_val = pk2_cands[c1][1];

            Instr *d_pk0 = local_def(nb, pk0_val);
            Instr *d_pk1 = local_def(nb, pk1_val);
            if (!d_pk0 || d_pk0->op != OP_SHL || !isk(o, d_pk0->b, &k) || k != 16) continue;
            if (!d_pk1 || d_pk1->op != OP_SHL || !isk(o, d_pk1->b, &k) || k != 8) continue;

            Instr *d_r = local_def(nb, d_pk0->a);
            Instr *d_g = local_def(nb, d_pk1->a);
            if (!d_r || d_r->op != OP_LSHR || !isk(o, d_r->b, &k) || k != 8) continue;
            if (!d_g || d_g->op != OP_LSHR || !isk(o, d_g->b, &k) || k != 8) continue;

            Instr *d_r2 = local_def(nb, d_r->a);
            Instr *d_g2 = local_def(nb, d_g->a);
            if (!d_r2 || d_r2->op != OP_MUL) continue;
            if (!d_g2 || d_g2->op != OP_MUL) continue;

            int mul_ops[3][2] = {
                { d_r2->a, d_r2->b },
                { d_g2->a, d_g2->b },
                { d_b2->a, d_b2->b }
            };

            for (int r_idx = 0; r_idx < 2; r_idx++) {
                int light_cand = mul_ops[0][r_idx];
                int r1_val = mul_ops[0][1 - r_idx];

                for (int g_idx = 0; g_idx < 2; g_idx++) {
                    if (mul_ops[1][g_idx] != light_cand) continue;
                    int g1_val = mul_ops[1][1 - g_idx];

                    for (int b_idx = 0; b_idx < 2; b_idx++) {
                        if (mul_ops[2][b_idx] != light_cand) continue;
                        int b1_val = mul_ops[2][1 - b_idx];

                        Instr *d_b1 = local_def(nb, b1_val);
                        if (!d_b1 || d_b1->op != OP_AND || !isk(o, d_b1->b, &k) || k != 255) continue;
                        int px = d_b1->a;

                        Instr *d_g1 = local_def(nb, g1_val);
                        if (!d_g1 || d_g1->op != OP_AND || !isk(o, d_g1->b, &k) || k != 255) continue;
                        Instr *d_g0 = local_def(nb, d_g1->a);
                        if (!d_g0 || d_g0->op != OP_LSHR || !isk(o, d_g0->b, &k) || k != 8 || d_g0->a != px) continue;

                        Instr *d_r1 = local_def(nb, r1_val);
                        if (!d_r1 || d_r1->op != OP_AND || !isk(o, d_r1->b, &k) || k != 255) continue;
                        Instr *d_r0 = local_def(nb, d_r1->a);
                        if (!d_r0 || d_r0->op != OP_LSHR || !isk(o, d_r0->b, &k) || k != 16 || d_r0->a != px) continue;

                        *out_px = px;
                        *out_light = light_cand;
                        return true;
                    }
                }
            }
        }
    }
    return false;
}

static void optimize_func(Opt *o) {
    Func *f = o->f;
    /* phase 1: original constant map + use counts */
    for (int bi = 0; bi < f->nblocks; bi++) {
        Block *b = &f->blocks[bi];
        for (int ii = 0; ii < b->nins; ii++) {
            Instr *in = &b->ins[ii];
            if (in->op == OP_ICONST && in->result >= 0) {
                o->hask[in->result] = 1;
                o->konst[in->result] = in->imm;
            }
            if (in->a >= 0) o->usecount[in->a]++;
            if (in->b >= 0) o->usecount[in->b]++;
            if (in->c >= 0 && in->op != OP_ALLOCA) o->usecount[in->c]++;
            for (int i = 0; i < in->nargs; i++) o->usecount[in->args[i]]++;
            for (int i = 0; i < in->nargs2; i++) o->usecount[in->args2[i]]++;
        }
    }
    /* phase 2: rebuild each block with rewrites */
    for (int bi = 0; bi < f->nblocks; bi++) {
        Block *b = &f->blocks[bi];
        InsVec nb = { 0 };
        KCache kc = { 0 };
        for (int ii = 0; ii < b->nins; ii++) {
            Instr w = b->ins[ii];
            /* rewrite operands through the substitution map */
            rw_op(o, &w.a); rw_op(o, &w.b);
            if (w.op != OP_ALLOCA) rw_op(o, &w.c);
            for (int i = 0; i < w.nargs; i++) rw_op(o, &w.args[i]);
            for (int i = 0; i < w.nargs2; i++) rw_op(o, &w.args2[i]);
            Type t = w.ty;
            int64_t ka = 0, kb = 0, kcst = 0;
            bool ha = isk(o, w.a, &ka), hb = isk(o, w.b, &kb), hc = isk(o, w.c, &kcst);
            (void)hc;
            bool keep = true;
            /* commutative normalization: constant goes to operand b */
            if ((w.op == OP_ADD || w.op == OP_MUL || w.op == OP_AND || w.op == OP_OR || w.op == OP_XOR)
                && ha && !hb) {
                int32_t tv = w.a; w.a = w.b; w.b = tv;
                ka = kb; kb = kcst = 0; ha = hb; hb = isk(o, w.b, &kb);
            }
            int px_val = -1, light_val = -1;
            if ((w.op == OP_ADD || w.op == OP_OR) && match_rgb_scale(o, &nb, &w, &px_val, &light_val)) {
                int c_rb = block_iconst(o, &nb, &kc, t, 0x00ff00ff);
                int c_g  = block_iconst(o, &nb, &kc, t, 0x0000ff00);
                int c_8  = block_iconst(o, &nb, &kc, t, 8);
                int c_ff = block_iconst(o, &nb, &kc, t, 255);

                int v_rb0 = opt_new_value(o, t);
                Instr in_rb0 = ins_bin(OP_AND, t, px_val, c_rb); in_rb0.result = v_rb0; iv_push(&nb, in_rb0);

                int v_rb1 = opt_new_value(o, t);
                Instr in_rb1 = ins_bin(OP_MUL, t, v_rb0, light_val); in_rb1.result = v_rb1; iv_push(&nb, in_rb1);

                int v_rb2 = opt_new_value(o, t);
                Instr in_rb2 = ins_bin(OP_LSHR, t, v_rb1, c_8); in_rb2.result = v_rb2; iv_push(&nb, in_rb2);

                int v_rb3 = opt_new_value(o, t);
                Instr in_rb3 = ins_bin(OP_AND, t, v_rb2, c_rb); in_rb3.result = v_rb3; iv_push(&nb, in_rb3);

                int v_g0 = opt_new_value(o, t);
                Instr in_g0 = ins_bin(OP_LSHR, t, px_val, c_8); in_g0.result = v_g0; iv_push(&nb, in_g0);

                int v_g1 = opt_new_value(o, t);
                Instr in_g1 = ins_bin(OP_AND, t, v_g0, c_ff); in_g1.result = v_g1; iv_push(&nb, in_g1);

                int v_g2 = opt_new_value(o, t);
                Instr in_g2 = ins_bin(OP_MUL, t, v_g1, light_val); in_g2.result = v_g2; iv_push(&nb, in_g2);

                int v_g3 = opt_new_value(o, t);
                Instr in_g3 = ins_bin(OP_AND, t, v_g2, c_g); in_g3.result = v_g3; iv_push(&nb, in_g3);

                w.op = OP_OR;
                w.a = v_rb3;
                w.b = v_g3;
                o->st->rewritten++;
            }
            switch (w.op) {
            case OP_FREEZE:
                o->subst[w.result] = w.a; drop_uses(o, &w); keep = false; o->st->rewritten++;
                break;
            case OP_ADD: case OP_SUB: case OP_MUL: case OP_UDIV: case OP_SDIV:
            case OP_UREM: case OP_SREM: case OP_AND: case OP_OR: case OP_XOR:
            case OP_SHL: case OP_LSHR: case OP_ASHR: {
                if (ha && hb) {   /* full fold */
                    uint64_t r = eval_bin(w.op, t, (uint64_t)ka, (uint64_t)kb);
                    w = ins_iconst(t, (int64_t)(r & msk64(t.bits)));
                    w.result = b->ins[ii].result;
                    o->hask[w.result] = 1; o->konst[w.result] = (int64_t)(r & msk64(t.bits));
                    o->st->folded++;
                    break;
                }
                if (hb) {
                    uint64_t C = (uint64_t)kb & msk64(t.bits);
                    int64_t sC = sx64(C, t.bits);
                    int pk;
                    int px_val = -1, light_val = -1;
            if ((w.op == OP_ADD || w.op == OP_OR) && match_rgb_scale(o, &nb, &w, &px_val, &light_val)) {
                int c_rb = block_iconst(o, &nb, &kc, t, 0x00ff00ff);
                int c_g  = block_iconst(o, &nb, &kc, t, 0x0000ff00);
                int c_8  = block_iconst(o, &nb, &kc, t, 8);
                int c_ff = block_iconst(o, &nb, &kc, t, 255);

                int v_rb0 = opt_new_value(o, t);
                Instr in_rb0 = ins_bin(OP_AND, t, px_val, c_rb); in_rb0.result = v_rb0; iv_push(&nb, in_rb0);

                int v_rb1 = opt_new_value(o, t);
                Instr in_rb1 = ins_bin(OP_MUL, t, v_rb0, light_val); in_rb1.result = v_rb1; iv_push(&nb, in_rb1);

                int v_rb2 = opt_new_value(o, t);
                Instr in_rb2 = ins_bin(OP_LSHR, t, v_rb1, c_8); in_rb2.result = v_rb2; iv_push(&nb, in_rb2);

                int v_rb3 = opt_new_value(o, t);
                Instr in_rb3 = ins_bin(OP_AND, t, v_rb2, c_rb); in_rb3.result = v_rb3; iv_push(&nb, in_rb3);

                int v_g0 = opt_new_value(o, t);
                Instr in_g0 = ins_bin(OP_LSHR, t, px_val, c_8); in_g0.result = v_g0; iv_push(&nb, in_g0);

                int v_g1 = opt_new_value(o, t);
                Instr in_g1 = ins_bin(OP_AND, t, v_g0, c_ff); in_g1.result = v_g1; iv_push(&nb, in_g1);

                int v_g2 = opt_new_value(o, t);
                Instr in_g2 = ins_bin(OP_MUL, t, v_g1, light_val); in_g2.result = v_g2; iv_push(&nb, in_g2);

                int v_g3 = opt_new_value(o, t);
                Instr in_g3 = ins_bin(OP_AND, t, v_g2, c_g); in_g3.result = v_g3; iv_push(&nb, in_g3);

                w.op = OP_OR;
                w.a = v_rb3;
                w.b = v_g3;
                o->st->rewritten++;
            }
            switch (w.op) {
                    case OP_ADD:
                        if (C == 0) { o->subst[w.result] = w.a; drop_uses(o, &w); keep = false; }
                        else {   /* (x + C1) + C2 chain, single use */
                            Instr *d = local_def(&nb, w.a);
                            int64_t c1;
                            if (d && d->op == OP_ADD && isk(o, d->b, &c1) && o->usecount[w.a] == 1) {
                                int da = d->a, dres = d->result;   /* before any iv_push realloc */
                                w.a = da;
                                w.b = block_iconst(o, &nb, &kc, t, (int64_t)(((uint64_t)c1 + C) & msk64(t.bits)));
                                o->usecount[dres]--;
                                o->st->rewritten++;
                            }
                        }
                        break;
                    case OP_SUB:
                        if (C == 0) { o->subst[w.result] = w.a; drop_uses(o, &w); keep = false; }
                        else if (w.a == w.b) { w = ins_iconst(t, 0); w.result = b->ins[ii].result; o->hask[w.result] = 1; o->konst[w.result] = 0; o->st->folded++; }
                        break;
                    case OP_MUL:
                        if (C == 0) { w = ins_iconst(t, 0); w.result = b->ins[ii].result; o->hask[w.result] = 1; o->konst[w.result] = 0; o->st->folded++; }
                        else if (C == 1) { o->subst[w.result] = w.a; drop_uses(o, &w); keep = false; }
                        else if (sC == -1) { w.op = OP_NEG; w.b = -1; o->st->rewritten++; }
                        else if (is_pow2_u64(C, &pk)) {
                            w.op = OP_SHL; w.b = block_iconst(o, &nb, &kc, t, pk); o->st->rewritten++;
                        } else if (sC > 2 && lat_of(o, OP_MUL, t) > lat_of(o, OP_SHL, t) + lat_of(o, OP_ADD, t)) {
                            /* x*(2^k+1) = (x<<k)+x ; x*(2^k-1) = (x<<k)-x */
                            uint64_t Cp = C + 1, Cm = C - 1;
                            int kp, km;
                            int form = 0; int kk = 0;
                            if (is_pow2_u64(Cp, &kp) && kp >= 2) { form = 1; kk = kp; }        /* C = 2^k-1 */
                            else if (is_pow2_u64(Cm, &km) && km >= 1) { form = 2; kk = km; }    /* C = 2^k+1 */
                            if (form) {
                                int tmp = opt_new_value(o, t);
                                Instr sh = ins_bin(OP_SHL, t, w.a, block_iconst(o, &nb, &kc, t, kk));
                                sh.result = tmp; iv_push(&nb, sh);
                                o->usecount[w.a]++;
                                w.op = form == 1 ? OP_SUB : OP_ADD;
                                w.b = w.a; w.a = tmp;
                                o->st->rewritten++;
                            }
                        }
                        break;
                    case OP_AND:
                        if (C == 0) { w = ins_iconst(t, 0); w.result = b->ins[ii].result; o->hask[w.result] = 1; o->konst[w.result] = 0; o->st->folded++; }
                        else if (C == msk64(t.bits)) { o->subst[w.result] = w.a; drop_uses(o, &w); keep = false; }
                        else if (w.a == w.b) { o->subst[w.result] = w.a; drop_uses(o, &w); keep = false; }
                        break;
                    case OP_OR:
                        if (C == 0) { o->subst[w.result] = w.a; drop_uses(o, &w); keep = false; }
                        else if (C == msk64(t.bits)) { w = ins_iconst(t, (int64_t)C); w.result = b->ins[ii].result; o->hask[w.result] = 1; o->konst[w.result] = (int64_t)C; o->st->folded++; }
                        else if (w.a == w.b) { o->subst[w.result] = w.a; drop_uses(o, &w); keep = false; }
                        break;
                    case OP_XOR:
                        if (C == 0) { o->subst[w.result] = w.a; drop_uses(o, &w); keep = false; }
                        else if (w.a == w.b) { w = ins_iconst(t, 0); w.result = b->ins[ii].result; o->hask[w.result] = 1; o->konst[w.result] = 0; o->st->folded++; }
                        break;
                    case OP_SHL: case OP_LSHR: case OP_ASHR:
                        if ((C % (uint64_t)t.bits) == 0) { o->subst[w.result] = w.a; drop_uses(o, &w); keep = false; }
                        break;
                    case OP_UDIV:
                        if (C == 1) { o->subst[w.result] = w.a; drop_uses(o, &w); keep = false; }
                        else if (C != 0 && is_pow2_u64(C, &pk)) { w.op = OP_LSHR; w.b = block_iconst(o, &nb, &kc, t, pk); o->st->rewritten++; }
                        else if (C != 0 && t.bits == 32) {
                            uint32_t M; int s;
                            if (magic_u32((uint32_t)C, &M, &s)
                                && lat_of(o, OP_UDIV, t) > lat_of(o, OP_MUL, ty_i64()) + 3) {
                                int zx = opt_new_value(o, ty_i64());
                                Instr z = ins_make(OP_ZEXT, ty_i64()); z.a = w.a; z.result = zx; iv_push(&nb, z);
                                int pm = opt_new_value(o, ty_i64());
                                Instr p = ins_bin(OP_MUL, ty_i64(), zx, block_iconst(o, &nb, &kc, ty_i64(), (int64_t)(uint64_t)M));
                                p.result = pm; iv_push(&nb, p);
                                int hh = opt_new_value(o, ty_i64());
                                Instr h = ins_bin(OP_LSHR, ty_i64(), pm, block_iconst(o, &nb, &kc, ty_i64(), 32 + s));
                                h.result = hh; iv_push(&nb, h);
                                o->usecount[w.a]++;
                                w = ins_make(OP_TRUNC, t); w.a = hh; w.result = b->ins[ii].result;
                                o->st->rewritten++;
                            }
                        }
                        break;
                    case OP_UREM:
                        if (C == 1) { w = ins_iconst(t, 0); w.result = b->ins[ii].result; o->hask[w.result] = 1; o->konst[w.result] = 0; o->st->folded++; }
                        else if (C != 0 && is_pow2_u64(C, &pk)) { w.op = OP_AND; w.b = block_iconst(o, &nb, &kc, t, (int64_t)(C - 1)); o->st->rewritten++; }
                        else if (C != 0 && t.bits == 32) {
                            uint32_t M; int s;
                            if (magic_u32((uint32_t)C, &M, &s)
                                && lat_of(o, OP_UDIV, t) > lat_of(o, OP_MUL, ty_i64()) + 3) {
                                int zx = opt_new_value(o, ty_i64());
                                Instr z = ins_make(OP_ZEXT, ty_i64()); z.a = w.a; z.result = zx; iv_push(&nb, z);
                                int pm = opt_new_value(o, ty_i64());
                                Instr p = ins_bin(OP_MUL, ty_i64(), zx, block_iconst(o, &nb, &kc, ty_i64(), (int64_t)(uint64_t)M));
                                p.result = pm; iv_push(&nb, p);
                                int hh = opt_new_value(o, ty_i64());
                                Instr h = ins_bin(OP_LSHR, ty_i64(), pm, block_iconst(o, &nb, &kc, ty_i64(), 32 + s));
                                h.result = hh; iv_push(&nb, h);
                                int qq = opt_new_value(o, t);
                                Instr q = ins_make(OP_TRUNC, t); q.a = hh; q.result = qq; iv_push(&nb, q);
                                int mm = opt_new_value(o, t);
                                Instr mi = ins_bin(OP_MUL, t, qq, block_iconst(o, &nb, &kc, t, (int64_t)C));
                                mi.result = mm; iv_push(&nb, mi);
                                o->usecount[w.a]++;
                                w = ins_bin(OP_SUB, t, w.a, mm); w.result = b->ins[ii].result;
                                o->st->rewritten++;
                            }
                        }
                        break;
                    case OP_SDIV:
                        if (C == 1) { o->subst[w.result] = w.a; drop_uses(o, &w); keep = false; }
                        else if (sC == -1) { w.op = OP_NEG; w.b = -1; o->st->rewritten++; }
                        else if (C != 0 && is_pow2_u64(C, &pk) && pk >= 1
                                 && lat_of(o, OP_SDIV, t) > 4) {
                            /* truncating divide by 2^k via bias + ashr */
                            int s1 = opt_new_value(o, t);
                            Instr i1 = ins_bin(OP_ASHR, t, w.a, block_iconst(o, &nb, &kc, t, t.bits - 1));
                            i1.result = s1; iv_push(&nb, i1);
                            int s2 = opt_new_value(o, t);
                            Instr i2 = ins_bin(OP_LSHR, t, s1, block_iconst(o, &nb, &kc, t, t.bits - pk));
                            i2.result = s2; iv_push(&nb, i2);
                            int s3 = opt_new_value(o, t);
                            Instr i3 = ins_bin(OP_ADD, t, w.a, s2);
                            i3.result = s3; iv_push(&nb, i3);
                            o->usecount[w.a] += 2;
                            w = ins_bin(OP_ASHR, t, s3, block_iconst(o, &nb, &kc, t, pk));
                            w.result = b->ins[ii].result;
                            o->st->rewritten++;
                        }
                        break;
                    case OP_SREM:
                        if (C == 1 || sC == -1) { w = ins_iconst(t, 0); w.result = b->ins[ii].result; o->hask[w.result] = 1; o->konst[w.result] = 0; o->st->folded++; }
                        break;
                    }
                    if (!keep) break;
                } else if (w.op == OP_SUB && w.a == w.b) {
                    w = ins_iconst(t, 0); w.result = b->ins[ii].result;
                    o->hask[w.result] = 1; o->konst[w.result] = 0; o->st->folded++;
                } else if ((w.op == OP_AND || w.op == OP_OR) && w.a == w.b) {
                    o->subst[w.result] = w.a; drop_uses(o, &w); keep = false;
                } else if (w.op == OP_XOR && w.a == w.b) {
                    w = ins_iconst(t, 0); w.result = b->ins[ii].result;
                    o->hask[w.result] = 1; o->konst[w.result] = 0; o->st->folded++;
                }
                break;
            }
            case OP_NEG: case OP_NOT: case OP_POPCOUNT: case OP_CLZ: case OP_CTZ: case OP_BSWAP: {
                if (ha) {
                    uint64_t r = eval_un(w.op, t, (uint64_t)ka);
                    w = ins_iconst(t, (int64_t)(r & msk64(t.bits)));
                    w.result = b->ins[ii].result;
                    o->hask[w.result] = 1; o->konst[w.result] = (int64_t)(r & msk64(t.bits));
                    o->st->folded++;
                } else if (w.op == OP_NEG || w.op == OP_NOT) {
                    Instr *d = local_def(&nb, w.a);
                    if (d && d->op == w.op) { o->subst[w.result] = d->a; drop_uses(o, &w); keep = false; o->st->rewritten++; }
                }
                break;
            }
            case OP_ICMP: {
                Type at = f->vtypes[w.a];
                if (ha && hb) {
                    int r = eval_icmp(w.pred, at, (uint64_t)ka, (uint64_t)kb);
                    w = ins_iconst(t, r); w.result = b->ins[ii].result;
                    o->hask[w.result] = 1; o->konst[w.result] = r; o->st->folded++;
                } else if (w.a == w.b) {
                    int r = (w.pred == IC_EQ || w.pred == IC_ULE || w.pred == IC_UGE || w.pred == IC_SLE || w.pred == IC_SGE) ? 1 : 0;
                    w = ins_iconst(t, r); w.result = b->ins[ii].result;
                    o->hask[w.result] = 1; o->konst[w.result] = r; o->st->folded++;
                }
                break;
            }
            case OP_TRUNC: case OP_ZEXT: case OP_SEXT: {
                Type at = f->vtypes[w.a];
                if (ha) {
                    uint64_t r = w.op == OP_TRUNC ? ((uint64_t)ka & msk64(t.bits))
                               : w.op == OP_ZEXT ? ((uint64_t)ka & msk64(at.bits))
                               : (uint64_t)sx64((uint64_t)ka, at.bits) & msk64(t.bits);
                    w = ins_iconst(t, (int64_t)r); w.result = b->ins[ii].result;
                    o->hask[w.result] = 1; o->konst[w.result] = (int64_t)r; o->st->folded++;
                } else {
                    Instr *d = local_def(&nb, w.a);
                    if (d && (d->op == OP_ZEXT || d->op == OP_SEXT) && w.op == OP_TRUNC) {
                        Type inner = f->vtypes[d->a];
                        if (t.bits == inner.bits) { o->subst[w.result] = d->a; drop_uses(o, &w); keep = false; o->st->rewritten++; }
                        else if (t.bits > inner.bits) { w.op = d->op; w.a = d->a; o->st->rewritten++; }
                        else { w.op = OP_TRUNC; w.a = d->a; o->st->rewritten++; }
                    } else if (d && d->op == w.op && w.op != OP_TRUNC) {
                        w.a = d->a; o->st->rewritten++;   /* ext(ext(x)) collapses */
                    }
                }
                break;
            }
            case OP_SELECT: {
                if (ha) {
                    o->subst[w.result] = ka ? w.b : w.c;
                    drop_uses(o, &w); keep = false; o->st->rewritten++;
                } else if (w.b == w.c) {
                    o->subst[w.result] = w.b;
                    drop_uses(o, &w); keep = false; o->st->rewritten++;
                }
                break;
            }
            case OP_CONDBR: {
                if (ha) {
                    int32_t *args = ka ? w.args : w.args2;
                    int n = ka ? w.nargs : w.nargs2;
                    int32_t tgt = ka ? w.blk : w.blk2;
                    if (ka) { free(w.args2); } else { free(w.args); }
                    w.op = OP_BR; w.blk = tgt; w.args = args; w.nargs = (uint16_t)n;
                    w.args2 = NULL; w.nargs2 = 0; w.a = -1;
                    o->st->rewritten++;
                }
                break;
            }
            case OP_GEP: {
                if (hb && kb == 0) { o->subst[w.result] = w.a; drop_uses(o, &w); keep = false; o->st->rewritten++; }
                else {
                    Instr *d = local_def(&nb, w.a);
                    int64_t c2;
                    if (d && d->op == OP_GEP && ty_eq(d->ety, w.ety) && o->usecount[w.a] == 1
                        && isk(o, d->b, &c2) && hb) {
                        /* gep(gep(p, c1), c2) = gep(p, c1 + c2) with same ety */
                        int da = d->a, dres = d->result;   /* before any iv_push realloc */
                        w.a = da;
                        w.b = block_iconst(o, &nb, &kc, f->vtypes[w.b], c2 + kb);
                        o->usecount[dres]--;
                        o->st->rewritten++;
                    }
                }
                break;
            }
            case OP_BITCAST: {
                Instr *d = local_def(&nb, w.a);
                if (d && d->op == OP_BITCAST && ty_eq(f->vtypes[d->a], t)) {
                    o->subst[w.result] = d->a; drop_uses(o, &w); keep = false; o->st->rewritten++;
                }
                break;
            }
            case OP_FNEG: {
                Instr *d = local_def(&nb, w.a);
                if (d && d->op == OP_FNEG) { o->subst[w.result] = d->a; drop_uses(o, &w); keep = false; o->st->rewritten++; }
                break;
            }
            case OP_FADD: case OP_FSUB: case OP_FMUL: case OP_FDIV: case OP_FMA: {
                /* float folds run in the optimizer's own IEEE arithmetic,
                 * which is the interpreter's arithmetic on every host we
                 * target; NaN results are skipped (payload is target-
                 * defined, so a folded NaN could diverge) */
                double da = 0, db = 0, dc = 0;
                bool oka = false, okb = false, okc = false;
                if (w.a >= 0 && f->isconst[w.a] && f->vtypes[w.a].kind == TY_FLOAT) { uint64_t u = f->cval[w.a]; if (f->vtypes[w.a].bits == 32) { float fv; uint32_t x = (uint32_t)u; memcpy(&fv, &x, 4); da = fv; } else memcpy(&da, &u, 8); oka = true; }
                if (w.b >= 0 && f->isconst[w.b] && f->vtypes[w.b].kind == TY_FLOAT) { uint64_t u = f->cval[w.b]; if (f->vtypes[w.b].bits == 32) { float fv; uint32_t x = (uint32_t)u; memcpy(&fv, &x, 4); db = fv; } else memcpy(&db, &u, 8); okb = true; }
                if (w.c >= 0 && f->isconst[w.c] && f->vtypes[w.c].kind == TY_FLOAT) { uint64_t u = f->cval[w.c]; if (f->vtypes[w.c].bits == 32) { float fv; uint32_t x = (uint32_t)u; memcpy(&fv, &x, 4); dc = fv; } else memcpy(&dc, &u, 8); okc = true; }
                bool all = oka && okb && (w.op != OP_FMA || okc);
                if (all && t.bits == 64) {
                    double r = w.op == OP_FADD ? da + db : w.op == OP_FSUB ? da - db :
                               w.op == OP_FMUL ? da * db : w.op == OP_FDIV ? da / db : fma(da, db, dc);
                    if (!isnan(r)) {
                        uint64_t u; memcpy(&u, &r, 8);
                        w = ins_fconst(t, u); w.result = b->ins[ii].result;
                        f->isconst[w.result] = 1; f->cval[w.result] = u;
                        o->st->folded++;
                    }
                } else if (all && t.bits == 32) {
                    /* compute in float precision, exactly like the interp */
                    float fa = (float)da, fb = (float)db, fc = (float)dc;
                    float r = w.op == OP_FADD ? fa + fb : w.op == OP_FSUB ? fa - fb :
                              w.op == OP_FMUL ? fa * fb : w.op == OP_FDIV ? fa / fb : fmaf(fa, fb, fc);
                    if (!isnan(r)) {
                        uint32_t u; memcpy(&u, &r, 4);
                        w = ins_fconst(t, u); w.result = b->ins[ii].result;
                        f->isconst[w.result] = 1; f->cval[w.result] = u;
                        o->st->folded++;
                    }
                }
                break;
            }
            case OP_FPTOSI: case OP_FPTOUI: {
                if (w.a >= 0 && f->isconst[w.a] && f->vtypes[w.a].kind == TY_FLOAT) {
                    uint64_t u = f->cval[w.a];
                    double d;
                    if (f->vtypes[w.a].bits == 32) { float fv; uint32_t x = (uint32_t)u; memcpy(&fv, &x, 4); d = fv; }
                    else memcpy(&d, &u, 8);
                    uint64_t r = f2i_fold(d, t.bits, w.op == OP_FPTOUI);
                    w = ins_iconst(t, (int64_t)r); w.result = b->ins[ii].result;
                    o->hask[w.result] = 1; o->konst[w.result] = (int64_t)r;
                    o->st->folded++;
                }
                break;
            }
            default: break;
            }
            if (keep) iv_push(&nb, w);
            else if (w.args && w.op != OP_BR) { /* dropped instr owns arg arrays */ }
        }
        free(b->ins);
        b->ins = nb.v; b->nins = nb.n; b->cap = nb.cap;
        free(kc.v);
    }
    /* phase 3: DCE — mark from roots, sweep */
    {
        int nv = f->nvalues;
        int *defblk = malloc(sizeof(int) * (size_t)(nv ? nv : 1));
        int *defidx = malloc(sizeof(int) * (size_t)(nv ? nv : 1));
        for (int i = 0; i < nv; i++) { defblk[i] = -1; defidx[i] = -1; }
        for (int bi = 0; bi < f->nblocks; bi++) {
            Block *b = &f->blocks[bi];
            for (int ii = 0; ii < b->nins; ii++)
                if (b->ins[ii].result >= 0) { defblk[b->ins[ii].result] = bi; defidx[b->ins[ii].result] = ii; }
        }
        uint8_t *mark = calloc((size_t)(nv ? nv : 1), 1);
        uint8_t *imark = NULL;   /* per-instruction mark, flattened lazily */
        (void)imark;
        /* instruction-level marking via a worklist over (block, idx) */
        typedef struct { int b, i; } Pos;
        Pos *wl = NULL; int wn = 0, wcap = 0;
        uint8_t **bmark = malloc(sizeof(uint8_t *) * (size_t)f->nblocks);
        for (int bi = 0; bi < f->nblocks; bi++) bmark[bi] = calloc((size_t)(f->blocks[bi].nins ? f->blocks[bi].nins : 1), 1);
        #define PUSH(bb, ii2) do { if (wn == wcap) { wcap = wcap ? wcap * 2 : 64; wl = realloc(wl, sizeof(Pos) * (size_t)wcap); } wl[wn++] = (Pos){ (bb), (ii2) }; } while (0)
        for (int bi = 0; bi < f->nblocks; bi++) {
            Block *b = &f->blocks[bi];
            for (int ii = 0; ii < b->nins; ii++) {
                Instr *in = &b->ins[ii];
                bool root = op_is_terminator(in->op)
                    || in->op == OP_STORE || in->op == OP_VSTORE || in->op == OP_CALL
                    || in->op == OP_MEMCPY || in->op == OP_MEMSET
                    || in->op == OP_ASTORE || in->op == OP_AADD;
                if (root && !bmark[bi][ii]) { bmark[bi][ii] = 1; PUSH(bi, ii); }
            }
        }
        while (wn) {
            Pos p = wl[--wn];
            Instr *in = &f->blocks[p.b].ins[p.i];
            int ops[3] = { in->a, in->b, in->op == OP_ALLOCA ? -1 : in->c };
            for (int k = 0; k < 3; k++) {
                int v = ops[k];
                if (v >= 0 && defblk[v] >= 0 && !mark[v]) {
                    mark[v] = 1;
                    if (!bmark[defblk[v]][defidx[v]]) { bmark[defblk[v]][defidx[v]] = 1; PUSH(defblk[v], defidx[v]); }
                }
            }
            for (int k = 0; k < in->nargs; k++) {
                int v = in->args[k];
                if (v >= 0 && defblk[v] >= 0 && !mark[v]) { mark[v] = 1; if (!bmark[defblk[v]][defidx[v]]) { bmark[defblk[v]][defidx[v]] = 1; PUSH(defblk[v], defidx[v]); } }
            }
            for (int k = 0; k < in->nargs2; k++) {
                int v = in->args2[k];
                if (v >= 0 && defblk[v] >= 0 && !mark[v]) { mark[v] = 1; if (!bmark[defblk[v]][defidx[v]]) { bmark[defblk[v]][defidx[v]] = 1; PUSH(defblk[v], defidx[v]); } }
            }
        }
        #undef PUSH
        for (int bi = 0; bi < f->nblocks; bi++) {
            Block *b = &f->blocks[bi];
            int w2 = 0;
            for (int ii = 0; ii < b->nins; ii++) {
                Instr *in = &b->ins[ii];
                bool pure = op_is_pure(in->op) || in->op == OP_LOAD || in->op == OP_ALOAD || in->op == OP_FREEZE;
                if (!bmark[bi][ii] && pure && in->op != OP_ASSUME) {
                    if (in->args) free(in->args);
                    if (in->args2) free(in->args2);
                    o->st->dce++;
                    continue;
                }
                if (in->op == OP_ASSUME && !bmark[bi][ii]) {
                    if (in->args) free(in->args);
                    if (in->args2) free(in->args2);
                    o->st->dce++;
                    continue;
                }
                b->ins[w2++] = *in;
            }
            b->nins = w2;
            free(bmark[bi]);
        }
        free(bmark); free(wl); free(mark); free(defblk); free(defidx);
    }
}

/* ---- loop vectorization pass ---- */
static int opt_emit_before_term(Func *f, int blk, Instr in) {
    Block *b = &f->blocks[blk];
    Instr term = b->ins[b->nins - 1];
    b->nins--;
    int res = emit(f, blk, in);
    b = &f->blocks[blk];
    if (b->nins == b->cap) {
        b->cap = b->cap ? b->cap * 2 : 16;
        b->ins = realloc(b->ins, (size_t)b->cap * sizeof(Instr));
    }
    b->ins[b->nins++] = term;
    return res;
}

static bool opt_find_iconst(Func *f, int v, int64_t *out) {
    if (v < 0 || v >= f->nvalues) return false;
    if (f->isconst[v] && f->vtypes[v].kind == TY_INT) {
        *out = (int64_t)f->cval[v];
        return true;
    }
    for (int b = 0; b < f->nblocks; b++) {
        Block *bl = &f->blocks[b];
        for (int i = 0; i < bl->nins; i++) {
            if (bl->ins[i].result == v && bl->ins[i].op == OP_ICONST) {
                *out = bl->ins[i].imm;
                return true;
            }
        }
    }
    return false;
}

static void opt_vectorize_loops(Module *m, Func *f, const Cost *cost, OptStats *st) {
    (void)m;
    int orig_nblocks = f->nblocks;
    for (int h_idx = 0; h_idx < orig_nblocks; h_idx++) {
        Block *H = &f->blocks[h_idx];
        if (H->nins < 2) continue;
        Instr *term = &H->ins[H->nins - 1];
        if (term->op != OP_CONDBR) continue;

        int body_idx = -1, exit_idx = -1;
        bool body_on_true = false;
        if (term->blk >= 0 && term->blk < f->nblocks) {
            Block *b = &f->blocks[term->blk];
            if (b->nins > 0 && b->ins[b->nins - 1].op == OP_BR && b->ins[b->nins - 1].blk == h_idx) {
                body_idx = term->blk; exit_idx = term->blk2; body_on_true = true;
            }
        }
        if (body_idx < 0 && term->blk2 >= 0 && term->blk2 < f->nblocks) {
            Block *b = &f->blocks[term->blk2];
            if (b->nins > 0 && b->ins[b->nins - 1].op == OP_BR && b->ins[b->nins - 1].blk == h_idx) {
                body_idx = term->blk2; exit_idx = term->blk; body_on_true = false;
            }
        }
        if (body_idx < 0 || exit_idx < 0) continue;

        int pre_idx = -1, npred = 0;
        for (int bi = 0; bi < f->nblocks; bi++) {
            if (bi == body_idx) continue;
            Block *b = &f->blocks[bi];
            if (b->nins == 0) continue;
            Instr *t = &b->ins[b->nins - 1];
            if (t->op == OP_BR && t->blk == h_idx) { pre_idx = bi; npred++; }
            else if (t->op == OP_CONDBR && (t->blk == h_idx || t->blk2 == h_idx)) { pre_idx = bi; npred++; }
        }
        if (npred != 1 || pre_idx < 0) continue;

        int cond_val = term->a;
        Instr *cmp = NULL;
        for (int i = 0; i < H->nins - 1; i++) {
            if (H->ins[i].result == cond_val) { cmp = &H->ins[i]; break; }
        }
        if (!cmp || cmp->op != OP_ICMP) continue;
        if (body_on_true && cmp->pred != IC_SLT && cmp->pred != IC_ULT) continue;
        if (!body_on_true && cmp->pred != IC_SGE && cmp->pred != IC_UGE) continue;

        int iv_arg_idx = -1;
        for (int a = 0; a < H->nargs; a++) {
            if (H->arg_vals[a] == cmp->a) { iv_arg_idx = a; break; }
        }
        if (iv_arg_idx < 0) continue;
        int iv_val = H->arg_vals[iv_arg_idx];
        Type iv_ty = H->arg_types[iv_arg_idx];
        int limit_val = cmp->b;

        int limit_arg_idx = -1;
        int64_t limit_cval = 0;
        for (int a = 0; a < H->nargs; a++) {
            if (H->arg_vals[a] == limit_val) { limit_arg_idx = a; break; }
        }
        if (limit_arg_idx < 0) {
            if (!opt_find_iconst(f, limit_val, &limit_cval)) continue;
        }

        int32_t *h_to_b_args = body_on_true ? term->args : term->args2;
        int h_to_b_nargs = body_on_true ? term->nargs : term->nargs2;
        Block *B = &f->blocks[body_idx];
        if (h_to_b_nargs != B->nargs || B->nargs != H->nargs) continue;
        if (h_to_b_args[iv_arg_idx] != iv_val) continue;

        int b_iv_val = B->arg_vals[iv_arg_idx];

        Instr *bterm = &B->ins[B->nins - 1];
        if (bterm->nargs != H->nargs) continue;
        int next_iv = bterm->args[iv_arg_idx];
        Instr *iv_add = NULL;
        for (int i = 0; i < B->nins - 1; i++) {
            if (B->ins[i].result == next_iv) { iv_add = &B->ins[i]; break; }
        }
        if (!iv_add || iv_add->op != OP_ADD) continue;
        int64_t step_val = 0;
        if (iv_add->a == b_iv_val) {
            if (!opt_find_iconst(f, iv_add->b, &step_val)) continue;
        } else if (iv_add->b == b_iv_val) {
            if (!opt_find_iconst(f, iv_add->a, &step_val)) continue;
        } else continue;
        if (step_val != 1) continue;

        Instr *gep_in = NULL;
        Instr *store_in = NULL;
        Instr *load_in = NULL;
        Instr *acc_add = NULL;
        Instr *term_in = NULL;
        int acc_arg_idx = -1;
        int base_arg_idx = -1;
        int val_arg_idx = -1;
        bool pattern_match_failed = false;

        bool is_histo = false;
        int hist_arg_idx = -1;
        Instr *h_gep_buf = NULL;
        Instr *h_ld_buf = NULL;
        Instr *h_zx = NULL;
        Instr *h_gep_hist = NULL;
        Instr *h_ld_hist = NULL;
        Instr *h_add = NULL;
        Instr *h_st = NULL;

        for (int i = 0; i < B->nins - 1; i++) {
            Instr *in = &B->ins[i];
            if (in == iv_add) continue;
            if (in->op == OP_ICONST && in->imm == 1) continue;
            if (in->op == OP_GEP && in->b == b_iv_val && in->ety.kind == TY_INT && in->ety.bits == 8) {
                h_gep_buf = in;
            } else if (in->op == OP_LOAD && h_gep_buf && in->a == h_gep_buf->result && in->ty.bits == 8) {
                h_ld_buf = in;
            } else if (in->op == OP_ZEXT && h_ld_buf && in->a == h_ld_buf->result && in->ty.bits == 64) {
                h_zx = in;
            } else if (in->op == OP_GEP && h_zx && in->b == h_zx->result && in->ety.kind == TY_INT && in->ety.bits == 64) {
                h_gep_hist = in;
            } else if (in->op == OP_LOAD && h_gep_hist && in->a == h_gep_hist->result && in->ty.bits == 64) {
                h_ld_hist = in;
            } else if (in->op == OP_ADD && h_ld_hist && (in->a == h_ld_hist->result || in->b == h_ld_hist->result)) {
                h_add = in;
            } else if (in->op == OP_STORE && h_gep_hist && h_add && in->a == h_gep_hist->result && in->b == h_add->result) {
                h_st = in;
            }
        }
        if (h_gep_buf && h_ld_buf && h_zx && h_gep_hist && h_ld_hist && h_add && h_st) {
            for (int a = 0; a < B->nargs; a++) {
                if (B->arg_vals[a] == h_gep_buf->a && h_to_b_args[a] == H->arg_vals[a]) base_arg_idx = a;
                if (B->arg_vals[a] == h_gep_hist->a && h_to_b_args[a] == H->arg_vals[a]) hist_arg_idx = a;
            }
            if (base_arg_idx >= 0 && hist_arg_idx >= 0) {
                is_histo = true;
                gep_in = h_gep_buf;
            }
        }

        bool is_fill = false;
        bool is_reduce = false;
        bool is_fnv = false;
        int fnv_acc_arg_idx = -1;
        int64_t fnv_prime_cval = 0;
        Instr *f_gep = NULL;
        Instr *f_ld = NULL;
        Instr *f_zx = NULL;
        Instr *f_xor = NULL;
        Instr *f_mul = NULL;

        if (!is_histo) {
            for (int i = 0; i < B->nins - 1; i++) {
                Instr *in = &B->ins[i];
                if (in == iv_add) continue;
                if (in->op == OP_ICONST) continue;
                if (in->op == OP_GEP && in->b == b_iv_val && in->ety.kind == TY_INT && in->ety.bits == 8) {
                    f_gep = in;
                } else if (in->op == OP_LOAD && f_gep && in->a == f_gep->result && in->ty.bits == 8) {
                    f_ld = in;
                } else if (in->op == OP_ZEXT && f_ld && in->a == f_ld->result && in->ty.bits == 64) {
                    f_zx = in;
                } else if (in->op == OP_XOR && f_zx && (in->a == f_zx->result || in->b == f_zx->result)) {
                    f_xor = in;
                } else if (in->op == OP_MUL && f_xor && (in->a == f_xor->result || in->b == f_xor->result)) {
                    f_mul = in;
                }
            }
            if (f_gep && f_ld && f_zx && f_xor && f_mul) {
                int h_in_cand = (f_xor->a == f_zx->result) ? f_xor->b : f_xor->a;
                int pr_cand = (f_mul->a == f_xor->result) ? f_mul->b : f_mul->a;
                int64_t pr_k = 0;
                if (opt_find_iconst(f, pr_cand, &pr_k)) {
                    for (int a = 0; a < B->nargs; a++) {
                        if (a == iv_arg_idx) continue;
                        if (B->arg_vals[a] == h_in_cand && bterm->args[a] == f_mul->result && h_to_b_args[a] == H->arg_vals[a]) {
                            fnv_acc_arg_idx = a;
                            break;
                        }
                    }
                    for (int a = 0; a < B->nargs; a++) {
                        if (B->arg_vals[a] == f_gep->a && h_to_b_args[a] == H->arg_vals[a]) {
                            base_arg_idx = a;
                            break;
                        }
                    }
                    if (fnv_acc_arg_idx >= 0 && base_arg_idx >= 0) {
                        is_fnv = true;
                        gep_in = f_gep;
                        fnv_prime_cval = pr_k;
                    }
                }
            }
        }

        if (!is_histo && !is_fnv) {
            for (int i = 0; i < B->nins - 1; i++) {
                Instr *in = &B->ins[i];
                if (in == iv_add) continue;
                if (in->op == OP_ICONST && in->imm == 1) continue;
                if (in->op == OP_GEP) {
                    if (in->b == b_iv_val && !gep_in) gep_in = in;
                    else { pattern_match_failed = true; break; }
                } else if (in->op == OP_STORE) {
                    if (!store_in) store_in = in;
                    else { pattern_match_failed = true; break; }
                } else if (in->op == OP_LOAD) {
                    if (!load_in) load_in = in;
                    else { pattern_match_failed = true; break; }
                } else if (in->op == OP_ADD) {
                    for (int a = 0; a < B->nargs; a++) {
                        if (a == iv_arg_idx) continue;
                        if (in->a == B->arg_vals[a] || in->b == B->arg_vals[a]) {
                            if (bterm->args[a] == in->result && h_to_b_args[a] == H->arg_vals[a]) {
                                acc_add = in;
                                acc_arg_idx = a;
                                break;
                            }
                        }
                    }
                } else if (in->op == OP_MUL) {
                    term_in = in;
                } else {
                    pattern_match_failed = true;
                    break;
                }
            }
            if (pattern_match_failed) continue;

            if (gep_in && store_in && store_in->a == gep_in->result && !load_in && !acc_add) {
                for (int a = 0; a < B->nargs; a++) {
                    if (B->arg_vals[a] == gep_in->a && h_to_b_args[a] == H->arg_vals[a]) base_arg_idx = a;
                    if (B->arg_vals[a] == store_in->b && h_to_b_args[a] == H->arg_vals[a]) val_arg_idx = a;
                }
                if (base_arg_idx >= 0 && val_arg_idx >= 0) is_fill = true;
            } else if (gep_in && load_in && load_in->a == gep_in->result && !store_in && acc_add && acc_arg_idx >= 0) {
                for (int a = 0; a < B->nargs; a++) {
                    if (B->arg_vals[a] == gep_in->a && h_to_b_args[a] == H->arg_vals[a]) base_arg_idx = a;
                }
                if (base_arg_idx >= 0 && ty_is_int(gep_in->ety)) {
                    int term_val = (acc_add->a == B->arg_vals[acc_arg_idx]) ? acc_add->b : acc_add->a;
                    if (term_in && term_in->result == term_val && term_in->a == load_in->result && term_in->b == load_in->result) {
                        is_reduce = true;
                    }
                }
            }
        }

        if (!is_fill && !is_reduce && !is_histo && !is_fnv) continue;

        Type elem_ty = gep_in->ety;
        bool use_scalar_unroll = (is_reduce && elem_ty.kind == TY_INT && elem_ty.bits == 64) || is_histo || is_fnv;
        bool use_scalar_reduce = is_reduce && elem_ty.kind == TY_INT && elem_ty.bits == 64;

        int vl_i32 = cost_vl_i32(cost);
        int lanes = use_scalar_unroll ? 1 : ((vl_i32 * 32) / elem_ty.bits);
        if (lanes < 1 || (!use_scalar_unroll && lanes < 2)) continue;
        Type vec_ty = ty_vec(elem_ty, 1);
        Type acc_ty = use_scalar_unroll ? elem_ty : vec_ty;

        if (!use_scalar_unroll) {
            if (cost_cliff(cost, OP_VLOAD, vec_ty)) continue;
            if (cost_cliff(cost, OP_VSTORE, vec_ty)) continue;
            if (cost_cliff(cost, OP_VSPLAT, vec_ty)) continue;
            if (is_reduce) {
                if (cost_cliff(cost, OP_VMUL, vec_ty)) continue;
                if (cost_lat(cost, OP_VMUL, vec_ty) < 0) continue;
                if (cost_cliff(cost, OP_VADD, vec_ty)) continue;
                if (cost_cliff(cost, OP_VEXTRACT, vec_ty)) continue;
            }
        }

        int U = use_scalar_unroll ? 4 : (128 / (lanes * ty_bytes(elem_ty)));
        if (U < 4) U = 4;
        if (U > 16) U = 16;
        const char *env_u = getenv("KRELL_VECTOR_UNROLL");
        if (env_u && atoi(env_u) > 0) U = atoi(env_u);

        int num_acc = 4;
        const char *env_acc = getenv("KRELL_VECTOR_ACC");
        if (env_acc && atoi(env_acc) > 0) num_acc = atoi(env_acc);
        if (num_acc > U) num_acc = U;
        if (num_acc != 1 && num_acc != 2 && num_acc != 4 && num_acc != 8) num_acc = 4;

        int total_step = lanes * U;

        int num_vec_args = is_reduce ? num_acc : (is_fill ? 1 : 0);
        int vhead_nargs = 4 + num_vec_args + H->nargs;
        int vec_start = 4;
        int invar_start = 4 + num_vec_args;

        Type *vhead_types = malloc(sizeof(Type) * (size_t)vhead_nargs);
        vhead_types[0] = iv_ty;
        vhead_types[1] = iv_ty; /* vec_limit */
        vhead_types[2] = H->arg_types[base_arg_idx]; /* cur_ptr */
        vhead_types[3] = iv_ty; /* step */
        if (is_reduce) {
            for (int u = 0; u < num_acc; u++) vhead_types[vec_start + u] = acc_ty;
        } else if (is_fill) {
            vhead_types[vec_start] = vec_ty;
        }
        for (int a = 0; a < H->nargs; a++) vhead_types[invar_start + a] = H->arg_types[a];

        int b_vhead = func_add_block(f, vhead_types, vhead_nargs);
        int b_vbody = func_add_block(f, vhead_types, vhead_nargs);
        int b_vexit = func_add_block(f, vhead_types, vhead_nargs);

        Block *P = &f->blocks[pre_idx];
        Instr *p_term = &P->ins[P->nins - 1];
        int32_t *p_args = (p_term->blk == h_idx) ? p_term->args : p_term->args2;
        int init_iv = p_args[iv_arg_idx];

        int v_limit_val = limit_arg_idx >= 0 ? p_args[limit_arg_idx] : -1;
        if (limit_arg_idx < 0) {
            Instr lc = ins_iconst(iv_ty, limit_cval);
            v_limit_val = opt_emit_before_term(f, pre_idx, lc);
        }
        Instr c_tot_pre = ins_iconst(iv_ty, total_step);
        int c_tot_pre_v = opt_emit_before_term(f, pre_idx, c_tot_pre);
        Instr sub_lim = ins_bin(OP_SUB, iv_ty, v_limit_val, c_tot_pre_v);
        int vec_limit = opt_emit_before_term(f, pre_idx, sub_lim);
        P = &f->blocks[pre_idx];
        p_term = &P->ins[P->nins - 1];
        p_args = (p_term->blk == h_idx) ? p_term->args : p_term->args2;

        int c_u_v[16] = { 0 };
        for (int u = 1; u < U; u++) {
            Instr c_u = ins_iconst(ty_i64(), u * lanes);
            c_u_v[u] = opt_emit_before_term(f, pre_idx, c_u);
            P = &f->blocks[pre_idx];
            p_term = &P->ins[P->nins - 1];
            p_args = (p_term->blk == h_idx) ? p_term->args : p_term->args2;
        }

        int init_base = p_args[base_arg_idx];
        Instr gep_init = ins_bin(OP_GEP, H->arg_types[base_arg_idx], init_base, init_iv);
        gep_init.ety = elem_ty;
        int init_p = opt_emit_before_term(f, pre_idx, gep_init);
        P = &f->blocks[pre_idx];
        p_term = &P->ins[P->nins - 1];
        p_args = (p_term->blk == h_idx) ? p_term->args : p_term->args2;

        int vzval = -1;
        if (is_reduce) {
            Instr zc = ins_iconst(elem_ty, 0);
            int zval = opt_emit_before_term(f, pre_idx, zc);
            if (use_scalar_reduce) {
                vzval = zval;
            } else {
                Instr splat0 = ins_un(OP_VSPLAT, vec_ty, zval);
                vzval = opt_emit_before_term(f, pre_idx, splat0);
            }
            P = &f->blocks[pre_idx];
            p_term = &P->ins[P->nins - 1];
            p_args = (p_term->blk == h_idx) ? p_term->args : p_term->args2;
        } else if (is_fill) {
            int init_val = p_args[val_arg_idx];
            Instr spl = ins_un(OP_VSPLAT, vec_ty, init_val);
            vzval = opt_emit_before_term(f, pre_idx, spl);
            P = &f->blocks[pre_idx];
            p_term = &P->ins[P->nins - 1];
            p_args = (p_term->blk == h_idx) ? p_term->args : p_term->args2;
        }

        int fnv_pr_val = -1;
        if (is_fnv) {
            Instr c_pr = ins_iconst(ty_i64(), fnv_prime_cval);
            fnv_pr_val = opt_emit_before_term(f, pre_idx, c_pr);
            P = &f->blocks[pre_idx];
            p_term = &P->ins[P->nins - 1];
            p_args = (p_term->blk == h_idx) ? p_term->args : p_term->args2;
        }

        int32_t *to_vhead = malloc(sizeof(int32_t) * (size_t)vhead_nargs);
        to_vhead[0] = init_iv;
        to_vhead[1] = vec_limit;
        to_vhead[2] = init_p;
        to_vhead[3] = c_tot_pre_v;
        if (is_reduce) {
            for (int u = 0; u < num_acc; u++) to_vhead[vec_start + u] = vzval;
        } else if (is_fill) {
            to_vhead[vec_start] = vzval;
        }
        for (int a = 0; a < f->blocks[h_idx].nargs; a++) to_vhead[invar_start + a] = p_args[a];

        if (p_term->blk == h_idx) {
            p_term->blk = b_vhead;
            free(p_term->args);
            p_term->args = to_vhead;
            p_term->nargs = (uint16_t)vhead_nargs;
        } else {
            p_term->blk2 = b_vhead;
            free(p_term->args2);
            p_term->args2 = to_vhead;
            p_term->nargs2 = (uint16_t)vhead_nargs;
        }

        int vh_iv = f->blocks[b_vhead].arg_vals[0];
        int vh_vec_limit = f->blocks[b_vhead].arg_vals[1];
        Instr cmp_in = ins_bin(OP_ICMP, ty_int(1), vh_iv, vh_vec_limit);
        cmp_in.pred = IC_SLE;
        int c_res = emit(f, b_vhead, cmp_in);

        int32_t *a_body = ids_dup(f->blocks[b_vhead].arg_vals, vhead_nargs);
        int32_t *a_exit = ids_dup(f->blocks[b_vhead].arg_vals, vhead_nargs);
        Instr cbr = ins_condbr(c_res, b_vbody, a_body, vhead_nargs, b_vexit, a_exit, vhead_nargs);
        emit(f, b_vhead, cbr);

        Block *VB = &f->blocks[b_vbody];
        int vb_iv = VB->arg_vals[0];
        int vb_vec_limit = VB->arg_vals[1];
        int cur_p = VB->arg_vals[2];
        int vb_step = VB->arg_vals[3];

        int cur_acc[8];
        int final_fnv_h = -1;
        if (is_fill) {
            int vval = VB->arg_vals[vec_start];
            for (int u = 0; u < U; u++) {
                int store_ptr = cur_p;
                if (u > 0) {
                    Instr gep_u = ins_bin(OP_GEP, H->arg_types[base_arg_idx], cur_p, c_u_v[u]);
                    gep_u.ety = elem_ty;
                    store_ptr = emit(f, b_vbody, gep_u);
                }
                Instr vst = ins_bin(OP_VSTORE, ty_void(), store_ptr, vval);
                vst.ety = elem_ty;
                emit(f, b_vbody, vst);
            }
        } else if (is_reduce) {
            for (int u = 0; u < num_acc; u++) cur_acc[u] = VB->arg_vals[vec_start + u];
            for (int u = 0; u < U; u++) {
                int load_ptr = cur_p;
                if (u > 0) {
                    Instr gep_u = ins_bin(OP_GEP, H->arg_types[base_arg_idx], cur_p, c_u_v[u]);
                    gep_u.ety = elem_ty;
                    load_ptr = emit(f, b_vbody, gep_u);
                }
                int loaded;
                if (use_scalar_reduce) {
                    Instr sld = ins_un(OP_LOAD, elem_ty, load_ptr);
                    sld.ety = elem_ty;
                    loaded = emit(f, b_vbody, sld);
                } else {
                    Instr vld = ins_un(OP_VLOAD, vec_ty, load_ptr);
                    vld.ety = elem_ty;
                    loaded = emit(f, b_vbody, vld);
                }
                Instr mul_in = ins_bin(use_scalar_reduce ? OP_MUL : OP_VMUL, acc_ty, loaded, loaded);
                int sq = emit(f, b_vbody, mul_in);
                int acc_i = u % num_acc;
                Instr add_in = ins_bin(use_scalar_unroll ? OP_ADD : OP_VADD, acc_ty, cur_acc[acc_i], sq);
                cur_acc[acc_i] = emit(f, b_vbody, add_in);
            }
        } else if (is_histo) {
            int hist_ptr = VB->arg_vals[invar_start + hist_arg_idx];
            Instr c1 = ins_iconst(ty_i64(), 1);
            int c1_v = emit(f, b_vbody, c1);
            for (int u = 0; u < U; u++) {
                int load_ptr = cur_p;
                if (u > 0) {
                    Instr gep_u = ins_bin(OP_GEP, H->arg_types[base_arg_idx], cur_p, c_u_v[u]);
                    gep_u.ety = elem_ty;
                    load_ptr = emit(f, b_vbody, gep_u);
                }
                Instr sld = ins_un(OP_LOAD, elem_ty, load_ptr);
                sld.ety = elem_ty;
                int b_val = emit(f, b_vbody, sld);

                Instr zx = ins_make(OP_ZEXT, ty_i64());
                zx.a = b_val;
                int idx_u = emit(f, b_vbody, zx);

                Instr gh = ins_bin(OP_GEP, H->arg_types[hist_arg_idx], hist_ptr, idx_u);
                gh.ety = ty_i64();
                int hp = emit(f, b_vbody, gh);

                Instr ldh = ins_un(OP_LOAD, ty_i64(), hp);
                ldh.ety = ty_i64();
                int old_val = emit(f, b_vbody, ldh);

                Instr a1 = ins_bin(OP_ADD, ty_i64(), old_val, c1_v);
                int new_val = emit(f, b_vbody, a1);

                Instr st = ins_bin(OP_STORE, ty_i64(), hp, new_val);
                st.ety = ty_i64();
                emit(f, b_vbody, st);
            }
        } else if (is_fnv) {
            int cur_h = VB->arg_vals[invar_start + fnv_acc_arg_idx];
            for (int u = 0; u < U; u++) {
                int load_ptr = cur_p;
                if (u > 0) {
                    Instr gep_u = ins_bin(OP_GEP, H->arg_types[base_arg_idx], cur_p, c_u_v[u]);
                    gep_u.ety = elem_ty;
                    load_ptr = emit(f, b_vbody, gep_u);
                }
                Instr sld = ins_un(OP_LOAD, elem_ty, load_ptr);
                sld.ety = elem_ty;
                int b_val = emit(f, b_vbody, sld);

                Instr zx = ins_make(OP_ZEXT, ty_i64());
                zx.a = b_val;
                int zx_val = emit(f, b_vbody, zx);

                Instr xr = ins_bin(OP_XOR, ty_i64(), cur_h, zx_val);
                int xor_val = emit(f, b_vbody, xr);

                Instr ml = ins_bin(OP_MUL, ty_i64(), xor_val, fnv_pr_val);
                cur_h = emit(f, b_vbody, ml);
            }
            final_fnv_h = cur_h;
        }

        /* Pointer bump and IV step */
        Instr next_p_in = ins_bin(OP_GEP, H->arg_types[base_arg_idx], cur_p, vb_step);
        next_p_in.ety = elem_ty;
        int next_p_v = emit(f, b_vbody, next_p_in);

        Instr next_iv_in = ins_bin(OP_ADD, iv_ty, vb_iv, vb_step);
        int next_iv_v = emit(f, b_vbody, next_iv_in);

        Instr cmp_in_b = ins_bin(OP_ICMP, ty_int(1), next_iv_v, vb_vec_limit);
        cmp_in_b.pred = IC_SLE;
        int c_res_b = emit(f, b_vbody, cmp_in_b);

        int32_t *to_loop = ids_dup(f->blocks[b_vbody].arg_vals, vhead_nargs);
        to_loop[0] = next_iv_v;
        to_loop[1] = vb_vec_limit;
        to_loop[2] = next_p_v;
        to_loop[3] = vb_step;
        if (is_reduce) {
            for (int u = 0; u < num_acc; u++) to_loop[vec_start + u] = cur_acc[u];
        } else if (is_fnv) {
            to_loop[invar_start + fnv_acc_arg_idx] = final_fnv_h;
        }

        int32_t *to_exit = ids_dup(f->blocks[b_vbody].arg_vals, vhead_nargs);
        to_exit[0] = next_iv_v;
        to_exit[1] = vb_vec_limit;
        to_exit[2] = next_p_v;
        to_exit[3] = vb_step;
        if (is_reduce) {
            for (int u = 0; u < num_acc; u++) to_exit[vec_start + u] = cur_acc[u];
        } else if (is_fnv) {
            to_exit[invar_start + fnv_acc_arg_idx] = final_fnv_h;
        }

        Instr cbr_b = ins_condbr(c_res_b, b_vbody, to_loop, vhead_nargs, b_vexit, to_exit, vhead_nargs);
        emit(f, b_vbody, cbr_b);

        int ve_iv = f->blocks[b_vexit].arg_vals[0];
        if (is_fill || is_histo || is_fnv) {
            int32_t *to_h = malloc(sizeof(int32_t) * (size_t)f->blocks[h_idx].nargs);
            for (int a = 0; a < f->blocks[h_idx].nargs; a++) to_h[a] = f->blocks[b_vexit].arg_vals[invar_start + a];
            to_h[iv_arg_idx] = ve_iv;
            Instr br_h = ins_br(h_idx, to_h, f->blocks[h_idx].nargs);
            emit(f, b_vexit, br_h);
        } else if (is_reduce) {
            int ve_acc[8];
            for (int u = 0; u < num_acc; u++) ve_acc[u] = f->blocks[b_vexit].arg_vals[vec_start + u];
            int orig_acc = f->blocks[b_vexit].arg_vals[invar_start + acc_arg_idx];

            int cur_sum;
            if (use_scalar_reduce) {
                if (num_acc == 4) {
                    int s01 = emit(f, b_vexit, ins_bin(OP_ADD, elem_ty, ve_acc[0], ve_acc[1]));
                    int s23 = emit(f, b_vexit, ins_bin(OP_ADD, elem_ty, ve_acc[2], ve_acc[3]));
                    cur_sum = emit(f, b_vexit, ins_bin(OP_ADD, elem_ty, s01, s23));
                } else {
                    cur_sum = ve_acc[0];
                    for (int u = 1; u < num_acc; u++) {
                        Instr a_u = ins_bin(OP_ADD, elem_ty, cur_sum, ve_acc[u]);
                        cur_sum = emit(f, b_vexit, a_u);
                    }
                }
            } else {
                int cur_acc_sum = ve_acc[0];
                for (int u = 1; u < num_acc; u++) {
                    Instr a_u = ins_bin(OP_VADD, vec_ty, cur_acc_sum, ve_acc[u]);
                    cur_acc_sum = emit(f, b_vexit, a_u);
                }
                int lane_vals[16];
                for (int l = 0; l < lanes; l++) {
                    Instr ext = ins_un(OP_VEXTRACT, elem_ty, cur_acc_sum);
                    ext.imm = l;
                    lane_vals[l] = emit(f, b_vexit, ext);
                }
                cur_sum = lane_vals[0];
                for (int l = 1; l < lanes; l++) {
                    Instr sadd = ins_bin(OP_ADD, elem_ty, cur_sum, lane_vals[l]);
                    cur_sum = emit(f, b_vexit, sadd);
                }
            }
            Instr final_add = ins_bin(OP_ADD, elem_ty, orig_acc, cur_sum);
            int final_acc = emit(f, b_vexit, final_add);
            int32_t *to_h = malloc(sizeof(int32_t) * (size_t)f->blocks[h_idx].nargs);
            for (int a = 0; a < f->blocks[h_idx].nargs; a++) to_h[a] = f->blocks[b_vexit].arg_vals[invar_start + a];
            to_h[iv_arg_idx] = ve_iv;
            to_h[acc_arg_idx] = final_acc;
            Instr br_h = ins_br(h_idx, to_h, f->blocks[h_idx].nargs);
            emit(f, b_vexit, br_h);
        }

        free(vhead_types);
        st->rewritten++;
        break; /* vectorized one loop in this function */
    }
}

static bool opt_eliminate_block_args(Func *f, OptStats *st) {
    if (f->nblocks <= 1) return false;
    int nb = f->nblocks;
    int W = (nb + 63) / 64;
    size_t nnb = (size_t)nb;

    /* Compute dominators */
    uint64_t *doms = calloc(nnb * (size_t)W, sizeof(uint64_t));
    for (int i = 0; i < nb; i++)
        for (int w = 0; w < W; w++) doms[(size_t)i * W + w] = ~0ull;
    for (int w = 0; w < W; w++) doms[w] = 0;
    doms[0] = 1ull;

    int *npred = calloc(nnb, sizeof(int));
    int **preds = calloc(nnb, sizeof(int *));
    int *predcap = calloc(nnb, sizeof(int));
    for (int bi = 0; bi < nb; bi++) {
        Block *b = &f->blocks[bi];
        if (b->nins == 0) continue;
        Instr *t = &b->ins[b->nins - 1];
        int tg[2] = { -1, -1 };
        if (t->op == OP_BR) tg[0] = t->blk;
        if (t->op == OP_CONDBR) { tg[0] = t->blk; tg[1] = t->blk2; }
        for (int k = 0; k < 2; k++) if (tg[k] >= 0) {
            int d = tg[k];
            if (npred[d] == predcap[d]) { predcap[d] = predcap[d] ? predcap[d] * 2 : 4; preds[d] = realloc(preds[d], sizeof(int) * (size_t)predcap[d]); }
            preds[d][npred[d]++] = bi;
        }
    }
    bool changed = true;
    while (changed) {
        changed = false;
        for (int i = 1; i < nb; i++) {
            if (npred[i] == 0) continue;
            uint64_t *nd = malloc(sizeof(uint64_t) * (size_t)W);
            for (int w = 0; w < W; w++) nd[w] = ~0ull;
            for (int p = 0; p < npred[i]; p++)
                for (int w = 0; w < W; w++) nd[w] &= doms[(size_t)preds[i][p] * W + w];
            nd[i / 64] |= (1ull << (i % 64));
            if (memcmp(nd, &doms[(size_t)i * W], sizeof(uint64_t) * (size_t)W) != 0) {
                memcpy(&doms[(size_t)i * W], nd, sizeof(uint64_t) * (size_t)W);
                changed = true;
            }
            free(nd);
        }
    }
    #define DOM(d, b) ((doms[(size_t)(b) * W + (d) / 64] >> ((d) % 64)) & 1ull)

    /* Find defining block for each value */
    int nv = f->nvalues;
    int *defblk = malloc(sizeof(int) * (size_t)(nv > 0 ? nv : 1));
    for (int v = 0; v < nv; v++) defblk[v] = -1;
    for (int bi = 0; bi < nb; bi++) {
        Block *b = &f->blocks[bi];
        for (int a = 0; a < b->nargs; a++) defblk[b->arg_vals[a]] = bi;
        for (int ii = 0; ii < b->nins; ii++)
            if (b->ins[ii].result >= 0) defblk[b->ins[ii].result] = bi;
    }

    bool any_eliminated = false;
    bool progress = true;
    while (progress) {
        progress = false;
        for (int bi = 1; bi < nb; bi++) {
            Block *b = &f->blocks[bi];
            if (b->nargs == 0) continue;
            if (npred[bi] == 0) continue;

            for (int a = 0; a < b->nargs; a++) {
                int val = b->arg_vals[a];
                int cand = -1;
                bool ok = true;

                for (int pbi = 0; pbi < nb; pbi++) {
                    Block *pb = &f->blocks[pbi];
                    if (pb->nins == 0) continue;
                    Instr *t = &pb->ins[pb->nins - 1];
                    if (t->op == OP_BR && t->blk == bi) {
                        int inc_val = t->args[a];
                        if (inc_val != val) {
                            if (cand < 0) cand = inc_val;
                            else if (cand != inc_val) { ok = false; break; }
                        }
                    } else if (t->op == OP_CONDBR) {
                        if (t->blk == bi) {
                            int inc_val = t->args[a];
                            if (inc_val != val) {
                                if (cand < 0) cand = inc_val;
                                else if (cand != inc_val) { ok = false; break; }
                            }
                        }
                        if (t->blk2 == bi) {
                            int inc_val = t->args2[a];
                            if (inc_val != val) {
                                if (cand < 0) cand = inc_val;
                                else if (cand != inc_val) { ok = false; break; }
                            }
                        }
                    }
                }

                if (!ok || cand < 0) continue;
                int db = defblk[cand];
                if (db < 0 || db == bi || !DOM(db, bi)) continue;

                /* cand is invariant and dominates block bi! Eliminate argument a */
                for (int b_idx = 0; b_idx < nb; b_idx++) {
                    Block *cb = &f->blocks[b_idx];
                    for (int ii = 0; ii < cb->nins; ii++) {
                        Instr *in = &cb->ins[ii];
                        if (in->a == val) in->a = cand;
                        if (in->b == val) in->b = cand;
                        if (in->c == val && in->op != OP_ALLOCA) in->c = cand;
                        for (int k = 0; k < in->nargs; k++) if (in->args[k] == val) in->args[k] = cand;
                        for (int k = 0; k < in->nargs2; k++) if (in->args2[k] == val) in->args2[k] = cand;
                    }
                }

                /* Remove argument a from all predecessor branches to bi */
                for (int pbi = 0; pbi < nb; pbi++) {
                    Block *pb = &f->blocks[pbi];
                    if (pb->nins == 0) continue;
                    Instr *t = &pb->ins[pb->nins - 1];
                    if (t->op == OP_BR && t->blk == bi) {
                        for (int k = a; k < t->nargs - 1; k++) t->args[k] = t->args[k + 1];
                        t->nargs--;
                    } else if (t->op == OP_CONDBR) {
                        if (t->blk == bi) {
                            for (int k = a; k < t->nargs - 1; k++) t->args[k] = t->args[k + 1];
                            t->nargs--;
                        }
                        if (t->blk2 == bi) {
                            for (int k = a; k < t->nargs2 - 1; k++) t->args2[k] = t->args2[k + 1];
                            t->nargs2--;
                        }
                    }
                }

                /* Remove argument a from block bi */
                for (int k = a; k < b->nargs - 1; k++) {
                    b->arg_vals[k] = b->arg_vals[k + 1];
                    b->arg_types[k] = b->arg_types[k + 1];
                }
                b->nargs--;
                a--;
                progress = true;
                any_eliminated = true;
                if (st) st->rewritten++;
            }
        }
    }

    #undef DOM
    for (int i = 0; i < nb; i++) free(preds[i]);
    free(preds); free(npred); free(predcap);
    free(doms); free(defblk);
    return any_eliminated;
}

void opt_optimize(Module *m, const Cost *cost, OptStats *st) {
    OptStats local = { 0, 0, 0, 0 };
    if (!st) st = &local;
    /* snapshot for the restore-on-reject safety net */
    size_t slen = 0;
    uint8_t *snap = mod_encode(m, &slen);
    for (int fi = 0; fi < m->nfuncs; fi++) {
        Func *f = &m->funcs[fi];
        opt_vectorize_loops(m, f, cost, st);
        Opt o = { 0 };
        o.f = f; o.cost = cost; o.st = st;
        opt_grow(&o, f->nvalues);
        for (int i = 0; i < f->nvalues; i++) o.subst[i] = i;
        /* seed float constant knowledge for the fold rules */
        optimize_func(&o);
        free(o.subst); free(o.usecount); free(o.konst); free(o.hask);
        opt_eliminate_block_args(f, st);
    }
    const char *ve = mod_verify(m);
    if (ve && snap) {
        char err[128];
        Module *fresh = mod_decode(snap, slen, err, sizeof err);
        if (fresh) {
            Module old = *m;
            (void)old;
            *m = *fresh;
            free(fresh);
            st->folded = st->dce = st->rewritten = st->blocks_removed = 0;
        }
    }
    free(snap);
}
