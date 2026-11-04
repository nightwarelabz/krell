/* Krell — LLVM IR lowering lane (the release/performance backend).
 * Emits textual LLVM IR (LLVM >= 15, opaque pointers) for the whole
 * module; clang/llc do register allocation and instruction selection.
 * Krell's total semantics are preserved against LLVM's poison rules:
 *  - divisions get a select guard (divisor 0, and INT_MIN/-1);
 *  - shifts mask their amount before shifting;
 *  - fptosi/fptoui get a saturation select chain (NaN -> 0);
 *  - selects only ever select the poison arm when it is not chosen.
 * Block arguments lower to phi nodes; a condbr whose two targets are
 * the same block is split through a synthetic trampoline block.
 * Internal calls use fastcc; externs use the C ABI. */
#include "krell.h"
#include <stdarg.h>
#include <math.h>

typedef struct {
    FILE *out;
    Module *m;
    Func *f;
    int vl;
    int lbl;              /* fresh SSA counter for temporaries */
    int bi;               /* current block index */
    int split_idx;        /* division splits so far in this block */
    int *splits;          /* per block: number of division splits */
    int ntramp;           /* trampoline counter */
    int *alias;           /* value -> aliased value (freeze) */
    Instr **def;          /* value -> defining instruction */
    /* trampoline table: (from_block, target) -> trampoline id */
    struct { int from, tgt, id; } tramps[64];
    int ntr;
    /* intrinsic declaration needs */
    bool need_ctpop[65], need_ctlz[65], need_cttz[65], need_bswap[65];
    bool need_fshl[129], need_fshr[129];
    bool need_fma32, need_fma64, need_fabs32, need_fabs64;
    bool need_memcpy, need_memset;
    const bool *addrtaken;   /* internal funcs whose address escapes (funcptr) */
} Ctx;

static void E(Ctx *c, const char *fmt, ...) {
    va_list ap; va_start(ap, fmt);
    vfprintf(c->out, fmt, ap);
    va_end(ap);
    fputc('\n', c->out);
}

static void ty_str(Ctx *c, Type t, char *buf, size_t cap) {
    switch (t.kind) {
    case TY_VOID: snprintf(buf, cap, "void"); break;
    case TY_INT: snprintf(buf, cap, "i%d", t.bits); break;
    case TY_FLOAT: snprintf(buf, cap, "%s", t.bits == 32 ? "float" : "double"); break;
    case TY_PTR: snprintf(buf, cap, "ptr"); break;
    case TY_VEC: {
        char eb[32];
        Type e = ty_elem(t);
        if (e.kind == TY_FLOAT) snprintf(eb, sizeof eb, "%s", e.bits == 32 ? "float" : "double");
        else snprintf(eb, sizeof eb, "i%d", e.bits);
        snprintf(buf, cap, "<%d x %s>", ty_lanes(t, c->vl), eb);
        break;
    }
    default: snprintf(buf, cap, "i64"); break;
    }
}

/* operand text for a value: literal for constants, %v<id> otherwise */
static void op_str(Ctx *c, int v, char *buf, size_t cap) {
    while (v >= 0 && c->alias[v] != v) v = c->alias[v];
    Instr *d = (v >= 0 && v < c->f->nvalues) ? c->def[v] : NULL;
    if (d && d->op == OP_ICONST) {
        snprintf(buf, cap, "%lld", (long long)d->imm);
        return;
    }
    if (d && d->op == OP_FCONST) {
        if (d->ty.bits == 32) {
            float fv; uint32_t x = (uint32_t)d->imm; memcpy(&fv, &x, 4);
            double dv = fv; uint64_t u; memcpy(&u, &dv, 8);
            snprintf(buf, cap, "0x%016llx", (unsigned long long)u);
        } else {
            snprintf(buf, cap, "0x%016llx", (unsigned long long)d->imm);
        }
        return;
    }
    snprintf(buf, cap, "%%v%d", v);
}
static int fresh(Ctx *c) { return ++c->lbl; }

/* emit `  %tN = <rhs>` and return N */
static int emit_tmp(Ctx *c, const char *fmt, ...) {
    int n = fresh(c);
    fprintf(c->out, "  %%t%d = ", n);
    va_list ap; va_start(ap, fmt);
    vfprintf(c->out, fmt, ap);
    va_end(ap);
    fputc('\n', c->out);
    return n;
}

/* convert an integer value to i64 in SSA (sext for gep indices, zext
 * for byte counts) */
static void to_i64(Ctx *c, int v, Type vt, bool sext, char *buf, size_t cap) {
    if (vt.kind == TY_INT && vt.bits == 64) { op_str(c, v, buf, cap); return; }
    char ob[80]; op_str(c, v, ob, sizeof ob);
    int n = emit_tmp(c, "%s i%d %s to i64", sext ? "sext" : "zext", vt.bits, ob);
    snprintf(buf, cap, "%%t%d", n);
}

/* ---- division guards: returns temp id of the guarded result ----
 * The guard must be CONTROL FLOW, not a select: LLVM lowers an
 * unconditional udiv/sdiv to the hardware divide, which traps on a
 * zero divisor before any select can discard the poison. The current
 * block is split: [tests] -> br valid, div-block, cont-block(phi). */
static int guarded_div(Ctx *c, Instr *in, const char *opname, bool is_signed, bool is_rem) {
    Type t = in->ty;
    char tb[48], ab[80], bb[80];
    ty_str(c, t, tb, sizeof tb);
    op_str(c, in->a, ab, sizeof ab);
    op_str(c, in->b, bb, sizeof bb);
    int nz = emit_tmp(c, "icmp ne %s %s, 0", tb, bb);
    int valid = nz;
    char fb[96];
    snprintf(fb, sizeof fb, "0");
    if (is_signed) {
        /* bad = (a == INT_MIN && b == -1); bad gives a for div, 0 for rem */
        int64_t mn = t.bits == 64 ? INT64_MIN : -(1ll << (t.bits - 1));
        int ea = emit_tmp(c, "icmp eq %s %s, %lld", tb, ab, (long long)mn);
        int eb = emit_tmp(c, "icmp eq %s %s, -1", tb, bb);
        int bad = emit_tmp(c, "and i1 %%t%d, %%t%d", ea, eb);
        int notbad = emit_tmp(c, "xor i1 %%t%d, 1", bad);
        valid = emit_tmp(c, "and i1 %%t%d, %%t%d", nz, notbad);
        if (!is_rem) {
            int fbt = emit_tmp(c, "select i1 %%t%d, %s %s, %s 0", bad, tb, ab, tb);
            snprintf(fb, sizeof fb, "%%t%d", fbt);
        }
    }
    int idx = ++c->split_idx;
    char prev[40], dlbl[40], clbl[40];
    if (idx == 1) snprintf(prev, sizeof prev, "b%d", c->bi);
    else snprintf(prev, sizeof prev, "c%d_%d", c->bi, idx - 1);
    snprintf(dlbl, sizeof dlbl, "d%d_%d", c->bi, idx);
    snprintf(clbl, sizeof clbl, "c%d_%d", c->bi, idx);
    E(c, "  br i1 %%t%d, label %%%s, label %%%s", valid, dlbl, clbl);
    E(c, "%s:", dlbl);
    int q = emit_tmp(c, "%s %s %s, %s", opname, tb, ab, bb);
    E(c, "  br label %%%s", clbl);
    E(c, "%s:", clbl);
    int r = emit_tmp(c, "phi %s [ %%t%d, %%%s ], [ %s, %%%s ]", tb, q, dlbl, fb, prev);
    return r;
}

/* saturating float->int: returns temp id */
static int sat_f2i(Ctx *c, Instr *in, bool unsig) {
    Type t = in->ty;                 /* int result */
    Type st = c->f->vtypes[in->a];   /* float source */
    char stb[48], tb[48], ab[80];
    ty_str(c, st, stb, sizeof stb);
    ty_str(c, t, tb, sizeof tb);
    op_str(c, in->a, ab, sizeof ab);
    const char *cv = unsig ? "fptoui" : "fptosi";
    int q = emit_tmp(c, "%s %s %s to %s", cv, stb, ab, tb);
    int uno = emit_tmp(c, "fcmp uno %s %s, 0.000000e+00", stb, ab);
    int r;
    if (!unsig) {
        double hi = ldexp(1.0, t.bits - 1);    /* 2^(bits-1), exact */
        uint64_t hb; { double d = hi; memcpy(&hb, &d, 8); }
        uint64_t lb2; { double d = -hi; memcpy(&lb2, &d, 8); }
        /* compare in the source precision */
        char hib[32], lob[32];
        if (st.bits == 32) {
            float fh = (float)hi; uint32_t x; memcpy(&x, &fh, 4);
            double dd = fh; uint64_t u; memcpy(&u, &dd, 8);
            snprintf(hib, sizeof hib, "0x%016llx", (unsigned long long)u);
            float fl = (float)(-hi); memcpy(&x, &fl, 4);
            dd = fl; memcpy(&u, &dd, 8);
            snprintf(lob, sizeof lob, "0x%016llx", (unsigned long long)u);
        } else {
            snprintf(hib, sizeof hib, "0x%016llx", (unsigned long long)hb);
            snprintf(lob, sizeof lob, "0x%016llx", (unsigned long long)lb2);
        }
        int hiok = emit_tmp(c, "fcmp olt %s %s, %s", stb, ab, hib);
        int look = emit_tmp(c, "fcmp oge %s %s, %s", stb, ab, lob);
        int ok = emit_tmp(c, "and i1 %%t%d, %%t%d", hiok, look);
        int isneg = emit_tmp(c, "fcmp olt %s %s, 0.000000e+00", stb, ab);
        int64_t mx = t.bits == 64 ? INT64_MAX : (int64_t)((1ull << (t.bits - 1)) - 1);
        int64_t mn = t.bits == 64 ? INT64_MIN : -(1ll << (t.bits - 1));
        int sat = emit_tmp(c, "select i1 %%t%d, %s %lld, %s %lld", isneg, tb, (long long)mn, tb, (long long)mx);
        r = emit_tmp(c, "select i1 %%t%d, %s %%t%d, %s %%t%d", ok, tb, q, tb, sat);
    } else {
        double hi = ldexp(1.0, t.bits);        /* 2^bits */
        char hib[32], neg1[32];
        if (st.bits == 32) {
            float fh = (float)hi; double dd = fh; uint64_t u; memcpy(&u, &dd, 8);
            snprintf(hib, sizeof hib, "0x%016llx", (unsigned long long)u);
            float fm = -1.0f; dd = fm; memcpy(&u, &dd, 8);
            snprintf(neg1, sizeof neg1, "0x%016llx", (unsigned long long)u);
        } else {
            uint64_t u; double dd = hi; memcpy(&u, &dd, 8);
            snprintf(hib, sizeof hib, "0x%016llx", (unsigned long long)u);
            dd = -1.0; memcpy(&u, &dd, 8);
            snprintf(neg1, sizeof neg1, "0x%016llx", (unsigned long long)u);
        }
        int hiok = emit_tmp(c, "fcmp olt %s %s, %s", stb, ab, hib);
        int look = emit_tmp(c, "fcmp ogt %s %s, %s", stb, ab, neg1);
        int ok = emit_tmp(c, "and i1 %%t%d, %%t%d", hiok, look);
        int isbig = emit_tmp(c, "fcmp oge %s %s, %s", stb, ab, hib);
        uint64_t mx = t.bits == 64 ? ~0ull : ((1ull << t.bits) - 1);
        int sat = emit_tmp(c, "select i1 %%t%d, %s %llu, %s 0", isbig, tb, (unsigned long long)mx, tb);
        r = emit_tmp(c, "select i1 %%t%d, %s %%t%d, %s %%t%d", ok, tb, q, tb, sat);
    }
    int res = emit_tmp(c, "select i1 %%t%d, %s 0, %s %%t%d", uno, tb, tb, r);
    return res;
}

static int tramp_of(Ctx *c, int from, int tgt) {
    for (int i = 0; i < c->ntr; i++)
        if (c->tramps[i].from == from && c->tramps[i].tgt == tgt) return c->tramps[i].id;
    return -1;
}

static void emit_instr(Ctx *c, Instr *in) {
    Func *f = c->f;
    Type t = in->ty;
    char tb[48], ab[80], bb[80], cb[80];
    ty_str(c, t, tb, sizeof tb);
    if (in->a >= 0) op_str(c, in->a, ab, sizeof ab);
    if (in->b >= 0) op_str(c, in->b, bb, sizeof bb);
    if (in->c >= 0 && in->op != OP_ALLOCA) op_str(c, in->c, cb, sizeof cb);
    const char *R = NULL;
    char rbuf[16];
    if (in->result >= 0) { snprintf(rbuf, sizeof rbuf, "%%v%d", in->result); R = rbuf; }
    switch (in->op) {
    case OP_ICONST: case OP_FCONST: break;   /* folded into operands */
    case OP_FREEZE: break;                   /* alias recorded */
    case OP_ASSUME: break;
    case OP_ADD: E(c, "  %s = add %s %s, %s", R, tb, ab, bb); break;
    case OP_SUB: E(c, "  %s = sub %s %s, %s", R, tb, ab, bb); break;
    case OP_MUL: E(c, "  %s = mul %s %s, %s", R, tb, ab, bb); break;
    case OP_NEG: E(c, "  %s = sub %s 0, %s", R, tb, ab); break;
    case OP_AND: E(c, "  %s = and %s %s, %s", R, tb, ab, bb); break;
    case OP_OR:  E(c, "  %s = or %s %s, %s", R, tb, ab, bb); break;
    case OP_XOR: E(c, "  %s = xor %s %s, %s", R, tb, ab, bb); break;
    case OP_NOT: E(c, "  %s = xor %s %s, -1", R, tb, ab); break;
    case OP_UDIV: { int r = guarded_div(c, in, "udiv", false, false); E(c, "  %s = add %s %%t%d, 0", R, tb, r); break; }
    case OP_SDIV: { int r = guarded_div(c, in, "sdiv", true, false); E(c, "  %s = add %s %%t%d, 0", R, tb, r); break; }
    case OP_UREM: { int r = guarded_div(c, in, "urem", false, true); E(c, "  %s = add %s %%t%d, 0", R, tb, r); break; }
    case OP_SREM: { int r = guarded_div(c, in, "srem", true, true); E(c, "  %s = add %s %%t%d, 0", R, tb, r); break; }
    case OP_SHL: case OP_LSHR: case OP_ASHR: {
        int amt = emit_tmp(c, "and i%d %s, %d", t.bits, bb, t.bits - 1);
        const char *nm = in->op == OP_SHL ? "shl" : in->op == OP_LSHR ? "lshr" : "ashr";
        E(c, "  %s = %s %s %s, %%t%d", R, nm, tb, ab, amt);
        break;
    }
    case OP_ICMP: {
        static const char *P[10] = { "eq","ne","ult","ule","ugt","uge","slt","sle","sgt","sge" };
        char atb[48]; ty_str(c, f->vtypes[in->a], atb, sizeof atb);
        E(c, "  %s = icmp %s %s %s, %s", R, P[in->pred], atb, ab, bb);
        break;
    }
    case OP_POPCOUNT: case OP_CLZ: case OP_CTZ: {
        const char *nm = in->op == OP_POPCOUNT ? "ctpop" : in->op == OP_CLZ ? "ctlz" : "cttz";
        if (in->op == OP_POPCOUNT) c->need_ctpop[t.bits] = true;
        if (in->op == OP_CLZ) c->need_ctlz[t.bits] = true;
        if (in->op == OP_CTZ) c->need_cttz[t.bits] = true;
        if (in->op == OP_POPCOUNT) E(c, "  %s = call %s @llvm.ctpop.i%d(%s %s)", R, tb, t.bits, tb, ab);
        else E(c, "  %s = call %s @llvm.%s.i%d(%s %s, i1 false)", R, tb, nm, t.bits, tb, ab);
        break;
    }
    case OP_BSWAP: {
        if (t.bits == 8) { E(c, "  %s = add %s %s, 0", R, tb, ab); }
        else {
            c->need_bswap[t.bits] = true;
            E(c, "  %s = call %s @llvm.bswap.i%d(%s %s)", R, tb, t.bits, tb, ab);
        }
        break;
    }
    case OP_TRUNC: { char sb[48]; ty_str(c, f->vtypes[in->a], sb, sizeof sb); E(c, "  %s = trunc %s %s to %s", R, sb, ab, tb); break; }
    case OP_ZEXT:  { char sb[48]; ty_str(c, f->vtypes[in->a], sb, sizeof sb); E(c, "  %s = zext %s %s to %s", R, sb, ab, tb); break; }
    case OP_SEXT:  { char sb[48]; ty_str(c, f->vtypes[in->a], sb, sizeof sb); E(c, "  %s = sext %s %s to %s", R, sb, ab, tb); break; }
    case OP_FADD: E(c, "  %s = fadd %s %s, %s", R, tb, ab, bb); break;
    case OP_FSUB: E(c, "  %s = fsub %s %s, %s", R, tb, ab, bb); break;
    case OP_FMUL: E(c, "  %s = fmul %s %s, %s", R, tb, ab, bb); break;
    case OP_FDIV: E(c, "  %s = fdiv %s %s, %s", R, tb, ab, bb); break;
    case OP_FNEG: E(c, "  %s = fneg %s %s", R, tb, ab); break;
    case OP_FABS: {
        if (t.bits == 32) c->need_fabs32 = true; else c->need_fabs64 = true;
        E(c, "  %s = call %s @llvm.fabs.f%d(%s %s)", R, tb, t.bits, tb, ab);
        break;
    }
    case OP_FMA: {
        if (t.bits == 32) c->need_fma32 = true; else c->need_fma64 = true;
        E(c, "  %s = call %s @llvm.fma.f%d(%s %s, %s %s, %s %s)", R, tb, t.bits, tb, ab, tb, bb, tb, cb);
        break;
    }
    case OP_FSHL: case OP_FSHR: {
        const char *nm = in->op == OP_FSHL ? "fshl" : "fshr";
        if (in->op == OP_FSHL) c->need_fshl[t.bits] = true; else c->need_fshr[t.bits] = true;
        E(c, "  %s = call %s @llvm.%s.i%d(%s %s, %s %s, %s %s)", R, tb, nm, t.bits, tb, ab, tb, bb, tb, cb);
        break;
    }
    case OP_FCMP: {
        static const char *P[14] = { "oeq","one","olt","ole","ogt","oge","ueq","une","ult","ule","ugt","uge","ord","uno" };
        char stb[48]; ty_str(c, f->vtypes[in->a], stb, sizeof stb);
        E(c, "  %s = fcmp %s %s %s, %s", R, P[in->pred], stb, ab, bb);
        break;
    }
    case OP_FTRUNC: E(c, "  %s = fptrunc double %s to float", R, ab); break;
    case OP_FEXT:   E(c, "  %s = fpext float %s to double", R, ab); break;
    case OP_FPTOSI: { int r = sat_f2i(c, in, false); E(c, "  %s = add %s %%t%d, 0", R, tb, r); break; }
    case OP_FPTOUI: { int r = sat_f2i(c, in, true); E(c, "  %s = add %s %%t%d, 0", R, tb, r); break; }
    case OP_SITOFP: { char sb[48]; ty_str(c, f->vtypes[in->a], sb, sizeof sb); E(c, "  %s = sitofp %s %s to %s", R, sb, ab, tb); break; }
    case OP_UITOFP: { char sb[48]; ty_str(c, f->vtypes[in->a], sb, sizeof sb); E(c, "  %s = uitofp %s %s to %s", R, sb, ab, tb); break; }
    case OP_BITCAST: { char sb[48]; ty_str(c, f->vtypes[in->a], sb, sizeof sb); E(c, "  %s = bitcast %s %s to %s", R, sb, ab, tb); break; }
    case OP_SELECT:
        E(c, "  %s = select i1 %s, %s %s, %s %s", R, ab, tb, bb, tb, cb);
        break;
    case OP_ALLOCA:
        E(c, "  %s = alloca i8, i64 %lld, align %d", R, (long long)in->imm, (int)in->c);
        break;
    case OP_LOAD:
        E(c, "  %s = load %s, ptr %s, align 1", R, tb, ab);
        break;
    case OP_LOADV:
        E(c, "  %s = load volatile %s, ptr %s, align 1", R, tb, ab);
        break;
    case OP_STORE: {
        char stb[48]; ty_str(c, f->vtypes[in->b], stb, sizeof stb);
        E(c, "  store %s %s, ptr %s, align 1", stb, bb, ab);
        break;
    }
    case OP_STOREV: {
        char stb[48]; ty_str(c, f->vtypes[in->b], stb, sizeof stb);
        E(c, "  store volatile %s %s, ptr %s, align 1", stb, bb, ab);
        break;
    }
    case OP_VLOAD:
        E(c, "  %s = load %s, ptr %s, align 1", R, tb, ab);
        break;
    case OP_VSTORE: {
        char stb[48]; ty_str(c, f->vtypes[in->b], stb, sizeof stb);
        E(c, "  store %s %s, ptr %s, align 1", stb, bb, ab);
        break;
    }
    case OP_GEP: {
        char eb[48]; ty_str(c, in->ety, eb, sizeof eb);
        char ib[80]; to_i64(c, in->b, f->vtypes[in->b], true, ib, sizeof ib);
        E(c, "  %s = getelementptr %s, ptr %s, i64 %s", R, eb, ab, ib);
        break;
    }
    case OP_MEMCPY: {
        c->need_memcpy = true;
        char nb[80]; to_i64(c, in->c, f->vtypes[in->c], false, nb, sizeof nb);
        E(c, "  call void @llvm.memcpy.p0.p0.i64(ptr %s, ptr %s, i64 %s, i1 false)", ab, bb, nb);
        break;
    }
    case OP_MEMSET: {
        c->need_memset = true;
        char nb[80]; to_i64(c, in->c, f->vtypes[in->c], false, nb, sizeof nb);
        if (f->vtypes[in->b].bits == 8) {
            E(c, "  call void @llvm.memset.p0.i64(ptr %s, i8 %s, i64 %s, i1 false)", ab, bb, nb);
        } else {
            int bv = emit_tmp(c, "trunc i%d %s to i8", f->vtypes[in->b].bits, bb);
            E(c, "  call void @llvm.memset.p0.i64(ptr %s, i8 %%t%d, i64 %s, i1 false)", ab, bv, nb);
        }
        break;
    }
    case OP_DATAPTR:
        E(c, "  %s = getelementptr i8, ptr @__krell_data_%d, i64 0", R, (int)in->imm);
        break;
    case OP_VSPLAT: {
        Type et = ty_elem(t);
        char eb[48]; ty_str(c, et, eb, sizeof eb);
        int lanes = ty_lanes(t, c->vl);
        int ins = emit_tmp(c, "insertelement %s poison, %s %s, i64 0", tb, eb, ab);
        char mask[512]; int pos = 0;
        pos += snprintf(mask + pos, sizeof mask - (size_t)pos, "<");
        for (int i = 0; i < lanes; i++)
            pos += snprintf(mask + pos, sizeof mask - (size_t)pos, "%si32 0", i ? ", " : "");
        snprintf(mask + pos, sizeof mask - (size_t)pos, ">");
        char mtb[64]; snprintf(mtb, sizeof mtb, "<%d x i32>", lanes);
        E(c, "  %s = shufflevector %s %%t%d, %s poison, %s %s", R, tb, ins, tb, mtb, mask);
        break;
    }
    case OP_VADD: E(c, "  %s = add %s %s, %s", R, tb, ab, bb); break;
    case OP_VSUB: E(c, "  %s = sub %s %s, %s", R, tb, ab, bb); break;
    case OP_VMUL: E(c, "  %s = mul %s %s, %s", R, tb, ab, bb); break;
    case OP_VUDIV: {
        Type et = ty_elem(t);
        char eb[48]; ty_str(c, et, eb, sizeof eb);
        int q = emit_tmp(c, "udiv %s %s, %s", tb, ab, bb);
        int lanes = ty_lanes(t, c->vl);
        char zb[256]; int pos = 0;
        pos += snprintf(zb + pos, sizeof zb - pos, "<");
        for (int i = 0; i < lanes; i++) pos += snprintf(zb + pos, sizeof zb - (size_t)pos, i ? ", i1 0" : "i1 0");
        snprintf(zb + pos, sizeof zb - (size_t)pos, ">");
        /* isnz per lane: divisor != 0 */
        char dv[80]; op_str(c, in->b, dv, sizeof dv);
        int cmp = emit_tmp(c, "icmp ne %s %s, zeroinitializer", tb, dv);
        E(c, "  %s = select <%d x i1> %%t%d, %s %%t%d, %s zeroinitializer", R, lanes, cmp, tb, q, tb);
        (void)eb; (void)zb;
        break;
    }
    case OP_VFADD: E(c, "  %s = fadd %s %s, %s", R, tb, ab, bb); break;
    case OP_VFSUB: E(c, "  %s = fsub %s %s, %s", R, tb, ab, bb); break;
    case OP_VFMUL: E(c, "  %s = fmul %s %s, %s", R, tb, ab, bb); break;
    case OP_VFDIV: E(c, "  %s = fdiv %s %s, %s", R, tb, ab, bb); break;
    case OP_VAND: E(c, "  %s = and %s %s, %s", R, tb, ab, bb); break;
    case OP_VOR:  E(c, "  %s = or %s %s, %s", R, tb, ab, bb); break;
    case OP_VXOR: E(c, "  %s = xor %s %s, %s", R, tb, ab, bb); break;
    case OP_VLSHR: E(c, "  %s = lshr %s %s, %s", R, tb, ab, bb); break;
    case OP_VWIDEN: {
        /* zext the operand to the result element width, fold each
         * group of consecutive lanes with a shuffle/add butterfly
         * (after steps 1,2,4,... every lane holds its aligned
         * group's sum), then gather the group-leading lanes */
        Type at = f->vtypes[in->a];
        Type oet = ty_elem(t);
        char atb[48]; ty_str(c, at, atb, sizeof atb);
        int iln = ty_lanes(at, c->vl), oln = ty_lanes(t, c->vl);
        int grp = iln / oln;
        char wtb[64]; snprintf(wtb, sizeof wtb, "<%d x i%d>", iln, (int)oet.bits);
        int cur = emit_tmp(c, "zext %s %s to %s", atb, ab, wtb);
        for (int s = 1; s < grp; s *= 2) {
            char mask[1024]; int pos = 0;
            pos += snprintf(mask + pos, sizeof mask - (size_t)pos, "<");
            for (int i = 0; i < iln; i++)
                pos += snprintf(mask + pos, sizeof mask - (size_t)pos, "%si32 %d", i ? ", " : "", i ^ s);
            snprintf(mask + pos, sizeof mask - (size_t)pos, ">");
            char mtb[64]; snprintf(mtb, sizeof mtb, "<%d x i32>", iln);
            int sh = emit_tmp(c, "shufflevector %s %%t%d, %s poison, %s %s", wtb, cur, wtb, mtb, mask);
            cur = emit_tmp(c, "add %s %%t%d, %%t%d", wtb, cur, sh);
        }
        char gmask[256]; int gpos = 0;
        gpos += snprintf(gmask + gpos, sizeof gmask - (size_t)gpos, "<");
        for (int j = 0; j < oln; j++)
            gpos += snprintf(gmask + gpos, sizeof gmask - (size_t)gpos, "%si32 %d", j ? ", " : "", j * grp);
        snprintf(gmask + gpos, sizeof gmask - (size_t)gpos, ">");
        char gmtb[64]; snprintf(gmtb, sizeof gmtb, "<%d x i32>", oln);
        E(c, "  %s = shufflevector %s %%t%d, %s poison, %s %s", R, wtb, cur, wtb, gmtb, gmask);
        break;
    }
    case OP_VEXTRACT: {
        char vb[48]; ty_str(c, f->vtypes[in->a], vb, sizeof vb);
        E(c, "  %s = extractelement %s %s, i64 %lld", R, vb, ab, (long long)in->imm);
        break;
    }
    case OP_VINSERT: {
        char vb[48]; ty_str(c, f->vtypes[in->a], vb, sizeof vb);
        char eb[48]; ty_str(c, ty_elem(t), eb, sizeof eb);
        E(c, "  %s = insertelement %s %s, %s %s, i64 %lld", R, vb, ab, eb, bb, (long long)in->imm);
        break;
    }
    case OP_ALOAD: {
        const char *ord = in->aux == AO_SEQCST ? "seq_cst" : (in->aux == AO_ACQREL || in->aux == AO_ACQUIRE) ? "acquire" : "monotonic";
        int al = t.bits >= 8 ? t.bits / 8 : 1;
        E(c, "  %s = load atomic %s, ptr %s %s, align %d", R, tb, ab, ord, al);
        break;
    }
    case OP_ASTORE: {
        char stb[48]; ty_str(c, f->vtypes[in->b], stb, sizeof stb);
        const char *ord = in->aux == AO_SEQCST ? "seq_cst" : (in->aux == AO_ACQREL || in->aux == AO_RELEASE) ? "release" : "monotonic";
        int al = f->vtypes[in->b].bits >= 8 ? f->vtypes[in->b].bits / 8 : 1;
        E(c, "  store atomic %s %s, ptr %s %s, align %d", stb, bb, ab, ord, al);
        break;
    }
    case OP_AADD: {
        const char *ord = in->aux == AO_SEQCST ? "seq_cst" : in->aux == AO_ACQREL ? "acq_rel" : "monotonic";
        int al = t.bits >= 8 ? t.bits / 8 : 1;
        E(c, "  %s = atomicrmw add ptr %s, %s %s %s, align %d", R, ab, tb, bb, ord, al);
        break;
    }
    case OP_ACMPXCHG: {
        /* strong cmpxchg; the IR result is the old value (first element
         * of LLVM's {ty, i1} pair). The failure ordering is the success
         * ordering weakened: acq_rel -> acquire, release -> monotonic
         * (LLVM forbids release/acq_rel as a failure ordering). */
        char ctb[48]; ty_str(c, f->vtypes[in->c], ctb, sizeof ctb);
        const char *ord = in->aux == AO_SEQCST ? "seq_cst" : in->aux == AO_ACQREL ? "acq_rel"
                        : in->aux == AO_ACQUIRE ? "acquire" : in->aux == AO_RELEASE ? "release" : "monotonic";
        const char *ford = in->aux == AO_ACQREL ? "acquire" : in->aux == AO_RELEASE ? "monotonic" : ord;
        int al = t.bits >= 8 ? t.bits / 8 : 1;
        int n = emit_tmp(c, "cmpxchg ptr %s, %s %s, %s %s %s %s, align %d",
                         ab, tb, bb, ctb, cb, ord, ford, al);
        E(c, "  %s = extractvalue { %s, i1 } %%t%d, 0", R, tb, n);
        break;
    }
    case OP_AXCHG: case OP_ASUB: case OP_AAND: case OP_AOR: case OP_AXOR:
    case OP_AMINS: case OP_AMAXS: case OP_AMINU: case OP_AMAXU: {
        const char *nm = in->op == OP_AXCHG ? "xchg" : in->op == OP_ASUB ? "sub"
                       : in->op == OP_AAND ? "and" : in->op == OP_AOR ? "or"
                       : in->op == OP_AXOR ? "xor" : in->op == OP_AMINS ? "min"
                       : in->op == OP_AMAXS ? "max" : in->op == OP_AMINU ? "umin" : "umax";
        const char *ord = in->aux == AO_SEQCST ? "seq_cst" : in->aux == AO_ACQREL ? "acq_rel"
                        : in->aux == AO_ACQUIRE ? "acquire" : in->aux == AO_RELEASE ? "release" : "monotonic";
        int al = t.bits >= 8 ? t.bits / 8 : 1;
        E(c, "  %s = atomicrmw %s ptr %s, %s %s %s, align %d", R, nm, ab, tb, bb, ord, al);
        break;
    }
    case OP_FENCE: {
        const char *ord = in->aux == AO_SEQCST ? "seq_cst" : in->aux == AO_ACQREL ? "acq_rel"
                        : in->aux == AO_ACQUIRE ? "acquire" : "release";
        E(c, "  fence %s", ord);
        break;
    }
    case OP_FUNCP: {
        const char *name = in->callee_extern ? c->m->exts[in->callee].name : c->m->funcs[in->callee].name;
        E(c, "  %s = getelementptr inbounds i8, ptr @%s, i64 0", R, name);
        break;
    }
    case OP_CALLI: case OP_TAILCALLI: {
        /* indirect calls always use the C convention; the function
         * type comes from the signature-table entry */
        Sig *g = &c->m->sigs[in->callee];
        char rtb[48]; ty_str(c, g->ret, rtb, sizeof rtb);
        char fty[1024]; int fpos = 0; fty[0] = 0;
        for (int i = 0; i < g->nparams; i++) {
            char pb[48]; ty_str(c, g->params[i], pb, sizeof pb);
            fpos += snprintf(fty + fpos, sizeof fty - (size_t)fpos, "%s%s", i ? ", " : "", pb);
        }
        char args[2048]; int pos = 0; args[0] = 0;
        for (int i = 0; i < in->nargs; i++) {
            char pb[48], ob[80];
            ty_str(c, g->params[i], pb, sizeof pb);
            op_str(c, in->args[i], ob, sizeof ob);
            pos += snprintf(args + pos, sizeof args - (size_t)pos, "%s%s %s", i ? ", " : "", pb, ob);
        }
        /* the type is variadic: the target may be an extern, and a
         * variadic-typed call makes the backend set AL (x86_64) to the
         * FP register count of the fixed prefix, exactly like the
         * native lanes; fixed callees observe no other difference */
        fpos += snprintf(fty + fpos, sizeof fty - (size_t)fpos, "%s...", g->nparams ? ", " : "");
        char fp[80]; op_str(c, in->a, fp, sizeof fp);
        const char *tail = in->op == OP_TAILCALLI ? "tail " : "";
        if (g->ret.kind == TY_VOID) {
            E(c, "  %scall %s (%s) %s(%s)", tail, rtb, fty, fp, args);
            if (in->op == OP_TAILCALLI) E(c, "  ret void");
        } else if (in->op == OP_TAILCALLI) {
            int n = emit_tmp(c, "%scall %s (%s) %s(%s)", tail, rtb, fty, fp, args);
            E(c, "  ret %s %%t%d", rtb, n);
        } else {
            E(c, "  %s = %scall %s (%s) %s(%s)", R, tail, rtb, fty, fp, args);
        }
        break;
    }
    case OP_CALL: case OP_TAILCALL: {
        const Type *ps; const char *name; Type rt;
        if (in->callee_extern) { ps = c->m->exts[in->callee].params; name = c->m->exts[in->callee].name; rt = c->m->exts[in->callee].ret; }
        else { Func *g = &c->m->funcs[in->callee]; ps = g->blocks[0].arg_types; name = g->name; rt = g->ret; }
        char rtb[48]; ty_str(c, rt, rtb, sizeof rtb);
        /* build argument text */
        char args[2048]; int pos = 0; args[0] = 0;
        for (int i = 0; i < in->nargs; i++) {
            char pb[48], ob[80];
            ty_str(c, ps[i], pb, sizeof pb);
            op_str(c, in->args[i], ob, sizeof ob);
            pos += snprintf(args + pos, sizeof args - (size_t)pos, "%s%s %s", i ? ", " : "", pb, ob);
        }
        const char *cc = (in->callee_extern || (c->addrtaken && in->callee >= 0 && c->addrtaken[in->callee])) ? "" : "fastcc ";
        const char *tail = in->op == OP_TAILCALL ? "tail " : "";
        if (in->callee_extern) {
            /* extern calls carry an explicit variadic function type
             * (see OP_CALLI): the fixed prefix is passed identically,
             * and the backend sets AL on x86_64 */
            char fty[1024]; int fpos = 0; fty[0] = 0;
            int np2 = in->callee_extern ? c->m->exts[in->callee].nparams : 0;
            for (int i = 0; i < np2; i++) {
                char pb[48]; ty_str(c, ps[i], pb, sizeof pb);
                fpos += snprintf(fty + fpos, sizeof fty - (size_t)fpos, "%s%s", i ? ", " : "", pb);
            }
            fpos += snprintf(fty + fpos, sizeof fty - (size_t)fpos, "%s...", np2 ? ", " : "");
            (void)fpos;
            if (rt.kind == TY_VOID) {
                E(c, "  %scall void (%s) @%s(%s)", tail, fty, name, args);
                if (in->op == OP_TAILCALL) E(c, "  ret void");
            } else if (in->op == OP_TAILCALL) {
                int n = emit_tmp(c, "%scall %s (%s) @%s(%s)", tail, rtb, fty, name, args);
                E(c, "  ret %s %%t%d", rtb, n);
            } else {
                E(c, "  %s = %scall %s (%s) @%s(%s)", R, tail, rtb, fty, name, args);
            }
            break;
        }
        if (rt.kind == TY_VOID) {
            E(c, "  %scall %svoid @%s(%s)", tail, cc, name, args);
            if (in->op == OP_TAILCALL) E(c, "  ret void");
        } else if (in->op == OP_TAILCALL) {
            int n = emit_tmp(c, "%scall %s%s @%s(%s)", tail, cc, rtb, name, args);
            E(c, "  ret %s %%t%d", rtb, n);
        } else {
            E(c, "  %s = %scall %s%s @%s(%s)", R, tail, cc, rtb, name, args);
        }
        break;
    }
    case OP_BR: case OP_CONDBR: case OP_RET: break;   /* emitted by caller */
    default: break;
    }
}

/* definition for an unreachable block argument (keeps the IR valid) */
static void zero_def(Ctx *c, int v, Type t) {
    char tb[48]; ty_str(c, t, tb, sizeof tb);
    switch (t.kind) {
    case TY_INT: E(c, "  %%v%d = add %s 0, 0", v, tb); break;
    case TY_FLOAT: E(c, "  %%v%d = bitcast %s 0 to %s", v, t.bits == 32 ? "i32" : "i64", tb); break;
    case TY_PTR: E(c, "  %%v%d = inttoptr i64 0 to ptr", v); break;
    case TY_VEC: {
        Type e = ty_elem(t);
        if (e.kind == TY_FLOAT) {
            char ib[64];
            snprintf(ib, sizeof ib, "<%d x i%d>", ty_lanes(t, c->vl), e.bits);
            E(c, "  %%v%d = bitcast %s zeroinitializer to %s", v, ib, tb);
        } else E(c, "  %%v%d = add %s zeroinitializer, zeroinitializer", v, tb);
        break;
    }
    default: break;
    }
}

typedef struct { int from; const int32_t *args; int tramp; } Edge;

static void emit_func(Ctx *c, int fi) {
    Module *m = c->m;
    Func *f = &m->funcs[fi];
    c->f = f;
    c->lbl = 0;
    c->ntr = 0;
    /* def map + freeze aliases (order-independent pre-pass) */
    int nv = f->nvalues;
    c->alias = malloc(sizeof(int) * (size_t)(nv ? nv : 1));
    c->def = calloc((size_t)(nv ? nv : 1), sizeof(Instr *));
    for (int i = 0; i < nv; i++) c->alias[i] = i;
    for (int bi = 0; bi < f->nblocks; bi++)
        for (int ii = 0; ii < f->blocks[bi].nins; ii++) {
            Instr *in = &f->blocks[bi].ins[ii];
            if (in->result >= 0) c->def[in->result] = in;
        }
    for (int bi = 0; bi < f->nblocks; bi++)
        for (int ii = 0; ii < f->blocks[bi].nins; ii++) {
            Instr *in = &f->blocks[bi].ins[ii];
            if (in->op == OP_FREEZE && in->result >= 0) {
                int a = in->a;
                while (a >= 0 && c->alias[a] != a) a = c->alias[a];
                c->alias[in->result] = a;
            }
        }
    /* trampolines for condbrs whose targets coincide */
    for (int bi = 0; bi < f->nblocks; bi++) {
        Block *b = &f->blocks[bi];
        if (!b->nins) continue;
        Instr *t = &b->ins[b->nins - 1];
        if (t->op == OP_CONDBR && t->blk == t->blk2 && c->ntr < 64) {
            c->tramps[c->ntr].from = bi;
            c->tramps[c->ntr].tgt = t->blk;
            c->tramps[c->ntr].id = c->ntramp++;
            c->ntr++;
        }
    }
    /* per-block division-split counts (for phi incoming labels) */
    c->splits = calloc((size_t)(f->nblocks ? f->nblocks : 1), sizeof(int));
    for (int bi = 0; bi < f->nblocks; bi++)
        for (int ii = 0; ii < f->blocks[bi].nins; ii++) {
            int op = f->blocks[bi].ins[ii].op;
            if (op == OP_UDIV || op == OP_SDIV || op == OP_UREM || op == OP_SREM) c->splits[bi]++;
        }
    /* signature */
    char rtb[48]; ty_str(c, f->ret, rtb, sizeof rtb);
    const char *cc = (strcmp(f->name, "main") == 0 || (c->addrtaken && c->addrtaken[fi])) ? "" : "fastcc ";
    fprintf(c->out, "define %s%s @%s(", cc, rtb, f->name);
    if (f->nblocks > 0) {
        Block *b0 = &f->blocks[0];
        for (int i = 0; i < b0->nargs; i++) {
            char pb[48]; ty_str(c, b0->arg_types[i], pb, sizeof pb);
            fprintf(c->out, "%s%s %%v%d", i ? ", " : "", pb, b0->arg_vals[i]);
        }
    }
    fprintf(c->out, ") {\n");
    if (f->nblocks == 0) {
        E(c, "  unreachable");
        E(c, "}");
        free(c->alias); free(c->def);
        return;
    }
    for (int bi = 0; bi < f->nblocks; bi++) {
        Block *b = &f->blocks[bi];
        c->bi = bi;
        c->split_idx = 0;
        E(c, "b%d:", bi);
        /* phis / param defs */
        if (bi > 0 && b->nargs > 0) {
            Edge edges[64]; int ne = 0;
            for (int pb = 0; pb < f->nblocks && ne < 64; pb++) {
                Block *pbb = &f->blocks[pb];
                if (!pbb->nins) continue;
                Instr *t = &pbb->ins[pbb->nins - 1];
                if (t->op == OP_BR && t->blk == bi) {
                    edges[ne++] = (Edge){ pb, t->args, -1 };
                } else if (t->op == OP_CONDBR) {
                    if (t->blk == bi) edges[ne++] = (Edge){ pb, t->args, -1 };
                    if (t->blk2 == bi) {
                        int tr = (t->blk == t->blk2) ? tramp_of(c, pb, bi) : -1;
                        edges[ne++] = (Edge){ pb, t->args2, tr };
                    }
                }
            }
            if (ne == 0) {
                for (int j = 0; j < b->nargs; j++) zero_def(c, b->arg_vals[j], b->arg_types[j]);
            } else {
                for (int j = 0; j < b->nargs; j++) {
                    char pb2[48]; ty_str(c, b->arg_types[j], pb2, sizeof pb2);
                    fprintf(c->out, "  %%v%d = phi %s ", b->arg_vals[j], pb2);
                    for (int e2 = 0; e2 < ne; e2++) {
                        char ob[80]; op_str(c, edges[e2].args[j], ob, sizeof ob);
                        if (edges[e2].tramp >= 0) fprintf(c->out, "%s[ %s, %%bx%d ]", e2 ? ", " : "", ob, edges[e2].tramp);
                        else if (c->splits[edges[e2].from] > 0)
                            fprintf(c->out, "%s[ %s, %%c%d_%d ]", e2 ? ", " : "", ob, edges[e2].from, c->splits[edges[e2].from]);
                        else fprintf(c->out, "%s[ %s, %%b%d ]", e2 ? ", " : "", ob, edges[e2].from);
                    }
                    fputc('\n', c->out);
                }
            }
        }
        /* instructions, then the terminator */
        for (int ii = 0; ii < b->nins; ii++) {
            Instr *in = &b->ins[ii];
            if (op_is_terminator(in->op)) continue;
            emit_instr(c, in);
        }
        Instr *t = b->nins ? &b->ins[b->nins - 1] : NULL;
        if (t && t->op == OP_BR) {
            E(c, "  br label %%b%d", t->blk);
        } else if (t && t->op == OP_CONDBR) {
            char cb[80]; op_str(c, t->a, cb, sizeof cb);
            int tr = tramp_of(c, bi, t->blk2);
            if (t->blk == t->blk2 && tr >= 0) E(c, "  br i1 %s, label %%b%d, label %%bx%d", cb, t->blk, tr);
            else E(c, "  br i1 %s, label %%b%d, label %%b%d", cb, t->blk, t->blk2);
        } else if (t && t->op == OP_RET) {
            if (t->a < 0) E(c, "  ret void");
            else {
                char rb[48], ob[80];
                ty_str(c, f->ret, rb, sizeof rb);
                op_str(c, t->a, ob, sizeof ob);
                E(c, "  ret %s %s", rb, ob);
            }
        } else if (t && (t->op == OP_TAILCALL || t->op == OP_TAILCALLI)) {
            emit_instr(c, t);   /* emits the call and its ret */
        } else {
            E(c, "  unreachable");
        }
    }
    /* trampoline blocks */
    for (int i = 0; i < c->ntr; i++) {
        E(c, "bx%d:", c->tramps[i].id);
        E(c, "  br label %%b%d", c->tramps[i].tgt);
    }
    E(c, "}");
    free(c->alias); free(c->def); free(c->splits);
    c->alias = NULL; c->def = NULL; c->splits = NULL;
}

int be_llvm(Module *m, const Cost *cost, FILE *out, char *err, size_t errcap) {
    const char *ve = mod_verify(m);
    if (ve) { snprintf(err, errcap, "%s", ve); return -1; }
    /* address-taken internal functions are emitted with the C
     * convention (definition and every call site, direct or
     * indirect): an indirect call cannot use fastcc */
    bool *addrtaken = calloc((size_t)(m->nfuncs ? m->nfuncs : 1), sizeof(bool));
    for (int i = 0; i < m->nfuncs; i++) {
        Func *g = &m->funcs[i];
        for (int b = 0; b < g->nblocks; b++)
            for (int j = 0; j < g->blocks[b].nins; j++) {
                Instr *in = &g->blocks[b].ins[j];
                if (in->op == OP_FUNCP && !in->callee_extern && in->callee >= 0 && in->callee < m->nfuncs)
                    addrtaken[in->callee] = true;
            }
    }
    Ctx c = { .out = out, .m = m, .vl = cost_vl_i32(cost), .addrtaken = addrtaken };
    E(&c, "; Krell-IR -> LLVM IR (lowering lane)");
    /* data globals */
    for (int i = 0; i < m->ndata; i++) {
        DataBlob *d = &m->data[i];
        fprintf(out, "@__krell_data_%d = private unnamed_addr constant [%u x i8] c\"", i, d->len ? d->len : 0);
        for (uint32_t j = 0; j < d->len; j++) {
            uint8_t ch = d->bytes[j];
            if (ch >= 0x20 && ch < 0x7f && ch != '"' && ch != '\\') fputc(ch, out);
            else fprintf(out, "\\%02X", ch);
        }
        fprintf(out, "\", align %u\n", d->align ? d->align : 1);
    }
    for (int i = 0; i < m->nfuncs; i++) emit_func(&c, i);
    /* external function declarations */
    for (int i = 0; i < m->nexts; i++) {
        Extern *ex = &m->exts[i];
        char rty[48];
        ty_str(&c, ex->ret, rty, sizeof rty);
        fprintf(out, "declare %s @%s(", rty, ex->name);
        for (int p = 0; p < ex->nparams; p++) {
            char pty[48];
            ty_str(&c, ex->params[p], pty, sizeof pty);
            fprintf(out, "%s%s", p ? ", " : "", pty);
        }
        fprintf(out, ")\n");
    }
    /* intrinsic declarations used */
    for (int w = 1; w < 65; w++) {
        if (c.need_ctpop[w]) E(&c, "declare i%d @llvm.ctpop.i%d(i%d)", w, w, w);
        if (c.need_ctlz[w]) E(&c, "declare i%d @llvm.ctlz.i%d(i%d, i1 immarg)", w, w, w);
        if (c.need_cttz[w]) E(&c, "declare i%d @llvm.cttz.i%d(i%d, i1 immarg)", w, w, w);
        if (c.need_bswap[w]) E(&c, "declare i%d @llvm.bswap.i%d(i%d)", w, w, w);
        if (w < 129 && c.need_fshl[w]) E(&c, "declare i%d @llvm.fshl.i%d(i%d, i%d, i%d)", w, w, w, w, w);
        if (w < 129 && c.need_fshr[w]) E(&c, "declare i%d @llvm.fshr.i%d(i%d, i%d, i%d)", w, w, w, w, w);
    }
    if (c.need_fma32) E(&c, "declare float @llvm.fma.f32(float, float, float)");
    if (c.need_fma64) E(&c, "declare double @llvm.fma.f64(double, double, double)");
    if (c.need_fabs32) E(&c, "declare float @llvm.fabs.f32(float)");
    if (c.need_fabs64) E(&c, "declare double @llvm.fabs.f64(double)");
    if (c.need_memcpy) E(&c, "declare void @llvm.memcpy.p0.p0.i64(ptr, ptr, i64, i1 immarg)");
    if (c.need_memset) E(&c, "declare void @llvm.memset.p0.i64(ptr, i8, i64, i1 immarg)");
    free(addrtaken);
    return 0;
}
