/* fuzz_gen — random-module differential fuzzer generator.
 * Builds a module of random functions (scalar DAGs, memory functions,
 * branch functions, bounded loops), re-decodes it from its binary form
 * (so builder-side folding cannot mask optimizer bugs), records
 * interpreter-expected results, optionally optimizes, cross-checks the
 * optimizer in-process (interp before vs after), then emits backend
 * code + a case file + a symbol table for fuzz_driver.c.
 *
 * usage: fuzz_gen <x86|arm|rv|llvm> <seed> <nfuncs> <opt|noopt> <outprefix> */
#include "krell.h"
#include <stdio.h>
#include <string.h>

static uint64_t rs;
static uint64_t rnd(void) { rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17; return rs; }
static int ri(int n) { return (int)(rnd() % (uint64_t)n); }

static const int64_t CPOOL[] = { 0, 1, 2, 3, 4, 5, 7, 8, 9, 10, 11, 13, 15, 16, 17,
    19, 21, 25, 27, 31, 32, 37, 63, 64, 100, 127, 128, 255, 256, 1000, 4095,
    65535, 65536, 1000003, 2147483647, -1, -2, -3, -7, -16, -100,
    (int64_t)0x123456789aLL, (int64_t)0xdeadbeefLL, INT64_MIN + 1, INT64_MAX };
#define NCP (sizeof(CPOOL) / sizeof(CPOOL[0]))

typedef struct { int v; Type ty; } PV;
typedef struct { PV p[256]; int n; } Pool;
static void pool_push(Pool *pl, int v, Type ty) { if (pl->n < 256) pl->p[pl->n++] = (PV){ v, ty }; }
static int pool_pick(Pool *pl, Type ty) {
    int cnt = 0;
    for (int i = 0; i < pl->n; i++) if (ty_eq(pl->p[i].ty, ty)) cnt++;
    if (!cnt) return -1;
    int k = ri(cnt);
    for (int i = 0; i < pl->n; i++) if (ty_eq(pl->p[i].ty, ty) && k-- == 0) return pl->p[i].v;
    return -1;
}

static int gen_const(Func *f, int blk, Pool *pl, Type ty) {
    int64_t c = CPOOL[ri((int)NCP)];
    if (ri(3) == 0) c = (int64_t)rnd();
    int v = emit(f, blk, ins_iconst(ty, c));
    pool_push(pl, v, ty);
    return v;
}
/* divisor: often a constant (drives the div-by-constant rules) */
static int gen_divisor(Func *f, int blk, Pool *pl, Type ty) {
    if (ri(100) < 40) return gen_const(f, blk, pl, ty);
    int v = pool_pick(pl, ty);
    return v >= 0 ? v : gen_const(f, blk, pl, ty);
}

static const int BINOPS[] = { OP_ADD, OP_SUB, OP_MUL, OP_AND, OP_OR, OP_XOR,
    OP_SHL, OP_LSHR, OP_ASHR, OP_UDIV, OP_SDIV, OP_UREM, OP_SREM };
static const int UNOPS[] = { OP_NEG, OP_NOT, OP_POPCOUNT, OP_CLZ, OP_CTZ, OP_BSWAP };

/* append n random ops to the pool in this block; returns nothing */
static void gen_ops(Func *f, int blk, Pool *pl, int n, bool allow_mem, int ptrv) {
    for (int s = 0; s < n; s++) {
        int what = ri(100);
        if (what < 52) {          /* i64 binop */
            int op = BINOPS[ri((int)(sizeof(BINOPS) / sizeof(int)))];
            int a = pool_pick(pl, ty_i64());
            if (a < 0) a = gen_const(f, blk, pl, ty_i64());
            int b;
            if (op == OP_UDIV || op == OP_SDIV || op == OP_UREM || op == OP_SREM)
                b = gen_divisor(f, blk, pl, ty_i64());
            else {
                b = pool_pick(pl, ty_i64());
                if (b < 0 || ri(4) == 0) b = gen_const(f, blk, pl, ty_i64());
            }
            int v = emit(f, blk, ins_bin((uint8_t)op, ty_i64(), a, b));
            pool_push(pl, v, ty_i64());
        } else if (what < 62) {   /* narrow excursion */
            static const int widths[3] = { 8, 16, 32 };
            Type nt = ty_int(widths[ri(3)]);
            int a = pool_pick(pl, ty_i64());
            if (a < 0) continue;
            Instr tr = ins_make(OP_TRUNC, nt); tr.a = a;
            int tv = emit(f, blk, tr);
            int op = BINOPS[ri((int)(sizeof(BINOPS) / sizeof(int)))];
            int b;
            if (op == OP_UDIV || op == OP_SDIV || op == OP_UREM || op == OP_SREM)
                b = gen_divisor(f, blk, pl, nt);
            else { b = gen_const(f, blk, pl, nt); if (ri(2)) { int b2 = pool_pick(pl, nt); if (b2 >= 0) b = b2; } }
            int v = emit(f, blk, ins_bin((uint8_t)op, nt, tv, b));
            Instr ex = ins_make(ri(2) ? OP_ZEXT : OP_SEXT, ty_i64()); ex.a = v;
            int ev = emit(f, blk, ex);
            pool_push(pl, ev, ty_i64());
        } else if (what < 72) {   /* unop */
            int a = pool_pick(pl, ty_i64());
            if (a < 0) continue;
            int op = UNOPS[ri((int)(sizeof(UNOPS) / sizeof(int)))];
            int v = emit(f, blk, ins_un((uint8_t)op, ty_i64(), a));
            pool_push(pl, v, ty_i64());
        } else if (what < 84) {   /* icmp + select */
            int a = pool_pick(pl, ty_i64()), b = pool_pick(pl, ty_i64());
            if (a < 0 || b < 0) continue;
            Instr ic = ins_make(OP_ICMP, ty_i1()); ic.a = a; ic.b = b; ic.pred = (uint8_t)ri(10);
            int cnd = emit(f, blk, ic);
            int x = pool_pick(pl, ty_i64()), y = pool_pick(pl, ty_i64());
            if (x < 0 || y < 0) continue;
            Instr sl = ins_make(OP_SELECT, ty_i64()); sl.a = cnd; sl.b = x; sl.c = y;
            int v = emit(f, blk, sl);
            pool_push(pl, v, ty_i64());
        } else if (what < 92 && allow_mem) {   /* store + load through ptr */
            int a = pool_pick(pl, ty_i64());
            if (a < 0) continue;
            int raw = pool_pick(pl, ty_i64());
            if (raw < 0) raw = gen_const(f, blk, pl, ty_i64());
            /* index bounded to the 256-byte test image: (raw & 63) i32s */
            int idx = emit(f, blk, ins_bin(OP_AND, ty_i64(), raw,
                           emit(f, blk, ins_iconst(ty_i64(), 63))));
            Instr g = ins_make(OP_GEP, ty_ptr()); g.a = ptrv; g.b = idx; g.ety = ty_i32();
            int gp = emit(f, blk, g);
            Instr tr = ins_make(OP_TRUNC, ty_i32()); tr.a = a;
            int tv = emit(f, blk, tr);
            Instr st = ins_make(OP_STORE, ty_i32()); st.a = gp; st.b = tv;
            emit(f, blk, st);
            Instr ld = ins_make(OP_LOAD, ty_i32()); ld.a = gp;
            int lv = emit(f, blk, ld);
            Instr ex = ins_make(ri(2) ? OP_ZEXT : OP_SEXT, ty_i64()); ex.a = lv;
            int ev = emit(f, blk, ex);
            pool_push(pl, ev, ty_i64());
        } else {                  /* plain constant or copy-ish add */
            if (ri(2)) gen_const(f, blk, pl, ty_i64());
            else {
                int a = pool_pick(pl, ty_i64());
                if (a < 0) continue;
                int v = emit(f, blk, ins_bin(OP_ADD, ty_i64(), a, gen_const(f, blk, pl, ty_i64())));
                pool_push(pl, v, ty_i64());
            }
        }
    }
}
static int pool_last_i64(Pool *pl) {
    for (int i = pl->n - 1; i >= 0; i--) if (ty_eq(pl->p[i].ty, ty_i64())) return pl->p[i].v;
    return -1;
}

enum { FK_S, FK_M, FK_B, FK_L };
typedef struct { char name[16]; int kind; } FEnt;
static FEnt fents[512];
static int nfents = 0;

static void build_one(Module *m, int fi, int kind) {
        char name[16];
        if (kind == FK_S) {
            snprintf(name, sizeof name, "fs%d", fi);
            Func *f = mod_add_func(m, name, ty_i64(), 0);
            int b = func_add_block(f, (Type[]){ ty_i64(), ty_i64(), ty_i64() }, 3);
            Pool pl = { 0 };
            for (int i = 0; i < 3; i++) pool_push(&pl, f->blocks[b].arg_vals[i], ty_i64());
            gen_ops(f, b, &pl, 6 + ri(22), false, -1);
            int r = pool_last_i64(&pl);
            if (r < 0) r = f->blocks[b].arg_vals[0];
            emit(f, b, ins_ret(r));
        } else if (kind == FK_M) {
            snprintf(name, sizeof name, "fm%d", fi);
            Func *f = mod_add_func(m, name, ty_i64(), 0);
            int b = func_add_block(f, (Type[]){ ty_ptr(), ty_i64(), ty_i64() }, 3);
            Pool pl = { 0 };
            pool_push(&pl, f->blocks[b].arg_vals[1], ty_i64());
            pool_push(&pl, f->blocks[b].arg_vals[2], ty_i64());
            gen_ops(f, b, &pl, 6 + ri(18), true, f->blocks[b].arg_vals[0]);
            int r = pool_last_i64(&pl);
            if (r < 0) r = f->blocks[b].arg_vals[1];
            emit(f, b, ins_ret(r));
        } else if (kind == FK_B) {
            snprintf(name, sizeof name, "fb%d", fi);
            Func *f = mod_add_func(m, name, ty_i64(), 0);
            int b0 = func_add_block(f, (Type[]){ ty_i64(), ty_i64(), ty_i64() }, 3);
            int b1 = func_add_block(f, (Type[]){ ty_i64() }, 1);
            int b2 = func_add_block(f, (Type[]){ ty_i64() }, 1);
            int b3 = func_add_block(f, (Type[]){ ty_i64() }, 1);
            Pool pl = { 0 };
            for (int i = 0; i < 3; i++) pool_push(&pl, f->blocks[b0].arg_vals[i], ty_i64());
            gen_ops(f, b0, &pl, 3 + ri(6), false, -1);
            int a = pool_pick(&pl, ty_i64()), bb = gen_const(f, b0, &pl, ty_i64());
            Instr ic = ins_make(OP_ICMP, ty_i1()); ic.a = a; ic.b = bb; ic.pred = (uint8_t)ri(10);
            int cnd = emit(f, b0, ic);
            int pass = pool_last_i64(&pl);
            emit(f, b0, ins_condbr(cnd, b1, ids_dup((int32_t[]){ pass }, 1), 1,
                                       b2, ids_dup((int32_t[]){ pass }, 1), 1));
            Pool p1 = { 0 }; pool_push(&p1, f->blocks[b1].arg_vals[0], ty_i64());
            gen_ops(f, b1, &p1, 3 + ri(10), false, -1);
            emit(f, b1, ins_br(b3, ids_dup((int32_t[]){ pool_last_i64(&p1) }, 1), 1));
            Pool p2 = { 0 }; pool_push(&p2, f->blocks[b2].arg_vals[0], ty_i64());
            gen_ops(f, b2, &p2, 3 + ri(10), false, -1);
            emit(f, b2, ins_br(b3, ids_dup((int32_t[]){ pool_last_i64(&p2) }, 1), 1));
            emit(f, b3, ins_ret(f->blocks[b3].arg_vals[0]));
        } else {
            snprintf(name, sizeof name, "fl%d", fi);
            Func *f = mod_add_func(m, name, ty_i64(), 0);
            int b0 = func_add_block(f, (Type[]){ ty_i64() }, 1);
            int b1 = func_add_block(f, (Type[]){ ty_i64(), ty_i64(), ty_i64() }, 3);
            int b2 = func_add_block(f, (Type[]){ ty_i64(), ty_i64() }, 2);
            int b3 = func_add_block(f, (Type[]){ ty_i64() }, 1);
            int arg = f->blocks[b0].arg_vals[0];
            /* trip count: n = arg & 15 */
            int mask = emit(f, b0, ins_bin(OP_AND, ty_i64(), arg, emit(f, b0, ins_iconst(ty_i64(), 15))));
            int z = emit(f, b0, ins_iconst(ty_i64(), 0));
            int one = emit(f, b0, ins_iconst(ty_i64(), 1));
            emit(f, b0, ins_br(b1, ids_dup((int32_t[]){ z, z, mask }, 3), 3));
            int i1 = f->blocks[b1].arg_vals[0], acc1 = f->blocks[b1].arg_vals[1], n1 = f->blocks[b1].arg_vals[2];
            Instr ic = ins_make(OP_ICMP, ty_i1()); ic.a = i1; ic.b = n1; ic.pred = IC_SLT;
            int cnd = emit(f, b1, ic);
            emit(f, b1, ins_condbr(cnd, b2, ids_dup((int32_t[]){ i1, acc1 }, 2), 2,
                                       b3, ids_dup((int32_t[]){ acc1 }, 1), 1));
            int i2 = f->blocks[b2].arg_vals[0], acc2 = f->blocks[b2].arg_vals[1];
            Pool pl = { 0 };
            pool_push(&pl, i2, ty_i64()); pool_push(&pl, arg, ty_i64()); pool_push(&pl, acc2, ty_i64());
            gen_ops(f, b2, &pl, 2 + ri(6), false, -1);
            int nacc = emit(f, b2, ins_bin(OP_ADD, ty_i64(), acc2, pool_last_i64(&pl)));
            int ni = emit(f, b2, ins_bin(OP_ADD, ty_i64(), i2, one));
            emit(f, b2, ins_br(b1, ids_dup((int32_t[]){ ni, nacc, n1 }, 3), 3));
            emit(f, b3, ins_ret(f->blocks[b3].arg_vals[0]));
            (void)one;
        }
}

/* Generate with per-function validation: the builder's hash-consing can
 * return a value from a sibling branch block, which fails dominance.
 * Build each function in a scratch module first; on verify failure,
 * retry with fresh randomness (deterministic per seed via rs state). */
static Module *gen_module(int nfuncs) {
    Module *m = mod_new();
    for (int fi = 0; fi < nfuncs; fi++) {
        bool ok = false;
        int kind = FK_S;
        for (int attempt = 0; attempt < 40 && !ok; attempt++) {
            uint64_t saved = rs;
            int k = ri(10);
            k = k < 5 ? FK_S : k < 7 ? FK_M : k < 9 ? FK_B : FK_L;
            Module *scratch = mod_new();
            build_one(scratch, fi, k);
            if (mod_verify(scratch) == NULL) {
                rs = saved;             /* replay the same draws into m */
                int k2 = ri(10);
                k2 = k2 < 5 ? FK_S : k2 < 7 ? FK_M : k2 < 9 ? FK_B : FK_L;
                build_one(m, fi, k2);
                kind = k2;
                ok = true;
            }
            mod_free(scratch);
        }
        if (!ok) {   /* fallback: identity function */
            char name[16];
            snprintf(name, sizeof name, "fs%d", fi);
            Func *f = mod_add_func(m, name, ty_i64(), 0);
            int b = func_add_block(f, (Type[]){ ty_i64(), ty_i64(), ty_i64() }, 3);
            emit(f, b, ins_ret(f->blocks[b].arg_vals[0]));
            kind = FK_S;
        }
        const char *pre = kind == FK_S ? "fs" : kind == FK_M ? "fm" : kind == FK_B ? "fb" : "fl";
        snprintf(fents[nfents].name, sizeof fents[nfents].name, "%s%d", pre, fi);
        fents[nfents].kind = kind;
        nfents++;
    }
    return m;
}

/* case file */
static FILE *cf;
static void w8(uint8_t v) { fputc(v, cf); }
static void w32(uint32_t v) { fwrite(&v, 4, 1, cf); }
static void w64(uint64_t v) { fwrite(&v, 8, 1, cf); }

int main(int argc, char **argv) {
    if (argc < 6) { fprintf(stderr, "usage: fuzz_gen <be> <seed> <nfuncs> <opt|noopt> <outprefix>\n"); return 2; }
    const char *be = argv[1];
    rs = strtoull(argv[2], NULL, 0) | 1;
    int nfuncs = atoi(argv[3]);
    bool use_opt = strcmp(argv[4], "opt") == 0;
    const char *prefix = argv[5];

    Module *m0 = gen_module(nfuncs);
    const char *e;
    if ((e = mod_verify(m0))) { fprintf(stderr, "gen verify: %s\n", e); return 1; }
    /* re-decode from binary: the consumer's view (no builder state) */
    size_t blen; uint8_t *bytes = mod_encode(m0, &blen);
    char err[256];
    Module *m = mod_decode(bytes, blen, err, sizeof err);
    if (!m) { fprintf(stderr, "decode: %s\n", err); return 1; }
    mod_free(m0);

    {   /* always leave a text dump beside the outputs for debugging */
        char dp[512];
        snprintf(dp, sizeof dp, "%s.dump.txt", prefix);
        FILE *df = fopen(dp, "w");
        if (df) { mod_dump(m, df); fclose(df); }
    }
    Interp *it = interp_new(m);
    /* record expected results BEFORE optimizing */
    typedef struct { int func, kind; uint64_t a[3]; uint64_t exp; uint8_t img_in[256], img_exp[256]; } Case;
    Case *cases = NULL; int ncase = 0, ccap = 0;
    #define PUSH_CASE(cs) do { if (ncase == ccap) { ccap = ccap ? ccap * 2 : 1024; cases = realloc(cases, sizeof(Case) * (size_t)ccap); } cases[ncase++] = (cs); } while (0)
    for (int fi = 0; fi < nfents; fi++) {
        int reps = fents[fi].kind == FK_M ? 10 : fents[fi].kind == FK_L ? 16 : 24;
        for (int r = 0; r < reps; r++) {
            Case cs; memset(&cs, 0, sizeof cs);
            cs.func = fi; cs.kind = fents[fi].kind;
            if (cs.kind == FK_M) {
                for (int i = 0; i < 256; i++) cs.img_in[i] = (uint8_t)rnd();
                cs.a[1] = rnd() % 13; cs.a[2] = rnd();
                size_t ms; uint8_t *mem = interp_mem(it, &ms);
                uint64_t base = interp_alloc(it, 256, 16);
                memcpy(mem + base, cs.img_in, 256);
                IVal av[3], rv; uint64_t lb[3][256];
                for (int i = 0; i < 3; i++) { av[i].lanes = lb[i]; }
                av[0].lanes[0] = base; av[1].lanes[0] = cs.a[1]; av[2].lanes[0] = cs.a[2];
                rv.lanes = lb[0] + 8;
                if (interp_call(it, fents[fi].name, av, 3, &rv) != 0) { fprintf(stderr, "interp fail %s\n", fents[fi].name); return 1; }
                cs.exp = rv.lanes[0];
                memcpy(cs.img_exp, mem + base, 256);
            } else {
                int nargs = cs.kind == FK_L ? 1 : 3;
                for (int i = 0; i < nargs; i++) {
                    uint64_t v = ri(2) ? (uint64_t)CPOOL[ri((int)NCP)] : rnd();
                    cs.a[i] = v;
                }
                IVal av[3], rv; uint64_t lb[3][256];
                for (int i = 0; i < 3; i++) { av[i].lanes = lb[i]; av[i].lanes[0] = cs.a[i]; }
                rv.lanes = lb[0] + 8;
                if (interp_call(it, fents[fi].name, av, nargs, &rv) != 0) { fprintf(stderr, "interp fail %s\n", fents[fi].name); return 1; }
                cs.exp = rv.lanes[0];
            }
            PUSH_CASE(cs);
        }
    }
    if (use_opt) {
        Cost *cost = cost_load("x86_64");
        OptStats st = { 0, 0, 0, 0 };
        opt_optimize(m, cost, &st);
        printf("FUZZ_OPT folded=%d dce=%d rewritten=%d\n", st.folded, st.dce, st.rewritten);
        if ((e = mod_verify(m))) { fprintf(stderr, "verify after opt: %s\n", e); return 1; }
        /* in-process optimizer check: interp the optimized module and
         * compare against the recorded expectations */
        Interp *it2 = interp_new(m);
        for (int ci = 0; ci < ncase; ci++) {
            Case *cs = &cases[ci];
            IVal av[3], rv; uint64_t lb[3][256];
            for (int i = 0; i < 3; i++) { av[i].lanes = lb[i]; }
            rv.lanes = lb[0] + 8;
            if (cs->kind == FK_M) {
                size_t ms; uint8_t *mem = interp_mem(it2, &ms);
                uint64_t base = interp_alloc(it2, 256, 16);
                memcpy(mem + base, cs->img_in, 256);
                av[0].lanes[0] = base; av[1].lanes[0] = cs->a[1]; av[2].lanes[0] = cs->a[2];
                if (interp_call(it2, fents[cs->func].name, av, 3, &rv) != 0) { fprintf(stderr, "interp2 fail\n"); return 1; }
                if (rv.lanes[0] != cs->exp || memcmp(mem + base, cs->img_exp, 256) != 0) {
                    fprintf(stderr, "OPT MISCOMPILE (interp) func %s case %d\n", fents[cs->func].name, ci);
                    return 1;
                }
            } else {
                int nargs = cs->kind == FK_L ? 1 : 3;
                for (int i = 0; i < nargs; i++) av[i].lanes[0] = cs->a[i];
                if (interp_call(it2, fents[cs->func].name, av, nargs, &rv) != 0) { fprintf(stderr, "interp2 fail\n"); return 1; }
                if (rv.lanes[0] != cs->exp) {
                    fprintf(stderr, "OPT MISCOMPILE (interp) func %s case %d: got 0x%llx want 0x%llx\n",
                            fents[cs->func].name, ci, (unsigned long long)rv.lanes[0], (unsigned long long)cs->exp);
                    return 1;
                }
            }
        }
        interp_free(it2);
        printf("OPT_INTERP_CHECK_OK cases=%d\n", ncase);
    }
    interp_free(it);

    /* emit code */
    Cost *cost = cost_load(strcmp(be, "arm") == 0 ? "aarch64" : strcmp(be, "rv") == 0 ? "riscv64" : "x86_64");
    char path[512];
    snprintf(path, sizeof path, "%s.fz.%s", prefix, strcmp(be, "llvm") == 0 ? "ll" : "s");
    FILE *out = fopen(path, "w");
    if (!out) { perror("asm"); return 1; }
    int rc = 0;
#ifdef KRELL_BE_X86
    if (strcmp(be, "x86") == 0) rc = be_x86_64(m, cost, out, err, sizeof err);
    else
#endif
#ifdef KRELL_BE_ARM
    if (strcmp(be, "arm") == 0) rc = be_aarch64(m, cost, out, err, sizeof err);
    else
#endif
#ifdef KRELL_BE_RV
    if (strcmp(be, "rv") == 0) rc = be_riscv64(m, cost, out, err, sizeof err);
    else
#endif
#ifdef KRELL_BE_LLVM
    if (strcmp(be, "llvm") == 0) rc = be_llvm(m, cost, out, err, sizeof err);
    else
#endif
    { rc = -99; }
    fclose(out);
    if (rc) { fprintf(stderr, "backend: %s\n", err); return 1; }

    /* case file */
    snprintf(path, sizeof path, "%s.fcases", prefix);
    cf = fopen(path, "wb");
    if (!cf) { perror("cases"); return 1; }
    fwrite("RFUZ", 1, 4, cf);
    w32(1);
    w32((uint32_t)nfents);
    for (int i = 0; i < nfents; i++) {
        w8((uint8_t)strlen(fents[i].name));
        fwrite(fents[i].name, 1, strlen(fents[i].name), cf);
        w8((uint8_t)fents[i].kind);
    }
    w32((uint32_t)ncase);
    for (int i = 0; i < ncase; i++) {
        Case *cs = &cases[i];
        w32((uint32_t)cs->func);
        w64(cs->a[0]); w64(cs->a[1]); w64(cs->a[2]);
        w64(cs->exp);
        if (cs->kind == FK_M) { fwrite(cs->img_in, 1, 256, cf); fwrite(cs->img_exp, 1, 256, cf); }
    }
    fclose(cf);
    /* symbol table header for the driver */
    snprintf(path, sizeof path, "%s.ftab.h", prefix);
    FILE *th = fopen(path, "w");
    if (!th) { perror("ftab"); return 1; }
    for (int i = 0; i < nfents; i++) {
        if (fents[i].kind == FK_M) fprintf(th, "extern uint64_t %s(void *, uint64_t, uint64_t);\n", fents[i].name);
        else if (fents[i].kind == FK_L) fprintf(th, "extern uint64_t %s(uint64_t);\n", fents[i].name);
        else fprintf(th, "extern uint64_t %s(uint64_t, uint64_t, uint64_t);\n", fents[i].name);
    }
    fprintf(th, "typedef struct { const char *name; int kind; void *fn; } FTabEnt;\n");
    fprintf(th, "static const FTabEnt FTAB[] = {\n");
    for (int i = 0; i < nfents; i++)
        fprintf(th, "    { \"%s\", %d, (void *)%s },\n", fents[i].name, fents[i].kind, fents[i].name);
    fprintf(th, "};\n#define NFTAB (sizeof(FTAB) / sizeof(FTAB[0]))\n");
    fclose(th);
    printf("FUZZ_GEN_OK funcs=%d cases=%d opt=%d\n", nfents, ncase, use_opt ? 1 : 0);
    return 0;
}
