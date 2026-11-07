/* The differential battery: ~28 small functions covering the op menu.
 * Built once; executed by the interpreter (gen) and by every backend
 * (driver) over identical recorded inputs. */
#include "krell.h"

#define B(f, blk, op, ty, a, b) emit((f), (blk), ins_bin((op), (ty), (a), (b)))
#define U(f, blk, op, ty, a)    emit((f), (blk), ins_un((op), (ty), (a)))
#define K(f, blk, ty, v)        emit((f), (blk), ins_iconst((ty), (v)))
#define IC(F_, BLK, PRED, A, B)  ({ Instr _i = ins_make(OP_ICMP, ty_i1()); _i.a = (A); _i.b = (B); _i.pred = (PRED); emit((F_), (BLK), _i); })
#define T3(F_, BLK, OP, TY, A, B, C) ({ Instr _i = ins_make((OP), (TY)); _i.a = (A); _i.b = (B); _i.c = (C); emit((F_), (BLK), _i); })
#define FC(F_, BLK, PRED, A, B)  ({ Instr _i = ins_make(OP_FCMP, ty_i1()); _i.a = (A); _i.b = (B); _i.pred = (PRED); emit((F_), (BLK), _i); })
#define ARG(f, blk, i)          ((f)->blocks[(blk)].arg_vals[(i)])

Module *build_battery(void) {
    Module *m = mod_new();
    /* externs exercised by the alchk functions: the driver provides
     * probes that report the AL value they were called with */
    mod_add_extern(m, "alprobe", (Type[]){ ty_f64() }, 1, ty_i64());
    mod_add_extern(m, "alprobe2", (Type[]){ ty_f64(), ty_f64() }, 2, ty_i64());
    static const uint32_t tab[4] = { 11, 22, 33, 44 };
    mod_add_data(m, "tab", 4, tab, sizeof tab);

    /* 0 arith64(i64 a, i64 b) -> i64 */
    {
        Func *f = mod_add_func(m, "arith64", ty_i64(), 0);
        int b = func_add_block(f, (Type[]){ ty_i64(), ty_i64() }, 2);
        int a = ARG(f, b, 0), bb = ARG(f, b, 1);
        int t1 = B(f, b, OP_MUL, ty_i64(), a, K(f, b, ty_i64(), 3));
        int t2 = B(f, b, OP_ADD, ty_i64(), t1, bb);
        int sh = B(f, b, OP_AND, ty_i64(), bb, K(f, b, ty_i64(), 63));
        int t3 = B(f, b, OP_ASHR, ty_i64(), a, sh);
        int t4 = B(f, b, OP_XOR, ty_i64(), t2, t3);
        int t5 = B(f, b, OP_SHL, ty_i64(), bb, K(f, b, ty_i64(), 2));
        int t6 = B(f, b, OP_SUB, ty_i64(), t4, t5);
        int pc = U(f, b, OP_POPCOUNT, ty_i64(), a);
        emit(f, b, ins_ret(B(f, b, OP_ADD, ty_i64(), t6, pc)));
    }
    /* 1 divs(i64 a, i64 b) -> i64 : a/b*7 + a%b */
    {
        Func *f = mod_add_func(m, "divs", ty_i64(), 0);
        int b = func_add_block(f, (Type[]){ ty_i64(), ty_i64() }, 2);
        int a = ARG(f, b, 0), bb = ARG(f, b, 1);
        int q = B(f, b, OP_SDIV, ty_i64(), a, bb);
        int r = B(f, b, OP_SREM, ty_i64(), a, bb);
        int q7 = B(f, b, OP_MUL, ty_i64(), q, K(f, b, ty_i64(), 7));
        emit(f, b, ins_ret(B(f, b, OP_ADD, ty_i64(), q7, r)));
    }
    /* 2 divu(u64 a, u64 b) -> u64 */
    {
        Func *f = mod_add_func(m, "divu", ty_i64(), 0);
        int b = func_add_block(f, (Type[]){ ty_i64(), ty_i64() }, 2);
        int a = ARG(f, b, 0), bb = ARG(f, b, 1);
        int q = B(f, b, OP_UDIV, ty_i64(), a, bb);
        int r = B(f, b, OP_UREM, ty_i64(), a, bb);
        emit(f, b, ins_ret(B(f, b, OP_ADD, ty_i64(), q, r)));
    }
    /* 3 narrow(i32 a, i32 b) -> i32 */
    {
        Func *f = mod_add_func(m, "narrow", ty_i32(), 0);
        int b = func_add_block(f, (Type[]){ ty_i32(), ty_i32() }, 2);
        int a = ARG(f, b, 0), bb = ARG(f, b, 1);
        int d = B(f, b, OP_OR, ty_i32(), bb, K(f, b, ty_i32(), 1));
        int q = B(f, b, OP_SDIV, ty_i32(), a, d);
        int r = B(f, b, OP_MUL, ty_i32(), q, K(f, b, ty_i32(), 31));
        int sh = B(f, b, OP_AND, ty_i32(), bb, K(f, b, ty_i32(), 7));
        r = B(f, b, OP_ASHR, ty_i32(), r, sh);
        r = B(f, b, OP_ADD, ty_i32(), r, U(f, b, OP_CLZ, ty_i32(), a));
        r = B(f, b, OP_ADD, ty_i32(), r, U(f, b, OP_CTZ, ty_i32(), bb));
        r = B(f, b, OP_ADD, ty_i32(), r, U(f, b, OP_POPCOUNT, ty_i32(),
                        B(f, b, OP_XOR, ty_i32(), a, bb)));
        int bs = U(f, b, OP_BSWAP, ty_i32(), a);
        r = B(f, b, OP_XOR, ty_i32(), r, B(f, b, OP_LSHR, ty_i32(), bs, K(f, b, ty_i32(), 16)));
        emit(f, b, ins_ret(r));
    }
    /* 4 fcalc(f64 a, f64 b) -> f64 : fma(a,b,1.25) - a/b + a*b */
    {
        Func *f = mod_add_func(m, "fcalc", ty_f64(), 0);
        int b = func_add_block(f, (Type[]){ ty_f64(), ty_f64() }, 2);
        int a = ARG(f, b, 0), bb = ARG(f, b, 1);
        double c125 = 1.25; uint64_t bits; memcpy(&bits, &c125, 8);
        int cc = emit(f, b, ins_fconst(ty_f64(), bits));
        Instr fm = ins_make(OP_FMA, ty_f64()); fm.a = a; fm.b = bb; fm.c = cc;
        int r1 = emit(f, b, fm);
        int dv = B(f, b, OP_FDIV, ty_f64(), a, bb);
        int mu = B(f, b, OP_FMUL, ty_f64(), a, bb);
        int r = B(f, b, OP_FSUB, ty_f64(), r1, dv);
        r = B(f, b, OP_FADD, ty_f64(), r, mu);
        emit(f, b, ins_ret(r));
    }
    /* 5 fcalc32(f32 a, f32 b) -> f32 */
    {
        Func *f = mod_add_func(m, "fcalc32", ty_f32(), 0);
        int b = func_add_block(f, (Type[]){ ty_f32(), ty_f32() }, 2);
        int a = ARG(f, b, 0), bb = ARG(f, b, 1);
        int mu = B(f, b, OP_FMUL, ty_f32(), a, bb);
        int r = B(f, b, OP_FADD, ty_f32(), mu, bb);
        r = B(f, b, OP_FSUB, ty_f32(), r, B(f, b, OP_FDIV, ty_f32(), a, bb));
        r = B(f, b, OP_FADD, ty_f32(), r, U(f, b, OP_FABS, ty_f32(), a));
        r = B(f, b, OP_FSUB, ty_f32(), r, U(f, b, OP_FNEG, ty_f32(), bb));
        emit(f, b, ins_ret(r));
    }
    /* 6 cvt_i(f64) -> i64 */
    {
        Func *f = mod_add_func(m, "cvt_i", ty_i64(), 0);
        int b = func_add_block(f, (Type[]){ ty_f64() }, 1);
        Instr i = ins_make(OP_FPTOSI, ty_i64()); i.a = ARG(f, b, 0);
        emit(f, b, ins_ret(emit(f, b, i)));
    }
    /* 7 cvt_u(f64) -> u64 */
    {
        Func *f = mod_add_func(m, "cvt_u", ty_i64(), 0);
        int b = func_add_block(f, (Type[]){ ty_f64() }, 1);
        Instr i = ins_make(OP_FPTOUI, ty_i64()); i.a = ARG(f, b, 0);
        emit(f, b, ins_ret(emit(f, b, i)));
    }
    /* 8 cvt_f(i64) -> f64 */
    {
        Func *f = mod_add_func(m, "cvt_f", ty_f64(), 0);
        int b = func_add_block(f, (Type[]){ ty_i64() }, 1);
        Instr i = ins_make(OP_SITOFP, ty_f64()); i.a = ARG(f, b, 0);
        emit(f, b, ins_ret(emit(f, b, i)));
    }
    /* 9 cvt_uf(u64) -> f64 */
    {
        Func *f = mod_add_func(m, "cvt_uf", ty_f64(), 0);
        int b = func_add_block(f, (Type[]){ ty_i64() }, 1);
        Instr i = ins_make(OP_UITOFP, ty_f64()); i.a = ARG(f, b, 0);
        emit(f, b, ins_ret(emit(f, b, i)));
    }
    /* 10 cvt_f32i(f32) -> i32 */
    {
        Func *f = mod_add_func(m, "cvt_f32i", ty_i32(), 0);
        int b = func_add_block(f, (Type[]){ ty_f32() }, 1);
        Instr i = ins_make(OP_FPTOSI, ty_i32()); i.a = ARG(f, b, 0);
        emit(f, b, ins_ret(emit(f, b, i)));
    }
    /* 11 cmp64(i64 a, i64 b) -> i64 bitmask */
    {
        Func *f = mod_add_func(m, "cmp64", ty_i64(), 0);
        int b = func_add_block(f, (Type[]){ ty_i64(), ty_i64() }, 2);
        int a = ARG(f, b, 0), bb = ARG(f, b, 1);
        int r = K(f, b, ty_i64(), 0);
        int preds[4] = { IC_SLT, IC_EQ, IC_UGT, IC_SGE };
        for (int i = 0; i < 4; i++) {
            int cnd = IC(f, b, preds[i], a, bb);
            int zx = U(f, b, OP_ZEXT, ty_i64(), cnd);
            int sh = B(f, b, OP_SHL, ty_i64(), zx, K(f, b, ty_i64(), i));
            r = B(f, b, OP_OR, ty_i64(), r, sh);
        }
        emit(f, b, ins_ret(r));
    }
    /* 12 fcmp64(f64 a, f64 b) -> i64 bitmask */
    {
        Func *f = mod_add_func(m, "fcmp64", ty_i64(), 0);
        int b = func_add_block(f, (Type[]){ ty_f64(), ty_f64() }, 2);
        int a = ARG(f, b, 0), bb = ARG(f, b, 1);
        int r = K(f, b, ty_i64(), 0);
        int preds[4] = { FC_OLT, FC_OEQ, FC_UNO, FC_UGE };
        for (int i = 0; i < 4; i++) {
            int cnd = FC(f, b, preds[i], a, bb);
            int zx = U(f, b, OP_ZEXT, ty_i64(), cnd);
            int sh = B(f, b, OP_SHL, ty_i64(), zx, K(f, b, ty_i64(), i));
            r = B(f, b, OP_OR, ty_i64(), r, sh);
        }
        emit(f, b, ins_ret(r));
    }
    /* 13 sel(i64 c, i64 a, i64 b) -> i64 */
    {
        Func *f = mod_add_func(m, "sel", ty_i64(), 0);
        int b = func_add_block(f, (Type[]){ ty_i64(), ty_i64(), ty_i64() }, 3);
        int cnd = IC(f, b, IC_NE, ARG(f, b, 0), K(f, b, ty_i64(), 0));
        Instr s = ins_make(OP_SELECT, ty_i64());
        s.a = cnd; s.b = ARG(f, b, 1); s.c = ARG(f, b, 2);
        emit(f, b, ins_ret(emit(f, b, s)));
    }
    /* 14 branch(i64 x) -> i64 : x > 10 ? x*2 : x+100 */
    {
        Func *f = mod_add_func(m, "branch", ty_i64(), 0);
        int b0 = func_add_block(f, (Type[]){ ty_i64() }, 1);
        int b1 = func_add_block(f, (Type[]){ ty_i64() }, 1);
        int b2 = func_add_block(f, (Type[]){ ty_i64() }, 1);
        int x = ARG(f, b0, 0);
        int cnd = IC(f, b0, IC_SGT, x, K(f, b0, ty_i64(), 10));
        emit(f, b0, ins_condbr(cnd, b1, ids_dup((int32_t[]){ x }, 1), 1,
                                   b2, ids_dup((int32_t[]){ x }, 1), 1));
        int x1 = ARG(f, b1, 0);
        emit(f, b1, ins_ret(B(f, b1, OP_MUL, ty_i64(), x1, K(f, b1, ty_i64(), 2))));
        int x2 = ARG(f, b2, 0);
        emit(f, b2, ins_ret(B(f, b2, OP_ADD, ty_i64(), x2, K(f, b2, ty_i64(), 100))));
    }
    /* 15 loop(i64 n) -> i64 : sum of squares */
    {
        Func *f = mod_add_func(m, "loop", ty_i64(), 0);
        int b0 = func_add_block(f, (Type[]){ ty_i64() }, 1);
        int b1 = func_add_block(f, (Type[]){ ty_i64(), ty_i64() }, 2);
        int b2 = func_add_block(f, (Type[]){ ty_i64(), ty_i64() }, 2);
        int b3 = func_add_block(f, (Type[]){ ty_i64() }, 1);
        int n = ARG(f, b0, 0);
        int z = K(f, b0, ty_i64(), 0), one = K(f, b0, ty_i64(), 1);
        emit(f, b0, ins_br(b1, ids_dup((int32_t[]){ one, z }, 2), 2));
        int i1 = ARG(f, b1, 0), acc1 = ARG(f, b1, 1);
        int cnd = IC(f, b1, IC_SLE, i1, n);
        emit(f, b1, ins_condbr(cnd, b2, ids_dup((int32_t[]){ i1, acc1 }, 2), 2,
                                   b3, ids_dup((int32_t[]){ acc1 }, 1), 1));
        int i2 = ARG(f, b2, 0), acc2 = ARG(f, b2, 1);
        int sq = B(f, b2, OP_MUL, ty_i64(), i2, i2);
        int acc3 = B(f, b2, OP_ADD, ty_i64(), acc2, sq);
        int inext = B(f, b2, OP_ADD, ty_i64(), i2, K(f, b2, ty_i64(), 1));
        emit(f, b2, ins_br(b1, ids_dup((int32_t[]){ inext, acc3 }, 2), 2));
        emit(f, b3, ins_ret(ARG(f, b3, 0)));
        (void)n;
    }
    /* 16 caller(i64 a, i64 b) -> i64 : arith64(a,b) + divs(a,b) */
    {
        Func *f = mod_add_func(m, "caller", ty_i64(), 0);
        int b = func_add_block(f, (Type[]){ ty_i64(), ty_i64() }, 2);
        int a = ARG(f, b, 0), bb = ARG(f, b, 1);
        int fi_arith = mod_find_func(m, "arith64");
        int fi_divs = mod_find_func(m, "divs");
        int r1 = emit(f, b, ins_call(ty_i64(), fi_arith, false, ids_dup((int32_t[]){ a, bb }, 2), 2, false));
        int r2 = emit(f, b, ins_call(ty_i64(), fi_divs, false, ids_dup((int32_t[]){ a, bb }, 2), 2, false));
        emit(f, b, ins_ret(B(f, b, OP_ADD, ty_i64(), r1, r2)));
    }
    /* 17 fact(i64 n) -> i64 recursive */
    {
        Func *f = mod_add_func(m, "fact", ty_i64(), 0);
        int fi_self = m->nfuncs - 1;
        int b0 = func_add_block(f, (Type[]){ ty_i64() }, 1);
        int b1 = func_add_block(f, (Type[]){ ty_i64() }, 1);
        int b2 = func_add_block(f, (Type[]){ ty_i64() }, 1);
        int n = ARG(f, b0, 0);
        int cnd = IC(f, b0, IC_SLE, n, K(f, b0, ty_i64(), 1));
        emit(f, b0, ins_condbr(cnd, b1, ids_dup((int32_t[]){ n }, 1), 1,
                                   b2, ids_dup((int32_t[]){ n }, 1), 1));
        emit(f, b1, ins_ret(K(f, b1, ty_i64(), 1)));
        int n2 = ARG(f, b2, 0);
        int nm1 = B(f, b2, OP_SUB, ty_i64(), n2, K(f, b2, ty_i64(), 1));
        int rec = emit(f, b2, ins_call(ty_i64(), fi_self, false, ids_dup((int32_t[]){ nm1 }, 1), 1, false));
        emit(f, b2, ins_ret(B(f, b2, OP_MUL, ty_i64(), n2, rec)));
    }
    /* 18 tail(i64 n, i64 acc) -> i64 tail recursion */
    {
        Func *f = mod_add_func(m, "tail", ty_i64(), 0);
        int fi_self = m->nfuncs - 1;
        int b0 = func_add_block(f, (Type[]){ ty_i64(), ty_i64() }, 2);
        int b1 = func_add_block(f, (Type[]){ ty_i64(), ty_i64() }, 2);
        int b2 = func_add_block(f, (Type[]){ ty_i64(), ty_i64() }, 2);
        int n = ARG(f, b0, 0), acc = ARG(f, b0, 1);
        int cnd = IC(f, b0, IC_EQ, n, K(f, b0, ty_i64(), 0));
        emit(f, b0, ins_condbr(cnd, b1, ids_dup((int32_t[]){ n, acc }, 2), 2,
                                   b2, ids_dup((int32_t[]){ n, acc }, 2), 2));
        emit(f, b1, ins_ret(ARG(f, b1, 1)));
        int n2 = ARG(f, b2, 0), acc2 = ARG(f, b2, 1);
        int nm1 = B(f, b2, OP_SUB, ty_i64(), n2, K(f, b2, ty_i64(), 1));
        int acc3 = B(f, b2, OP_ADD, ty_i64(), acc2, n2);
        emit(f, b2, ins_call(ty_i64(), fi_self, false, ids_dup((int32_t[]){ nm1, acc3 }, 2), 2, true));
    }
    /* 19 mem(ptr p, i64 i, i32 v) -> i32 */
    {
        Func *f = mod_add_func(m, "mem", ty_i32(), 0);
        int b = func_add_block(f, (Type[]){ ty_ptr(), ty_i64(), ty_i32() }, 3);
        int p = ARG(f, b, 0), i = ARG(f, b, 1), v = ARG(f, b, 2);
        Instr g = ins_make(OP_GEP, ty_ptr()); g.a = p; g.b = i; g.ety = ty_i32();
        int gp = emit(f, b, g);
        Instr st = ins_make(OP_STORE, ty_i32()); st.a = gp; st.b = v;
        emit(f, b, st);
        int i1 = B(f, b, OP_ADD, ty_i64(), i, K(f, b, ty_i64(), 1));
        Instr g2 = ins_make(OP_GEP, ty_ptr()); g2.a = p; g2.b = i1; g2.ety = ty_i32();
        int gp2 = emit(f, b, g2);
        int v1 = B(f, b, OP_ADD, ty_i32(), v, K(f, b, ty_i32(), 1));
        Instr st2 = ins_make(OP_STORE, ty_i32()); st2.a = gp2; st2.b = v1;
        emit(f, b, st2);
        Instr ld = ins_make(OP_LOAD, ty_i32()); ld.a = gp;
        emit(f, b, ins_ret(emit(f, b, ld)));
    }
    /* 20 alloca(i32 x) -> i32 */
    {
        Func *f = mod_add_func(m, "alloca", ty_i32(), 0);
        int b = func_add_block(f, (Type[]){ ty_i32() }, 1);
        int x = ARG(f, b, 0);
        Instr al = ins_make(OP_ALLOCA, ty_ptr()); al.imm = 16; al.c = 8;
        int sp = emit(f, b, al);
        Instr st = ins_make(OP_STORE, ty_i32()); st.a = sp; st.b = x;
        emit(f, b, st);
        Instr g = ins_make(OP_GEP, ty_ptr()); g.a = sp; g.b = K(f, b, ty_i64(), 1); g.ety = ty_i32();
        int sp1 = emit(f, b, g);
        int x2 = B(f, b, OP_ADD, ty_i32(), x, x);
        Instr st2 = ins_make(OP_STORE, ty_i32()); st2.a = sp1; st2.b = x2;
        emit(f, b, st2);
        Instr ld = ins_make(OP_LOAD, ty_i32()); ld.a = sp;
        int r1 = emit(f, b, ld);
        Instr ld2 = ins_make(OP_LOAD, ty_i32()); ld2.a = sp1;
        int r2 = emit(f, b, ld2);
        emit(f, b, ins_ret(B(f, b, OP_ADD, ty_i32(), r1, r2)));
    }
    /* 21 atomic(ptr p, i64 v) -> i64 : old=aadd(p,v); return old*1000 + aload(p) */
    {
        Func *f = mod_add_func(m, "atomic", ty_i64(), 0);
        int b = func_add_block(f, (Type[]){ ty_ptr(), ty_i64() }, 2);
        int p = ARG(f, b, 0), v = ARG(f, b, 1);
        Instr aa = ins_make(OP_AADD, ty_i64()); aa.a = p; aa.b = v; aa.aux = AO_SEQCST;
        int old = emit(f, b, aa);
        Instr al = ins_make(OP_ALOAD, ty_i64()); al.a = p; al.aux = AO_SEQCST;
        int cur = emit(f, b, al);
        int r = B(f, b, OP_MUL, ty_i64(), old, K(f, b, ty_i64(), 1000));
        emit(f, b, ins_ret(B(f, b, OP_ADD, ty_i64(), r, cur)));
    }
    /* 22 rmw(ptr p, i64 v) -> i64 : the v3 RMW family + cmpxchg over one
     * cell. Every op returns the old value; fold them together and finish
     * with the final cell contents (memory is compared too, via the B-case
     * image). The first cmpxchg must succeed (expected = current cell),
     * the second must fail unless the cell coincidentally holds 42. */
    {
        Func *f = mod_add_func(m, "rmw", ty_i64(), 0);
        int b = func_add_block(f, (Type[]){ ty_ptr(), ty_i64() }, 2);
        int p = ARG(f, b, 0), v = ARG(f, b, 1);
        #define RMW1(op, operand) ({ Instr _i = ins_make((op), ty_i64()); _i.a = p; _i.b = (operand); _i.aux = AO_SEQCST; emit(f, b, _i); })
        int o1 = RMW1(OP_AXCHG, v);
        int o2 = RMW1(OP_ASUB, K(f, b, ty_i64(), 5));
        int o3 = RMW1(OP_AAND, v);
        int o4 = RMW1(OP_AOR, K(f, b, ty_i64(), 0x5a5a));
        int o5 = RMW1(OP_AXOR, v);
        int o6 = RMW1(OP_AMINS, K(f, b, ty_i64(), -3));
        int o7 = RMW1(OP_AMAXS, K(f, b, ty_i64(), 17));
        int o8 = RMW1(OP_AMINU, K(f, b, ty_i64(), 1000));
        int o9 = RMW1(OP_AMAXU, K(f, b, ty_i64(), 3));
        #undef RMW1
        Instr al = ins_make(OP_ALOAD, ty_i64()); al.a = p; al.aux = AO_SEQCST;
        int cur = emit(f, b, al);
        Instr cx = ins_make(OP_ACMPXCHG, ty_i64()); cx.a = p; cx.b = cur; cx.c = K(f, b, ty_i64(), 42); cx.aux = AO_SEQCST;
        int oc = emit(f, b, cx);
        Instr cx2 = ins_make(OP_ACMPXCHG, ty_i64()); cx2.a = p; cx2.b = cur; cx2.c = K(f, b, ty_i64(), 43); cx2.aux = AO_ACQREL;
        int oc2 = emit(f, b, cx2);
        Instr al2 = ins_make(OP_ALOAD, ty_i64()); al2.a = p; al2.aux = AO_RELAXED;
        int fin = emit(f, b, al2);
        int olds[11] = { o1, o2, o3, o4, o5, o6, o7, o8, o9, oc, oc2 };
        int r = fin;
        for (int i = 0; i < 11; i++)
            r = B(f, b, OP_ADD, ty_i64(), B(f, b, OP_MUL, ty_i64(), r, K(f, b, ty_i64(), 31)), olds[i]);
        emit(f, b, ins_ret(r));
    }
    /* 23 rmw32(ptr p, i32 v) -> i32 : the 32-bit forms */
    {
        Func *f = mod_add_func(m, "rmw32", ty_i32(), 0);
        int b = func_add_block(f, (Type[]){ ty_ptr(), ty_i32() }, 2);
        int p = ARG(f, b, 0), v = ARG(f, b, 1);
        #define RMW32(op, operand) ({ Instr _i = ins_make((op), ty_i32()); _i.a = p; _i.b = (operand); _i.aux = AO_SEQCST; emit(f, b, _i); })
        int o1 = RMW32(OP_AXCHG, v);
        int o2 = RMW32(OP_ASUB, K(f, b, ty_i32(), 100000));
        int o3 = RMW32(OP_AMINS, K(f, b, ty_i32(), -7));
        int o4 = RMW32(OP_AMAXU, K(f, b, ty_i32(), 65536));
        #undef RMW32
        Instr al = ins_make(OP_ALOAD, ty_i32()); al.a = p; al.aux = AO_SEQCST;
        int cur = emit(f, b, al);
        Instr cx = ins_make(OP_ACMPXCHG, ty_i32()); cx.a = p; cx.b = cur; cx.c = K(f, b, ty_i32(), -1); cx.aux = AO_SEQCST;
        int oc = emit(f, b, cx);
        int olds[5] = { o1, o2, o3, o4, oc };
        int r = cur;
        for (int i = 0; i < 5; i++)
            r = B(f, b, OP_ADD, ty_i32(), B(f, b, OP_MUL, ty_i32(), r, K(f, b, ty_i32(), 31)), olds[i]);
        emit(f, b, ins_ret(r));
    }
    /* 24 rmw8(ptr p, i64 v) -> i64 : the 8-bit (sub-word) forms */
    {
        Func *f = mod_add_func(m, "rmw8", ty_i64(), 0);
        int b = func_add_block(f, (Type[]){ ty_ptr(), ty_i64() }, 2);
        int p = ARG(f, b, 0), v = ARG(f, b, 1);
        int v8 = U(f, b, OP_TRUNC, ty_i8(), v);
        #define RMW8(op, operand) ({ Instr _i = ins_make((op), ty_i8()); _i.a = p; _i.b = (operand); _i.aux = AO_SEQCST; emit(f, b, _i); })
        int o1 = RMW8(OP_AXCHG, v8);
        int o2 = RMW8(OP_ASUB, K(f, b, ty_i8(), 3));
        int o3 = RMW8(OP_AAND, v8);
        int o4 = RMW8(OP_AMAXS, K(f, b, ty_i8(), -2));
        #undef RMW8
        Instr al = ins_make(OP_ALOAD, ty_i8()); al.a = p; al.aux = AO_SEQCST;
        int cur = emit(f, b, al);
        Instr cx = ins_make(OP_ACMPXCHG, ty_i8()); cx.a = p; cx.b = cur; cx.c = K(f, b, ty_i8(), 0x55); cx.aux = AO_SEQCST;
        int oc = emit(f, b, cx);
        int olds[5] = { o1, o2, o3, o4, oc };
        int r = U(f, b, OP_ZEXT, ty_i64(), cur);
        for (int i = 0; i < 5; i++) {
            int z = U(f, b, OP_ZEXT, ty_i64(), olds[i]);
            r = B(f, b, OP_ADD, ty_i64(), B(f, b, OP_MUL, ty_i64(), r, K(f, b, ty_i64(), 31)), z);
        }
        emit(f, b, ins_ret(r));
    }
    /* 26 w128(i64 a, i64 b) -> i64 : i128 arithmetic end to end -
     * zext, shl into the high word, add (carry), mul by 3, lshr,
     * icmp, popcount, and an alloca store/load round trip - folded
     * into an i64 checksum the driver can compare */
    {
        Func *f = mod_add_func(m, "w128", ty_i64(), 0);
        int b = func_add_block(f, (Type[]){ ty_i64(), ty_i64() }, 2);
        int a = ARG(f, b, 0), bb = ARG(f, b, 1);
        Type W = ty_i128();
        int x = U(f, b, OP_ZEXT, W, a);
        int y = U(f, b, OP_ZEXT, W, bb);
        y = B(f, b, OP_SHL, W, y, K(f, b, W, 64));
        int v = B(f, b, OP_ADD, W, x, y);
        int w = B(f, b, OP_MUL, W, v, K(f, b, W, 3));
        int sh = B(f, b, OP_LSHR, W, w, K(f, b, W, 37));
        int pc = U(f, b, OP_POPCOUNT, W, sh);
        Instr cmp = ins_make(OP_ICMP, ty_i1()); cmp.a = sh; cmp.b = K(f, b, W, 1000); cmp.pred = IC_UGT;
        int gt = emit(f, b, cmp);
        int g1 = U(f, b, OP_ZEXT, ty_i64(), gt);
        Instr al = ins_make(OP_ALLOCA, ty_ptr()); al.imm = 16; al.c = 16;
        int cell = emit(f, b, al);
        Instr st = ins_make(OP_STORE, W); st.a = cell; st.b = v;
        emit(f, b, st);
        Instr ld = ins_make(OP_LOAD, W); ld.a = cell;
        int back = emit(f, b, ld);
        back = B(f, b, OP_ADD, W, back, K(f, b, W, 1));
        int lo = U(f, b, OP_TRUNC, ty_i64(), sh);
        int hi = U(f, b, OP_TRUNC, ty_i64(), B(f, b, OP_LSHR, W, sh, K(f, b, W, 64)));
        int mlo = U(f, b, OP_TRUNC, ty_i64(), back);
        int pclo = U(f, b, OP_TRUNC, ty_i64(), pc);
        int r = B(f, b, OP_ADD, ty_i64(), B(f, b, OP_MUL, ty_i64(), lo, K(f, b, ty_i64(), 31)), hi);
        r = B(f, b, OP_ADD, ty_i64(), B(f, b, OP_MUL, ty_i64(), r, K(f, b, ty_i64(), 31)), mlo);
        r = B(f, b, OP_ADD, ty_i64(), B(f, b, OP_MUL, ty_i64(), r, K(f, b, ty_i64(), 31)), pclo);
        r = B(f, b, OP_ADD, ty_i64(), r, g1);
        emit(f, b, ins_ret(r));
    }
    /* 25 vecadd(ptr dst, ptr src) */
    {
        Func *f = mod_add_func(m, "vecadd", ty_void(), 0);
        int b = func_add_block(f, (Type[]){ ty_ptr(), ty_ptr() }, 2);
        Type vt = ty_vec(ty_i32(), 1);
        Instr vl = ins_make(OP_VLOAD, vt); vl.a = ARG(f, b, 1);
        int v = emit(f, b, vl);
        int sp = emit(f, b, ins_un(OP_VSPLAT, vt, K(f, b, ty_i32(), 7)));
        int r = B(f, b, OP_VADD, vt, v, sp);
        Instr vs = ins_make(OP_VSTORE, ty_void()); vs.a = ARG(f, b, 0); vs.b = r;
        emit(f, b, vs);
        emit(f, b, ins_ret(-1));
    }
    /* 23 vecf(ptr dst, ptr src, f32 k) */
    {
        Func *f = mod_add_func(m, "vecf", ty_void(), 0);
        int b = func_add_block(f, (Type[]){ ty_ptr(), ty_ptr(), ty_f32() }, 3);
        Type vt = ty_vec(ty_f32(), 1);
        Instr vl = ins_make(OP_VLOAD, vt); vl.a = ARG(f, b, 1);
        int v = emit(f, b, vl);
        int sp = emit(f, b, ins_un(OP_VSPLAT, vt, ARG(f, b, 2)));
        int r = B(f, b, OP_VFMUL, vt, v, sp);
        r = B(f, b, OP_VFADD, vt, r, v);
        Instr vs = ins_make(OP_VSTORE, ty_void()); vs.a = ARG(f, b, 0); vs.b = r;
        emit(f, b, vs);
        emit(f, b, ins_ret(-1));
    }
    /* 24 memcpy_(ptr dst, ptr src, i64 n) / 25 memset_(ptr dst, i32 byte, i64 n) */
    {
        Func *f = mod_add_func(m, "memcpy_", ty_void(), 0);
        int b = func_add_block(f, (Type[]){ ty_ptr(), ty_ptr(), ty_i64() }, 3);
        Instr mc = ins_make(OP_MEMCPY, ty_void());
        mc.a = ARG(f, b, 0); mc.b = ARG(f, b, 1); mc.c = ARG(f, b, 2);
        emit(f, b, mc);
        emit(f, b, ins_ret(-1));
    }
    {
        Func *f = mod_add_func(m, "memset_", ty_void(), 0);
        int b = func_add_block(f, (Type[]){ ty_ptr(), ty_i32(), ty_i64() }, 3);
        Instr ms = ins_make(OP_MEMSET, ty_void());
        ms.a = ARG(f, b, 0); ms.b = ARG(f, b, 1); ms.c = ARG(f, b, 2);
        emit(f, b, ms);
        emit(f, b, ins_ret(-1));
    }
    /* 26 data_load() -> i32 : tab[2] */
    {
        Func *f = mod_add_func(m, "data_load", ty_i32(), 0);
        int b = func_add_block(f, NULL, 0);
        Instr dp = ins_make(OP_DATAPTR, ty_ptr()); dp.imm = 0;
        int p = emit(f, b, dp);
        Instr g = ins_make(OP_GEP, ty_ptr()); g.a = p; g.b = K(f, b, ty_i64(), 2); g.ety = ty_i32();
        int gp = emit(f, b, g);
        Instr ld = ins_make(OP_LOAD, ty_i32()); ld.a = gp;
        emit(f, b, ins_ret(emit(f, b, ld)));
    }
    /* 27 vecins(ptr dst, ptr src, i32 v) */
    {
        Func *f = mod_add_func(m, "vecins", ty_void(), 0);
        int b = func_add_block(f, (Type[]){ ty_ptr(), ty_ptr(), ty_i32() }, 3);
        Type vt = ty_vec(ty_i32(), 1);
        Instr vl = ins_make(OP_VLOAD, vt); vl.a = ARG(f, b, 1);
        int v = emit(f, b, vl);
        Instr vi = ins_make(OP_VINSERT, vt); vi.a = v; vi.b = ARG(f, b, 2); vi.imm = 2;
        int r = emit(f, b, vi);
        Instr vs = ins_make(OP_VSTORE, ty_void()); vs.a = ARG(f, b, 0); vs.b = r;
        emit(f, b, vs);
        emit(f, b, ins_ret(-1));
    }
    /* 28 vecext(ptr src) -> i32 : lane 3 */
    {
        Func *f = mod_add_func(m, "vecext", ty_i32(), 0);
        int b = func_add_block(f, (Type[]){ ty_ptr() }, 1);
        Type vt = ty_vec(ty_i32(), 1);
        Instr vl = ins_make(OP_VLOAD, vt); vl.a = ARG(f, b, 0);
        int v = emit(f, b, vl);
        Instr ve = ins_make(OP_VEXTRACT, ty_i32()); ve.a = v; ve.imm = 3;
        emit(f, b, ins_ret(emit(f, b, ve)));
    }
    /* 29 gepneg(ptr p) -> i32 : *(p - 1) */
    {
        Func *f = mod_add_func(m, "gepneg", ty_i32(), 0);
        int b = func_add_block(f, (Type[]){ ty_ptr() }, 1);
        Instr g = ins_make(OP_GEP, ty_ptr()); g.a = ARG(f, b, 0); g.b = K(f, b, ty_i64(), -1); g.ety = ty_i32();
        int gp = emit(f, b, g);
        Instr ld = ins_make(OP_LOAD, ty_i32()); ld.a = gp;
        emit(f, b, ins_ret(emit(f, b, ld)));
    }
    /* 30 bitcast_df(f64) -> i64 / bitcast_id(i64) -> f64 */
    {
        Func *f = mod_add_func(m, "bitcast_df", ty_i64(), 0);
        int b = func_add_block(f, (Type[]){ ty_f64() }, 1);
        Instr bc = ins_make(OP_BITCAST, ty_i64()); bc.a = ARG(f, b, 0);
        emit(f, b, ins_ret(emit(f, b, bc)));
    }
    {
        Func *f = mod_add_func(m, "bitcast_id", ty_f64(), 0);
        int b = func_add_block(f, (Type[]){ ty_i64() }, 1);
        Instr bc = ins_make(OP_BITCAST, ty_f64()); bc.a = ARG(f, b, 0);
        emit(f, b, ins_ret(emit(f, b, bc)));
    }
    /* 31 fround(f32) -> f64 (fext) / fround2(f64) -> f32 (ftrunc) */
    {
        Func *f = mod_add_func(m, "fround", ty_f64(), 0);
        int b = func_add_block(f, (Type[]){ ty_f32() }, 1);
        Instr e = ins_make(OP_FEXT, ty_f64()); e.a = ARG(f, b, 0);
        emit(f, b, ins_ret(emit(f, b, e)));
    }
    {
        Func *f = mod_add_func(m, "fround2", ty_f32(), 0);
        int b = func_add_block(f, (Type[]){ ty_f64() }, 1);
        Instr e = ins_make(OP_FTRUNC, ty_f32()); e.a = ARG(f, b, 0);
        emit(f, b, ins_ret(emit(f, b, e)));
    }
    /* 32 manyargs: 8 i64 + 2 f64 args (stack-arg coverage) */
    {
        Func *f = mod_add_func(m, "manyargs", ty_i64(), 0);
        Type pa[10] = { ty_i64(), ty_i64(), ty_i64(), ty_i64(), ty_i64(), ty_i64(),
                        ty_i64(), ty_i64(), ty_f64(), ty_f64() };
        int b = func_add_block(f, pa, 10);
        int r = ARG(f, b, 0);
        for (int i = 1; i < 8; i++) r = B(f, b, OP_ADD, ty_i64(), r, ARG(f, b, i));
        Instr c1 = ins_make(OP_FPTOSI, ty_i64()); c1.a = ARG(f, b, 8);
        int t1 = emit(f, b, c1);
        Instr c2 = ins_make(OP_FPTOSI, ty_i64()); c2.a = ARG(f, b, 9);
        int t2 = emit(f, b, c2);
        r = B(f, b, OP_ADD, ty_i64(), r, t1);
        r = B(f, b, OP_ADD, ty_i64(), r, t2);
        emit(f, b, ins_ret(r));
    }
    /* 33 spills: many live values across a call */
    {
        Func *f = mod_add_func(m, "spills", ty_i64(), 0);
        int fi_arith = mod_find_func(m, "arith64");
        int b = func_add_block(f, (Type[]){ ty_i64() }, 1);
        int x = ARG(f, b, 0);
        int vs[16];
        for (int i = 0; i < 16; i++)
            vs[i] = B(f, b, OP_ADD, ty_i64(), x, K(f, b, ty_i64(), i * 7 + 1));
        int mid = emit(f, b, ins_call(ty_i64(), fi_arith, false,
                        ids_dup((int32_t[]){ vs[3], vs[9] }, 2), 2, false));
        int r = mid;
        for (int i = 0; i < 16; i++) r = B(f, b, OP_ADD, ty_i64(), r, vs[i]);
        emit(f, b, ins_ret(r));
    }
    /* 36 clobx(i64 seed) -> i64 : register-pressure loop saturated
     * with clobber-class operations -- twelve loop-carried values
     * stay live across a variable shift (count is itself a carried
     * value), a funnel shift, a division (divisor likewise), and a
     * store/load round trip under pressure. Exercises the x86
     * clobber-aware pool: homes in RAX/RCX/RDX are only sound where
     * the clobber analysis proves the interval clear, and operands
     * consumed by the clobbering instruction itself rely on the
     * blessing rules. */
    {
        Func *f = mod_add_func(m, "clobx", ty_i64(), 0);
        int b0 = func_add_block(f, (Type[]){ ty_i64() }, 1);
        Type ht[14];
        for (int i = 0; i < 14; i++) ht[i] = ty_i64();
        int b1 = func_add_block(f, ht, 14);
        int b2 = func_add_block(f, (Type[]){ ty_i64() }, 1);
        int seed = ARG(f, b0, 0);
        Instr al = ins_make(OP_ALLOCA, ty_ptr()); al.imm = 8; al.c = 8;
        int cell = emit(f, b0, al);
        int v0[12];
        for (int i = 0; i < 12; i++)
            v0[i] = B(f, b0, OP_ADD, ty_i64(), seed, K(f, b0, ty_i64(), i * 37 + 11));
        emit(f, b0, ins_br(b1, ids_dup((int32_t[]){ v0[0], v0[1], v0[2], v0[3], v0[4], v0[5],
                        v0[6], v0[7], v0[8], v0[9], v0[10], v0[11],
                        K(f, b0, ty_i64(), 0), K(f, b0, ty_i64(), 0) }, 14), 14));
        int v[12], it, acc;
        for (int i = 0; i < 12; i++) v[i] = ARG(f, b1, i);
        it = ARG(f, b1, 12); acc = ARG(f, b1, 13);
        int t0 = B(f, b1, OP_SHL, ty_i64(), v[0], v[1]);
        int t1 = T3(f, b1, OP_FSHL, ty_i64(), v[2], v[3], v[4]);
        int dv = B(f, b1, OP_OR, ty_i64(), v[6], K(f, b1, ty_i64(), 1));
        int t2 = B(f, b1, OP_SDIV, ty_i64(), v[5], dv);
        Instr st = ins_make(OP_STORE, ty_i64()); st.a = cell; st.b = v[7];
        emit(f, b1, st);
        Instr ld = ins_make(OP_LOAD, ty_i64()); ld.a = cell;
        int t3 = emit(f, b1, ld);
        int n[12];
        n[0] = B(f, b1, OP_ADD, ty_i64(), v[0], t0);
        n[1] = B(f, b1, OP_XOR, ty_i64(), v[1], t1);
        n[2] = B(f, b1, OP_ADD, ty_i64(), v[2], t2);
        n[3] = B(f, b1, OP_ADD, ty_i64(), B(f, b1, OP_MUL, ty_i64(), v[3], K(f, b1, ty_i64(), 3)), t3);
        n[4] = B(f, b1, OP_ADD, ty_i64(), v[4], v[8]);
        n[5] = B(f, b1, OP_ADD, ty_i64(), v[5], v[9]);
        n[6] = B(f, b1, OP_ADD, ty_i64(), v[6], v[10]);
        n[7] = B(f, b1, OP_ADD, ty_i64(), v[7], v[11]);
        n[8] = B(f, b1, OP_ADD, ty_i64(), v[8], t0);
        n[9] = B(f, b1, OP_ADD, ty_i64(), v[9], t1);
        n[10] = B(f, b1, OP_ADD, ty_i64(), v[10], t2);
        n[11] = B(f, b1, OP_ADD, ty_i64(), v[11], t3);
        int nacc = B(f, b1, OP_ADD, ty_i64(), acc, t2);
        int nit = B(f, b1, OP_ADD, ty_i64(), it, K(f, b1, ty_i64(), 1));
        int cnd = IC(f, b1, IC_SLT, nit, K(f, b1, ty_i64(), 24));
        emit(f, b1, ins_condbr(cnd, b1, ids_dup((int32_t[]){ n[0], n[1], n[2], n[3], n[4], n[5],
                        n[6], n[7], n[8], n[9], n[10], n[11], nit, nacc }, 14), 14,
                                   b2, ids_dup((int32_t[]){ nacc }, 1), 1));
        emit(f, b2, ins_ret(ARG(f, b2, 0)));
    }
    /* 37 clobcall(i64 seed) -> i64 : mixed intervals -- six long
     * values live across two calls while a burst of short shift /
     * funnel / divide temps churns between them. The long values
     * must never sit in a caller-saved home; the temps may. */
    {
        Func *f = mod_add_func(m, "clobcall", ty_i64(), 0);
        int fi_arith = mod_find_func(m, "arith64");
        int b = func_add_block(f, (Type[]){ ty_i64() }, 1);
        int x = ARG(f, b, 0);
        int L[6];
        for (int i = 0; i < 6; i++)
            L[i] = B(f, b, OP_ADD, ty_i64(), B(f, b, OP_MUL, ty_i64(), x, K(f, b, ty_i64(), i + 2)),
                     K(f, b, ty_i64(), i * 101 + 7));
        int c1 = emit(f, b, ins_call(ty_i64(), fi_arith, false,
                        ids_dup((int32_t[]){ L[0], L[1] }, 2), 2, false));
        int ts = K(f, b, ty_i64(), 0);
        for (int i = 0; i < 6; i++) {
            int t = B(f, b, OP_SHL, ty_i64(), L[i], B(f, b, OP_AND, ty_i64(), L[(i + 2) % 6], K(f, b, ty_i64(), 63)));
            t = T3(f, b, OP_FSHR, ty_i64(), t, L[(i + 1) % 6], B(f, b, OP_AND, ty_i64(), L[(i + 3) % 6], K(f, b, ty_i64(), 63)));
            t = B(f, b, OP_ADD, ty_i64(), t, B(f, b, OP_SDIV, ty_i64(), L[(i + 4) % 6],
                      B(f, b, OP_OR, ty_i64(), L[(i + 5) % 6], K(f, b, ty_i64(), 1))));
            ts = B(f, b, OP_ADD, ty_i64(), ts, t);
        }
        int c2 = emit(f, b, ins_call(ty_i64(), fi_arith, false,
                        ids_dup((int32_t[]){ L[2], L[3] }, 2), 2, false));
        int r = B(f, b, OP_ADD, ty_i64(), c1, c2);
        r = B(f, b, OP_ADD, ty_i64(), r, ts);
        for (int i = 0; i < 6; i++) r = B(f, b, OP_ADD, ty_i64(), r, L[i]);
        emit(f, b, ins_ret(r));
    }
    /* 38 selx(i64 seed) -> i64 : two-state interleave selects under
     * register pressure -- state = turn ? s1 : s2, then s1/s2 are
     * conditionally updated from the decoded value while six other
     * values stay live. Witness for the x86 OP_SELECT emission
     * hazard: when the allocator homes a select's result in its
     * true arm's register, a false-arm-first copy order destroys
     * the arm before the conditional copy reads it. */
    {
        Func *f = mod_add_func(m, "selx", ty_i64(), 0);
        int b0 = func_add_block(f, (Type[]){ ty_i64() }, 1);
        Type ht[11];
        for (int i = 0; i < 11; i++) ht[i] = ty_i64();
        int b1 = func_add_block(f, ht, 11);
        int b2 = func_add_block(f, (Type[]){ ty_i64() }, 1);
        int seed = ARG(f, b0, 0);
        int iv[11];
        for (int i = 0; i < 11; i++)
            iv[i] = B(f, b0, OP_ADD, ty_i64(), seed, K(f, b0, ty_i64(), i * 53 + 3));
        iv[2] = K(f, b0, ty_i64(), 0);   /* turn */
        iv[9] = K(f, b0, ty_i64(), 0);   /* it */
        iv[10] = K(f, b0, ty_i64(), 0);  /* acc */
        emit(f, b0, ins_br(b1, ids_dup(iv, 11), 11));
        int s1 = ARG(f, b1, 0), s2 = ARG(f, b1, 1), turn = ARG(f, b1, 2);
        int p[6];
        for (int i = 0; i < 6; i++) p[i] = ARG(f, b1, 3 + i);
        int it = ARG(f, b1, 9), acc = ARG(f, b1, 10);
        Instr eq = ins_make(OP_ICMP, ty_i1()); eq.a = turn; eq.b = K(f, b1, ty_i64(), 0); eq.pred = IC_EQ;
        int ist1 = emit(f, b1, eq);
        Instr sel0 = ins_make(OP_SELECT, ty_i64()); sel0.a = ist1; sel0.b = s1; sel0.c = s2;
        int state = emit(f, b1, sel0);
        int snew = B(f, b1, OP_ADD, ty_i64(), B(f, b1, OP_MUL, ty_i64(), state, K(f, b1, ty_i64(), 31)),
                     B(f, b1, OP_XOR, ty_i64(), p[0], p[3]));
        Instr sel1 = ins_make(OP_SELECT, ty_i64()); sel1.a = ist1; sel1.b = snew; sel1.c = s1;
        int s1n = emit(f, b1, sel1);
        Instr sel2 = ins_make(OP_SELECT, ty_i64()); sel2.a = ist1; sel2.b = s2; sel2.c = snew;
        int s2n = emit(f, b1, sel2);
        int np[6], nacc = acc;
        for (int i = 0; i < 6; i++) {
            np[i] = B(f, b1, OP_ADD, ty_i64(), p[i], B(f, b1, OP_SHL, ty_i64(), snew, K(f, b1, ty_i64(), i + 1)));
            nacc = B(f, b1, OP_ADD, ty_i64(), nacc, np[i]);
        }
        int nit = B(f, b1, OP_ADD, ty_i64(), it, K(f, b1, ty_i64(), 1));
        int nturn = B(f, b1, OP_XOR, ty_i64(), turn, K(f, b1, ty_i64(), 1));
        int cnd = IC(f, b1, IC_SLT, nit, K(f, b1, ty_i64(), 30));
        int b3 = func_add_block(f, ht, 11);
        emit(f, b1, ins_condbr(cnd, b3, ids_dup((int32_t[]){ s1n, s2n, nturn, np[0], np[1], np[2],
                        np[3], np[4], np[5], nit, nacc }, 11), 11,
                                   b2, ids_dup((int32_t[]){ nacc }, 1), 1));
        /* the body block returns to the header with an unconditional
         * branch -- the shape under which the allocator hands the
         * s2 select its true arm's home via block-arg coalescing */
        int fwd[11];
        for (int i = 0; i < 11; i++) fwd[i] = ARG(f, b3, i);
        emit(f, b3, ins_br(b1, ids_dup(fwd, 11), 11));
        emit(f, b2, ins_ret(ARG(f, b2, 0)));
    }
    /* 39 rotw(i64 w, i64 u0) -> i64 : loop-rotation witness. The
     * header/body split passes every value through the body block,
     * so identity block-argument elimination removes ALL of the
     * body's parameters and its instructions end up referencing the
     * header's parameters directly. Loop rotation rewrites the
     * back edge into a self edge bound by the body's own parameter
     * list; for this shape the carried values (i, u, acc) have no
     * binding on that edge, so rotation must reject the loop --
     * rotating it freezes the carried values at their entry values
     * (the krellproof span kernel hangs on exactly this shape).
     * Expected: acc = sum of u over w iterations, u stepping by 3. */
    {
        Func *f = mod_add_func(m, "rotw", ty_i64(), 0);
        Type pt[5];
        for (int i = 0; i < 5; i++) pt[i] = ty_i64();
        int b0 = func_add_block(f, (Type[]){ ty_i64(), ty_i64() }, 2);
        int b1 = func_add_block(f, pt, 5);
        int b2 = func_add_block(f, pt, 5);
        int b3 = func_add_block(f, (Type[]){ ty_i64() }, 1);
        int w = ARG(f, b0, 0), u0 = ARG(f, b0, 1);
        emit(f, b0, ins_br(b1, ids_dup((int32_t[]){ K(f, b0, ty_i64(), 0), u0,
                        K(f, b0, ty_i64(), 0), w, K(f, b0, ty_i64(), 3) }, 5), 5));
        int hi = ARG(f, b1, 0), hu = ARG(f, b1, 1), hacc = ARG(f, b1, 2);
        int hw = ARG(f, b1, 3), hdu = ARG(f, b1, 4);
        int c = IC(f, b1, IC_SLT, hi, hw);
        emit(f, b1, ins_condbr(c, b2, ids_dup((int32_t[]){ hi, hu, hacc, hw, hdu }, 5), 5,
                                  b3, ids_dup((int32_t[]){ hacc }, 1), 1));
        int bi = ARG(f, b2, 0), bu = ARG(f, b2, 1), bacc = ARG(f, b2, 2);
        int bw = ARG(f, b2, 3), bdu = ARG(f, b2, 4);
        int nacc = B(f, b2, OP_ADD, ty_i64(), bacc, bu);
        int nu = B(f, b2, OP_ADD, ty_i64(), bu, bdu);
        int ni = B(f, b2, OP_ADD, ty_i64(), bi, K(f, b2, ty_i64(), 1));
        emit(f, b2, ins_br(b1, ids_dup((int32_t[]){ ni, nu, nacc, bw, bdu }, 5), 5));
        emit(f, b3, ins_ret(ARG(f, b3, 0)));
    }
    /* 34 tadd/tmul: indirect-call targets (no driver cases of their own) */
    {
        Func *f = mod_add_func(m, "tadd", ty_i64(), 0);
        int b = func_add_block(f, (Type[]){ ty_i64(), ty_i64() }, 2);
        emit(f, b, ins_ret(B(f, b, OP_ADD, ty_i64(), ARG(f, b, 0), ARG(f, b, 1))));
    }
    {
        Func *f = mod_add_func(m, "tmul", ty_i64(), 0);
        int b = func_add_block(f, (Type[]){ ty_i64(), ty_i64() }, 2);
        emit(f, b, ins_ret(B(f, b, OP_MUL, ty_i64(), ARG(f, b, 0), ARG(f, b, 1))));
    }
    /* 35 vtable(i64 sel, i64 x) -> i64 : a two-entry function-pointer
     * table in an alloca, indexed, loaded, and called indirectly */
    {
        int sg = mod_add_sig(m, (Type[]){ ty_i64(), ty_i64() }, 2, ty_i64());
        Func *f = mod_add_func(m, "vtable", ty_i64(), 0);
        int b = func_add_block(f, (Type[]){ ty_i64(), ty_i64() }, 2);
        int sel = ARG(f, b, 0), x = ARG(f, b, 1);
        Instr al = ins_make(OP_ALLOCA, ty_ptr()); al.imm = 16; al.c = 8;
        int cell = emit(f, b, al);
        int pa = emit(f, b, ins_funcptr(mod_find_func(m, "tadd"), false));
        Instr st0 = ins_make(OP_STORE, ty_ptr()); st0.a = cell; st0.b = pa;
        emit(f, b, st0);
        Instr g1 = ins_make(OP_GEP, ty_ptr()); g1.a = cell; g1.b = K(f, b, ty_i64(), 1); g1.ety = ty_ptr();
        int slot1 = emit(f, b, g1);
        int pb = emit(f, b, ins_funcptr(mod_find_func(m, "tmul"), false));
        Instr st1 = ins_make(OP_STORE, ty_ptr()); st1.a = slot1; st1.b = pb;
        emit(f, b, st1);
        int idx = B(f, b, OP_AND, ty_i64(), sel, K(f, b, ty_i64(), 1));
        Instr gs = ins_make(OP_GEP, ty_ptr()); gs.a = cell; gs.b = idx; gs.ety = ty_ptr();
        int slot = emit(f, b, gs);
        Instr ld = ins_make(OP_LOAD, ty_ptr()); ld.a = slot;
        int fp = emit(f, b, ld);
        int r = emit(f, b, ins_calli(ty_i64(), sg, fp, ids_dup((int32_t[]){ x, K(f, b, ty_i64(), 10) }, 2), 2, false));
        emit(f, b, ins_ret(r));
    }
    /* 36 vtail(i64 sel, i64 x) -> i64 : funcptr chosen by select,
     * dispatched with an indirect tail call */
    {
        int sg = mod_add_sig(m, (Type[]){ ty_i64(), ty_i64() }, 2, ty_i64());
        Func *f = mod_add_func(m, "vtail", ty_i64(), 0);
        int b = func_add_block(f, (Type[]){ ty_i64(), ty_i64() }, 2);
        int sel = ARG(f, b, 0), x = ARG(f, b, 1);
        int pa = emit(f, b, ins_funcptr(mod_find_func(m, "tadd"), false));
        int pb = emit(f, b, ins_funcptr(mod_find_func(m, "tmul"), false));
        int bit = B(f, b, OP_AND, ty_i64(), sel, K(f, b, ty_i64(), 1));
        Instr sc = ins_make(OP_ICMP, ty_i1()); sc.a = bit; sc.b = K(f, b, ty_i64(), 0); sc.pred = IC_NE;
        int cond = emit(f, b, sc);
        Instr sl = ins_make(OP_SELECT, ty_ptr()); sl.a = cond; sl.b = pb; sl.c = pa;
        int fp = emit(f, b, sl);
        emit(f, b, ins_calli(ty_i64(), sg, fp, ids_dup((int32_t[]){ x, K(f, b, ty_i64(), 7) }, 2), 2, true));
    }
    /* 37 alchk / alchk1: extern calls with FP arguments - on x86_64
     * the caller must set AL to the number of FP registers used by
     * the fixed signature; the probes return what they observed */
    {
        Func *f = mod_add_func(m, "alchk", ty_i64(), 0);
        int b = func_add_block(f, (Type[]){ ty_f64(), ty_f64() }, 2);
        emit(f, b, ins_ret(emit(f, b, ins_call(ty_i64(),
            mod_find_extern(m, "alprobe2"), true,
            ids_dup((int32_t[]){ ARG(f, b, 0), ARG(f, b, 1) }, 2), 2, false))));
    }
    {
        Func *f = mod_add_func(m, "alchk1", ty_i64(), 0);
        int b = func_add_block(f, (Type[]){ ty_f64() }, 1);
        emit(f, b, ins_ret(emit(f, b, ins_call(ty_i64(),
            mod_find_extern(m, "alprobe"), true,
            ids_dup((int32_t[]){ ARG(f, b, 0) }, 1), 1, false))));
    }
    /* 38 fsh64(i64 a, i64 b, i64 s) -> i64 : funnel shifts at 64 bits,
     * including the a == b rotate form */
    {
        Func *f = mod_add_func(m, "fsh64", ty_i64(), 0);
        int b = func_add_block(f, (Type[]){ ty_i64(), ty_i64(), ty_i64() }, 3);
        int a = ARG(f, b, 0), bb = ARG(f, b, 1), s = ARG(f, b, 2);
        int l = T3(f, b, OP_FSHL, ty_i64(), a, bb, s);
        int r = T3(f, b, OP_FSHR, ty_i64(), bb, a, s);
        int rol = T3(f, b, OP_FSHL, ty_i64(), a, a, s);
        int x = B(f, b, OP_XOR, ty_i64(), l, r);
        x = B(f, b, OP_ADD, ty_i64(), x, rol);
        emit(f, b, ins_ret(x));
    }
    /* 39 fsh32(i32 a, i32 b, i32 s) -> i32 */
    {
        Func *f = mod_add_func(m, "fsh32", ty_i32(), 0);
        int b = func_add_block(f, (Type[]){ ty_i32(), ty_i32(), ty_i32() }, 3);
        int a = ARG(f, b, 0), bb = ARG(f, b, 1), s = ARG(f, b, 2);
        int l = T3(f, b, OP_FSHL, ty_i32(), a, bb, s);
        int r = T3(f, b, OP_FSHR, ty_i32(), bb, a, s);
        int rol = T3(f, b, OP_FSHL, ty_i32(), a, a, s);
        int x = B(f, b, OP_XOR, ty_i32(), l, r);
        x = B(f, b, OP_ADD, ty_i32(), x, rol);
        emit(f, b, ins_ret(x));
    }
    /* 41 asmchk(i64 a, i64 b) -> i64 : assume-driven folds. nb is in
     * 1..8 by construction, so the assertion always holds; the select
     * and the branch must resolve to the nb-path in optimized code,
     * exactly as the interpreter computes them honestly. */
    {
        Func *f = mod_add_func(m, "asmchk", ty_i64(), 0);
        int b0 = func_add_block(f, (Type[]){ ty_i64(), ty_i64() }, 2);
        int a = ARG(f, b0, 0), bb = ARG(f, b0, 1);
        int m = B(f, b0, OP_AND, ty_i64(), a, K(f, b0, ty_i64(), 7));
        int nb = B(f, b0, OP_OR, ty_i64(), m, K(f, b0, ty_i64(), 1));
        int nz = IC(f, b0, IC_NE, nb, K(f, b0, ty_i64(), 0));
        Instr as = ins_make(OP_ASSUME, ty_void()); as.a = nz; emit(f, b0, as);
        int z = IC(f, b0, IC_EQ, nb, K(f, b0, ty_i64(), 0));
        int big = B(f, b0, OP_ADD, ty_i64(), bb, K(f, b0, ty_i64(), 1000));
        int t3 = B(f, b0, OP_MUL, ty_i64(), nb, K(f, b0, ty_i64(), 3));
        Instr sl = ins_make(OP_SELECT, ty_i64()); sl.a = z; sl.b = big; sl.c = t3;
        int v = emit(f, b0, sl);
        int b1 = func_add_block(f, (Type[]){ ty_i64() }, 1);
        int b2 = func_add_block(f, (Type[]){ ty_i64() }, 1);
        emit(f, b0, ins_condbr(nz, b1, ids_dup((int32_t[]){ v }, 1), 1,
                                   b2, ids_dup((int32_t[]){ v }, 1), 1));
        int v1 = ARG(f, b1, 0);
        emit(f, b1, ins_ret(B(f, b1, OP_ADD, ty_i64(), v1, K(f, b1, ty_i64(), 5))));
        int v2 = ARG(f, b2, 0);
        emit(f, b2, ins_ret(B(f, b2, OP_SUB, ty_i64(), v2, K(f, b2, ty_i64(), 5))));
    }
    /* 42 extch(i32 a, i32 b) -> i64 : field-extraction chains --
     * zext of narrow lshr/and/or/xor results, trunc of shifted
     * values; the interpreter computes them at face value while the
     * optimizer and backends strength-reduce them */
    {
        Func *f = mod_add_func(m, "extch", ty_i64(), 0);
        int b = func_add_block(f, (Type[]){ ty_i32(), ty_i32() }, 2);
        int a = ARG(f, b, 0), bb = ARG(f, b, 1);
        int f1 = B(f, b, OP_LSHR, ty_i32(), a, K(f, b, ty_i32(), 24));
        int z1 = emit(f, b, ins_un(OP_ZEXT, ty_i64(), f1));
        int f2 = B(f, b, OP_AND, ty_i32(), a, K(f, b, ty_i32(), 65535));
        int z2 = emit(f, b, ins_un(OP_ZEXT, ty_i64(), f2));
        int f3 = B(f, b, OP_XOR, ty_i32(), a, bb);
        int f4 = B(f, b, OP_AND, ty_i32(), f3, K(f, b, ty_i32(), 255));
        int z4 = emit(f, b, ins_un(OP_ZEXT, ty_i64(), f4));
        int f5 = B(f, b, OP_LSHR, ty_i32(), a, K(f, b, ty_i32(), 16));
        int t5 = emit(f, b, ins_un(OP_TRUNC, ty_i8(), f5));
        int z5 = emit(f, b, ins_un(OP_ZEXT, ty_i64(), t5));
        int r = B(f, b, OP_ADD, ty_i64(), z1, B(f, b, OP_MUL, ty_i64(), z2, K(f, b, ty_i64(), 3)));
        r = B(f, b, OP_ADD, ty_i64(), r, B(f, b, OP_MUL, ty_i64(), z4, K(f, b, ty_i64(), 5)));
        r = B(f, b, OP_ADD, ty_i64(), r, B(f, b, OP_MUL, ty_i64(), z5, K(f, b, ty_i64(), 7)));
        emit(f, b, ins_ret(r));
    }
    /* 40 fsh16(i16 a, i16 b, i16 s) -> i16 */
    {
        Func *f = mod_add_func(m, "fsh16", ty_i16(), 0);
        int b = func_add_block(f, (Type[]){ ty_i16(), ty_i16(), ty_i16() }, 3);
        int a = ARG(f, b, 0), bb = ARG(f, b, 1), s = ARG(f, b, 2);
        int l = T3(f, b, OP_FSHL, ty_i16(), a, bb, s);
        int r = T3(f, b, OP_FSHR, ty_i16(), bb, a, s);
        int rol = T3(f, b, OP_FSHL, ty_i16(), a, a, s);
        int x = B(f, b, OP_XOR, ty_i16(), l, r);
        x = B(f, b, OP_ADD, ty_i16(), x, rol);
        emit(f, b, ins_ret(x));
    }
    /* 43 stx(ptr out, ptr tab, i64 n) -> i64 : store-through-folded-GEP
     * pressure case, shaped like an entropy-decoder body: eight
     * loop-carried block arguments, four interleaved rounds per
     * iteration, each round loading a table entry, extracting three
     * fields, and storing a byte through gep(out, i + k) while the
     * index add and the stored byte are both live among a dozen other
     * values. Regression guard: a backend that materializes the
     * folded address and the stored value through one shared scratch
     * register corrupts the store address as soon as the allocator
     * spills either operand; the B-case image compare catches the
     * misdirected stores byte for byte. States are masked to the
     * 32-entry table inside the image. */
    {
        Func *f = mod_add_func(m, "stx", ty_i64(), 0);
        Type hd[10] = { ty_i64(), ty_i64(), ty_i64(), ty_i64(), ty_i64(), ty_i64(), ty_ptr(), ty_ptr(), ty_i64(), ty_i64() };
        int b0 = func_add_block(f, (Type[]){ ty_ptr(), ty_ptr(), ty_i64() }, 3);
        int b1 = func_add_block(f, hd, 10);
        int b2 = func_add_block(f, hd, 10);
        int b3 = func_add_block(f, (Type[]){ ty_i64() }, 1);
        int out = ARG(f, b0, 0), tab = ARG(f, b0, 1), n0 = ARG(f, b0, 2);
        int z0 = K(f, b0, ty_i64(), 0), p0 = K(f, b0, ty_i64(), 100);
        emit(f, b0, ins_br(b1, ids_dup((int32_t[]){ z0, z0, z0, z0, p0, z0, out, tab, n0, z0 }, 10), 10));
        int hi = ARG(f, b1, 0);
        int hout = ARG(f, b1, 6), htab = ARG(f, b1, 7), hn = ARG(f, b1, 8);
        int hcont = ARG(f, b1, 3), hacc = ARG(f, b1, 9);
        int hcnd = IC(f, b1, IC_SLT, hi, hn);
        int htot = B(f, b1, OP_ADD, ty_i64(), hacc, hcont);
        int hargs[10]; for (int q = 0; q < 10; q++) hargs[q] = ARG(f, b1, q);
        emit(f, b1, ins_condbr(hcnd, b2, ids_dup(hargs, 10), 10,
                                     b3, ids_dup((int32_t[]){ htot }, 1), 1));
        (void)hout; (void)htab;
        int i = ARG(f, b2, 0), s1 = ARG(f, b2, 1), s2 = ARG(f, b2, 2);
        int cont = ARG(f, b2, 3), poff = ARG(f, b2, 4), cons = ARG(f, b2, 5);
        int bout = ARG(f, b2, 6), btab = ARG(f, b2, 7), bn = ARG(f, b2, 8);
        int acc = ARG(f, b2, 9);
        int states[2] = { s1, s2 };
        /* all four store indices computed up front: they stay live
         * across every round, under the full carried state */
        int idxs[4];
        idxs[0] = i;
        for (int k = 1; k < 4; k++) idxs[k] = B(f, b2, OP_ADD, ty_i64(), i, K(f, b2, ty_i64(), k));
        for (int k = 0; k < 4; k++) {
            int st = states[k & 1];
            Instr g = ins_make(OP_GEP, ty_ptr()); g.a = btab; g.b = st; g.ety = ty_i32();
            int gp = emit(f, b2, g);
            Instr ld = ins_make(OP_LOAD, ty_i32()); ld.a = gp;
            int e = emit(f, b2, ld);
            int nb32 = B(f, b2, OP_LSHR, ty_i32(), e, K(f, b2, ty_i32(), 24));
            int nb = emit(f, b2, ins_un(OP_ZEXT, ty_i64(), nb32));
            nb = B(f, b2, OP_AND, ty_i64(), nb, K(f, b2, ty_i64(), 15));
            int sy32 = B(f, b2, OP_LSHR, ty_i32(), e, K(f, b2, ty_i32(), 16));
            int sy = emit(f, b2, ins_un(OP_TRUNC, ty_i8(), sy32));
            int ns32 = B(f, b2, OP_AND, ty_i32(), e, K(f, b2, ty_i32(), 65535));
            int ns = emit(f, b2, ins_un(OP_ZEXT, ty_i64(), ns32));
            int sh = B(f, b2, OP_SHL, ty_i64(), cont, cons);
            int rs = B(f, b2, OP_SUB, ty_i64(), K(f, b2, ty_i64(), 64), nb);
            int lb0 = B(f, b2, OP_LSHR, ty_i64(), sh, rs);
            Instr sel = ins_make(OP_SELECT, ty_i64());
            sel.a = IC(f, b2, IC_EQ, nb, K(f, b2, ty_i64(), 0)); sel.b = K(f, b2, ty_i64(), 0); sel.c = lb0;
            int lb = emit(f, b2, sel);
            int nst = B(f, b2, OP_ADD, ty_i64(), ns, lb);
            nst = B(f, b2, OP_AND, ty_i64(), nst, K(f, b2, ty_i64(), 31));
            int idx = idxs[k];
            Instr g2 = ins_make(OP_GEP, ty_ptr()); g2.a = bout; g2.b = idx; g2.ety = ty_i8();
            int dp = emit(f, b2, g2);
            Instr st8 = ins_make(OP_STORE, ty_i8()); st8.a = dp; st8.b = sy;
            emit(f, b2, st8);
            cons = B(f, b2, OP_ADD, ty_i64(), cons, nb);
            acc = B(f, b2, OP_ADD, ty_i64(), acc, nst);
            states[k & 1] = nst;
        }
        int nb8 = B(f, b2, OP_LSHR, ty_i64(), cons, K(f, b2, ty_i64(), 3));
        int poffn = B(f, b2, OP_SUB, ty_i64(), poff, nb8);
        int consn = B(f, b2, OP_AND, ty_i64(), cons, K(f, b2, ty_i64(), 7));
        Instr g3 = ins_make(OP_GEP, ty_ptr()); g3.a = btab; g3.b = poffn; g3.ety = ty_i8();
        int pp = emit(f, b2, g3);
        Instr lc = ins_make(OP_LOAD, ty_i64()); lc.a = pp;
        int contn = emit(f, b2, lc);
        int inext = B(f, b2, OP_ADD, ty_i64(), i, K(f, b2, ty_i64(), 4));
        emit(f, b2, ins_br(b1, ids_dup((int32_t[]){ inext, states[0], states[1], contn, poffn, consn, bout, btab, bn, acc }, 10), 10));
        emit(f, b3, ins_ret(ARG(f, b3, 0)));
    }
    /* 44 vecstage(ptr dst, ptr src) : FP-pool staging witness
     * (WP29C). Eighteen live vec(i64,1) values; a[0] is stored
     * early to free its home, then a register-result i64 VMUL --
     * whose pmuludq decomposition stages partials through xmm13
     * and a slot-resident operand through xmm14 -- and finally
     * every value is stored out and image-checked. When xmm13 /
     * xmm14 were FP pool homes (clob=0, and x86_clob_mask models
     * GP classes only, so nothing ever forbade them), the value
     * homed in xmm13 was silently destroyed by the decomposition.
     * The pool now ends at xmm12; xmm13/14/15 are permanent
     * emitter scratch. Discriminates in the standard x86 lane
     * (the decomposition runs at every tier). */
    {
        Func *f = mod_add_func(m, "vecstage", ty_void(), 0);
        int b = func_add_block(f, (Type[]){ ty_ptr(), ty_ptr() }, 2);
        int dst = ARG(f, b, 0), src = ARG(f, b, 1);
        Type vt = ty_vec(ty_i64(), 1);
        int a[18];
        for (int i = 0; i < 18; i++) {
            Instr g = ins_make(OP_GEP, ty_ptr()); g.ety = ty_i64();
            g.a = src; g.b = K(f, b, ty_i64(), i);
            Instr vl = ins_make(OP_VLOAD, vt); vl.a = emit(f, b, g);
            a[i] = emit(f, b, vl);
        }
        { Instr g = ins_make(OP_GEP, ty_ptr()); g.ety = ty_i64();
          g.a = dst; g.b = K(f, b, ty_i64(), 0);
          Instr vs = ins_make(OP_VSTORE, ty_void()); vs.a = emit(f, b, g); vs.b = a[0];
          emit(f, b, vs); }
        int z = B(f, b, OP_VMUL, vt, a[17], a[16]);
        for (int i = 17; i >= 1; i--) {
            Instr g = ins_make(OP_GEP, ty_ptr()); g.ety = ty_i64();
            g.a = dst; g.b = K(f, b, ty_i64(), i);
            Instr vs = ins_make(OP_VSTORE, ty_void()); vs.a = emit(f, b, g); vs.b = a[i];
            emit(f, b, vs);
        }
        { Instr g = ins_make(OP_GEP, ty_ptr()); g.ety = ty_i64();
          g.a = dst; g.b = K(f, b, ty_i64(), 18);
          Instr vs = ins_make(OP_VSTORE, ty_void()); vs.a = emit(f, b, g); vs.b = z;
          emit(f, b, vs); }
        emit(f, b, ins_ret(-1));
    }
    /* 45 vecstageu(ptr dst, ptr src) : the WP29A stress shape --
     * the same eighteen live vectors across a scalarized VUDIV,
     * whose lane loop stages the result through xmm14 on the
     * wide tiers (vec_insert_reg512 quarters at vl 16, the
     * high-half insert at vl 8). At the battery's vl-4 x86 lane
     * the int lane loop inserts directly and this shape does
     * not discriminate; it pins the original repro in the
     * corpus (it fails on the pre-WP29C compiler at vl 8/16,
     * proven by the standalone probe) and covers the fixed
     * pool on every lane that runs it. */
    {
        Func *f = mod_add_func(m, "vecstageu", ty_void(), 0);
        int b = func_add_block(f, (Type[]){ ty_ptr(), ty_ptr() }, 2);
        int dst = ARG(f, b, 0), src = ARG(f, b, 1);
        Type vt = ty_vec(ty_i64(), 1);
        int a[18];
        for (int i = 0; i < 18; i++) {
            Instr g = ins_make(OP_GEP, ty_ptr()); g.ety = ty_i64();
            g.a = src; g.b = K(f, b, ty_i64(), i);
            Instr vl = ins_make(OP_VLOAD, vt); vl.a = emit(f, b, g);
            a[i] = emit(f, b, vl);
        }
        { Instr g = ins_make(OP_GEP, ty_ptr()); g.ety = ty_i64();
          g.a = dst; g.b = K(f, b, ty_i64(), 0);
          Instr vs = ins_make(OP_VSTORE, ty_void()); vs.a = emit(f, b, g); vs.b = a[0];
          emit(f, b, vs); }
        int z = B(f, b, OP_VUDIV, vt, a[17], a[16]);
        for (int i = 17; i >= 1; i--) {
            Instr g = ins_make(OP_GEP, ty_ptr()); g.ety = ty_i64();
            g.a = dst; g.b = K(f, b, ty_i64(), i);
            Instr vs = ins_make(OP_VSTORE, ty_void()); vs.a = emit(f, b, g); vs.b = a[i];
            emit(f, b, vs);
        }
        { Instr g = ins_make(OP_GEP, ty_ptr()); g.ety = ty_i64();
          g.a = dst; g.b = K(f, b, ty_i64(), 18);
          Instr vs = ins_make(OP_VSTORE, ty_void()); vs.a = emit(f, b, g); vs.b = z;
          emit(f, b, vs); }
        emit(f, b, ins_ret(-1));
    }
    /* 46 allocsave(i64 seed) -> i64 : alloca top-addressing witness
     * (WP34). allocsave keeps sixteen values live across a call to
     * acorrupt; three of them (the mul chain roots h2/h4/h6) sit in
     * callee-saved homes r12/r13/r14. acorrupt keeps five values live
     * across its own call (all five callee-saved homes used, nothing
     * spilled) and stores four i64 constants into a 64-byte alloca at
     * byte offsets 0/8/16/24, then reads them back. When be.c sampled
     * allo_off at the region's cumulative START, the alloca value was
     * the region's top edge: the stores at bytes 8/16/24 landed in
     * acorrupt's own callee-save slots ([rbp-40]/[rbp-32]/[rbp-24])
     * and its epilogue restored the constants into r14/r13/r12, so
     * allocsave's h2/h4/h6 came back as poison (native result off by
     * exactly (P1+P2+P3) - (h2+h4+h6)). allo_off is now the region's
     * cumulative END — the lowest byte — and every store stays inside
     * the region. Fails on the pre-WP34 compiler in the x86 lane. */
    {
        Func *f = mod_add_func(m, "awide5", ty_i64(), 0);
        int b = func_add_block(f, (Type[]){ ty_i64(), ty_i64(), ty_i64(), ty_i64(), ty_i64() }, 5);
        int s0 = B(f, b, OP_ADD, ty_i64(), ARG(f, b, 0), ARG(f, b, 1));
        int s1 = B(f, b, OP_ADD, ty_i64(), ARG(f, b, 2), ARG(f, b, 3));
        int t = B(f, b, OP_ADD, ty_i64(), s0, s1);
        emit(f, b, ins_ret(B(f, b, OP_ADD, ty_i64(), t, ARG(f, b, 4))));
    }
    {
        Func *f = mod_add_func(m, "acorrupt", ty_i64(), 0);
        int b = func_add_block(f, (Type[]){ ty_i64() }, 1);
        int s = ARG(f, b, 0);
        static const int64_t POISON[4] = { 1111111111111111111LL, 2459565876494606882LL,
                                           3689348814741910323LL, 4924975585200113572LL };
        int a[5], q[4], l[4];
        for (int i = 0; i < 5; i++) a[i] = B(f, b, OP_ADD, ty_i64(), s, K(f, b, ty_i64(), i + 1));
        Instr al = ins_make(OP_ALLOCA, ty_ptr()); al.imm = 64; al.c = 8;
        int cell = emit(f, b, al);
        for (int j = 0; j < 4; j++) {
            Instr g = ins_make(OP_GEP, ty_ptr()); g.a = cell; g.b = K(f, b, ty_i64(), j); g.ety = ty_i64();
            q[j] = emit(f, b, g);
            Instr st = ins_make(OP_STORE, ty_i64()); st.a = q[j]; st.b = K(f, b, ty_i64(), POISON[j]);
            emit(f, b, st);
        }
        for (int j = 0; j < 4; j++) {
            Instr ld = ins_make(OP_LOAD, ty_i64()); ld.a = q[j];
            l[j] = emit(f, b, ld);
        }
        int ls = B(f, b, OP_ADD, ty_i64(), B(f, b, OP_ADD, ty_i64(), l[0], l[1]),
                                          B(f, b, OP_ADD, ty_i64(), l[2], l[3]));
        int fi_wide = mod_find_func(m, "awide5");
        int t = emit(f, b, ins_call(ty_i64(), fi_wide, false,
                                    ids_dup((int32_t[]){ a[0], a[1], a[2], a[3], a[4] }, 5), 5, false));
        emit(f, b, ins_ret(B(f, b, OP_ADD, ty_i64(), t, ls)));
    }
    {
        Func *f = mod_add_func(m, "allocsave", ty_i64(), 0);
        int b = func_add_block(f, (Type[]){ ty_i64() }, 1);
        int seed = ARG(f, b, 0);
        int h[16];
        for (int i = 0; i < 16; i++) {
            if (i == 0 || (i & 1)) h[i] = B(f, b, OP_ADD, ty_i64(), seed, K(f, b, ty_i64(), (i + 1) * 100));
            else h[i] = B(f, b, OP_MUL, ty_i64(), seed, K(f, b, ty_i64(), i + 1));
        }
        int fi_cor = mod_find_func(m, "acorrupt");
        int r = emit(f, b, ins_call(ty_i64(), fi_cor, false, ids_dup((int32_t[]){ seed }, 1), 1, false));
        int s[8], t[4];
        for (int i = 0; i < 8; i++) s[i] = B(f, b, OP_ADD, ty_i64(), h[2 * i], h[2 * i + 1]);
        for (int i = 0; i < 4; i++) t[i] = B(f, b, OP_ADD, ty_i64(), s[2 * i], s[2 * i + 1]);
        int sum = B(f, b, OP_ADD, ty_i64(), B(f, b, OP_ADD, ty_i64(), t[0], t[1]),
                                           B(f, b, OP_ADD, ty_i64(), t[2], t[3]));
        emit(f, b, ins_ret(B(f, b, OP_ADD, ty_i64(), sum, r)));
    }
    /* 47 chainpress(i64 v, i64 c) -> i64 : add-chain root-liveness
     * witness (WP36). Four chains root at the argument v: an add
     * chain (a0 = v+11 executes -- it feeds a shift; a4 = a0+5 and
     * a8 = a4+9 and a12 = a8+13 are chain-skipped and materialized
     * at their consumers from the root as v+16 / v+25 / v+38), plus
     * xor, mul and sub chains whose links all execute. Between the
     * chain definitions and the consumers sits a3 = sub v, 4444: an
     * in-place-eligible definition. When the allocator's folded-use
     * walk expanded a chain use to the chain add's operands (a0)
     * instead of the recorded root (v), v's interval ended at a3,
     * a3 took v's register in place, and the t3/t5/t6
     * materializations read a3 back as v (native result off by a
     * constant). Chain uses now expand to the root. Fails on the
     * pre-WP36 compiler in the x86 lane. */
    {
        Func *f = mod_add_func(m, "chainpress", ty_i64(), 0);
        int b = func_add_block(f, (Type[]){ ty_i64(), ty_i64() }, 2);
        int v = ARG(f, b, 0), c = ARG(f, b, 1);
        int a0 = B(f, b, OP_ADD, ty_i64(), v, K(f, b, ty_i64(), 11));
        int a1 = B(f, b, OP_XOR, ty_i64(), v, K(f, b, ty_i64(), 222));
        int a2 = B(f, b, OP_MUL, ty_i64(), v, K(f, b, ty_i64(), 3));
        int a3 = B(f, b, OP_SUB, ty_i64(), v, K(f, b, ty_i64(), 4444));
        int a4 = B(f, b, OP_ADD, ty_i64(), a0, K(f, b, ty_i64(), 5));
        int a5 = B(f, b, OP_XOR, ty_i64(), a1, K(f, b, ty_i64(), 66));
        int a6 = B(f, b, OP_MUL, ty_i64(), a2, K(f, b, ty_i64(), 7));
        int a7 = B(f, b, OP_SUB, ty_i64(), a3, K(f, b, ty_i64(), 8888));
        int a8 = B(f, b, OP_ADD, ty_i64(), a4, K(f, b, ty_i64(), 9));
        int a9 = B(f, b, OP_XOR, ty_i64(), a5, K(f, b, ty_i64(), 1010));
        int a10 = B(f, b, OP_MUL, ty_i64(), a6, K(f, b, ty_i64(), 11));
        int a11 = B(f, b, OP_SUB, ty_i64(), a7, K(f, b, ty_i64(), 1212));
        int a12 = B(f, b, OP_ADD, ty_i64(), a8, K(f, b, ty_i64(), 13));
        int a13 = B(f, b, OP_XOR, ty_i64(), a9, K(f, b, ty_i64(), 1414));
        int s0 = B(f, b, OP_SHL, ty_i64(), a0, c);
        int s1 = B(f, b, OP_LSHR, ty_i64(), a5, c);
        int s2 = B(f, b, OP_ASHR, ty_i64(), a9, c);
        int s3 = B(f, b, OP_SHL, ty_i64(), a13, s1);
        int t0 = B(f, b, OP_ADD, ty_i64(), s0, s1);
        int t1 = B(f, b, OP_ADD, ty_i64(), s2, s3);
        int t2 = B(f, b, OP_ADD, ty_i64(), a1, a2);
        int t3 = B(f, b, OP_ADD, ty_i64(), a3, a4);
        int t4 = B(f, b, OP_ADD, ty_i64(), a6, a7);
        int t5 = B(f, b, OP_ADD, ty_i64(), a8, a10);
        int t6 = B(f, b, OP_ADD, ty_i64(), a11, a12);
        int t7 = B(f, b, OP_ADD, ty_i64(), a13, s0);
        int u0 = B(f, b, OP_ADD, ty_i64(), t0, t1);
        int u1 = B(f, b, OP_ADD, ty_i64(), t2, t3);
        int u2 = B(f, b, OP_ADD, ty_i64(), t4, t5);
        int u3 = B(f, b, OP_ADD, ty_i64(), t6, t7);
        int w0 = B(f, b, OP_ADD, ty_i64(), u0, u1);
        int w1 = B(f, b, OP_ADD, ty_i64(), u2, u3);
        emit(f, b, ins_ret(B(f, b, OP_ADD, ty_i64(), w0, w1)));
    }
    /* 48 gepdirect(ptr p, i64 i, i64 j) -> i64 : WP39 direct-LEA GEP
     * witness. Five GEPs off one register-resident base: a variable
     * i64 index at esz 8 (reg/reg lea), the same index + 1 (an add
     * the chain pass may skip -- the legacy materialization must stay
     * correct), a constant index (lea disp form), an i32 index at
     * esz 2 (RAX sign-extension staging form), and a variable index
     * at esz 1. Indices are masked into [0,8) / [0,4) so every case
     * stays inside the driver's 256-byte image. A staging-form GEP
     * that swapped base/index, lost the sign extension, or wrote its
     * result over a still-live operand reads the wrong cell here. */
    {
        Func *f = mod_add_func(m, "gepdirect", ty_i64(), 0);
        int b = func_add_block(f, (Type[]){ ty_ptr(), ty_i64(), ty_i64() }, 3);
        int p = ARG(f, b, 0), i = ARG(f, b, 1), j = ARG(f, b, 2);
        int im = B(f, b, OP_AND, ty_i64(), i, K(f, b, ty_i64(), 7));
        int jm = B(f, b, OP_AND, ty_i64(), j, K(f, b, ty_i64(), 3));
        Instr g1 = ins_make(OP_GEP, ty_ptr()); g1.a = p; g1.b = im; g1.ety = ty_i64();
        int gp1 = emit(f, b, g1);
        Instr l1 = ins_make(OP_LOAD, ty_i64()); l1.a = gp1;
        int v1 = emit(f, b, l1);
        int ip1 = B(f, b, OP_ADD, ty_i64(), im, K(f, b, ty_i64(), 1));
        Instr g2 = ins_make(OP_GEP, ty_ptr()); g2.a = p; g2.b = ip1; g2.ety = ty_i64();
        int gp2 = emit(f, b, g2);
        Instr l2 = ins_make(OP_LOAD, ty_i64()); l2.a = gp2;
        int v2 = emit(f, b, l2);
        Instr g3 = ins_make(OP_GEP, ty_ptr()); g3.a = p; g3.b = K(f, b, ty_i64(), 2); g3.ety = ty_i64();
        int gp3 = emit(f, b, g3);
        Instr l3 = ins_make(OP_LOAD, ty_i64()); l3.a = gp3;
        int v3 = emit(f, b, l3);
        int jt = U(f, b, OP_TRUNC, ty_i32(), jm);
        Instr g4 = ins_make(OP_GEP, ty_ptr()); g4.a = p; g4.b = jt; g4.ety = ty_i16();
        int gp4 = emit(f, b, g4);
        Instr l4 = ins_make(OP_LOAD, ty_i16()); l4.a = gp4;
        int v4 = U(f, b, OP_ZEXT, ty_i64(), emit(f, b, l4));
        Instr g5 = ins_make(OP_GEP, ty_ptr()); g5.a = p; g5.b = im; g5.ety = ty_i8();
        int gp5 = emit(f, b, g5);
        Instr l5 = ins_make(OP_LOAD, ty_i8()); l5.a = gp5;
        int v5 = U(f, b, OP_ZEXT, ty_i64(), emit(f, b, l5));
        int s = B(f, b, OP_ADD, ty_i64(), v1,
                  B(f, b, OP_MUL, ty_i64(), v2, K(f, b, ty_i64(), 3)));
        s = B(f, b, OP_ADD, ty_i64(), s,
              B(f, b, OP_MUL, ty_i64(), v3, K(f, b, ty_i64(), 5)));
        s = B(f, b, OP_ADD, ty_i64(), s,
              B(f, b, OP_MUL, ty_i64(), v4, K(f, b, ty_i64(), 7)));
        s = B(f, b, OP_ADD, ty_i64(), s,
              B(f, b, OP_MUL, ty_i64(), v5, K(f, b, ty_i64(), 11)));
        emit(f, b, ins_ret(s));
    }
    return m;
}
