/* The differential battery: ~28 small functions covering the op menu.
 * Built once; executed by the interpreter (gen) and by every backend
 * (driver) over identical recorded inputs. */
#include "krell.h"

#define B(f, blk, op, ty, a, b) emit((f), (blk), ins_bin((op), (ty), (a), (b)))
#define U(f, blk, op, ty, a)    emit((f), (blk), ins_un((op), (ty), (a)))
#define K(f, blk, ty, v)        emit((f), (blk), ins_iconst((ty), (v)))
#define IC(F_, BLK, PRED, A, B)  ({ Instr _i = ins_make(OP_ICMP, ty_i1()); _i.a = (A); _i.b = (B); _i.pred = (PRED); emit((F_), (BLK), _i); })
#define FC(F_, BLK, PRED, A, B)  ({ Instr _i = ins_make(OP_FCMP, ty_i1()); _i.a = (A); _i.b = (B); _i.pred = (PRED); emit((F_), (BLK), _i); })
#define ARG(f, blk, i)          ((f)->blocks[(blk)].arg_vals[(i)])

Module *build_battery(void) {
    Module *m = mod_new();
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
    return m;
}
