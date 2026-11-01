/* Krell — RISC-V RV64 backend (lp64d ABI, GNU as).
 * Baseline: RV64GC + Zbb (RVA23-class). Values: GP in 64-bit regs/slots,
 * canonical zero-extended; FP in f regs; vectors memory-resident and
 * scalarized (the cost oracle prices them accordingly). Scratch:
 * t0/t1/t2 (x5-x7), plus the a/f a argument registers mid-instruction
 * (never allocated homes). Frame slots are SP-relative; deep slots and
 * vector addresses are materialized in a scratch register.
 * Division and float conversion sequences implement SEMANTICS.md:
 * RISC-V div-by-zero yields -1/dividend natively, so quotients and
 * remainders are zeroed with a (b != 0) multiply; fcvt saturates but
 * maps NaN to the range end, so results are zeroed with an ordered
 * self-compare multiply. */
#include "be.h"
#include <stdarg.h>

enum { T0 = 5, T1 = 6, T2 = 7 };
#define FA0 10
#define FA1 11
static const int ARG_GP[8] = { 10, 11, 12, 13, 14, 15, 16, 17 };

static const PoolReg POOL_GP[] = {
    { 12,0 }, { 13,0 }, { 14,0 }, { 15,0 }, { 16,0 }, { 17,0 },
    { 28,0 }, { 29,0 }, { 30,0 }, { 31,0 },
    { 9,1 }, { 18,1 }, { 19,1 }, { 20,1 }, { 21,1 }, { 22,1 }, { 23,1 },
    { 24,1 }, { 25,1 }, { 26,1 }, { 27,1 },
};
static const PoolReg POOL_FP[] = {
    { 0,0 }, { 1,0 }, { 2,0 }, { 3,0 }, { 4,0 }, { 5,0 }, { 6,0 }, { 7,0 },
    { 28,0 }, { 29,0 }, { 30,0 }, { 31,0 },
    { 8,1 }, { 9,1 }, { 18,1 }, { 19,1 }, { 20,1 }, { 21,1 }, { 22,1 },
    { 23,1 }, { 24,1 }, { 25,1 }, { 26,1 }, { 27,1 },
};

typedef struct {
    FILE *out;
    Module *m;
    Func *f;
    BeFunc *bf;
    int fi;
    int lbl;
    int vl;
} Ctx;

static void E(Ctx *c, const char *fmt, ...) {
    va_list ap; va_start(ap, fmt);
    vfprintf(c->out, fmt, ap);
    va_end(ap);
    fputc('\n', c->out);
}

static void mask_reg(Ctx *c, int reg, Type t) {
    if (t.bits < 64) { int k = 64 - t.bits; E(c, "  slli x%d, x%d, %d", reg, reg, k); E(c, "  srli x%d, x%d, %d", reg, reg, k); }
}
static void sext_reg(Ctx *c, int reg, int bits) {
    if (bits < 64) { E(c, "  slli x%d, x%d, %d", reg, reg, 64 - bits); E(c, "  srai x%d, x%d, %d", reg, reg, 64 - bits); }
}
/* put (s0 - delta) into x<reg> (delta >= 0) */
static void addr_of(Ctx *c, int reg, int delta) {
    if (delta <= 2047) E(c, "  addi x%d, s0, -%d", reg, delta);
    else { E(c, "  li x%d, %d", reg, delta); E(c, "  sub x%d, s0, x%d", reg, reg); }
}
static int sp_imm(Ctx *c, Loc *l) { return c->bf->frame_bytes - l->off; }

/* slot load/store with the deep-frame fallback through a scratch reg */
static void load_gp(Ctx *c, int reg, int v) {
    Loc *l = &c->bf->loc[v];
    if (l->is_reg && l->cls == BCLS_GP && l->idx == reg) return;
    if (l->is_reg) { E(c, "  mv x%d, x%d", reg, l->idx); return; }
    int imm = sp_imm(c, l);
    if (imm <= 2047) { E(c, "  ld x%d, %d(sp)", reg, imm); return; }
    int as = reg == T0 ? T1 : T0;
    E(c, "  li x%d, %d", as, imm);
    E(c, "  add x%d, sp, x%d", as, as);
    E(c, "  ld x%d, 0(x%d)", reg, as);
}
static void store_gp(Ctx *c, int v, int reg) {
    Loc *l = &c->bf->loc[v];
    if (l->is_reg && l->cls == BCLS_GP && l->idx == reg) return;
    if (l->is_reg) { E(c, "  mv x%d, x%d", l->idx, reg); return; }
    int imm = sp_imm(c, l);
    if (imm <= 2047) { E(c, "  sd x%d, %d(sp)", reg, imm); return; }
    int as = reg == T0 ? T1 : T0;
    E(c, "  li x%d, %d", as, imm);
    E(c, "  add x%d, sp, x%d", as, as);
    E(c, "  sd x%d, 0(x%d)", reg, as);
}
static void load_fp(Ctx *c, int freg, int v) {
    Loc *l = &c->bf->loc[v];
    Type t = c->f->vtypes[v];
    const char *ld = t.bits == 32 ? "flw" : "fld";
    const char *mv = t.bits == 32 ? "fmv.s" : "fmv.d";
    if (l->is_reg && l->cls == BCLS_FP && l->idx == freg) return;
    if (l->is_reg) { E(c, "  %s f%d, f%d", mv, freg, l->idx); return; }
    int imm = sp_imm(c, l);
    if (imm <= 2047) { E(c, "  %s f%d, %d(sp)", ld, freg, imm); return; }
    E(c, "  li x%d, %d", T0, imm);
    E(c, "  add x%d, sp, x%d", T0, T0);
    E(c, "  %s f%d, 0(x%d)", ld, freg, T0);
}
static void store_fp(Ctx *c, int v, int freg) {
    Loc *l = &c->bf->loc[v];
    Type t = c->f->vtypes[v];
    const char *sd = t.bits == 32 ? "fsw" : "fsd";
    const char *mv = t.bits == 32 ? "fmv.s" : "fmv.d";
    if (l->is_reg && l->cls == BCLS_FP && l->idx == freg) return;
    if (l->is_reg) { E(c, "  %s f%d, f%d", mv, l->idx, freg); return; }
    int imm = sp_imm(c, l);
    if (imm <= 2047) { E(c, "  %s f%d, %d(sp)", sd, freg, imm); return; }
    E(c, "  li x%d, %d", T0, imm);
    E(c, "  add x%d, sp, x%d", T0, T0);
    E(c, "  %s f%d, 0(x%d)", sd, freg, T0);
}
/* copy a scalar/vector value to another value's home, via scratch */
static void copy_value(Ctx *c, int dst, int src) {
    if (dst == src) return;
    Type t = c->f->vtypes[src];
    int cls = be_class_of(t);
    if (cls == BCLS_GP) { load_gp(c, T0, src); store_gp(c, dst, T0); }
    else if (cls == BCLS_FP) { load_fp(c, 31, src); store_fp(c, dst, 31); }
    else {
        Loc *dl = &c->bf->loc[dst], *sl = &c->bf->loc[src];
        int bytes = 16 * t.n;
        for (int off = 0; off < bytes; off += 8) {
            addr_of(c, T0, sl->off - off);
            E(c, "  ld x%d, 0(x%d)", T1, T0);
            addr_of(c, T0, dl->off - off);
            E(c, "  sd x%d, 0(x%d)", T1, T0);
        }
    }
}

/* parallel-move callback */
typedef struct { Ctx *c; } MvCtx;
static void mem_text(Ctx *c, Loc *l, char *buf, size_t cap) {
    if (l->off >= 0) snprintf(buf, cap, "%d(sp)", c->bf->frame_bytes - l->off);
    else snprintf(buf, cap, "%d(s0)", -l->off);
}
static void rv_mv(void *p, Loc dst, Loc src) {
    MvCtx *mc = p; Ctx *c = mc->c;
    char db[48], sb[48];
    if (dst.cls == BCLS_GP) {
        if (dst.is_reg && src.is_reg) { if (dst.idx != src.idx) E(c, "  mv x%d, x%d", dst.idx, src.idx); return; }
        if (dst.is_reg) {
            if (!src.is_reg && src.off >= 0 && c->bf->frame_bytes - src.off > 2047) {
                E(c, "  li x%d, %d", T1, c->bf->frame_bytes - src.off);
                E(c, "  add x%d, sp, x%d", T1, T1);
                E(c, "  ld x%d, 0(x%d)", dst.idx, T1);
                return;
            }
            mem_text(c, &src, sb, sizeof sb); E(c, "  ld x%d, %s", dst.idx, sb); return;
        }
        if (src.is_reg) {
            if (dst.off >= 0 && c->bf->frame_bytes - dst.off > 2047) {
                E(c, "  li x%d, %d", T1, c->bf->frame_bytes - dst.off);
                E(c, "  add x%d, sp, x%d", T1, T1);
                E(c, "  sd x%d, 0(x%d)", src.idx, T1);
                return;
            }
            mem_text(c, &dst, db, sizeof db); E(c, "  sd x%d, %s", src.idx, db); return;
        }
        mem_text(c, &src, sb, sizeof sb);
        mem_text(c, &dst, db, sizeof db);
        E(c, "  ld x%d, %s", T0, sb);
        E(c, "  sd x%d, %s", T0, db);
    } else {
        if (dst.is_reg && src.is_reg) { if (dst.idx != src.idx) E(c, "  fmv.d f%d, f%d", dst.idx, src.idx); return; }
        if (dst.is_reg) { mem_text(c, &src, sb, sizeof sb); E(c, "  fld f%d, %s", dst.idx, sb); return; }
        if (src.is_reg) { mem_text(c, &dst, db, sizeof db); E(c, "  fsd f%d, %s", src.idx, db); return; }
        mem_text(c, &src, sb, sizeof sb);
        mem_text(c, &dst, db, sizeof db);
        E(c, "  fld f31, %s", sb);
        E(c, "  fsd f31, %s", db);
    }
}
static void parallel_moves(Ctx *c, Loc *srcs, Loc *dsts, int n, int cls) {
    if (n <= 0) return;
    MvCtx mc = { c };
    Loc scratch = { 1, (int8_t)cls, cls == BCLS_GP ? T0 : 31, 0 };
    be_parallel_move(&mc, rv_mv, srcs, dsts, n, scratch);
}

static int mem_size_of(Type t, int vl) {
    if (t.kind == TY_VEC) return ty_lanes(t, vl) * (t.elem_bits / 8);
    return ty_bytes(t);
}

static void save_regs(Ctx *c) {
    BeFunc *bf = c->bf;
    for (int i = 0; i < bf->nsave_gp; i++) {
        int imm = bf->frame_bytes - (16 + 8 * i);
        if (imm <= 2047) E(c, "  sd x%d, %d(sp)", bf->save_gp[i], imm);
        else { E(c, "  li x%d, %d", T0, imm); E(c, "  add x%d, sp, x%d", T0, T0); E(c, "  sd x%d, 0(x%d)", bf->save_gp[i], T0); }
    }
    for (int i = 0; i < bf->nsave_fp; i++) {
        int imm = bf->frame_bytes - (16 + 8 * (bf->nsave_gp + i));
        if (imm <= 2047) E(c, "  fsd f%d, %d(sp)", bf->save_fp[i], imm);
        else { E(c, "  li x%d, %d", T0, imm); E(c, "  add x%d, sp, x%d", T0, T0); E(c, "  fsd f%d, 0(x%d)", bf->save_fp[i], T0); }
    }
}
static void restore_regs(Ctx *c) {
    BeFunc *bf = c->bf;
    for (int i = 0; i < bf->nsave_fp; i++) {
        int imm = bf->frame_bytes - (16 + 8 * (bf->nsave_gp + i));
        if (imm <= 2047) E(c, "  fld f%d, %d(sp)", bf->save_fp[i], imm);
        else { E(c, "  li x%d, %d", T0, imm); E(c, "  add x%d, sp, x%d", T0, T0); E(c, "  fld f%d, 0(x%d)", bf->save_fp[i], T0); }
    }
    for (int i = 0; i < bf->nsave_gp; i++) {
        int imm = bf->frame_bytes - (16 + 8 * i);
        if (imm <= 2047) E(c, "  ld x%d, %d(sp)", bf->save_gp[i], imm);
        else { E(c, "  li x%d, %d", T0, imm); E(c, "  add x%d, sp, x%d", T0, T0); E(c, "  ld x%d, 0(x%d)", bf->save_gp[i], T0); }
    }
}
static void emit_epilogue(Ctx *c) {
    restore_regs(c);
    E(c, "  mv sp, s0");
    E(c, "  ld ra, 8(sp)");
    E(c, "  ld s0, 0(sp)");
    E(c, "  addi sp, sp, 16");
}

/* division: RISC-V div-by-zero gives -1 (quotient) / dividend
 * (remainder); zero the result with a (b != 0) multiply to match the
 * defined semantics. INT_MIN/-1 wraps natively, as required. */
static void emit_div(Ctx *c, Instr *in, bool is_signed, bool is_rem) {
    Type t = in->ty;
    load_gp(c, T0, in->a);
    load_gp(c, T1, in->b);
    if (is_signed && t.bits == 32) {
        E(c, "  %s x%d, x%d, x%d", is_rem ? "remw" : "divw", T0, T0, T1);
    } else {
        if (is_signed) { sext_reg(c, T0, t.bits); sext_reg(c, T1, t.bits); }
        E(c, "  %s x%d, x%d, x%d", is_rem ? (is_signed ? "rem" : "remu") : (is_signed ? "div" : "divu"), T0, T0, T1);
    }
    E(c, "  snez x%d, x%d", T2, T1);
    E(c, "  mul x%d, x%d, x%d", T0, T0, T2);
    mask_reg(c, T0, t);
    store_gp(c, in->result, T0);
}

/* float -> int: fcvt saturates (good) but NaN maps to the range end;
 * zero NaN results with an ordered self-compare, then clamp to widths
 * below the conversion width with Zbb min/max */
static void emit_f2i(Ctx *c, Instr *in, bool unsig) {
    Type t = in->ty;
    Type st = c->f->vtypes[in->a];
    load_fp(c, FA0, in->a);
    char sw = st.bits == 32 ? 's' : 'd';
    char mn[24];
    snprintf(mn, sizeof mn, "%s.%c", unsig ? (t.bits <= 32 ? "fcvt.wu" : "fcvt.lu")
                                          : (t.bits <= 32 ? "fcvt.w" : "fcvt.l"), sw);
    E(c, "  %s x%d, f%d, rtz", mn, T0, FA0);
    E(c, "  feq.%c x%d, f%d, f%d", sw, T1, FA0, FA0);
    E(c, "  mul x%d, x%d, x%d", T0, T0, T1);
    if (t.bits < 64) {
        if (unsig) {
            uint64_t hi = (1ull << t.bits) - 1;
            E(c, "  li x%d, %lld", T1, (long long)hi);
            E(c, "  minu x%d, x%d, x%d", T0, T0, T1);
        } else {
            int64_t hi = (int64_t)((1ll << (t.bits - 1)) - 1);
            int64_t lo = -(1ll << (t.bits - 1));
            E(c, "  li x%d, %lld", T1, (long long)hi);
            E(c, "  min x%d, x%d, x%d", T0, T0, T1);
            E(c, "  li x%d, %lld", T1, (long long)lo);
            E(c, "  max x%d, x%d, x%d", T0, T0, T1);
        }
    }
    store_gp(c, in->result, T0);
}

static void emit_call_args(Ctx *c, Instr *in, const Type *params, bool tail) {
    int np = in->nargs;
    Loc *gs = malloc(sizeof(Loc) * (size_t)(np ? np : 1));
    Loc *gd = malloc(sizeof(Loc) * (size_t)(np ? np : 1));
    Loc *fs = malloc(sizeof(Loc) * (size_t)(np ? np : 1));
    Loc *fd = malloc(sizeof(Loc) * (size_t)(np ? np : 1));
    int ng = 0, nf = 0, stk = 0;
    typedef struct { int v; int slot; } StkArg;
    StkArg *sa = malloc(sizeof(StkArg) * (size_t)(np ? np : 1));
    int nsa = 0;
    int gi = 0, fi2 = 0;
    for (int i = 0; i < np; i++) {
        int v = in->args[i];
        int cls = be_class_of(params[i]);
        if (cls == BCLS_GP && gi < 8) {
            gs[ng] = c->bf->loc[v];
            gd[ng] = (Loc){ 1, BCLS_GP, ARG_GP[gi], 0 };
            ng++; gi++;
        } else if (cls == BCLS_FP && fi2 < 8) {
            fs[nf] = c->bf->loc[v];
            fd[nf] = (Loc){ 1, BCLS_FP, 10 + fi2, 0 };
            nf++; fi2++;
        } else if (cls == BCLS_GP || cls == BCLS_FP) {
            sa[nsa].v = v; sa[nsa].slot = stk++; nsa++;
        }
    }
    for (int i = 0; i < nsa; i++) {
        int v = sa[i].v;
        int cls = be_class_of(c->f->vtypes[v]);
        if (cls == BCLS_GP) { load_gp(c, T0, v); E(c, "  sd x%d, %d(sp)", T0, 8 * sa[i].slot); }
        else { load_fp(c, 31, v); E(c, "  fsd f31, %d(sp)", 8 * sa[i].slot); }
    }
    if (tail) {
        for (int i = 0; i < nsa; i++) {
            int cls = be_class_of(c->f->vtypes[sa[i].v]);
            if (cls == BCLS_GP) {
                E(c, "  ld x%d, %d(sp)", T0, 8 * i);
                E(c, "  sd x%d, %d(s0)", T0, 16 + 8 * sa[i].slot);
            } else {
                E(c, "  fld f31, %d(sp)", 8 * i);
                E(c, "  fsd f31, %d(s0)", 16 + 8 * sa[i].slot);
            }
        }
    }
    parallel_moves(c, gs, gd, ng, BCLS_GP);
    parallel_moves(c, fs, fd, nf, BCLS_FP);
    free(gs); free(gd); free(fs); free(fd); free(sa);
}

static void emit_branch(Ctx *c, int tgt, const int32_t *args, int nargs) {
    Func *f = c->f;
    Block *tb = &f->blocks[tgt];
    Loc *gs = malloc(sizeof(Loc) * (size_t)(nargs ? nargs : 1));
    Loc *gd = malloc(sizeof(Loc) * (size_t)(nargs ? nargs : 1));
    Loc *fs = malloc(sizeof(Loc) * (size_t)(nargs ? nargs : 1));
    Loc *fd = malloc(sizeof(Loc) * (size_t)(nargs ? nargs : 1));
    int ng = 0, nf = 0;
    for (int i = 0; i < nargs; i++) {
        int sv = args[i], dv = tb->arg_vals[i];
        int cls = be_class_of(f->vtypes[sv]);
        if (cls == BCLS_GP) { gs[ng] = c->bf->loc[sv]; gd[ng] = c->bf->loc[dv]; ng++; }
        else if (cls == BCLS_FP) { fs[nf] = c->bf->loc[sv]; fd[nf] = c->bf->loc[dv]; nf++; }
        else copy_value(c, dv, sv);
    }
    parallel_moves(c, gs, gd, ng, BCLS_GP);
    parallel_moves(c, fs, fd, nf, BCLS_FP);
    free(gs); free(gd); free(fs); free(fd);
    E(c, "  j .Lb%d_%d", c->fi, tgt);
}

static void lane_load_into(Ctx *c, int reg, int addr, int eb) {
    if (eb == 1) E(c, "  lbu x%d, 0(x%d)", reg, addr);
    else if (eb == 2) E(c, "  lhu x%d, 0(x%d)", reg, addr);
    else if (eb == 4) E(c, "  lwu x%d, 0(x%d)", reg, addr);
    else E(c, "  ld x%d, 0(x%d)", reg, addr);
}
static void lane_store_from(Ctx *c, int reg, int addr, int eb) {
    if (eb == 1) E(c, "  sb x%d, 0(x%d)", reg, addr);
    else if (eb == 2) E(c, "  sh x%d, 0(x%d)", reg, addr);
    else if (eb == 4) E(c, "  sw x%d, 0(x%d)", reg, addr);
    else E(c, "  sd x%d, 0(x%d)", reg, addr);
}

static void emit_instr(Ctx *c, int bi, int ii) {
    Func *f = c->f;
    Instr *in = &f->blocks[bi].ins[ii];
    Type t = in->ty;
    switch (in->op) {
    case OP_ICONST: {
        E(c, "  li x%d, %lld", T0, (long long)in->imm);
        mask_reg(c, T0, t);
        store_gp(c, in->result, T0);
        break;
    }
    case OP_FCONST: {
        if (t.bits == 32) {
            E(c, "  li x%d, 0x%x", T0, (uint32_t)in->imm);
            E(c, "  fmv.s.x f31, x%d", T0);
        } else {
            E(c, "  li x%d, 0x%llx", T0, (unsigned long long)in->imm);
            E(c, "  fmv.d.x f31, x%d", T0);
        }
        store_fp(c, in->result, 31);
        break;
    }
    case OP_FREEZE: copy_value(c, in->result, in->a); break;
    case OP_BITCAST: {
        Type st = f->vtypes[in->a];
        int sc = be_class_of(st), dc = be_class_of(t);
        if (sc == dc) { copy_value(c, in->result, in->a); break; }
        if (sc == BCLS_GP && dc == BCLS_FP) {
            load_gp(c, T0, in->a);
            E(c, "  %s f31, x%d", t.bits == 32 ? "fmv.s.x" : "fmv.d.x", T0);
            store_fp(c, in->result, 31);
        } else {
            load_fp(c, 31, in->a);
            E(c, "  %s x%d, f31", st.bits == 32 ? "fmv.x.s" : "fmv.x.d", T0);
            store_gp(c, in->result, T0);
        }
        break;
    }
    case OP_ADD: case OP_SUB: case OP_AND: case OP_OR: case OP_XOR: case OP_MUL: {
        load_gp(c, T0, in->a);
        load_gp(c, T1, in->b);
        const char *nm = in->op == OP_ADD ? "add" : in->op == OP_SUB ? "sub" :
                         in->op == OP_MUL ? "mul" : in->op == OP_AND ? "and" :
                         in->op == OP_OR ? "or" : "xor";
        E(c, "  %s x%d, x%d, x%d", nm, T0, T0, T1);
        mask_reg(c, T0, t);
        store_gp(c, in->result, T0);
        break;
    }
    case OP_NEG: {
        load_gp(c, T0, in->a);
        E(c, "  neg x%d, x%d", T0, T0);
        mask_reg(c, T0, t);
        store_gp(c, in->result, T0);
        break;
    }
    case OP_NOT: {
        load_gp(c, T0, in->a);
        E(c, "  not x%d, x%d", T0, T0);
        mask_reg(c, T0, t);
        store_gp(c, in->result, T0);
        break;
    }
    case OP_SHL: case OP_LSHR: case OP_ASHR: {
        load_gp(c, T0, in->a);
        load_gp(c, T1, in->b);
        if (t.bits < 64) E(c, "  andi x%d, x%d, %d", T1, T1, t.bits - 1);
        if (in->op == OP_ASHR) sext_reg(c, T0, t.bits);
        E(c, "  %s x%d, x%d, x%d", in->op == OP_SHL ? "sll" : in->op == OP_LSHR ? "srl" : "sra", T0, T0, T1);
        mask_reg(c, T0, t);
        store_gp(c, in->result, T0);
        break;
    }
    case OP_SDIV: emit_div(c, in, true, false); break;
    case OP_SREM: emit_div(c, in, true, true); break;
    case OP_UDIV: emit_div(c, in, false, false); break;
    case OP_UREM: emit_div(c, in, false, true); break;
    case OP_ICMP: {
        Type ta = f->vtypes[in->a];
        bool sgn = in->pred >= IC_SLT;
        load_gp(c, T0, in->a);
        if (sgn) sext_reg(c, T0, ta.bits);
        load_gp(c, T1, in->b);
        if (sgn) sext_reg(c, T1, ta.bits);
        switch (in->pred) {
        case IC_EQ: E(c, "  xor x%d, x%d, x%d", T0, T0, T1); E(c, "  seqz x%d, x%d", T0, T0); break;
        case IC_NE: E(c, "  xor x%d, x%d, x%d", T0, T0, T1); E(c, "  snez x%d, x%d", T0, T0); break;
        case IC_SLT: case IC_ULT: E(c, "  %s x%d, x%d, x%d", sgn ? "slt" : "sltu", T0, T0, T1); break;
        case IC_SGT: case IC_UGT: E(c, "  %s x%d, x%d, x%d", sgn ? "slt" : "sltu", T0, T1, T0); break;
        case IC_SLE: case IC_ULE: E(c, "  %s x%d, x%d, x%d", sgn ? "slt" : "sltu", T0, T1, T0); E(c, "  xori x%d, x%d, 1", T0, T0); break;
        case IC_SGE: case IC_UGE: E(c, "  %s x%d, x%d, x%d", sgn ? "slt" : "sltu", T0, T0, T1); E(c, "  xori x%d, x%d, 1", T0, T0); break;
        }
        store_gp(c, in->result, T0);
        break;
    }
    case OP_POPCOUNT: {
        load_gp(c, T0, in->a);
        if (t.bits == 32) E(c, "  cpopw x%d, x%d", T0, T0);
        else E(c, "  cpop x%d, x%d", T0, T0);
        store_gp(c, in->result, T0);
        break;
    }
    case OP_CLZ: {
        load_gp(c, T0, in->a);
        if (t.bits == 32) E(c, "  clzw x%d, x%d", T0, T0);
        else if (t.bits == 64) E(c, "  clz x%d, x%d", T0, T0);
        else { E(c, "  clz x%d, x%d", T0, T0); E(c, "  addi x%d, x%d, -%d", T0, T0, 64 - t.bits); }
        store_gp(c, in->result, T0);
        break;
    }
    case OP_CTZ: {
        load_gp(c, T0, in->a);
        if (t.bits == 32) E(c, "  ctzw x%d, x%d", T0, T0);
        else if (t.bits == 64) E(c, "  ctz x%d, x%d", T0, T0);
        else {
            E(c, "  ctz x%d, x%d", T0, T0);
            E(c, "  li x%d, %d", T1, t.bits);
            E(c, "  min x%d, x%d, x%d", T0, T0, T1);
        }
        store_gp(c, in->result, T0);
        break;
    }
    case OP_BSWAP: {
        load_gp(c, T0, in->a);
        if (t.bits == 64) E(c, "  rev8 x%d, x%d", T0, T0);
        else if (t.bits == 32) { E(c, "  rev8 x%d, x%d", T0, T0); E(c, "  srli x%d, x%d, 32", T0, T0); }
        else if (t.bits == 16) { E(c, "  rev8 x%d, x%d", T0, T0); E(c, "  srli x%d, x%d, 48", T0, T0); }
        mask_reg(c, T0, t);
        store_gp(c, in->result, T0);
        break;
    }
    case OP_TRUNC: case OP_ZEXT: case OP_SEXT: {
        load_gp(c, T0, in->a);
        if (in->op == OP_SEXT) sext_reg(c, T0, f->vtypes[in->a].bits);
        else mask_reg(c, T0, t);
        store_gp(c, in->result, T0);
        break;
    }
    case OP_FADD: case OP_FSUB: case OP_FMUL: case OP_FDIV: {
        load_fp(c, FA0, in->a);
        load_fp(c, FA1, in->b);
        const char *nm = in->op == OP_FADD ? "fadd" : in->op == OP_FSUB ? "fsub" :
                         in->op == OP_FMUL ? "fmul" : "fdiv";
        char w = t.bits == 32 ? 's' : 'd';
        E(c, "  %s.%c f31, f%d, f%d", nm, w, FA0, FA1);
        store_fp(c, in->result, 31);
        break;
    }
    case OP_FNEG: case OP_FABS: {
        load_fp(c, FA0, in->a);
        char w = t.bits == 32 ? 's' : 'd';
        E(c, "  %s.%c f31, f%d", in->op == OP_FNEG ? "fneg" : "fabs", w, FA0);
        store_fp(c, in->result, 31);
        break;
    }
    case OP_FMA: {
        load_fp(c, FA0, in->a);
        load_fp(c, FA1, in->b);
        load_fp(c, 12, in->c);
        char w = t.bits == 32 ? 's' : 'd';
        E(c, "  fmadd.%c f31, f%d, f%d, f12", w, FA0, FA1);
        store_fp(c, in->result, 31);
        break;
    }
    case OP_FCMP: {
        load_fp(c, FA0, in->a);
        load_fp(c, FA1, in->b);
        char w = f->vtypes[in->a].bits == 32 ? 's' : 'd';
        /* t1 = ordered(a) && ordered(b), inverted -> un in x7 (T2) */
        E(c, "  feq.%c x%d, f%d, f%d", w, T0, FA0, FA0);
        E(c, "  feq.%c x%d, f%d, f%d", w, T1, FA1, FA1);
        E(c, "  and x%d, x%d, x%d", T0, T0, T1);
        E(c, "  xori x%d, x%d, 1", T2, T0);
        /* base comparison into x6 (T1): eq/lt/le direct, gt/ge swapped */
        switch (in->pred) {
        case FC_UNO: E(c, "  mv x%d, x%d", T0, T2); break;
        case FC_ORD: E(c, "  xori x%d, x%d, 1", T0, T2); break;
        case FC_OEQ: case FC_UEQ:
            E(c, "  feq.%c x%d, f%d, f%d", w, T1, FA0, FA1);
            if (in->pred == FC_OEQ) { E(c, "  xori x%d, x%d, 1", T0, T2); E(c, "  and x%d, x%d, x%d", T0, T1, T0); }
            else E(c, "  or x%d, x%d, x%d", T0, T1, T2);
            break;
        case FC_ONE: case FC_UNE:
            E(c, "  feq.%c x%d, f%d, f%d", w, T1, FA0, FA1);
            E(c, "  xori x%d, x%d, 1", T1, T1);
            if (in->pred == FC_ONE) { E(c, "  xori x%d, x%d, 1", T0, T2); E(c, "  and x%d, x%d, x%d", T0, T1, T0); }
            else E(c, "  or x%d, x%d, x%d", T0, T1, T2);
            break;
        case FC_OLT: case FC_ULT:
            E(c, "  flt.%c x%d, f%d, f%d", w, T1, FA0, FA1);
            if (in->pred == FC_OLT) { E(c, "  xori x%d, x%d, 1", T0, T2); E(c, "  and x%d, x%d, x%d", T0, T1, T0); }
            else E(c, "  or x%d, x%d, x%d", T0, T1, T2);
            break;
        case FC_OLE: case FC_ULE:
            E(c, "  fle.%c x%d, f%d, f%d", w, T1, FA0, FA1);
            if (in->pred == FC_OLE) { E(c, "  xori x%d, x%d, 1", T0, T2); E(c, "  and x%d, x%d, x%d", T0, T1, T0); }
            else E(c, "  or x%d, x%d, x%d", T0, T1, T2);
            break;
        case FC_OGT: case FC_UGT:
            E(c, "  flt.%c x%d, f%d, f%d", w, T1, FA1, FA0);
            if (in->pred == FC_OGT) { E(c, "  xori x%d, x%d, 1", T0, T2); E(c, "  and x%d, x%d, x%d", T0, T1, T0); }
            else E(c, "  or x%d, x%d, x%d", T0, T1, T2);
            break;
        case FC_OGE: case FC_UGE:
            E(c, "  fle.%c x%d, f%d, f%d", w, T1, FA1, FA0);
            if (in->pred == FC_OGE) { E(c, "  xori x%d, x%d, 1", T0, T2); E(c, "  and x%d, x%d, x%d", T0, T1, T0); }
            else E(c, "  or x%d, x%d, x%d", T0, T1, T2);
            break;
        }
        store_gp(c, in->result, T0);
        break;
    }
    case OP_FPTOSI: emit_f2i(c, in, false); break;
    case OP_FPTOUI: emit_f2i(c, in, true); break;
    case OP_SITOFP: case OP_UITOFP: {
        Type st = f->vtypes[in->a];
        load_gp(c, T0, in->a);
        char rd = t.bits == 32 ? 's' : 'd';
        bool un = in->op == OP_UITOFP;
        const char *sf;
        if (un) sf = st.bits == 32 ? "wu" : "lu";   /* zero-extended pattern is the value */
        else if (st.bits == 32) sf = "w";
        else { sext_reg(c, T0, st.bits); sf = "l"; }
        E(c, "  fcvt.%c.%s f31, x%d", rd, sf, T0);
        store_fp(c, in->result, 31);
        break;
    }
    case OP_FEXT: {
        load_fp(c, FA0, in->a);
        E(c, "  fcvt.d.s f31, f%d", FA0);
        store_fp(c, in->result, 31);
        break;
    }
    case OP_FTRUNC: {
        load_fp(c, FA0, in->a);
        E(c, "  fcvt.s.d f31, f%d", FA0);
        store_fp(c, in->result, 31);
        break;
    }
    case OP_SELECT: {
        int L = ++c->lbl;
        copy_value(c, in->result, in->c);
        load_gp(c, T0, in->a);
        E(c, "  beqz x%d, .Lx%d_%d", T0, c->fi, L);
        copy_value(c, in->result, in->b);
        E(c, ".Lx%d_%d:", c->fi, L);
        break;
    }
    case OP_ALLOCA: {
        int off = c->bf->allo_off[be_pos(c->bf, bi, ii)];
        addr_of(c, T0, off);
        store_gp(c, in->result, T0);
        break;
    }
    case OP_LOAD: {
        load_gp(c, T0, in->a);
        if (t.kind == TY_FLOAT) {
            E(c, "  %s f31, 0(x%d)", t.bits == 32 ? "flw" : "fld", T0);
            store_fp(c, in->result, 31);
        } else {
            int eb = t.bits == 64 || t.kind == TY_PTR ? 8 : t.bits / 8;
            lane_load_into(c, T1, T0, eb);
            if (t.bits == 1) E(c, "  andi x%d, x%d, 1", T1, T1);
            store_gp(c, in->result, T1);
        }
        break;
    }
    case OP_STORE: {
        load_gp(c, T0, in->a);
        Type vt = f->vtypes[in->b];
        if (vt.kind == TY_FLOAT) {
            load_fp(c, 31, in->b);
            E(c, "  %s f31, 0(x%d)", vt.bits == 32 ? "fsw" : "fsd", T0);
        } else {
            load_gp(c, T1, in->b);
            int eb = vt.bits == 64 || vt.kind == TY_PTR ? 8 : vt.bits / 8;
            lane_store_from(c, T1, T0, eb);
        }
        break;
    }
    case OP_VLOAD: case OP_VSTORE: {
        int v = in->op == OP_VLOAD ? in->result : in->b;
        Loc *l = &c->bf->loc[v];
        int bytes = 16 * (in->op == OP_VLOAD ? t.n : f->vtypes[in->b].n);
        for (int off = 0; off < bytes; off += 8) {
            load_gp(c, T0, in->a);
            if (off) E(c, "  addi x%d, x%d, %d", T0, T0, off);
            if (in->op == OP_VLOAD) {
                E(c, "  ld x%d, 0(x%d)", T1, T0);
                addr_of(c, T0, l->off - off);
                E(c, "  sd x%d, 0(x%d)", T1, T0);
            } else {
                addr_of(c, T0, l->off - off);
                E(c, "  ld x%d, 0(x%d)", T1, T0);
                load_gp(c, T0, in->a);
                if (off) E(c, "  addi x%d, x%d, %d", T0, T0, off);
                E(c, "  sd x%d, 0(x%d)", T1, T0);
            }
        }
        break;
    }
    case OP_GEP: {
        load_gp(c, T1, in->b);
        sext_reg(c, T1, f->vtypes[in->b].bits);
        int esz = mem_size_of(in->ety, c->vl);
        if (esz == 1) { /* no scale */ }
        else if ((esz & (esz - 1)) == 0) {
            int sh = 0; while ((1 << sh) < esz) sh++;
            E(c, "  slli x%d, x%d, %d", T1, T1, sh);
        } else {
            E(c, "  li x%d, %d", T2, esz);
            E(c, "  mul x%d, x%d, x%d", T1, T1, T2);
        }
        load_gp(c, T0, in->a);
        E(c, "  add x%d, x%d, x%d", T0, T0, T1);
        store_gp(c, in->result, T0);
        break;
    }
    case OP_DATAPTR:
        E(c, "  lla x%d, __krell_data_%d", T0, (int)in->imm);
        store_gp(c, in->result, T0);
        break;
    case OP_VSPLAT: {
        Type et = ty_elem(t);
        Loc *l = &c->bf->loc[in->result];
        int lanes = ty_lanes(t, c->vl);
        int eb = et.bits / 8;
        if (et.kind == TY_FLOAT) load_fp(c, 31, in->a);
        else load_gp(c, T0, in->a);
        for (int i = 0; i < lanes; i++) {
            addr_of(c, T1, l->off - i * eb);
            if (et.kind == TY_FLOAT) E(c, "  %s f31, 0(x%d)", et.bits == 32 ? "fsw" : "fsd", T1);
            else lane_store_from(c, T0, T1, eb);
        }
        break;
    }
    case OP_VADD: case OP_VSUB: case OP_VMUL: case OP_VUDIV:
    case OP_VAND: case OP_VOR: case OP_VXOR:
    case OP_VFADD: case OP_VFSUB: case OP_VFMUL: case OP_VFDIV: {
        Type et = ty_elem(t);
        Loc *dl = &c->bf->loc[in->result], *al = &c->bf->loc[in->a], *bl = &c->bf->loc[in->b];
        int lanes = ty_lanes(t, c->vl);
        int eb = et.bits / 8;
        for (int i = 0; i < lanes; i++) {
            addr_of(c, T0, al->off - i * eb);
            if (et.kind == TY_FLOAT) E(c, "  %s f%d, 0(x%d)", et.bits == 32 ? "flw" : "fld", FA0, T0);
            else lane_load_into(c, T0, T0, eb);
            addr_of(c, T1, bl->off - i * eb);
            if (et.kind == TY_FLOAT) E(c, "  %s f%d, 0(x%d)", et.bits == 32 ? "flw" : "fld", FA1, T1);
            else lane_load_into(c, T1, T1, eb);
            if (et.kind == TY_FLOAT) {
                const char *nm = in->op == OP_VFADD ? "fadd" : in->op == OP_VFSUB ? "fsub" :
                                 in->op == OP_VFMUL ? "fmul" : "fdiv";
                E(c, "  %s.%c f%d, f%d, f%d", nm, et.bits == 32 ? 's' : 'd', FA0, FA0, FA1);
            } else if (in->op == OP_VUDIV) {
                E(c, "  divu x%d, x%d, x%d", T0, T0, T1);
                E(c, "  snez x%d, x%d", T2, T1);
                E(c, "  mul x%d, x%d, x%d", T0, T0, T2);
            } else {
                const char *nm = in->op == OP_VADD ? "add" : in->op == OP_VSUB ? "sub" :
                                 in->op == OP_VMUL ? "mul" : in->op == OP_VAND ? "and" :
                                 in->op == OP_VOR ? "or" : "xor";
                E(c, "  %s x%d, x%d, x%d", nm, T0, T0, T1);
                mask_reg(c, T0, et);
            }
            addr_of(c, T1, dl->off - i * eb);
            if (et.kind == TY_FLOAT) E(c, "  %s f%d, 0(x%d)", et.bits == 32 ? "fsw" : "fsd", FA0, T1);
            else lane_store_from(c, T0, T1, eb);
        }
        break;
    }
    case OP_VEXTRACT: {
        Type et = in->ty;
        Loc *al = &c->bf->loc[in->a];
        int eb = et.bits / 8;
        addr_of(c, T0, al->off - (int)in->imm * eb);
        if (et.kind == TY_FLOAT) {
            E(c, "  %s f31, 0(x%d)", et.bits == 32 ? "flw" : "fld", T0);
            store_fp(c, in->result, 31);
        } else {
            lane_load_into(c, T0, T0, eb);
            store_gp(c, in->result, T0);
        }
        break;
    }
    case OP_VINSERT: {
        Type et = ty_elem(t);
        Loc *dl = &c->bf->loc[in->result], *al = &c->bf->loc[in->a];
        int bytes = 16 * t.n;
        for (int off = 0; off < bytes; off += 8) {
            addr_of(c, T0, al->off - off);
            E(c, "  ld x%d, 0(x%d)", T1, T0);
            addr_of(c, T0, dl->off - off);
            E(c, "  sd x%d, 0(x%d)", T1, T0);
        }
        int eb = et.bits / 8;
        addr_of(c, T1, dl->off - (int)in->imm * eb);
        if (et.kind == TY_FLOAT) {
            load_fp(c, 31, in->b);
            E(c, "  %s f31, 0(x%d)", et.bits == 32 ? "fsw" : "fsd", T1);
        } else {
            load_gp(c, T0, in->b);
            lane_store_from(c, T0, T1, eb);
        }
        break;
    }
    case OP_MEMCPY: case OP_MEMSET: {
        Loc srcs[3], dsts[3];
        int av[3] = { in->a, in->b, in->c };
        for (int i = 0; i < 3; i++) {
            srcs[i] = c->bf->loc[av[i]];
            dsts[i] = (Loc){ 1, BCLS_GP, 10 + i, 0 };
        }
        parallel_moves(c, srcs, dsts, 3, BCLS_GP);
        E(c, "  call %s", in->op == OP_MEMCPY ? "memcpy" : "memset");
        break;
    }
    case OP_CALL: {
        const Type *ps; const char *name; int np;
        if (in->callee_extern) { ps = c->m->exts[in->callee].params; np = c->m->exts[in->callee].nparams; name = c->m->exts[in->callee].name; }
        else { Func *g = &c->m->funcs[in->callee]; ps = g->blocks[0].arg_types; np = g->blocks[0].nargs; name = g->name; }
        (void)np;
        emit_call_args(c, in, ps, false);
        E(c, "  call %s", name);
        if (t.kind != TY_VOID) {
            if (be_class_of(t) == BCLS_FP) store_fp(c, in->result, 10);
            else store_gp(c, in->result, 10);
        }
        break;
    }
    case OP_TAILCALL: {
        const Type *ps; const char *name;
        if (in->callee_extern) { ps = c->m->exts[in->callee].params; name = c->m->exts[in->callee].name; }
        else { Func *g = &c->m->funcs[in->callee]; ps = g->blocks[0].arg_types; name = g->name; }
        emit_call_args(c, in, ps, true);
        emit_epilogue(c);
        E(c, "  tail %s", name);
        break;
    }
    case OP_ASSUME: break;
    case OP_BR:
        emit_branch(c, in->blk, in->args, in->nargs);
        break;
    case OP_CONDBR: {
        int L = ++c->lbl;
        load_gp(c, T0, in->a);
        E(c, "  beqz x%d, .Lx%d_%d", T0, c->fi, L);
        emit_branch(c, in->blk, in->args, in->nargs);
        E(c, ".Lx%d_%d:", c->fi, L);
        emit_branch(c, in->blk2, in->args2, in->nargs2);
        break;
    }
    case OP_ALOAD: {
        load_gp(c, T0, in->a);
        bool acq = in->aux >= AO_ACQREL;
        int eb = t.bits == 64 ? 8 : t.bits / 8;
        if (acq && eb == 4) { E(c, "  lr.w.aq x%d, (x%d)", T1, T0); }
        else if (acq && eb == 8) { E(c, "  lr.d.aq x%d, (x%d)", T1, T0); }
        else if (acq && eb < 4) {
            /* word load + extract */
            E(c, "  andi x%d, x%d, -4", T2, T0);
            E(c, "  lr.w.aq x%d, (x%d)", T1, T2);
            E(c, "  andi x%d, x%d, 3", T2, T0);
            E(c, "  slli x%d, x%d, 3", T2, T2);
            E(c, "  srl x%d, x%d, x%d", T1, T1, T2);
        } else {
            lane_load_into(c, T1, T0, eb);
        }
        mask_reg(c, T1, t);
        if (t.bits == 1) E(c, "  andi x%d, x%d, 1", T1, T1);
        store_gp(c, in->result, T1);
        break;
    }
    case OP_ASTORE: {
        load_gp(c, T0, in->a);
        load_gp(c, T1, in->b);
        Type vt = f->vtypes[in->b];
        bool rel = in->aux >= AO_ACQREL;
        int eb = vt.bits == 64 ? 8 : vt.bits / 8;
        if (rel && eb == 4) { E(c, "  amoswap.w.aqrl x%d, x%d, (x%d)", T2, T1, T0); }
        else if (rel && eb == 8) { E(c, "  amoswap.d.aqrl x%d, x%d, (x%d)", T2, T1, T0); }
        else if (rel && eb < 4) {
            int L = ++c->lbl;
            E(c, "  andi x%d, x%d, -4", T2, T0);
            E(c, "  andi a0, x%d, 3", T0);
            E(c, "  slli a0, a0, 3");
            E(c, "  li a1, %d", eb == 1 ? 0xff : 0xffff);
            E(c, ".Lx%d_%d:", c->fi, L);
            E(c, "  lr.w.aq a2, (x%d)", T2);
            E(c, "  sll a3, a1, a0");
            E(c, "  not a3, a3");
            E(c, "  and a2, a2, a3");
            E(c, "  and a3, x%d, a1", T1);
            E(c, "  sll a3, a3, a0");
            E(c, "  or a2, a2, a3");
            E(c, "  sc.w.rl a3, a2, (x%d)", T2);
            E(c, "  bnez a3, .Lx%d_%d", c->fi, L);
        } else {
            lane_store_from(c, T1, T0, eb);
        }
        break;
    }
    case OP_AADD: {
        load_gp(c, T0, in->a);
        load_gp(c, T1, in->b);
        const char *ord = in->aux >= AO_ACQREL ? ".aqrl" : "";
        if (t.bits == 64) { E(c, "  amoadd.d%s x%d, x%d, (x%d)", ord, T2, T1, T0); E(c, "  mv x%d, x%d", T0, T2); }
        else if (t.bits == 32) { E(c, "  amoadd.w%s x%d, x%d, (x%d)", ord, T2, T1, T0); E(c, "  mv x%d, x%d", T0, T2); }
        else {
            int L = ++c->lbl;
            int eb = t.bits / 8;
            E(c, "  andi x%d, x%d, -4", T2, T0);
            E(c, "  andi a0, x%d, 3", T0);
            E(c, "  slli a0, a0, 3");
            E(c, "  li a1, %d", eb == 1 ? 0xff : 0xffff);
            E(c, ".Lx%d_%d:", c->fi, L);
            E(c, "  lr.w%s a2, (x%d)", in->aux >= AO_ACQREL ? ".aq" : "", T2);
            E(c, "  srl a3, a2, a0");
            E(c, "  and a3, a3, a1");
            E(c, "  add a4, a3, x%d", T1);
            E(c, "  and a4, a4, a1");
            E(c, "  sll a5, a1, a0");
            E(c, "  not a5, a5");
            E(c, "  and a2, a2, a5");
            E(c, "  sll a4, a4, a0");
            E(c, "  or a2, a2, a4");
            E(c, "  sc.w%s a5, a2, (x%d)", in->aux >= AO_ACQREL ? ".rl" : "", T2);
            E(c, "  bnez a5, .Lx%d_%d", c->fi, L);
            E(c, "  mv x%d, a3", T0);
        }
        mask_reg(c, T0, t);
        store_gp(c, in->result, T0);
        break;
    }
    case OP_RET: {
        if (in->a >= 0) {
            Type rt = f->vtypes[in->a];
            if (be_class_of(rt) == BCLS_FP) load_fp(c, 10, in->a);
            else load_gp(c, 10, in->a);
        }
        emit_epilogue(c);
        E(c, "  ret");
        break;
    }
    default: break;
    }
}

static int emit_func(Ctx *c, int fi) {
    Module *m = c->m;
    Func *f = &m->funcs[fi];
    c->f = f; c->fi = fi; c->lbl = 0;
    Pools pools = { POOL_GP, 21, POOL_FP, 24 };
    BeFunc *bf = be_analyze(m, f, &pools);
    if (!bf) return -1;
    c->bf = bf;
    if (bf->frame_bytes > 30000) { be_free(bf); c->bf = NULL; return -1; }
    E(c, ".globl %s", f->name);
    E(c, ".type %s, @function", f->name);
    E(c, "%s:", f->name);
    E(c, "  addi sp, sp, -16");
    E(c, "  sd ra, 8(sp)");
    E(c, "  sd s0, 0(sp)");
    E(c, "  mv s0, sp");
    if (bf->frame_bytes) {
        if (bf->frame_bytes <= 2047) E(c, "  addi sp, sp, -%d", bf->frame_bytes);
        else { E(c, "  li x%d, %d", T0, bf->frame_bytes); E(c, "  sub sp, sp, x%d", T0); }
    }
    save_regs(c);
    /* entry: move ABI args into param homes */
    {
        Block *b0 = &f->blocks[0];
        Loc *gs = malloc(sizeof(Loc) * (size_t)(b0->nargs ? b0->nargs : 1));
        Loc *gd = malloc(sizeof(Loc) * (size_t)(b0->nargs ? b0->nargs : 1));
        Loc *fs = malloc(sizeof(Loc) * (size_t)(b0->nargs ? b0->nargs : 1));
        Loc *fd = malloc(sizeof(Loc) * (size_t)(b0->nargs ? b0->nargs : 1));
        int ng = 0, nf = 0, gi = 0, fi2 = 0, stk = 0;
        for (int i = 0; i < b0->nargs; i++) {
            int v = b0->arg_vals[i];
            int cls = be_class_of(b0->arg_types[i]);
            Loc dst = bf->loc[v];
            if (cls == BCLS_GP && gi < 8) { gs[ng] = (Loc){ 1, BCLS_GP, ARG_GP[gi], 0 }; gd[ng] = dst; ng++; gi++; }
            else if (cls == BCLS_FP && fi2 < 8) { fs[nf] = (Loc){ 1, BCLS_FP, 10 + fi2, 0 }; fd[nf] = dst; nf++; fi2++; }
            else {
                Loc src = { 0, (int8_t)cls, -1000 - stk, -(16 + 8 * stk) };
                stk++;
                if (cls == BCLS_GP) { gs[ng] = src; gd[ng] = dst; ng++; }
                else if (cls == BCLS_FP) { fs[nf] = src; fd[nf] = dst; nf++; }
            }
        }
        parallel_moves(c, gs, gd, ng, BCLS_GP);
        parallel_moves(c, fs, fd, nf, BCLS_FP);
        free(gs); free(gd); free(fs); free(fd);
        /* canonical form: narrow integer params are masked in place */
        for (int i = 0; i < b0->nargs; i++) {
            Type pt = b0->arg_types[i];
            if (pt.kind == TY_INT && pt.bits < 64) {
                Loc *l = &bf->loc[b0->arg_vals[i]];
                int k = 64 - pt.bits;
                if (l->is_reg) {
                    E(c, "  slli x%d, x%d, %d", l->idx, l->idx, k);
                    E(c, "  srli x%d, x%d, %d", l->idx, l->idx, k);
                } else {
                    int imm = sp_imm(c, l);
                    if (imm <= 2047) {
                        E(c, "  ld x%d, %d(sp)", T0, imm);
                        E(c, "  slli x%d, x%d, %d", T0, T0, k);
                        E(c, "  srli x%d, x%d, %d", T0, T0, k);
                        E(c, "  sd x%d, %d(sp)", T0, imm);
                    } else {
                        E(c, "  li x%d, %d", T0, imm);
                        E(c, "  add x%d, sp, x%d", T0, T0);
                        E(c, "  ld x%d, 0(x%d)", T1, T0);
                        E(c, "  slli x%d, x%d, %d", T1, T1, k);
                        E(c, "  srli x%d, x%d, %d", T1, T1, k);
                        E(c, "  sd x%d, 0(x%d)", T1, T0);
                    }
                }
            }
        }
    }
    for (int b = 0; b < f->nblocks; b++) {
        E(c, ".Lb%d_%d:", fi, b);
        for (int i = 0; i < f->blocks[b].nins; i++)
            emit_instr(c, b, i);
    }
    E(c, ".size %s, .-%s", f->name, f->name);
    be_free(bf);
    c->bf = NULL;
    return 0;
}

int be_riscv64(Module *m, const Cost *cost, FILE *out, char *err, size_t errcap) {
    const char *ve = mod_verify(m);
    if (ve) { be_err(err, errcap, ve); return -1; }
    Ctx c = { .out = out, .m = m, .vl = cost_vl_i32(cost) };
    E(&c, ".text");
    for (int i = 0; i < m->nfuncs; i++)
        if (emit_func(&c, i) != 0) { be_err(err, errcap, "riscv64: analysis failed"); return -1; }
    E(&c, ".section .rodata");
    for (int i = 0; i < m->ndata; i++) {
        DataBlob *d = &m->data[i];
        E(&c, ".balign %u", d->align ? d->align : 1);
        E(&c, "__krell_data_%d:", i);
        for (uint32_t j = 0; j < d->len; j += 8) {
            uint64_t v = 0;
            int rem = (int)(d->len - j); if (rem > 8) rem = 8;
            memcpy(&v, d->bytes + j, (size_t)rem);
            E(&c, "  .quad 0x%llx", (unsigned long long)v);
        }
        if (d->len == 0) E(&c, "  .quad 0");
    }
    E(&c, ".section .note.GNU-stack,\"\",@progbits");
    return 0;
}
