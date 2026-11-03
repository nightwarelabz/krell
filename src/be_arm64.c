/* Krell — AArch64 backend (AAPCS64, GNU as).
 * Values: GP in 64-bit regs/slots, canonical zero-extended; FP in v regs;
 * vectors memory-resident, chunked through v31. Scratch: x16, x17 plus
 * x0-x8 mid-instruction (argument registers are never allocated homes),
 * v31/v30 (FP). Frame slots are addressed SP-relative ([sp, #frame-off]);
 * vector slots and allocas materialize their address in a scratch reg.
 * Atomics use LSE instructions (ARMv8.1+); everything else is ARMv8.0.
 * Division and float conversion sequences implement SEMANTICS.md. */
#include "be.h"
#include <stdarg.h>

enum { X16 = 16, X17 = 17 };
static const int ARG_GP[8] = { 0, 1, 2, 3, 4, 5, 6, 7 };

static const PoolReg POOL_GP[] = {
    { 9,0 }, { 10,0 }, { 11,0 }, { 12,0 }, { 13,0 }, { 14,0 }, { 15,0 },
    { 19,1 }, { 20,1 }, { 21,1 }, { 22,1 }, { 23,1 }, { 24,1 }, { 25,1 },
    { 26,1 }, { 27,1 }, { 28,1 },
};
static const PoolReg POOL_FP[] = {
    { 16,0 }, { 17,0 }, { 18,0 }, { 19,0 }, { 20,0 }, { 21,0 }, { 22,0 }, { 23,0 },
    { 8,1 }, { 9,1 }, { 10,1 }, { 11,1 }, { 12,1 }, { 13,1 }, { 14,1 }, { 15,1 },
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

/* load an arbitrary 64-bit immediate via a movz/movk chain */
static void load_imm64(Ctx *c, int reg, uint64_t v) {
    if (v == 0) { E(c, "  mov x%d, #0", reg); return; }
    int started = 0;
    for (int i = 0; i < 4; i++) {
        uint64_t chunk = (v >> (16 * i)) & 0xffff;
        if (!chunk) continue;
        if (!started) { E(c, "  movz x%d, #0x%llx, lsl #%d", reg, (unsigned long long)chunk, 16 * i); started = 1; }
        else E(c, "  movk x%d, #0x%llx, lsl #%d", reg, (unsigned long long)chunk, 16 * i);
    }
}
/* put (x29 - delta) into x<reg>; delta >= 0 */
static void addr_of(Ctx *c, int reg, int delta) {
    if (delta <= 4095) E(c, "  sub x%d, x29, #%d", reg, delta);
    else { load_imm64(c, reg, (uint64_t)delta); E(c, "  sub x%d, x29, x%d", reg, reg); }
}
static void mask_reg(Ctx *c, int reg, Type t) {
    if (t.bits < 64) { int k = 64 - t.bits; E(c, "  lsl x%d, x%d, #%d", reg, reg, k); E(c, "  lsr x%d, x%d, #%d", reg, reg, k); }
}
static void sext_reg(Ctx *c, int reg, int bits) {
    if (bits < 64) { E(c, "  lsl x%d, x%d, #%d", reg, reg, 64 - bits); E(c, "  asr x%d, x%d, #%d", reg, reg, 64 - bits); }
}
/* SP-relative offset text for a stack location */
static int sp_imm(Ctx *c, Loc *l) { return c->bf->frame_bytes - l->off; }

static void load_gp(Ctx *c, int reg, int v) {
    Loc *l = &c->bf->loc[v];
    if (l->is_reg && l->cls == BCLS_GP && l->idx == reg) return;
    if (l->is_reg) E(c, "  mov x%d, x%d", reg, l->idx);
    else E(c, "  ldr x%d, [sp, #%d]", reg, sp_imm(c, l));
}
static void store_gp(Ctx *c, int v, int reg) {
    Loc *l = &c->bf->loc[v];
    if (l->is_reg && l->cls == BCLS_GP && l->idx == reg) return;
    if (l->is_reg) E(c, "  mov x%d, x%d", l->idx, reg);
    else E(c, "  str x%d, [sp, #%d]", reg, sp_imm(c, l));
}
static void load_fp(Ctx *c, int vreg, int v) {
    Loc *l = &c->bf->loc[v];
    Type t = c->f->vtypes[v];
    char w = t.bits == 32 ? 's' : 'd';
    if (l->is_reg && l->cls == BCLS_FP && l->idx == vreg) return;
    if (l->is_reg) E(c, "  fmov %c%d, %c%d", w, vreg, w, l->idx);
    else E(c, "  ldr %c%d, [sp, #%d]", w, vreg, sp_imm(c, l));
}
static void store_fp(Ctx *c, int v, int vreg) {
    Loc *l = &c->bf->loc[v];
    Type t = c->f->vtypes[v];
    char w = t.bits == 32 ? 's' : 'd';
    if (l->is_reg && l->cls == BCLS_FP && l->idx == vreg) return;
    if (l->is_reg) E(c, "  fmov %c%d, %c%d", w, l->idx, w, vreg);
    else E(c, "  str %c%d, [sp, #%d]", w, vreg, sp_imm(c, l));
}
/* copy a scalar/vector value to another value's home, via scratch */
static void copy_value(Ctx *c, int dst, int src) {
    if (dst == src) return;
    Type t = c->f->vtypes[src];
    int cls = be_class_of(t);
    if (cls == BCLS_GP) { load_gp(c, X16, src); store_gp(c, dst, X16); }
    else if (cls == BCLS_FP) { load_fp(c, 31, src); store_fp(c, dst, 31); }
    else {
        Loc *dl = &c->bf->loc[dst], *sl = &c->bf->loc[src];
        int bytes = 16 * t.n;
        for (int off = 0; off < bytes; off += 16) {
            addr_of(c, X16, sl->off - off);
            E(c, "  ldr q31, [x16]");
            addr_of(c, X16, dl->off - off);
            E(c, "  str q31, [x16]");
        }
    }
}

/* parallel-move callback: memory operands are [sp, #frame-off] for frame
 * slots (off >= 0) or [x29, #-off] for incoming stack args (off < 0) */
typedef struct { Ctx *c; } MvCtx;
static void mem_text(Ctx *c, Loc *l, char *buf, size_t cap) {
    if (l->off >= 0) snprintf(buf, cap, "[sp, #%d]", c->bf->frame_bytes - l->off);
    else snprintf(buf, cap, "[x29, #%d]", -l->off);
}
static void arm_mv(void *p, Loc dst, Loc src) {
    MvCtx *mc = p; Ctx *c = mc->c;
    char db[48], sb[48];
    if (dst.cls == BCLS_GP) {
        if (dst.is_reg && src.is_reg) { if (dst.idx != src.idx) E(c, "  mov x%d, x%d", dst.idx, src.idx); return; }
        if (dst.is_reg) { mem_text(c, &src, sb, sizeof sb); E(c, "  ldr x%d, %s", dst.idx, sb); return; }
        if (src.is_reg) { mem_text(c, &dst, db, sizeof db); E(c, "  str x%d, %s", src.idx, db); return; }
        mem_text(c, &src, sb, sizeof sb);
        mem_text(c, &dst, db, sizeof db);
        E(c, "  ldr x16, %s", sb);
        E(c, "  str x16, %s", db);
    } else {
        if (dst.is_reg && src.is_reg) { if (dst.idx != src.idx) E(c, "  fmov d%d, d%d", dst.idx, src.idx); return; }
        if (dst.is_reg) { mem_text(c, &src, sb, sizeof sb); E(c, "  ldr d%d, %s", dst.idx, sb); return; }
        if (src.is_reg) { mem_text(c, &dst, db, sizeof db); E(c, "  str d%d, %s", src.idx, db); return; }
        mem_text(c, &src, sb, sizeof sb);
        mem_text(c, &dst, db, sizeof db);
        E(c, "  ldr d31, %s", sb);
        E(c, "  str d31, %s", db);
    }
}
static void parallel_moves(Ctx *c, Loc *srcs, Loc *dsts, int n, int cls) {
    if (n <= 0) return;
    MvCtx mc = { c };
    Loc scratch = { 1, (int8_t)cls, cls == BCLS_GP ? X16 : 31, 0 };
    be_parallel_move(&mc, arm_mv, srcs, dsts, n, scratch);
}

static int mem_size_of(Type t, int vl) {
    if (t.kind == TY_VEC) return ty_lanes(t, vl) * (t.elem_bits / 8);
    return ty_bytes(t);
}

static void save_regs(Ctx *c) {
    BeFunc *bf = c->bf;
    for (int i = 0; i < bf->nsave_gp; i++)
        E(c, "  str x%d, [sp, #%d]", bf->save_gp[i], bf->frame_bytes - (16 + 8 * i));
    for (int i = 0; i < bf->nsave_fp; i++)
        E(c, "  str d%d, [sp, #%d]", bf->save_fp[i], bf->frame_bytes - (16 + 8 * (bf->nsave_gp + i)));
}
static void restore_regs(Ctx *c) {
    BeFunc *bf = c->bf;
    for (int i = 0; i < bf->nsave_fp; i++)
        E(c, "  ldr d%d, [sp, #%d]", bf->save_fp[i], bf->frame_bytes - (16 + 8 * (bf->nsave_gp + i)));
    for (int i = 0; i < bf->nsave_gp; i++)
        E(c, "  ldr x%d, [sp, #%d]", bf->save_gp[i], bf->frame_bytes - (16 + 8 * i));
}
static void emit_epilogue(Ctx *c) {
    restore_regs(c);
    E(c, "  mov sp, x29");
    E(c, "  ldp x29, x30, [sp], #16");
}

/* division with SEMANTICS.md rules: div-by-zero = 0, INT_MIN/-1 wraps
 * (both native to sdiv/udiv); remainder is a - q*b with a zero-divisor
 * override to 0 */
static void emit_div(Ctx *c, Instr *in, bool is_signed, bool is_rem) {
    Type t = in->ty;
    load_gp(c, X16, in->a);
    if (is_signed) sext_reg(c, X16, t.bits);
    load_gp(c, X17, in->b);
    if (is_signed) sext_reg(c, X17, t.bits);
    if (is_rem) E(c, "  mov x0, x16");      /* keep the dividend */
    E(c, "  %s x16, x16, x17", is_signed ? "sdiv" : "udiv");
    if (is_rem) {
        E(c, "  msub x16, x16, x17, x0");
        E(c, "  cmp x17, #0");
        E(c, "  mov x0, #0");
        E(c, "  csel x16, x0, x16, eq");
    }
    mask_reg(c, X16, t);
    store_gp(c, in->result, X16);
}

/* float -> int with saturation and NaN -> 0 (fcvtz saturates natively);
 * results narrower than the conversion width are clamped afterwards */
static void emit_f2i(Ctx *c, Instr *in, bool unsig) {
    Type t = in->ty;                       /* result int type */
    Type st = c->f->vtypes[in->a];         /* source float type */
    load_fp(c, 31, in->a);
    const char *op = unsig ? "fcvtzu" : "fcvtzs";
    char sw = st.bits == 32 ? 's' : 'd';
    if (t.bits <= 32) E(c, "  %s w16, %c31", op, sw);
    else E(c, "  %s x16, %c31", op, sw);
    /* a W-register write zero-extends; a signed result needs sign-extension
     * before the 64-bit clamp comparisons below */
    if (!unsig && t.bits <= 32) E(c, "  sxtw x16, w16");
    if (t.bits < 64) {
        if (unsig) {
            uint64_t hi = t.bits == 64 ? ~0ull : ((1ull << t.bits) - 1ull);
            load_imm64(c, X17, hi);
            E(c, "  cmp x16, x17");
            E(c, "  csel x16, x17, x16, hi");
        } else {
            uint64_t hi = (uint64_t)((1ll << (t.bits - 1)) - 1);
            uint64_t lo = (uint64_t)(-(1ll << (t.bits - 1)));
            load_imm64(c, X17, hi);
            E(c, "  cmp x16, x17");
            E(c, "  csel x16, x17, x16, gt");
            load_imm64(c, X17, lo);
            E(c, "  cmp x16, x17");
            E(c, "  csel x16, x17, x16, lt");
        }
    }
    store_gp(c, in->result, X16);
}

/* call arguments under AAPCS64 (8 GP + 8 FP registers, then stack) */
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
            fd[nf] = (Loc){ 1, BCLS_FP, fi2, 0 };
            nf++; fi2++;
        } else if (cls == BCLS_GP || cls == BCLS_FP) {
            sa[nsa].v = v; sa[nsa].slot = stk++; nsa++;
        }
    }
    /* stack args go to the outgoing area at [sp + 8*slot]; for a tail
     * call they are first parked there, then copied above the frame */
    for (int i = 0; i < nsa; i++) {
        int v = sa[i].v;
        int cls = be_class_of(c->f->vtypes[v]);
        if (cls == BCLS_GP) { load_gp(c, X16, v); E(c, "  str x16, [sp, #%d]", 8 * sa[i].slot); }
        else { load_fp(c, 31, v); E(c, "  str d31, [sp, #%d]", 8 * sa[i].slot); }
    }
    if (tail) {
        for (int i = 0; i < nsa; i++) {
            int cls = be_class_of(c->f->vtypes[sa[i].v]);
            if (cls == BCLS_GP) {
                E(c, "  ldr x16, [sp, #%d]", 8 * i);
                E(c, "  str x16, [x29, #%d]", 16 + 8 * sa[i].slot);
            } else {
                E(c, "  ldr d31, [sp, #%d]", 8 * i);
                E(c, "  str d31, [x29, #%d]", 16 + 8 * sa[i].slot);
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
    E(c, "  b .Lb%d_%d", c->fi, tgt);
}

/* sized memory ops: eb = element bytes, FP = float access */
static void lane_load_gp(Ctx *c, int reg, int eb) {   /* [x16] -> x<reg> */
    if (eb == 1) E(c, "  ldrb w%d, [x16]", reg);
    else if (eb == 2) E(c, "  ldrh w%d, [x16]", reg);
    else if (eb == 4) E(c, "  ldr w%d, [x16]", reg);
    else E(c, "  ldr x%d, [x16]", reg);
}
static void lane_store_gp(Ctx *c, int reg, int addr_reg, int eb) {
    if (eb == 1) E(c, "  strb w%d, [x%d]", reg, addr_reg);
    else if (eb == 2) E(c, "  strh w%d, [x%d]", reg, addr_reg);
    else if (eb == 4) E(c, "  str w%d, [x%d]", reg, addr_reg);
    else E(c, "  str x%d, [x%d]", reg, addr_reg);
}

static void emit_instr(Ctx *c, int bi, int ii) {
    Func *f = c->f;
    Instr *in = &f->blocks[bi].ins[ii];
    Type t = in->ty;
    switch (in->op) {
    case OP_ICONST: {
        load_imm64(c, X16, (uint64_t)in->imm);
        mask_reg(c, X16, t);
        store_gp(c, in->result, X16);
        break;
    }
    case OP_FCONST: {
        if (t.bits == 32) {
            uint32_t v = (uint32_t)in->imm;
            if (v == 0) E(c, "  mov w16, #0");
            else {
                E(c, "  movz w16, #0x%x", v & 0xffff);
                if (v >> 16) E(c, "  movk w16, #0x%x, lsl #16", v >> 16);
            }
            E(c, "  fmov s31, w16");
        } else {
            load_imm64(c, X16, (uint64_t)in->imm);
            E(c, "  fmov d31, x16");
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
            load_gp(c, X16, in->a);
            Loc *dl = &c->bf->loc[in->result];
            if (dl->is_reg) E(c, "  fmov %c%d, %c16", t.bits == 32 ? 's' : 'd', dl->idx, t.bits == 32 ? 'w' : 'x');
            else E(c, "  str %c16, [sp, #%d]", t.bits == 32 ? 'w' : 'x', sp_imm(c, dl));
        } else {
            load_fp(c, 31, in->a);
            E(c, "  fmov %c16, %c31", st.bits == 32 ? 'w' : 'x', st.bits == 32 ? 's' : 'd');
            store_gp(c, in->result, X16);
        }
        break;
    }
    case OP_ADD: case OP_SUB: case OP_AND: case OP_OR: case OP_XOR: case OP_MUL: {
        load_gp(c, X16, in->a);
        load_gp(c, X17, in->b);
        const char *nm = in->op == OP_ADD ? "add" : in->op == OP_SUB ? "sub" :
                         in->op == OP_MUL ? "mul" : in->op == OP_AND ? "and" :
                         in->op == OP_OR ? "orr" : "eor";
        E(c, "  %s x16, x16, x17", nm);
        mask_reg(c, X16, t);
        store_gp(c, in->result, X16);
        break;
    }
    case OP_NEG: {
        load_gp(c, X16, in->a);
        E(c, "  neg x16, x16");
        mask_reg(c, X16, t);
        store_gp(c, in->result, X16);
        break;
    }
    case OP_NOT: {
        load_gp(c, X16, in->a);
        E(c, "  mvn x16, x16");
        mask_reg(c, X16, t);
        store_gp(c, in->result, X16);
        break;
    }
    case OP_SHL: case OP_LSHR: case OP_ASHR: {
        load_gp(c, X16, in->a);
        load_gp(c, X17, in->b);
        if (t.bits < 64) E(c, "  and x17, x17, #%d", t.bits - 1);
        if (in->op == OP_ASHR) sext_reg(c, X16, t.bits);
        E(c, "  %s x16, x16, x17", in->op == OP_SHL ? "lsl" : in->op == OP_LSHR ? "lsr" : "asr");
        mask_reg(c, X16, t);
        store_gp(c, in->result, X16);
        break;
    }
    case OP_SDIV: emit_div(c, in, true, false); break;
    case OP_SREM: emit_div(c, in, true, true); break;
    case OP_UDIV: emit_div(c, in, false, false); break;
    case OP_UREM: emit_div(c, in, false, true); break;
    case OP_ICMP: {
        Type ta = f->vtypes[in->a];
        bool sgn = in->pred >= IC_SLT;
        load_gp(c, X16, in->a);
        if (sgn) sext_reg(c, X16, ta.bits);
        load_gp(c, X17, in->b);
        if (sgn) sext_reg(c, X17, ta.bits);
        static const char *conds[] = { "eq", "ne", "lo", "ls", "hi", "hs", "lt", "le", "gt", "ge" };
        E(c, "  cmp x16, x17");
        E(c, "  cset x16, %s", conds[in->pred]);
        store_gp(c, in->result, X16);
        break;
    }
    case OP_POPCOUNT: {
        load_gp(c, X16, in->a);
        E(c, "  fmov d31, x16");
        E(c, "  cnt v31.8b, v31.8b");
        E(c, "  addv b31, v31.8b");
        E(c, "  fmov w16, s31");
        store_gp(c, in->result, X16);
        break;
    }
    case OP_CLZ: {
        load_gp(c, X16, in->a);
        E(c, "  clz x16, x16");
        if (t.bits < 64) E(c, "  sub x16, x16, #%d", 64 - t.bits);
        store_gp(c, in->result, X16);
        break;
    }
    case OP_CTZ: {
        load_gp(c, X16, in->a);
        E(c, "  rbit x16, x16");
        E(c, "  clz x16, x16");
        if (t.bits < 64) {
            E(c, "  mov x17, #%d", t.bits);
            E(c, "  cmp x16, x17");
            E(c, "  csel x16, x17, x16, hi");
        }
        store_gp(c, in->result, X16);
        break;
    }
    case OP_BSWAP: {
        load_gp(c, X16, in->a);
        if (t.bits == 64) E(c, "  rev x16, x16");
        else if (t.bits == 32) E(c, "  rev w16, w16");
        else if (t.bits == 16) E(c, "  rev16 w16, w16");
        mask_reg(c, X16, t);
        store_gp(c, in->result, X16);
        break;
    }
    case OP_TRUNC: case OP_ZEXT: case OP_SEXT: {
        load_gp(c, X16, in->a);
        if (in->op == OP_SEXT) sext_reg(c, X16, f->vtypes[in->a].bits);
        else mask_reg(c, X16, t);
        store_gp(c, in->result, X16);
        break;
    }
    case OP_FADD: case OP_FSUB: case OP_FMUL: case OP_FDIV: {
        load_fp(c, 31, in->a);
        load_fp(c, 30, in->b);
        const char *nm = in->op == OP_FADD ? "fadd" : in->op == OP_FSUB ? "fsub" :
                         in->op == OP_FMUL ? "fmul" : "fdiv";
        char w = t.bits == 32 ? 's' : 'd';
        E(c, "  %s %c31, %c31, %c30", nm, w, w, w);
        store_fp(c, in->result, 31);
        break;
    }
    case OP_FNEG: case OP_FABS: {
        load_fp(c, 31, in->a);
        char w = t.bits == 32 ? 's' : 'd';
        E(c, "  %s %c31, %c31", in->op == OP_FNEG ? "fneg" : "fabs", w, w);
        store_fp(c, in->result, 31);
        break;
    }
    case OP_FMA: {
        Loc srcs[3], dsts[3];
        int av[3] = { in->a, in->b, in->c };
        for (int i = 0; i < 3; i++) {
            srcs[i] = c->bf->loc[av[i]];
            dsts[i] = (Loc){ 1, BCLS_FP, i, 0 };
        }
        parallel_moves(c, srcs, dsts, 3, BCLS_FP);
        E(c, "  bl %s", t.bits == 32 ? "fmaf" : "fma");
        store_fp(c, in->result, 0);
        break;
    }
    case OP_FCMP: {
        load_fp(c, 31, in->a);
        load_fp(c, 30, in->b);
        char w = f->vtypes[in->a].bits == 32 ? 's' : 'd';
        E(c, "  fcmp %c31, %c30", w, w);
        /* x16 = unordered flag; combine with one ordered comparison */
        E(c, "  cset x16, vs");
        switch (in->pred) {
        case FC_UNO: break;
        case FC_ORD: E(c, "  eor x16, x16, #1"); break;
        case FC_OEQ: E(c, "  cset x17, eq"); E(c, "  bic x16, x17, x16"); break;
        case FC_ONE: E(c, "  cset x17, ne"); E(c, "  bic x16, x17, x16"); break;
        case FC_OLT: E(c, "  cset x17, lt"); E(c, "  bic x16, x17, x16"); break;
        case FC_OLE: E(c, "  cset x17, le"); E(c, "  bic x16, x17, x16"); break;
        case FC_OGT: E(c, "  cset x17, gt"); E(c, "  bic x16, x17, x16"); break;
        case FC_OGE: E(c, "  cset x17, ge"); E(c, "  bic x16, x17, x16"); break;
        case FC_UEQ: E(c, "  cset x17, eq"); E(c, "  orr x16, x17, x16"); break;
        case FC_UNE: E(c, "  cset x17, ne"); E(c, "  orr x16, x17, x16"); break;
        case FC_ULT: E(c, "  cset x17, lt"); E(c, "  orr x16, x17, x16"); break;
        case FC_ULE: E(c, "  cset x17, ls"); E(c, "  orr x16, x17, x16"); break;
        case FC_UGT: E(c, "  cset x17, hi"); E(c, "  orr x16, x17, x16"); break;
        case FC_UGE: E(c, "  cset x17, hs"); E(c, "  orr x16, x17, x16"); break;
        }
        store_gp(c, in->result, X16);
        break;
    }
    case OP_FPTOSI: emit_f2i(c, in, false); break;
    case OP_FPTOUI: emit_f2i(c, in, true); break;
    case OP_SITOFP: case OP_UITOFP: {
        Type st = f->vtypes[in->a];
        load_gp(c, X16, in->a);
        if (in->op == OP_SITOFP) sext_reg(c, X16, st.bits);
        E(c, "  %s %c31, x16", in->op == OP_SITOFP ? "scvtf" : "ucvtf", t.bits == 32 ? 's' : 'd');
        store_fp(c, in->result, 31);
        break;
    }
    case OP_FEXT: {
        load_fp(c, 31, in->a);
        E(c, "  fcvt d31, s31");
        store_fp(c, in->result, 31);
        break;
    }
    case OP_FTRUNC: {
        load_fp(c, 31, in->a);
        E(c, "  fcvt s31, d31");
        store_fp(c, in->result, 31);
        break;
    }
    case OP_SELECT: {
        int L = ++c->lbl;
        /* false arm first: copy_value routes through the scratch regs,
         * and the flag-setting cmp comes after it (moves keep flags) */
        copy_value(c, in->result, in->c);
        load_gp(c, X16, in->a);
        E(c, "  cmp x16, #0");
        E(c, "  b.eq .Lx%d_%d", c->fi, L);
        copy_value(c, in->result, in->b);
        E(c, ".Lx%d_%d:", c->fi, L);
        break;
    }
    case OP_ALLOCA: {
        int off = c->bf->allo_off[be_pos(c->bf, bi, ii)];
        addr_of(c, X16, off);
        store_gp(c, in->result, X16);
        break;
    }
    case OP_LOAD: {
        load_gp(c, X16, in->a);
        if (t.kind == TY_FLOAT) {
            E(c, "  ldr %c31, [x16]", t.bits == 32 ? 's' : 'd');
            store_fp(c, in->result, 31);
        } else {
            int eb = t.bits == 64 || t.kind == TY_PTR ? 8 : t.bits / 8;
            lane_load_gp(c, X17, eb);
            if (t.bits == 1) E(c, "  and x17, x17, #1");
            store_gp(c, in->result, X17);
        }
        break;
    }
    case OP_STORE: {
        load_gp(c, X16, in->a);
        Type vt = f->vtypes[in->b];
        if (vt.kind == TY_FLOAT) {
            load_fp(c, 31, in->b);
            E(c, "  str %c31, [x16]", vt.bits == 32 ? 's' : 'd');
        } else {
            load_gp(c, X17, in->b);
            int eb = vt.bits == 64 || vt.kind == TY_PTR ? 8 : vt.bits / 8;
            lane_store_gp(c, X17, X16, eb);
        }
        break;
    }
    case OP_VLOAD: case OP_VSTORE: {
        load_gp(c, X17, in->a);
        int v = in->op == OP_VLOAD ? in->result : in->b;
        Loc *l = &c->bf->loc[v];
        int bytes = 16 * (in->op == OP_VLOAD ? t.n : f->vtypes[in->b].n);
        addr_of(c, X16, l->off);
        for (int off = 0; off < bytes; off += 16) {
            if (in->op == OP_VLOAD) {
                E(c, "  ldr q31, [x17, #%d]", off);
                E(c, "  str q31, [x16, #%d]", off);
            } else {
                E(c, "  ldr q31, [x16, #%d]", off);
                E(c, "  str q31, [x17, #%d]", off);
            }
        }
        break;
    }
    case OP_GEP: {
        load_gp(c, X16, in->b);
        sext_reg(c, X16, f->vtypes[in->b].bits);
        int esz = mem_size_of(in->ety, c->vl);
        if (esz == 1) { /* no scale */ }
        else if ((esz & (esz - 1)) == 0) {
            int sh = 0; while ((1 << sh) < esz) sh++;
            E(c, "  lsl x16, x16, #%d", sh);
        } else {
            load_imm64(c, X17, (uint64_t)esz);
            E(c, "  mul x16, x16, x17");
        }
        load_gp(c, X17, in->a);
        E(c, "  add x16, x17, x16");
        store_gp(c, in->result, X16);
        break;
    }
    case OP_DATAPTR:
        E(c, "  adrp x16, __krell_data_%d", (int)in->imm);
        E(c, "  add x16, x16, :lo12:__krell_data_%d", (int)in->imm);
        store_gp(c, in->result, X16);
        break;
    case OP_VSPLAT: {
        Type et = ty_elem(t);
        Loc *l = &c->bf->loc[in->result];
        int bytes = 16 * t.n;
        if (et.kind == TY_FLOAT) {
            load_fp(c, 31, in->a);
            if (et.bits == 32) E(c, "  dup v31.4s, v31.s[0]");
            else E(c, "  dup v31.2d, v31.d[0]");
        } else {
            load_gp(c, X16, in->a);
            int eb = et.bits / 8;
            if (eb == 1) E(c, "  dup v31.16b, w16");
            else if (eb == 2) E(c, "  dup v31.8h, w16");
            else if (eb == 4) E(c, "  dup v31.4s, w16");
            else E(c, "  dup v31.2d, x16");
        }
        addr_of(c, X16, l->off);
        for (int off = 0; off < bytes; off += 16)
            E(c, "  str q31, [x16, #%d]", off);
        break;
    }
    case OP_VADD: case OP_VSUB: case OP_VMUL: case OP_VUDIV:
    case OP_VAND: case OP_VOR: case OP_VXOR: case OP_VLSHR:
    case OP_VFADD: case OP_VFSUB: case OP_VFMUL: case OP_VFDIV: {
        Type et = ty_elem(t);
        Loc *dl = &c->bf->loc[in->result], *al = &c->bf->loc[in->a], *bl = &c->bf->loc[in->b];
        bool scalarize = in->op == OP_VUDIV || in->op == OP_VLSHR || (in->op == OP_VMUL && et.kind == TY_INT && et.bits == 64);
        if (!scalarize) {
            const char *nm;
            char arr[8];
            if (et.kind == TY_FLOAT) {
                nm = in->op == OP_VFADD ? "fadd" : in->op == OP_VFSUB ? "fsub" :
                     in->op == OP_VFMUL ? "fmul" : "fdiv";
                snprintf(arr, sizeof arr, "%s", et.bits == 32 ? ".4s" : ".2d");
            } else {
                nm = in->op == OP_VADD ? "add" : in->op == OP_VSUB ? "sub" :
                     in->op == OP_VMUL ? "mul" : in->op == OP_VAND ? "and" :
                     in->op == OP_VOR ? "orr" : "eor";
                if (in->op == OP_VAND || in->op == OP_VOR || in->op == OP_VXOR)
                    snprintf(arr, sizeof arr, ".16b");
                else {
                    int eb = et.bits / 8;
                    snprintf(arr, sizeof arr, "%s", eb == 1 ? ".16b" : eb == 2 ? ".8h" : eb == 4 ? ".4s" : ".2d");
                }
            }
            addr_of(c, X16, dl->off);
            addr_of(c, X17, al->off);
            addr_of(c, 0, bl->off);
            for (int off = 0; off < 16 * t.n; off += 16) {
                E(c, "  ldr q31, [x17, #%d]", off);
                E(c, "  ldr q30, [x0, #%d]", off);
                E(c, "  %s v31%s, v31%s, v30%s", nm, arr, arr, arr);
                E(c, "  str q31, [x16, #%d]", off);
            }
        } else {
            int lanes = ty_lanes(t, c->vl);
            int eb = et.bits / 8;
            for (int i = 0; i < lanes; i++) {
                addr_of(c, X16, al->off - i * eb);
                lane_load_gp(c, X16, eb);
                addr_of(c, X17, bl->off - i * eb);
                lane_load_gp(c, X17, eb);
                if (in->op == OP_VUDIV) E(c, "  udiv x16, x16, x17");
                else if (in->op == OP_VLSHR) {
                    /* amount modulo the lane width (a power of two) */
                    if (et.bits < 64) E(c, "  and x17, x17, #%d", et.bits - 1);
                    E(c, "  lsr x16, x16, x17");
                }
                else E(c, "  mul x16, x16, x17");
                mask_reg(c, X16, et);
                addr_of(c, X17, dl->off - i * eb);
                lane_store_gp(c, X16, X17, eb);
            }
        }
        break;
    }
    case OP_VEXTRACT: {
        Type et = in->ty;
        Loc *al = &c->bf->loc[in->a];
        int eb = et.kind == TY_FLOAT ? et.bits / 8 : et.bits / 8;
        addr_of(c, X16, al->off - (int)in->imm * eb);
        if (et.kind == TY_FLOAT) {
            E(c, "  ldr %c31, [x16]", et.bits == 32 ? 's' : 'd');
            store_fp(c, in->result, 31);
        } else {
            lane_load_gp(c, X16, eb);
            store_gp(c, in->result, X16);
        }
        break;
    }
    case OP_VINSERT: {
        Type et = ty_elem(t);
        Loc *dl = &c->bf->loc[in->result], *al = &c->bf->loc[in->a];
        int bytes = 16 * t.n;
        for (int off = 0; off < bytes; off += 16) {
            addr_of(c, X16, al->off - off);
            E(c, "  ldr q31, [x16]");
            addr_of(c, X16, dl->off - off);
            E(c, "  str q31, [x16]");
        }
        int eb = et.bits / 8;
        addr_of(c, X17, dl->off - (int)in->imm * eb);
        if (et.kind == TY_FLOAT) {
            load_fp(c, 31, in->b);
            E(c, "  str %c31, [x17]", et.bits == 32 ? 's' : 'd');
        } else {
            load_gp(c, X16, in->b);
            lane_store_gp(c, X16, X17, eb);
        }
        break;
    }
    case OP_MEMCPY: case OP_MEMSET: {
        Loc srcs[3], dsts[3];
        int av[3] = { in->a, in->b, in->c };
        for (int i = 0; i < 3; i++) {
            srcs[i] = c->bf->loc[av[i]];
            dsts[i] = (Loc){ 1, BCLS_GP, i, 0 };
        }
        parallel_moves(c, srcs, dsts, 3, BCLS_GP);
        E(c, "  bl %s", in->op == OP_MEMCPY ? "memcpy" : "memset");
        break;
    }
    case OP_CALL: {
        const Type *ps; const char *name; int np;
        if (in->callee_extern) { ps = c->m->exts[in->callee].params; np = c->m->exts[in->callee].nparams; name = c->m->exts[in->callee].name; }
        else { Func *g = &c->m->funcs[in->callee]; ps = g->blocks[0].arg_types; np = g->blocks[0].nargs; name = g->name; }
        (void)np;
        emit_call_args(c, in, ps, false);
        E(c, "  bl %s", name);
        if (t.kind != TY_VOID) {
            if (be_class_of(t) == BCLS_FP) store_fp(c, in->result, 0);
            else store_gp(c, in->result, 0);
        }
        break;
    }
    case OP_TAILCALL: {
        const Type *ps; const char *name;
        if (in->callee_extern) { ps = c->m->exts[in->callee].params; name = c->m->exts[in->callee].name; }
        else { Func *g = &c->m->funcs[in->callee]; ps = g->blocks[0].arg_types; name = g->name; }
        emit_call_args(c, in, ps, true);
        emit_epilogue(c);
        E(c, "  b %s", name);
        break;
    }
    case OP_ASSUME: break;
    case OP_BR:
        emit_branch(c, in->blk, in->args, in->nargs);
        break;
    case OP_CONDBR: {
        int L = ++c->lbl;
        load_gp(c, X16, in->a);
        E(c, "  cbz x16, .Lx%d_%d", c->fi, L);
        emit_branch(c, in->blk, in->args, in->nargs);
        E(c, ".Lx%d_%d:", c->fi, L);
        emit_branch(c, in->blk2, in->args2, in->nargs2);
        break;
    }
    case OP_AADD: {
        load_gp(c, X16, in->a);
        load_gp(c, X17, in->b);
        const char *ord = in->aux >= AO_ACQREL ? "al" : "";
        const char *sz = t.bits == 8 ? "b" : t.bits == 16 ? "h" : "";
        char wr = t.bits == 64 ? 'x' : 'w';
        E(c, "  ldadd%s%s %c17, %c0, [x16]", ord, sz, wr, wr);
        E(c, "  mov x16, x0");
        mask_reg(c, X16, t);
        store_gp(c, in->result, X16);
        break;
    }
    case OP_ALOAD: {
        load_gp(c, X16, in->a);
        bool acq = in->aux >= AO_ACQREL;
        int eb = t.bits == 64 ? 8 : t.bits / 8;
        if (eb == 1) E(c, "  %s w17, [x16]", acq ? "ldarb" : "ldrb");
        else if (eb == 2) E(c, "  %s w17, [x16]", acq ? "ldarh" : "ldrh");
        else if (eb == 4) E(c, "  %s w17, [x16]", acq ? "ldar" : "ldr");
        else E(c, "  %s x17, [x16]", acq ? "ldar" : "ldr");
        if (t.bits == 1) E(c, "  and x17, x17, #1");
        store_gp(c, in->result, X17);
        break;
    }
    case OP_ASTORE: {
        load_gp(c, X16, in->a);
        load_gp(c, X17, in->b);
        Type vt = f->vtypes[in->b];
        bool rel = in->aux >= AO_ACQREL;
        int eb = vt.bits == 64 ? 8 : vt.bits / 8;
        if (eb == 1) E(c, "  %s w17, [x16]", rel ? "stlrb" : "strb");
        else if (eb == 2) E(c, "  %s w17, [x16]", rel ? "stlrh" : "strh");
        else if (eb == 4) E(c, "  %s w17, [x16]", rel ? "stlr" : "str");
        else E(c, "  %s x17, [x16]", rel ? "stlr" : "str");
        break;
    }
    case OP_RET: {
        if (in->a >= 0) {
            Type rt = f->vtypes[in->a];
            if (be_class_of(rt) == BCLS_FP) load_fp(c, 0, in->a);
            else load_gp(c, 0, in->a);
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
    Pools pools = { POOL_GP, 17, POOL_FP, 16 };
    BeFunc *bf = be_analyze(m, f, &pools);
    if (!bf) return -1;
    c->bf = bf;
    if (bf->frame_bytes > 30000) { be_free(bf); c->bf = NULL; return -1; }
    E(c, ".globl %s", f->name);
    E(c, ".type %s, @function", f->name);
    E(c, "%s:", f->name);
    E(c, "  stp x29, x30, [sp, #-16]!");
    E(c, "  mov x29, sp");
    if (bf->frame_bytes) {
        if (bf->frame_bytes <= 4095) E(c, "  sub sp, sp, #%d", bf->frame_bytes);
        else { load_imm64(c, X16, (uint64_t)bf->frame_bytes); E(c, "  sub sp, sp, x16"); }
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
            else if (cls == BCLS_FP && fi2 < 8) { fs[nf] = (Loc){ 1, BCLS_FP, fi2, 0 }; fd[nf] = dst; nf++; fi2++; }
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
                    E(c, "  lsl x%d, x%d, #%d", l->idx, l->idx, k);
                    E(c, "  lsr x%d, x%d, #%d", l->idx, l->idx, k);
                } else {
                    E(c, "  ldr x16, [sp, #%d]", sp_imm(c, l));
                    E(c, "  lsl x16, x16, #%d", k);
                    E(c, "  lsr x16, x16, #%d", k);
                    E(c, "  str x16, [sp, #%d]", sp_imm(c, l));
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

int be_aarch64(Module *m, const Cost *cost, FILE *out, char *err, size_t errcap) {
    const char *ve = mod_verify(m);
    if (ve) { be_err(err, errcap, ve); return -1; }
    Ctx c = { .out = out, .m = m, .vl = cost_vl_i32(cost) };
    E(&c, ".text");
    for (int i = 0; i < m->nfuncs; i++)
        if (emit_func(&c, i) != 0) { be_err(err, errcap, "aarch64: analysis failed"); return -1; }
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
