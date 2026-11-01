/* Krell — x86_64 backend (System V, GNU as, Intel syntax).
 * Values: GP in 64-bit regs/slots, canonical zero-extended; FP in xmm;
 * vectors memory-resident, chunked through xmm15. Scratch: rax, rcx, rdx,
 * r11 (GP — excluded from the pool), xmm15 (FP). Division and float
 * conversion sequences implement the defined semantics of SEMANTICS.md. */
#include "be.h"
#include <stdarg.h>

enum { RAX, RCX, RDX, RBX, RSI, RDI, R8, R9, R10, R11, R12, R13, R14, R15 };
static const char *G64[15] = { "rax","rcx","rdx","rbx","rsi","rdi","r8","r9","r10","r11","r12","r13","r14","r15" };
static const char *G32[15] = { "eax","ecx","edx","ebx","esi","edi","r8d","r9d","r10d","r11d","r12d","r13d","r14d","r15d" };
static const char *G16[15] = { "ax","cx","dx","bx","si","di","r8w","r9w","r10w","r11w","r12w","r13w","r14w","r15w" };
static const char *G8[15]  = { "al","cl","dl","bl","sil","dil","r8b","r9b","r10b","r11b","r12b","r13b","r14b","r15b" };
static const char **gname(int sz) { return sz == 8 ? G64 : sz == 4 ? G32 : sz == 2 ? G16 : G8; }
static const int ARG_GP[6] = { RDI, RSI, RDX, RCX, R8, R9 };

static const PoolReg POOL_GP[] = {
    { RSI, 0 }, { RDI, 0 }, { R8, 0 }, { R9, 0 }, { R10, 0 },
    { RBX, 1 }, { R12, 1 }, { R13, 1 }, { R14, 1 }, { R15, 1 },
};
static const PoolReg POOL_FP[] = {
    { 0,0 },{ 1,0 },{ 2,0 },{ 3,0 },{ 4,0 },{ 5,0 },{ 6,0 },{ 7,0 },
    { 8,0 },{ 9,0 },{ 10,0 },{ 11,0 },{ 12,0 },{ 13,0 },{ 14,0 },
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

/* operand text for a value's home; sz in bytes for register naming */
static void locstr(Ctx *c, char *buf, size_t cap, int v, int sz) {
    Loc *l = &c->bf->loc[v];
    if (l->is_reg) {
        if (l->cls == BCLS_FP) snprintf(buf, cap, "xmm%d", l->idx);
        else snprintf(buf, cap, "%s", gname(sz)[l->idx]);
    } else {
        snprintf(buf, cap, "[rbp - %d]", l->off);
    }
}
static void locstr_off(char *buf, size_t cap, Loc *l, int sz) {
    if (l->is_reg) {
        if (l->cls == BCLS_FP) snprintf(buf, cap, "xmm%d", l->idx);
        else snprintf(buf, cap, "%s", gname(sz)[l->idx]);
    } else if (l->off >= 0) snprintf(buf, cap, "[rbp - %d]", l->off);
    else snprintf(buf, cap, "[rbp + %d]", -l->off);
}

static void load_gp(Ctx *c, int reg, int v) {
    Loc *l = &c->bf->loc[v];
    if (l->is_reg && l->cls == BCLS_GP && l->idx == reg) return;
    char b[64]; locstr(c, b, sizeof b, v, 8);
    E(c, "  mov %s, %s", G64[reg], b);
}
static void store_gp(Ctx *c, int v, int reg) {
    Loc *l = &c->bf->loc[v];
    if (l->is_reg && l->cls == BCLS_GP && l->idx == reg) return;
    char b[64]; locstr(c, b, sizeof b, v, 8);
    E(c, "  mov %s, %s", b, G64[reg]);
}
static void load_fp(Ctx *c, int xmm, int v) {
    Loc *l = &c->bf->loc[v];
    Type t = c->f->vtypes[v];
    const char *op = t.bits == 32 ? "movss" : "movsd";
    if (l->is_reg && l->cls == BCLS_FP && l->idx == xmm) return;
    char b[64]; locstr(c, b, sizeof b, v, 8);
    E(c, "  %s xmm%d, %s", op, xmm, b);
}
static void store_fp(Ctx *c, int v, int xmm) {
    Loc *l = &c->bf->loc[v];
    Type t = c->f->vtypes[v];
    const char *op = t.bits == 32 ? "movss" : "movsd";
    if (l->is_reg && l->cls == BCLS_FP && l->idx == xmm) return;
    char b[64]; locstr(c, b, sizeof b, v, 8);
    E(c, "  %s %s, xmm%d", op, b, xmm);
}
/* copy a scalar value (any class) to another value's home, via scratch */
static void copy_value(Ctx *c, int dst, int src) {
    if (dst == src) return;
    Type t = c->f->vtypes[src];
    int cls = be_class_of(t);
    if (cls == BCLS_GP) { load_gp(c, R11, src); store_gp(c, dst, R11); }
    else if (cls == BCLS_FP) { load_fp(c, 15, src); store_fp(c, dst, 15); }
    else { /* vector: chunk copy through xmm15 */
        Loc *dl = &c->bf->loc[dst], *sl = &c->bf->loc[src];
        int bytes = 16 * t.n;
        for (int off = 0; off < bytes; off += 16) {
            E(c, "  movups xmm15, [rbp - %d]", sl->off - off);
            E(c, "  movups [rbp - %d], xmm15", dl->off - off);
        }
    }
}

/* parallel-move callback */
typedef struct { Ctx *c; } MvCtx;
static void x86_mv(void *p, Loc dst, Loc src) {
    MvCtx *mc = p; Ctx *c = mc->c;
    char db[64], sb[64];
    if (dst.cls == BCLS_GP) {
        locstr_off(db, sizeof db, &dst, 8);
        locstr_off(sb, sizeof sb, &src, 8);
        if (!dst.is_reg && !src.is_reg) {
            E(c, "  mov r11, %s", sb);
            E(c, "  mov %s, r11", db);
        } else E(c, "  mov %s, %s", db, sb);
    } else {
        locstr_off(db, sizeof db, &dst, 8);
        locstr_off(sb, sizeof sb, &src, 8);
        if (!dst.is_reg && !src.is_reg) {
            E(c, "  movsd xmm15, %s", sb);
            E(c, "  movsd %s, xmm15", db);
        } else E(c, "  movsd %s, %s", db, sb);
    }
}
static void parallel_moves(Ctx *c, Loc *srcs, Loc *dsts, int n, int cls) {
    if (n <= 0) return;
    MvCtx mc = { c };
    Loc scratch = { 1, (int8_t)cls, cls == BCLS_GP ? R11 : 15, 0 };
    be_parallel_move(&mc, x86_mv, srcs, dsts, n, scratch);
}

/* sign-extend the value in r11 from `bits` to 64 (bits < 64) */
static void sext_r11(Ctx *c, int bits) {
    if (bits >= 64) return;
    E(c, "  shl r11, %d", 64 - bits);
    E(c, "  sar r11, %d", 64 - bits);
}
/* sign-extend the value in rax from `bits` to 64 (bits < 64) */
static void sext_rax(Ctx *c, int bits) {
    if (bits >= 64) return;
    E(c, "  shl rax, %d", 64 - bits);
    E(c, "  sar rax, %d", 64 - bits);
}
/* byte size of a type in memory (vector = lanes x elem) */
static int mem_size_of(Type t, int vl) {
    if (t.kind == TY_VEC) return ty_lanes(t, vl) * (t.elem_bits / 8);
    return ty_bytes(t);
}
static void mask_r11(Ctx *c, Type t) {
    /* zero-extend via shift pair: GAS rejects wide unsigned literals as
     * `and` immediates, and the pair needs no scratch register */
    if (t.bits < 64) { int k = 64 - t.bits; E(c, "  shl r11, %d", k); E(c, "  shr r11, %d", k); }
}

/* save/restore callee-saved regs */
static void save_regs(Ctx *c) {
    BeFunc *bf = c->bf;
    for (int i = 0; i < bf->nsave_gp; i++)
        E(c, "  mov [rbp - %d], %s", 16 + 8 * i, G64[bf->save_gp[i]]);
    for (int i = 0; i < bf->nsave_fp; i++)
        E(c, "  movsd [rbp - %d], xmm%d", 16 + 8 * (bf->nsave_gp + i), bf->save_fp[i]);
}
static void restore_regs(Ctx *c) {
    BeFunc *bf = c->bf;
    for (int i = 0; i < bf->nsave_fp; i++)
        E(c, "  movsd xmm%d, [rbp - %d]", bf->save_fp[i], 16 + 8 * (bf->nsave_gp + i));
    for (int i = 0; i < bf->nsave_gp; i++)
        E(c, "  mov %s, [rbp - %d]", G64[bf->save_gp[i]], 16 + 8 * i);
}

/* move call arguments into the ABI; tail calls write stack args through
 * the outgoing area then to the caller's stack-arg region */
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
        if (cls == BCLS_GP && gi < 6) {
            gs[ng] = c->bf->loc[v];
            gd[ng] = (Loc){ 1, BCLS_GP, ARG_GP[gi], 0 };
            ng++; gi++;
        } else if (cls == BCLS_FP && fi2 < 8) {
            fs[nf] = c->bf->loc[v];
            fd[nf] = (Loc){ 1, BCLS_FP, fi2, 0 };
            nf++; fi2++;
        } else if (cls == BCLS_GP) { sa[nsa].v = v; sa[nsa].slot = stk++; nsa++; }
        else if (cls == BCLS_FP) { sa[nsa].v = v; sa[nsa].slot = stk++; nsa++; }
        else { /* vector by value: not in the v1 ABI; treat as stack blob (shouldn't happen post-verify) */ }
        if (cls == BCLS_GP && gi >= 6) { /* subsequent GP args also stack */ }
    }
    /* NOTE: classification above assigns stack slots in argument order for
     * args that overflow their class file (SysV scalar subset). */
    int frame = c->bf->frame_bytes;
    for (int i = 0; i < nsa; i++) {
        int v = sa[i].v;
        int cls = be_class_of(c->f->vtypes[v]);
        if (tail) {
            /* phase 1: to outgoing temp; phase 2: to caller stack-arg area */
            if (cls == BCLS_GP) { load_gp(c, R11, v); E(c, "  mov [rbp - %d], r11", frame - 8 * i); }
            else { load_fp(c, 15, v); E(c, "  movsd [rbp - %d], xmm15", frame - 8 * i); }
        } else {
            if (cls == BCLS_GP) { load_gp(c, R11, v); E(c, "  mov [rbp - %d], r11", frame - 8 * sa[i].slot); }
            else { load_fp(c, 15, v); E(c, "  movsd [rbp - %d], xmm15", frame - 8 * sa[i].slot); }
        }
    }
    if (tail) {
        for (int i = 0; i < nsa; i++) {
            int cls = be_class_of(c->f->vtypes[sa[i].v]);
            if (cls == BCLS_GP) { E(c, "  mov r11, [rbp - %d]", frame - 8 * i); E(c, "  mov [rbp + %d], r11", 16 + 8 * sa[i].slot); }
            else { E(c, "  movsd xmm15, [rbp - %d]", frame - 8 * i); E(c, "  movsd [rbp + %d], xmm15", 16 + 8 * sa[i].slot); }
        }
    }
    parallel_moves(c, gs, gd, ng, BCLS_GP);
    parallel_moves(c, fs, fd, nf, BCLS_FP);
    free(gs); free(gd); free(fs); free(fd); free(sa);
}

static void emit_epilogue(Ctx *c) {
    restore_regs(c);
    E(c, "  leave");
}

/* branch to a block with its argument moves */
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
    E(c, "  jmp .Lb%d_%d", c->fi, tgt);
}

/* integer division family with the defined semantics (div-by-zero = 0,
 * INT_MIN/-1 wraps) */
static void emit_div(Ctx *c, Instr *in, bool is_signed, bool is_rem) {
    Type t = in->ty;
    int W = t.bits == 64 ? 8 : 4;
    const char **GN = gname(W);
    load_gp(c, RAX, in->a);
    if (is_signed) {
        /* sign-extend from the value's OWN width: widths under 32 need
         * the shift pair, exactly 32 takes movsxd, 64 is already there */
        if (t.bits < 32) { E(c, "  shl rax, %d", 64 - t.bits); E(c, "  sar rax, %d", 64 - t.bits); }
        else if (t.bits == 32) E(c, "  movsxd rax, eax");
    }
    load_gp(c, RCX, in->b);
    if (is_signed) {
        if (t.bits < 32) { E(c, "  shl rcx, %d", 64 - t.bits); E(c, "  sar rcx, %d", 64 - t.bits); }
        else if (t.bits == 32) E(c, "  movsxd rcx, ecx");
    }
    int L1 = ++c->lbl, L2 = ++c->lbl;
    E(c, "  test %s, %s", GN[RCX], GN[RCX]);
    E(c, "  jne .Lx%d_%d", c->fi, L1);
    E(c, "  xor r11d, r11d");
    E(c, "  jmp .Lx%d_%d", c->fi, L2);
    E(c, ".Lx%d_%d:", c->fi, L1);
    if (is_signed) {
        int L3 = ++c->lbl;
        /* INT_MIN / -1 guard */
        E(c, "  cmp %s, -1", GN[RCX]);
        E(c, "  jne .Lx%d_%d", c->fi, L3);
        if (W == 8) E(c, "  mov rdx, -9223372036854775808");
        else E(c, "  mov edx, -2147483648");
        E(c, "  cmp %s, %s", GN[RAX], GN[RDX]);
        E(c, "  jne .Lx%d_%d", c->fi, L3);
        if (is_rem) E(c, "  xor r11d, r11d");
        else E(c, "  mov r11, rax");
        E(c, "  jmp .Lx%d_%d", c->fi, L2);
        E(c, ".Lx%d_%d:", c->fi, L3);
        if (W == 8) E(c, "  cqo"); else E(c, "  cdq");
        E(c, "  idiv %s", GN[RCX]);
    } else {
        E(c, "  xor edx, edx");
        if (W == 8) E(c, "  xor rdx, rdx");
        E(c, "  div %s", GN[RCX]);
    }
    E(c, "  mov %s, %s", W == 8 ? "r11" : "r11d", is_rem ? GN[RDX] : GN[RAX]);
    E(c, ".Lx%d_%d:", c->fi, L2);
    mask_r11(c, t);
    store_gp(c, in->result, R11);
}

/* saturating float -> int (SEMANTICS §6) */
static void emit_f2i(Ctx *c, Instr *in, bool unsig) {
    Type tt = in->ty;
    Type st = c->f->vtypes[in->a];
    load_fp(c, 15, in->a);
    if (!unsig) {
        E(c, "  %s r11, xmm15", st.bits == 32 ? "cvttss2si" : "cvttsd2si");
        int L7 = ++c->lbl, L9 = ++c->lbl;
        E(c, "  mov rax, -9223372036854775808");
        E(c, "  cmp r11, rax");
        E(c, "  jne .Lx%d_%d", c->fi, L9);
        E(c, "  %s xmm15, [rip + __krell_zero]", st.bits == 32 ? "ucomiss" : "ucomisd");
        E(c, "  jp .Lx%d_%d", c->fi, L7);
        E(c, "  jb .Lx%d_%d", c->fi, L9);
        E(c, "  mov r11, 0x7fffffffffffffff");
        E(c, "  jmp .Lx%d_%d", c->fi, L9);
        E(c, ".Lx%d_%d:", c->fi, L7);
        E(c, "  xor r11d, r11d");
        E(c, ".Lx%d_%d:", c->fi, L9);
        if (tt.bits < 64) {
            int64_t hi = (int64_t)((1ull << (tt.bits - 1)) - 1);
            int64_t lo = -(int64_t)(1ull << (tt.bits - 1));
            E(c, "  mov rax, %lld", (long long)hi);
            E(c, "  cmp r11, rax");
            E(c, "  cmovg r11, rax");
            E(c, "  mov rax, %lld", (long long)lo);
            E(c, "  cmp r11, rax");
            E(c, "  cmovl r11, rax");
            mask_r11(c, tt);
        }
        store_gp(c, in->result, R11);
        return;
    }
    /* unsigned: work in f64 */
    if (st.bits == 32) E(c, "  cvtss2sd xmm15, xmm15");
    int Ln = ++c->lbl, Lmax = ++c->lbl, Lsimple = ++c->lbl, Ldone = ++c->lbl;
    E(c, "  ucomisd xmm15, [rip + __krell_zero]");
    E(c, "  jp .Lx%d_%d", c->fi, Ln);
    E(c, "  jb .Lx%d_%d", c->fi, Ln);           /* negative -> 0 */
    E(c, "  ucomisd xmm15, [rip + __krell_2_64]");
    E(c, "  jae .Lx%d_%d", c->fi, Lmax);
    E(c, "  ucomisd xmm15, [rip + __krell_2_63]");
    E(c, "  jb .Lx%d_%d", c->fi, Lsimple);
    /* 2^63 <= x < 2^64: subtract, convert, set top bit */
    E(c, "  subsd xmm15, [rip + __krell_2_63]");
    E(c, "  cvttsd2si r11, xmm15");
    E(c, "  mov rax, -9223372036854775808");
    E(c, "  or r11, rax");
    E(c, "  jmp .Lx%d_%d", c->fi, Ldone);
    E(c, ".Lx%d_%d:", c->fi, Ln);
    E(c, "  xor r11d, r11d");
    E(c, "  jmp .Lx%d_%d", c->fi, Ldone);
    E(c, ".Lx%d_%d:", c->fi, Lmax);
    E(c, "  mov r11, 0xffffffffffffffff");
    E(c, "  jmp .Lx%d_%d", c->fi, Ldone);
    E(c, ".Lx%d_%d:", c->fi, Lsimple);
    E(c, "  cvttsd2si r11, xmm15");
    E(c, ".Lx%d_%d:", c->fi, Ldone);
    if (tt.bits < 64) {
        uint64_t hi = (1ull << tt.bits) - 1;
        E(c, "  mov rax, 0x%llx", (unsigned long long)hi);
        E(c, "  cmp r11, rax");
        E(c, "  cmova r11, rax");
    }
    store_gp(c, in->result, R11);
}

static void emit_instr(Ctx *c, int bi, int ii) {
    Func *f = c->f;
    Instr *in = &f->blocks[bi].ins[ii];
    Type t = in->ty;
    char sb[64], sb2[64];
    switch (in->op) {
    case OP_ICONST: {
        E(c, "  mov r11, %lld", (long long)in->imm);
        mask_r11(c, t);
        store_gp(c, in->result, R11);
        break;
    }
    case OP_FCONST: {
        if (t.bits == 32) {
            E(c, "  mov eax, %llu", (unsigned long long)(uint32_t)in->imm);
            E(c, "  movd xmm15, eax");
        } else {
            E(c, "  mov rax, 0x%llx", (unsigned long long)in->imm);
            E(c, "  movq xmm15, rax");
        }
        store_fp(c, in->result, 15);
        break;
    }
    case OP_FREEZE: copy_value(c, in->result, in->a); break;
    case OP_BITCAST: {
        Type st = f->vtypes[in->a];
        int sc = be_class_of(st), dc = be_class_of(t);
        if (sc == dc) { copy_value(c, in->result, in->a); break; }
        if (sc == BCLS_GP && dc == BCLS_FP) {
            load_gp(c, RAX, in->a);
            Loc *dl = &c->bf->loc[in->result];
            if (dl->is_reg) E(c, "  %s xmm%d, rax", t.bits == 32 ? "movd" : "movq", dl->idx);
            else E(c, "  mov [rbp - %d], rax", dl->off);
        } else {
            load_fp(c, 15, in->a);
            E(c, "  %s rax, xmm15", st.bits == 32 ? "movd" : "movq");
            store_gp(c, in->result, RAX);
        }
        break;
    }
    case OP_ADD: case OP_SUB: case OP_AND: case OP_OR: case OP_XOR: case OP_MUL: {
        const char *nm = in->op == OP_ADD ? "add" : in->op == OP_SUB ? "sub" :
                         in->op == OP_AND ? "and" : in->op == OP_OR ? "or" :
                         in->op == OP_XOR ? "xor" : "imul";
        load_gp(c, R11, in->a);
        locstr(c, sb, sizeof sb, in->b, t.bits == 64 ? 8 : 4);
        if (t.bits == 64) E(c, "  %s r11, %s", nm, sb);
        else E(c, "  %s r11d, %s", nm, sb);
        mask_r11(c, t);
        store_gp(c, in->result, R11);
        break;
    }
    case OP_NEG:
        load_gp(c, R11, in->a);
        if (t.bits == 64) E(c, "  neg r11"); else E(c, "  neg r11d");
        mask_r11(c, t);
        store_gp(c, in->result, R11);
        break;
    case OP_NOT:
        load_gp(c, R11, in->a);
        if (t.bits == 64) E(c, "  not r11"); else E(c, "  not r11d");
        mask_r11(c, t);
        store_gp(c, in->result, R11);
        break;
    case OP_SHL: case OP_LSHR: case OP_ASHR: {
        const char *nm = in->op == OP_SHL ? "shl" : in->op == OP_LSHR ? "shr" : "sar";
        load_gp(c, R11, in->a);
        if (in->op == OP_ASHR) sext_r11(c, t.bits);
        int64_t k;
        if (be_iconst_val(f, in->b, &k)) {
            /* mathematical mod: C's % keeps the sign, semantics don't */
            int amt = t.bits ? (int)(((k % t.bits) + t.bits) % t.bits) : 0;
            if (t.bits == 64) E(c, "  %s r11, %d", nm, amt);
            else E(c, "  %s r11d, %d", nm, amt);
        } else {
            load_gp(c, RCX, in->b);
            if (t.bits < 64) E(c, "  and ecx, %d", t.bits - 1);
            if (t.bits == 64) E(c, "  %s r11, cl", nm);
            else E(c, "  %s r11d, cl", nm);
        }
        mask_r11(c, t);
        store_gp(c, in->result, R11);
        break;
    }
    case OP_UDIV: emit_div(c, in, false, false); break;
    case OP_SDIV: emit_div(c, in, true, false); break;
    case OP_UREM: emit_div(c, in, false, true); break;
    case OP_SREM: emit_div(c, in, true, true); break;
    case OP_ICMP: {
        static const char *CC[10] = { "e","ne","b","be","a","ae","l","le","g","ge" };
        bool sgn = in->pred >= IC_SLT;
        load_gp(c, R11, in->a);
        if (sgn) sext_r11(c, f->vtypes[in->a].bits);
        load_gp(c, RAX, in->b);
        if (sgn) sext_rax(c, f->vtypes[in->b].bits);
        E(c, "  cmp r11, rax");
        E(c, "  set%s al", CC[in->pred]);
        E(c, "  movzx eax, al");
        store_gp(c, in->result, RAX);
        break;
    }
    case OP_POPCOUNT:
        load_gp(c, R11, in->a);
        E(c, "  popcnt r11, r11");
        store_gp(c, in->result, R11);
        break;
    case OP_CLZ: case OP_CTZ: {
        int L1 = ++c->lbl, L2 = ++c->lbl;
        load_gp(c, R11, in->a);
        E(c, "  test r11, r11");
        E(c, "  jnz .Lx%d_%d", c->fi, L1);
        E(c, "  mov r11, %d", t.bits);
        E(c, "  jmp .Lx%d_%d", c->fi, L2);
        E(c, ".Lx%d_%d:", c->fi, L1);
        if (in->op == OP_CLZ) {
            E(c, "  bsr rax, r11");
            E(c, "  mov r11, %d", t.bits - 1);
            E(c, "  sub r11, rax");
        } else E(c, "  bsf r11, r11");
        E(c, ".Lx%d_%d:", c->fi, L2);
        store_gp(c, in->result, R11);
        break;
    }
    case OP_BSWAP:
        load_gp(c, R11, in->a);
        if (t.bits == 16) E(c, "  rol r11w, 8");
        else if (t.bits == 32) E(c, "  bswap r11d");
        else E(c, "  bswap r11");
        store_gp(c, in->result, R11);
        break;
    case OP_TRUNC:
        load_gp(c, R11, in->a);
        mask_r11(c, t);
        store_gp(c, in->result, R11);
        break;
    case OP_ZEXT: copy_value(c, in->result, in->a); break;
    case OP_SEXT:
        load_gp(c, R11, in->a);
        sext_r11(c, f->vtypes[in->a].bits);
        mask_r11(c, t);
        store_gp(c, in->result, R11);
        break;
    case OP_FADD: case OP_FSUB: case OP_FMUL: case OP_FDIV: {
        const char *nm = in->op == OP_FADD ? "add" : in->op == OP_FSUB ? "sub" :
                         in->op == OP_FMUL ? "mul" : "div";
        load_fp(c, 15, in->a);
        locstr(c, sb, sizeof sb, in->b, 8);
        E(c, "  %s%s xmm15, %s", nm, t.bits == 32 ? "ss" : "sd", sb);
        if (t.bits == 32) { E(c, "  movd eax, xmm15"); E(c, "  movd xmm15, eax"); }
        store_fp(c, in->result, 15);
        break;
    }
    case OP_FNEG:
        load_fp(c, 15, in->a);
        E(c, "  xorps xmm15, [rip + __krell_s%d]", t.bits);
        store_fp(c, in->result, 15);
        break;
    case OP_FABS:
        load_fp(c, 15, in->a);
        E(c, "  andps xmm15, [rip + __krell_a%d]", t.bits);
        store_fp(c, in->result, 15);
        break;
    case OP_FMA: {
        /* args go through the parallel-move resolver: an argument's home
         * may be one of the ABI registers another argument targets */
        Loc srcs[3], dsts[3];
        int av[3] = { in->a, in->b, in->c };
        for (int i = 0; i < 3; i++) {
            srcs[i] = c->bf->loc[av[i]];
            dsts[i] = (Loc){ 1, BCLS_FP, i, 0 };
        }
        parallel_moves(c, srcs, dsts, 3, BCLS_FP);
        E(c, "  call %s", t.bits == 32 ? "fmaf" : "fma");
        store_fp(c, in->result, 0);
        break;
    }
    case OP_FCMP: {
        static const char *CC[14] = { "e","ne","b","be","a","ae","e","ne","b","be","a","ae","","" };
        Type st = f->vtypes[in->a];
        load_fp(c, 15, in->a);
        locstr(c, sb, sizeof sb, in->b, 8);
        E(c, "  xor eax, eax");
        E(c, "  %s xmm15, %s", st.bits == 32 ? "ucomiss" : "ucomisd", sb);
        E(c, "  setp r11b");
        if (in->pred == FC_ORD) { E(c, "  xor r11b, 1"); E(c, "  mov eax, r11d"); }
        else if (in->pred == FC_UNO) { E(c, "  mov eax, r11d"); }
        else {
            E(c, "  set%s al", CC[in->pred]);
            if (in->pred <= FC_OGE) { E(c, "  xor r11b, 1"); E(c, "  and al, r11b"); }
            else E(c, "  or al, r11b");
            E(c, "  movzx eax, al");
        }
        /* mov eax, r11d above may carry garbage high bits in r11: normalize */
        if (in->pred == FC_ORD || in->pred == FC_UNO) { /* eax = r11d & 1 via setp byte only; mask */ E(c, "  and eax, 1"); }
        store_gp(c, in->result, RAX);
        break;
    }
    case OP_FTRUNC:
        locstr(c, sb, sizeof sb, in->a, 8);
        E(c, "  cvtsd2ss xmm15, %s", sb);
        store_fp(c, in->result, 15);
        break;
    case OP_FEXT:
        locstr(c, sb, sizeof sb, in->a, 8);
        E(c, "  cvtss2sd xmm15, %s", sb);
        store_fp(c, in->result, 15);
        break;
    case OP_FPTOSI: emit_f2i(c, in, false); break;
    case OP_FPTOUI: emit_f2i(c, in, true); break;
    case OP_SITOFP: {
        Type st = f->vtypes[in->a];
        load_gp(c, R11, in->a);
        sext_r11(c, st.bits);
        E(c, "  %s xmm15, r11", t.bits == 32 ? "cvtsi2ss" : "cvtsi2sd");
        store_fp(c, in->result, 15);
        break;
    }
    case OP_UITOFP: {
        Type st = f->vtypes[in->a];
        load_gp(c, R11, in->a);
        if (st.bits < 64) {
            E(c, "  %s xmm15, r11", t.bits == 32 ? "cvtsi2ss" : "cvtsi2sd");
        } else {
            int L1 = ++c->lbl, L2 = ++c->lbl;
            E(c, "  test r11, r11");
            E(c, "  jns .Lx%d_%d", c->fi, L1);
            E(c, "  mov rax, r11");
            E(c, "  shr rax, 1");
            E(c, "  and r11d, 1");
            E(c, "  or rax, r11");
            E(c, "  %s xmm15, rax", t.bits == 32 ? "cvtsi2ss" : "cvtsi2sd");
            E(c, "  %s xmm15, xmm15", t.bits == 32 ? "addss" : "addsd");
            E(c, "  jmp .Lx%d_%d", c->fi, L2);
            E(c, ".Lx%d_%d:", c->fi, L1);
            E(c, "  %s xmm15, r11", t.bits == 32 ? "cvtsi2ss" : "cvtsi2sd");
            E(c, ".Lx%d_%d:", c->fi, L2);
        }
        store_fp(c, in->result, 15);
        break;
    }
    case OP_ALLOCA: {
        int off = c->bf->allo_off[be_pos(c->bf, bi, ii)];
        E(c, "  lea r11, [rbp - %d]", off);
        store_gp(c, in->result, R11);
        break;
    }
    case OP_DATAPTR:
        E(c, "  lea r11, [rip + __krell_data_%d]", (int)in->imm);
        store_gp(c, in->result, R11);
        break;
    case OP_GEP: {
        load_gp(c, R11, in->a);
        load_gp(c, RAX, in->b);
        Type it2 = f->vtypes[in->b];
        if (it2.bits < 64) { E(c, "  shl rax, %d", 64 - it2.bits); E(c, "  sar rax, %d", 64 - it2.bits); }
        int esz = (int)mem_size_of(in->ety, c->vl);
        if (esz != 1) E(c, "  imul rax, rax, %d", esz);
        E(c, "  add r11, rax");
        store_gp(c, in->result, R11);
        break;
    }
    case OP_LOAD: {
        load_gp(c, RAX, in->a);
        if (t.kind == TY_FLOAT) {
            E(c, "  %s xmm15, [rax]", t.bits == 32 ? "movss" : "movsd");
            store_fp(c, in->result, 15);
        } else {
            const char *szp = t.bits == 8 ? "BYTE PTR" : t.bits == 16 ? "WORD PTR" : t.bits == 32 ? "DWORD PTR" : "QWORD PTR";
            if (t.bits == 8 || t.bits == 16) E(c, "  movzx r11d, %s [rax]", szp);
            else if (t.bits == 32) E(c, "  mov r11d, DWORD PTR [rax]");
            else E(c, "  mov r11, QWORD PTR [rax]");
            if (t.bits == 1) E(c, "  and r11, 1");
            store_gp(c, in->result, R11);
        }
        break;
    }
    case OP_STORE: {
        load_gp(c, RAX, in->a);
        Type vt = f->vtypes[in->b];
        if (vt.kind == TY_FLOAT) {
            load_fp(c, 15, in->b);
            E(c, "  %s [rax], xmm15", vt.bits == 32 ? "movss" : "movsd");
        } else {
            load_gp(c, R11, in->b);
            const char *r = vt.bits == 8 ? "r11b" : vt.bits == 16 ? "r11w" : vt.bits == 32 ? "r11d" : "r11";
            E(c, "  mov [rax], %s", r);
        }
        break;
    }
    case OP_VLOAD: case OP_VSTORE: {
        load_gp(c, RAX, in->a);
        int v = in->op == OP_VLOAD ? in->result : in->b;
        Loc *l = &c->bf->loc[v];
        int bytes = 16 * t.n;
        if (in->op == OP_VLOAD) bytes = 16 * t.n;
        else bytes = 16 * f->vtypes[in->b].n;
        for (int off = 0; off < bytes; off += 16) {
            if (in->op == OP_VLOAD) {
                E(c, "  movups xmm15, [rax + %d]", off);
                E(c, "  movups [rbp - %d], xmm15", l->off - off);
            } else {
                E(c, "  movups xmm15, [rbp - %d]", l->off - off);
                E(c, "  movups [rax + %d], xmm15", off);
            }
        }
        break;
    }
    case OP_VSPLAT: {
        Type et = ty_elem(t);
        Loc *l = &c->bf->loc[in->result];
        int lanes = ty_lanes(t, c->vl);
        int eb = et.bits / 8;
        if (et.kind == TY_FLOAT) load_fp(c, 15, in->a);
        else load_gp(c, R11, in->a);
        for (int i = 0; i < lanes; i++) {
            if (et.kind == TY_FLOAT)
                E(c, "  %s [rbp - %d], xmm15", et.bits == 32 ? "movss" : "movsd", l->off - i * eb);
            else {
                const char *r = eb == 1 ? "r11b" : eb == 2 ? "r11w" : eb == 4 ? "r11d" : "r11";
                E(c, "  mov [rbp - %d], %s", l->off - i * eb, r);
            }
        }
        break;
    }
    case OP_VADD: case OP_VSUB: case OP_VMUL: case OP_VUDIV:
    case OP_VAND: case OP_VOR: case OP_VXOR:
    case OP_VFADD: case OP_VFSUB: case OP_VFMUL: case OP_VFDIV: {
        Type et = ty_elem(t);
        Loc *dl = &c->bf->loc[in->result], *al = &c->bf->loc[in->a], *bl = &c->bf->loc[in->b];
        bool scalarize = in->op == OP_VUDIV || (in->op == OP_VMUL && et.kind == TY_INT && et.bits != 32 && et.bits != 16);
        if (!scalarize) {
            const char *nm = NULL;
            if (et.kind == TY_FLOAT) {
                nm = in->op == OP_VFADD ? (et.bits == 32 ? "addps" : "addpd") :
                     in->op == OP_VFSUB ? (et.bits == 32 ? "subps" : "subpd") :
                     in->op == OP_VFMUL ? (et.bits == 32 ? "mulps" : "mulpd") :
                                          (et.bits == 32 ? "divps" : "divpd");
            } else if (in->op == OP_VAND) nm = "pand";
            else if (in->op == OP_VOR) nm = "por";
            else if (in->op == OP_VXOR) nm = "pxor";
            else {
                const char *base = in->op == OP_VADD ? "padd" : in->op == OP_VSUB ? "psub" : "pmull";
                char tmp[16];
                snprintf(tmp, sizeof tmp, "%s%c", base, et.bits == 8 ? 'b' : et.bits == 16 ? 'w' : et.bits == 32 ? 'd' : 'q');
                if (in->op == OP_VMUL && et.bits == 64) nm = NULL;
                else nm = tmp;
                if (nm) {
                    for (int off = 0; off < 16 * t.n; off += 16) {
                        E(c, "  movups xmm15, [rbp - %d]", al->off - off);
                        E(c, "  %s xmm15, [rbp - %d]", nm, bl->off - off);
                        E(c, "  movups [rbp - %d], xmm15", dl->off - off);
                    }
                    break;
                }
                scalarize = true;
            }
            if (nm) {
                for (int off = 0; off < 16 * t.n; off += 16) {
                    E(c, "  movups xmm15, [rbp - %d]", al->off - off);
                    E(c, "  %s xmm15, [rbp - %d]", nm, bl->off - off);
                    E(c, "  movups [rbp - %d], xmm15", dl->off - off);
                }
                break;
            }
        }
        /* scalarized lane loop */
        int lanes = ty_lanes(t, c->vl);
        int eb = et.bits / 8;
        for (int i = 0; i < lanes; i++) {
            if (et.kind == TY_FLOAT) {
                E(c, "  %s xmm15, [rbp - %d]", et.bits == 32 ? "movss" : "movsd", al->off - i * eb);
                const char *nm = in->op == OP_VFADD ? "add" : in->op == OP_VFSUB ? "sub" : in->op == OP_VFMUL ? "mul" : "div";
                E(c, "  %s%s xmm15, [rbp - %d]", nm, et.bits == 32 ? "ss" : "sd", bl->off - i * eb);
                E(c, "  %s [rbp - %d], xmm15", et.bits == 32 ? "movss" : "movsd", dl->off - i * eb);
            } else {
                const char *szp = eb == 1 ? "BYTE PTR" : eb == 2 ? "WORD PTR" : eb == 4 ? "DWORD PTR" : "QWORD PTR";
                if (eb <= 2) E(c, "  movzx r11d, %s [rbp - %d]", szp, al->off - i * eb);
                else if (eb == 4) E(c, "  mov r11d, DWORD PTR [rbp - %d]", al->off - i * eb);
                else E(c, "  mov r11, QWORD PTR [rbp - %d]", al->off - i * eb);
                if (in->op == OP_VUDIV) {
                    int Ld = ++c->lbl, Ldone = ++c->lbl;
                    if (eb <= 2) E(c, "  movzx eax, %s [rbp - %d]", szp, bl->off - i * eb);
                    else if (eb == 4) E(c, "  mov eax, DWORD PTR [rbp - %d]", bl->off - i * eb);
                    else E(c, "  mov rax, QWORD PTR [rbp - %d]", bl->off - i * eb);
                    E(c, "  test rax, rax");
                    E(c, "  jne .Lx%d_%d", c->fi, Ld);
                    E(c, "  xor r11d, r11d");
                    E(c, "  jmp .Lx%d_%d", c->fi, Ldone);
                    E(c, ".Lx%d_%d:", c->fi, Ld);
                    E(c, "  mov rcx, rax");
                    E(c, "  mov rax, r11");
                    E(c, "  xor edx, edx");
                    E(c, "  div rcx");
                    E(c, "  mov r11, rax");
                    E(c, ".Lx%d_%d:", c->fi, Ldone);
                } else {
                    const char *nm = in->op == OP_VADD ? "add" : in->op == OP_VSUB ? "sub" :
                                     in->op == OP_VMUL ? "imul" : in->op == OP_VAND ? "and" :
                                     in->op == OP_VOR ? "or" : "xor";
                    if (eb <= 2) E(c, "  movzx eax, %s [rbp - %d]", szp, bl->off - i * eb);
                    else if (eb == 4) E(c, "  mov eax, DWORD PTR [rbp - %d]", bl->off - i * eb);
                    else E(c, "  mov rax, QWORD PTR [rbp - %d]", bl->off - i * eb);
                    E(c, "  %s r11, rax", nm);
                }
                mask_r11(c, et);
                const char *r = eb == 1 ? "r11b" : eb == 2 ? "r11w" : eb == 4 ? "r11d" : "r11";
                E(c, "  mov [rbp - %d], %s", dl->off - i * eb, r);
            }
        }
        break;
    }
    case OP_VEXTRACT: {
        Type et = ty_elem(f->vtypes[in->a]);
        Loc *al = &c->bf->loc[in->a];
        int eb = et.bits / 8;
        int off = al->off - (int)in->imm * eb;
        if (et.kind == TY_FLOAT) {
            E(c, "  %s xmm15, [rbp - %d]", et.bits == 32 ? "movss" : "movsd", off);
            store_fp(c, in->result, 15);
        } else {
            if (eb <= 2) E(c, "  movzx r11d, %s PTR [rbp - %d]", eb == 1 ? "BYTE" : "WORD", off);
            else if (eb == 4) E(c, "  mov r11d, DWORD PTR [rbp - %d]", off);
            else E(c, "  mov r11, QWORD PTR [rbp - %d]", off);
            store_gp(c, in->result, R11);
        }
        break;
    }
    case OP_VINSERT: {
        copy_value(c, in->result, in->a);
        Type et = ty_elem(t);
        Loc *dl = &c->bf->loc[in->result];
        int eb = et.bits / 8;
        int off = dl->off - (int)in->imm * eb;
        if (et.kind == TY_FLOAT) {
            load_fp(c, 15, in->b);
            E(c, "  %s [rbp - %d], xmm15", et.bits == 32 ? "movss" : "movsd", off);
        } else {
            load_gp(c, R11, in->b);
            const char *r = eb == 1 ? "r11b" : eb == 2 ? "r11w" : eb == 4 ? "r11d" : "r11";
            E(c, "  mov [rbp - %d], %s", off, r);
        }
        break;
    }
    case OP_ALOAD: {
        load_gp(c, RAX, in->a);
        const char *szp = t.bits == 8 ? "BYTE PTR" : t.bits == 16 ? "WORD PTR" : t.bits == 32 ? "DWORD PTR" : "QWORD PTR";
        if (t.bits == 8 || t.bits == 16) E(c, "  movzx r11d, %s [rax]", szp);
        else if (t.bits == 32) E(c, "  mov r11d, DWORD PTR [rax]");
        else E(c, "  mov r11, QWORD PTR [rax]");
        store_gp(c, in->result, R11);
        break;
    }
    case OP_ASTORE: {
        load_gp(c, RAX, in->a);
        load_gp(c, R11, in->b);
        Type vt = f->vtypes[in->b];
        const char *r = vt.bits == 8 ? "r11b" : vt.bits == 16 ? "r11w" : vt.bits == 32 ? "r11d" : "r11";
        if (in->aux == AO_SEQCST) E(c, "  xchg [rax], %s", r);
        else E(c, "  mov [rax], %s", r);
        break;
    }
    case OP_AADD: {
        load_gp(c, RAX, in->a);
        load_gp(c, R11, in->b);
        const char *r = t.bits == 8 ? "r11b" : t.bits == 16 ? "r11w" : t.bits == 32 ? "r11d" : "r11";
        E(c, "  lock xadd [rax], %s", r);
        mask_r11(c, t);
        store_gp(c, in->result, R11);
        break;
    }
    case OP_MEMCPY: case OP_MEMSET: {
        /* args (dst, src/byte, n) -> (rdi, rsi, rdx) via parallel moves */
        Loc srcs[3], dsts[3];
        int order[3] = { in->a, in->b, in->c };
        int regs3[3] = { RDI, RSI, RDX };
        for (int i = 0; i < 3; i++) {
            srcs[i] = c->bf->loc[order[i]];
            dsts[i] = (Loc){ 1, BCLS_GP, regs3[i], 0 };
        }
        parallel_moves(c, srcs, dsts, 3, BCLS_GP);
        E(c, "  call %s", in->op == OP_MEMCPY ? "memcpy" : "memset");
        break;
    }
    case OP_CALL: {
        const Type *ps; int np; const char *name;
        if (in->callee_extern) { ps = c->m->exts[in->callee].params; np = c->m->exts[in->callee].nparams; name = c->m->exts[in->callee].name; }
        else { Func *g = &c->m->funcs[in->callee]; ps = g->blocks[0].arg_types; np = g->blocks[0].nargs; name = g->name; }
        (void)np;
        emit_call_args(c, in, ps, false);
        E(c, "  call %s", name);
        if (t.kind != TY_VOID) {
            if (be_class_of(t) == BCLS_FP) store_fp(c, in->result, 0);
            else store_gp(c, in->result, RAX);
        }
        break;
    }
    case OP_TAILCALL: {
        const Type *ps; const char *name;
        if (in->callee_extern) { ps = c->m->exts[in->callee].params; name = c->m->exts[in->callee].name; }
        else { Func *g = &c->m->funcs[in->callee]; ps = g->blocks[0].arg_types; name = g->name; }
        emit_call_args(c, in, ps, true);
        emit_epilogue(c);
        E(c, "  jmp %s", name);
        break;
    }
    case OP_SELECT: {
        int L = ++c->lbl;
        /* false arm first: copy_value routes through r11, so the condition
         * is loaded only after it (movs do not clobber the test flags) */
        copy_value(c, in->result, in->c);
        load_gp(c, R11, in->a);
        E(c, "  test r11, r11");
        E(c, "  je .Lx%d_%d", c->fi, L);
        copy_value(c, in->result, in->b);
        E(c, ".Lx%d_%d:", c->fi, L);
        break;
    }
    case OP_ASSUME: break;
    case OP_BR:
        emit_branch(c, in->blk, in->args, in->nargs);
        break;
    case OP_CONDBR: {
        int L = ++c->lbl;
        load_gp(c, R11, in->a);
        E(c, "  test r11, r11");
        E(c, "  je .Lx%d_%d", c->fi, L);
        emit_branch(c, in->blk, in->args, in->nargs);
        E(c, ".Lx%d_%d:", c->fi, L);
        emit_branch(c, in->blk2, in->args2, in->nargs2);
        break;
    }
    case OP_RET: {
        if (in->a >= 0) {
            Type rt = f->vtypes[in->a];
            if (be_class_of(rt) == BCLS_FP) load_fp(c, 0, in->a);
            else load_gp(c, RAX, in->a);
        }
        emit_epilogue(c);
        E(c, "  ret");
        break;
    }
    default: break;
    }
    (void)sb2;
}

static int emit_func(Ctx *c, int fi) {
    Module *m = c->m;
    Func *f = &m->funcs[fi];
    c->f = f; c->fi = fi; c->lbl = 0;
    Pools pools = { POOL_GP, 10, POOL_FP, 15 };
    BeFunc *bf = be_analyze(m, f, &pools);
    if (!bf) return -1;
    c->bf = bf;
    E(c, ".globl %s", f->name);
    E(c, ".type %s, @function", f->name);
    E(c, "%s:", f->name);
    E(c, "  push rbp");
    E(c, "  mov rbp, rsp");
    if (bf->frame_bytes) E(c, "  sub rsp, %d", bf->frame_bytes);
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
            if (cls == BCLS_GP && gi < 6) { gs[ng] = (Loc){ 1, BCLS_GP, ARG_GP[gi], 0 }; gd[ng] = dst; ng++; gi++; }
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
        /* canonical form: narrow integer params are masked in place —
         * the C ABI leaves their high register bits unspecified */
        for (int i = 0; i < b0->nargs; i++) {
            Type pt = b0->arg_types[i];
            if (pt.kind == TY_INT && pt.bits < 64) {
                char b[64]; locstr(c, b, sizeof b, b0->arg_vals[i], 8);
                int k = 64 - pt.bits;
                if (strchr(b, '[')) {
                    E(c, "  mov r11, %s", b);
                    E(c, "  shl r11, %d", k); E(c, "  shr r11, %d", k);
                    E(c, "  mov %s, r11", b);
                } else {
                    E(c, "  shl %s, %d", b, k); E(c, "  shr %s, %d", b, k);
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

int be_x86_64(Module *m, const Cost *cost, FILE *out, char *err, size_t errcap) {
    const char *ve = mod_verify(m);
    if (ve) { be_err(err, errcap, ve); return -1; }
    Ctx c = { .out = out, .m = m, .vl = cost_vl_i32(cost) };
    E(&c, ".intel_syntax noprefix");
    E(&c, ".text");
    for (int i = 0; i < m->nfuncs; i++)
        if (emit_func(&c, i) != 0) { be_err(err, errcap, "x86_64: analysis failed"); return -1; }
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
    E(&c, ".balign 16");
    E(&c, "__krell_s32: .long 0x80000000, 0, 0, 0");
    E(&c, "__krell_s64: .quad 0x8000000000000000, 0");
    E(&c, "__krell_a32: .long 0x7fffffff, 0, 0, 0");
    E(&c, "__krell_a64: .quad 0x7fffffffffffffff, 0");
    E(&c, "__krell_zero: .quad 0");
    E(&c, "__krell_2_63: .quad 0x43e0000000000000");
    E(&c, "__krell_2_64: .quad 0x43f0000000000000");
    E(&c, ".section .note.GNU-stack,\"\",@progbits");
    return 0;
}
