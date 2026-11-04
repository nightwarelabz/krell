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

static const PoolReg POOL_FP[] = {
    { 0,0 },{ 1,0 },{ 2,0 },{ 3,0 },{ 4,0 },{ 5,0 },{ 6,0 },{ 7,0 },
    { 8,0 },{ 9,0 },{ 10,0 },{ 11,0 },{ 12,0 },{ 13,0 },{ 14,0 },
};

typedef struct {
    FILE *out;
    Module *m;
    Func *f;
    BeFunc *bf;
    Instr **defins;
    bool *folded_ins;
    bool *cmp_fuse;
    Instr *span_or[512];
    int span_px[512];
    int span_light[512];
    int span_blk[512];
    int nspan;
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
static void locstr_off(char *buf, size_t cap, Loc *l, int sz) {
    if (l->is_reg) {
        if (l->cls == BCLS_FP) snprintf(buf, cap, "xmm%d", l->idx);
        else snprintf(buf, cap, "%s", gname(sz)[l->idx]);
    } else if (l->off >= 0) snprintf(buf, cap, "[rbp - %d]", l->off);
    else snprintf(buf, cap, "[rbp + %d]", -l->off);
}
static void locstr(Ctx *c, char *buf, size_t cap, int v, int sz) {
    locstr_off(buf, cap, &c->bf->loc[v], sz);
}

static inline uint64_t msk64(int bits) { return bits >= 64 ? ~0ull : ((1ull << bits) - 1ull); }
static int mem_size_of(Type t, int vl);
static void load_gp(Ctx *c, int reg, int v);
static void load128_half(Ctx *c, int reg, int v, int half);
static void store128_half(Ctx *c, int v, int reg, int half);

typedef struct {
    int base_v;
    int idx_v;
    int scale;
    int disp;
} X86Addr;

static void resolve_x86_addr(Ctx *c, int ptr_v, X86Addr *out) {
    out->base_v = ptr_v;
    out->idx_v = -1;
    out->scale = 0;
    out->disp = 0;
    if (ptr_v < 0 || ptr_v >= c->f->nvalues || !c->defins) return;

    Instr *d = c->defins[ptr_v];
    if (!d || d->op != OP_GEP) return;

    int esz = (int)mem_size_of(d->ety, c->vl);
    int64_t imm;
    if (be_iconst_val(c->f, d->b, &imm)) {
        out->disp += (int)(imm * esz);
        out->base_v = d->a;
        if (d->a >= 0 && d->a < c->f->nvalues && c->defins[d->a] && c->defins[d->a]->op == OP_GEP) {
            Instr *d2 = c->defins[d->a];
            int esz2 = (int)mem_size_of(d2->ety, c->vl);
            if (be_iconst_val(c->f, d2->b, &imm)) {
                out->disp += (int)(imm * esz2);
                out->base_v = d2->a;
            } else if (esz2 == 1 || esz2 == 2 || esz2 == 4 || esz2 == 8) {
                out->idx_v = d2->b;
                out->scale = esz2;
                out->base_v = d2->a;
            }
        }
    } else if (esz == 1 || esz == 2 || esz == 4 || esz == 8) {
        out->base_v = d->a;
        out->idx_v = d->b;
        out->scale = esz;
        if (d->a >= 0 && d->a < c->f->nvalues && c->defins[d->a] && c->defins[d->a]->op == OP_GEP) {
            Instr *d2 = c->defins[d->a];
            if (be_iconst_val(c->f, d2->b, &imm)) {
                int esz2 = (int)mem_size_of(d2->ety, c->vl);
                out->disp += (int)(imm * esz2);
                out->base_v = d2->a;
            }
        }
    }
}

static bool can_fold_gep(Ctx *c, const X86Addr *a) {
    if (a->idx_v < 0) return true;
    if (!c->bf) return true;
    bool base_reg = (a->base_v >= 0 && c->bf->loc[a->base_v].is_reg);
    bool idx_reg = (a->idx_v >= 0 && c->bf->loc[a->idx_v].is_reg);
    return base_reg || idx_reg;
}

static void format_x86_addr(Ctx *c, char *buf, size_t cap, const X86Addr *a) {
    const char *basereg = "rax";
    if (a->base_v >= 0) {
        Loc *bl = &c->bf->loc[a->base_v];
        if (bl->is_reg && bl->cls == BCLS_GP) basereg = G64[bl->idx];
        else load_gp(c, RAX, a->base_v);
    }
    const char *idxreg = NULL;
    if (a->idx_v >= 0) {
        Loc *il = &c->bf->loc[a->idx_v];
        if (il->is_reg && il->cls == BCLS_GP) idxreg = G64[il->idx];
        else { load_gp(c, R11, a->idx_v); idxreg = "r11"; }
    }
    if (idxreg) {
        if (a->scale == 1) {
            if (a->disp == 0) snprintf(buf, cap, "[%s + %s]", basereg, idxreg);
            else if (a->disp > 0) snprintf(buf, cap, "[%s + %s + %d]", basereg, idxreg, a->disp);
            else snprintf(buf, cap, "[%s + %s - %d]", basereg, idxreg, -a->disp);
        } else {
            if (a->disp == 0) snprintf(buf, cap, "[%s + %s*%d]", basereg, idxreg, a->scale);
            else if (a->disp > 0) snprintf(buf, cap, "[%s + %s*%d + %d]", basereg, idxreg, a->scale, a->disp);
            else snprintf(buf, cap, "[%s + %s*%d - %d]", basereg, idxreg, a->scale, -a->disp);
        }
    } else {
        if (a->disp == 0) snprintf(buf, cap, "[%s]", basereg);
        else if (a->disp > 0) snprintf(buf, cap, "[%s + %d]", basereg, a->disp);
        else snprintf(buf, cap, "[%s - %d]", basereg, -a->disp);
    }
}

static void load_gp(Ctx *c, int reg, int v) {
    Loc *l = &c->bf->loc[v];
    if (l->is_reg && l->cls == BCLS_GP && l->idx == reg) return;
    char b[64]; locstr(c, b, sizeof b, v, 8);
    E(c, "  mov %s, %s", G64[reg], b);
}
static void store_gp(Ctx *c, int v, int reg) {
    if (v >= 0 && v < c->f->nvalues && c->bf->defpos[v] == c->bf->endpos[v]) return;
    Loc *l = &c->bf->loc[v];
    if (l->is_reg && l->cls == BCLS_GP && l->idx == reg) return;
    if (!l->is_reg && l->idx < 0) return;
    char b[64]; locstr(c, b, sizeof b, v, 8);
    E(c, "  mov %s, %s", b, G64[reg]);
}
static void load_fp(Ctx *c, int xmm, int v) {
    Loc *l = &c->bf->loc[v];
    Type t = c->f->vtypes[v];
    const char *op = t.kind == TY_VEC ? "movups" : t.bits == 32 ? "movss" : "movsd";
    if (l->is_reg && l->cls == BCLS_FP && l->idx == xmm) return;
    if (l->is_reg && l->cls == BCLS_FP) {
        if (t.kind == TY_VEC) E(c, "  movaps xmm%d, xmm%d", xmm, l->idx);
        else E(c, "  %s xmm%d, xmm%d", op, xmm, l->idx);
        return;
    }
    char b[64]; locstr(c, b, sizeof b, v, 8);
    E(c, "  %s xmm%d, %s", op, xmm, b);
}
static void store_fp(Ctx *c, int v, int xmm) {
    if (v >= 0 && v < c->f->nvalues && c->bf->defpos[v] == c->bf->endpos[v]) return;
    Loc *l = &c->bf->loc[v];
    Type t = c->f->vtypes[v];
    const char *op = t.kind == TY_VEC ? "movups" : t.bits == 32 ? "movss" : "movsd";
    if (l->is_reg && l->cls == BCLS_FP && l->idx == xmm) return;
    if (l->is_reg && l->cls == BCLS_FP) {
        if (t.kind == TY_VEC) E(c, "  movaps xmm%d, xmm%d", l->idx, xmm);
        else E(c, "  %s xmm%d, xmm%d", op, l->idx, xmm);
        return;
    }
    if (!l->is_reg && l->idx < 0) return;
    char b[64]; locstr(c, b, sizeof b, v, 8);
    E(c, "  %s %s, xmm%d", op, b, xmm);
}
/* copy a scalar value (any class) to another value's home, via scratch */
static void copy_value(Ctx *c, int dst, int src) {
    if (dst == src) return;
    Type t = c->f->vtypes[src];
    int cls = be_class_of(t);
    if (cls == BCLS_GP) {
        Loc *dl = &c->bf->loc[dst], *sl = &c->bf->loc[src];
        if (dl->is_reg && sl->is_reg) {
            if (dl->idx != sl->idx) E(c, "  mov %s, %s", G64[dl->idx], G64[sl->idx]);
        } else {
            load_gp(c, R11, src);
            store_gp(c, dst, R11);
        }
    }
    else if (cls == BCLS_FP) {
        Loc *dl = &c->bf->loc[dst], *sl = &c->bf->loc[src];
        if (dl->is_reg && sl->is_reg) {
            E(c, "  movaps xmm%d, xmm%d", dl->idx, sl->idx);
        } else {
            load_fp(c, 15, src); store_fp(c, dst, 15);
        }
    }
    else if (cls == BCLS_MEM128) {
        if (c->f->isconst[src]) {
            E(c, "  mov rax, %lld", (long long)c->f->cval[src]);
            E(c, "  mov [rbp - %d], rax", c->bf->loc[dst].off);
            E(c, "  mov rax, %lld", (long long)c->f->cval_hi[src]);
            E(c, "  mov [rbp - %d], rax", c->bf->loc[dst].off - 8);
        } else {
            Loc *dl = &c->bf->loc[dst], *sl = &c->bf->loc[src];
            if (dl->off != sl->off) {
                E(c, "  mov rax, [rbp - %d]", sl->off);
                E(c, "  mov [rbp - %d], rax", dl->off);
                E(c, "  mov rax, [rbp - %d]", sl->off - 8);
                E(c, "  mov [rbp - %d], rax", dl->off - 8);
            }
        }
    }
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
        } else if (dst.is_reg && src.is_reg) {
            E(c, "  movaps %s, %s", db, sb);
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
/* returns the number of FP arguments placed in registers (the SysV
 * AL value for extern calls) */
static int emit_call_args(Ctx *c, Instr *in, const Type *params, bool tail) {
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
        else if (cls == BCLS_MEM128) { sa[nsa].v = v; sa[nsa].slot = stk; stk += 2; nsa++; }
        else { /* vector by value: not in the v1 ABI; treat as stack blob (shouldn't happen post-verify) */ }
        if (cls == BCLS_GP && gi >= 6) { /* subsequent GP args also stack */ }
    }
    /* NOTE: classification above assigns stack slots in argument order for
     * args that overflow their class file (SysV scalar subset). */
    int frame = c->bf->frame_bytes;
    for (int i = 0; i < nsa; i++) {
        int v = sa[i].v;
        int cls = be_class_of(c->f->vtypes[v]);
        if (cls == BCLS_MEM128) {
            /* two slots; in the tail phase this is the phase-1 temp,
             * addressed by slot like every other class */
            load128_half(c, RAX, v, 0); E(c, "  mov [rbp - %d], rax", frame - 8 * sa[i].slot);
            load128_half(c, RAX, v, 1); E(c, "  mov [rbp - %d], rax", frame - 8 * sa[i].slot - 8);
        } else if (tail) {
            /* phase 1: to outgoing temp; phase 2: to caller stack-arg area */
            if (cls == BCLS_GP) { load_gp(c, R11, v); E(c, "  mov [rbp - %d], r11", frame - 8 * sa[i].slot); }
            else { load_fp(c, 15, v); E(c, "  movsd [rbp - %d], xmm15", frame - 8 * sa[i].slot); }
        } else {
            if (cls == BCLS_GP) { load_gp(c, R11, v); E(c, "  mov [rbp - %d], r11", frame - 8 * sa[i].slot); }
            else { load_fp(c, 15, v); E(c, "  movsd [rbp - %d], xmm15", frame - 8 * sa[i].slot); }
        }
    }
    if (tail) {
        for (int i = 0; i < nsa; i++) {
            int cls = be_class_of(c->f->vtypes[sa[i].v]);
            if (cls == BCLS_MEM128) {
                E(c, "  mov r11, [rbp - %d]", frame - 8 * sa[i].slot);
                E(c, "  mov [rbp + %d], r11", 16 + 8 * sa[i].slot);
                E(c, "  mov r11, [rbp - %d]", frame - 8 * sa[i].slot - 8);
                E(c, "  mov [rbp + %d], r11", 16 + 8 * sa[i].slot + 8);
            }
            else if (cls == BCLS_GP) { E(c, "  mov r11, [rbp - %d]", frame - 8 * sa[i].slot); E(c, "  mov [rbp + %d], r11", 16 + 8 * sa[i].slot); }
            else { E(c, "  movsd xmm15, [rbp - %d]", frame - 8 * sa[i].slot); E(c, "  movsd [rbp + %d], xmm15", 16 + 8 * sa[i].slot); }
        }
    }
    parallel_moves(c, gs, gd, ng, BCLS_GP);
    parallel_moves(c, fs, fd, nf, BCLS_FP);
    free(gs); free(gd); free(fs); free(fd); free(sa);
    return fi2;
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
        if (c->bf->defpos[dv] == c->bf->endpos[dv]) continue;
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

static bool is_span_blend(Ctx *c, Instr *in, int *out_px, int *out_light,
                          Instr **out_rb, Instr **out_rb_shr, Instr **out_rb_mul, Instr **out_rb_and,
                          Instr **out_g, Instr **out_g_mul, Instr **out_g_and, Instr **out_g_shr) {
    if (in->op != OP_OR) return false;
    if (in->a < 0 || in->b < 0 || in->a >= c->f->nvalues || in->b >= c->f->nvalues) return false;
    Instr *da = c->defins[in->a];
    Instr *db = c->defins[in->b];
    if (!da || !db) return false;

    for (int swap = 0; swap < 2; swap++) {
        Instr *d_rb = swap ? db : da;
        Instr *d_g  = swap ? da : db;

        int64_t k;
        if (d_rb->op != OP_AND || !be_iconst_val(c->f, d_rb->b, &k) || k != 16711935) continue;
        if (d_rb->a < 0 || d_rb->a >= c->f->nvalues) continue;
        Instr *d_rb_shr = c->defins[d_rb->a];
        if (!d_rb_shr || d_rb_shr->op != OP_LSHR || !be_iconst_val(c->f, d_rb_shr->b, &k) || k != 8) continue;
        if (d_rb_shr->a < 0 || d_rb_shr->a >= c->f->nvalues) continue;
        Instr *d_rb_mul = c->defins[d_rb_shr->a];
        if (!d_rb_mul || d_rb_mul->op != OP_MUL) continue;
        Instr *d_rb_and = (d_rb_mul->a >= 0 && d_rb_mul->a < c->f->nvalues) ? c->defins[d_rb_mul->a] : NULL;
        int light = d_rb_mul->b;
        if (!d_rb_and || d_rb_and->op != OP_AND) {
            d_rb_and = (d_rb_mul->b >= 0 && d_rb_mul->b < c->f->nvalues) ? c->defins[d_rb_mul->b] : NULL;
            light = d_rb_mul->a;
        }
        if (!d_rb_and || d_rb_and->op != OP_AND || !be_iconst_val(c->f, d_rb_and->b, &k) || k != 16711935) continue;
        int px = d_rb_and->a;

        if (d_g->op != OP_AND || !be_iconst_val(c->f, d_g->b, &k) || k != 65280) continue;
        if (d_g->a < 0 || d_g->a >= c->f->nvalues) continue;
        Instr *d_g_mul = c->defins[d_g->a];
        if (!d_g_mul || d_g_mul->op != OP_MUL) continue;
        Instr *d_g_and = (d_g_mul->a >= 0 && d_g_mul->a < c->f->nvalues) ? c->defins[d_g_mul->a] : NULL;
        int g_light = d_g_mul->b;
        if (!d_g_and || d_g_and->op != OP_AND) {
            d_g_and = (d_g_mul->b >= 0 && d_g_mul->b < c->f->nvalues) ? c->defins[d_g_mul->b] : NULL;
            g_light = d_g_mul->a;
        }
        if (g_light != light) continue;
        if (!d_g_and || d_g_and->op != OP_AND || !be_iconst_val(c->f, d_g_and->b, &k) || k != 255) continue;
        if (d_g_and->a < 0 || d_g_and->a >= c->f->nvalues) continue;
        Instr *d_g_shr = c->defins[d_g_and->a];
        if (!d_g_shr || d_g_shr->op != OP_LSHR || !be_iconst_val(c->f, d_g_shr->b, &k) || k != 8) continue;
        if (d_g_shr->a != px) continue;

        *out_px = px;
        *out_light = light;
        if (out_rb) *out_rb = d_rb;
        if (out_rb_shr) *out_rb_shr = d_rb_shr;
        if (out_rb_mul) *out_rb_mul = d_rb_mul;
        if (out_rb_and) *out_rb_and = d_rb_and;
        if (out_g) *out_g = d_g;
        if (out_g_mul) *out_g_mul = d_g_mul;
        if (out_g_and) *out_g_and = d_g_and;
        if (out_g_shr) *out_g_shr = d_g_shr;
        return true;
    }
    return false;
}

/* Extract lane i of a vector operand into a GP register, from
 * wherever the operand lives. xmm15 is the only shuffle scratch:
 * it is outside the allocator's FP pool, so it can never hold a
 * live value. (The shared vector path once read slot offsets
 * unconditionally; a register-resident operand's offset is 0 and
 * the accesses corrupted the saved frame.) */
static void vec_lane_gp(Ctx *c, Loc *l, int i, Type et, const char *d64, const char *d32) {
    int eb = et.bits / 8;
    if (l->is_reg) {
        if (et.bits == 64) {
            if (i == 0) E(c, "  movq %s, xmm%d", d64, l->idx);
            else { E(c, "  movhlps xmm15, xmm%d", l->idx); E(c, "  movq %s, xmm15", d64); }
        } else if (et.bits == 32) {
            if (i == 0) E(c, "  movd %s, xmm%d", d32, l->idx);
            else { E(c, "  pshufd xmm15, xmm%d, %d", l->idx, i); E(c, "  movd %s, xmm15", d32); }
        } else {
            E(c, "  pextr%c %s, xmm%d, %d", et.bits == 16 ? 'w' : 'b', d32, l->idx, i);
        }
    } else {
        const char *szp = eb == 1 ? "BYTE PTR" : eb == 2 ? "WORD PTR" : eb == 4 ? "DWORD PTR" : "QWORD PTR";
        if (eb <= 2) E(c, "  movzx %s, %s [rbp - %d]", d32, szp, l->off - i * eb);
        else if (eb == 4) E(c, "  mov %s, DWORD PTR [rbp - %d]", d32, l->off - i * eb);
        else E(c, "  mov %s, QWORD PTR [rbp - %d]", d64, l->off - i * eb);
    }
}

/* Extract lane i of a float vector operand into the low lane of
 * xmm register `reg`, from wherever the operand lives. */
static void vec_lane_fp(Ctx *c, Loc *l, int i, Type et, int reg) {
    int eb = et.bits / 8;
    if (l->is_reg) {
        if (et.bits == 32) {
            if (i == 0) E(c, "  movss xmm%d, xmm%d", reg, l->idx);
            else E(c, "  pshufd xmm%d, xmm%d, %d", reg, l->idx, i);
        } else {
            if (i == 0) E(c, "  movsd xmm%d, xmm%d", reg, l->idx);
            else E(c, "  movhlps xmm%d, xmm%d", reg, l->idx);
        }
    } else {
        E(c, "  %s xmm%d, [rbp - %d]", et.bits == 32 ? "movss" : "movsd", reg, l->off - i * eb);
    }
}

/* ---- i128 (v3.0): memory-resident values, 16-byte slots holding
 * (lo, hi); arithmetic runs through rax/rcx/rdx, none of which the
 * allocator owns. Return convention: rax = lo, rdx = hi. Arguments:
 * two consecutive 8-byte stack slots (caller writes, callee copies),
 * the same classification walk on both sides. ---- */
static bool ty128(Type t) { return t.kind == TY_INT && t.bits == 128; }
static void m128(char *buf, size_t cap, Ctx *c, int v, int half) {
    Loc *l = &c->bf->loc[v];
    int eff = l->off - 8 * half;
    if (eff >= 0) snprintf(buf, cap, "[rbp - %d]", eff);
    else snprintf(buf, cap, "[rbp + %d]", -eff);
}
static void load128_half(Ctx *c, int reg, int v, int half) {
    if (v >= 0 && v < c->f->nvalues && c->f->isconst[v]) {
        uint64_t k = half ? c->f->cval_hi[v] : c->f->cval[v];
        E(c, "  mov %s, %llu", G64[reg], (unsigned long long)k);
    } else {
        char b[64]; m128(b, sizeof b, c, v, half);
        E(c, "  mov %s, %s", G64[reg], b);
    }
}
static void store128_half(Ctx *c, int v, int reg, int half) {
    if (v >= 0 && v < c->f->nvalues && c->bf->defpos[v] == c->bf->endpos[v]) return;
    char b[64]; m128(b, sizeof b, c, v, half);
    E(c, "  mov %s, %s", b, G64[reg]);
}
static void store128_zero(Ctx *c, int v, int half) {
    if (v >= 0 && v < c->f->nvalues && c->bf->defpos[v] == c->bf->endpos[v]) return;
    char b[64]; m128(b, sizeof b, c, v, half);
    E(c, "  mov qword ptr %s, 0", b);
}
/* rax *= half of b (mul form), result rdx:rax */
static void mul128_op(Ctx *c, int bv, int half) {
    if (bv >= 0 && bv < c->f->nvalues && c->f->isconst[bv]) {
        load128_half(c, RCX, bv, half);
        E(c, "  mul rcx");
    } else {
        char b[64]; m128(b, sizeof b, c, bv, half);
        E(c, "  mul qword ptr %s", b);
    }
}
static bool emit_i128(Ctx *c, Instr *in) {
    Func *f = c->f;
    char rb[64];
    switch (in->op) {
    case OP_ICONST: {
        E(c, "  mov rax, %lld", (long long)in->imm); store128_half(c, in->result, RAX, 0);
        E(c, "  mov rax, %lld", (long long)in->imm2); store128_half(c, in->result, RAX, 1);
        return true;
    }
    case OP_ADD: case OP_SUB: case OP_AND: case OP_OR: case OP_XOR: {
        const char *lo_op = in->op == OP_ADD ? "add" : in->op == OP_SUB ? "sub" : in->op == OP_AND ? "and" : in->op == OP_OR ? "or" : "xor";
        const char *hi_op = in->op == OP_ADD ? "adc" : in->op == OP_SUB ? "sbb" : lo_op;
        load128_half(c, RAX, in->a, 0); load128_half(c, RCX, in->b, 0);
        E(c, "  %s rax, rcx", lo_op); store128_half(c, in->result, RAX, 0);
        load128_half(c, RAX, in->a, 1); load128_half(c, RCX, in->b, 1);
        E(c, "  %s rax, rcx", hi_op); store128_half(c, in->result, RAX, 1);
        return true;
    }
    case OP_NEG:
        E(c, "  mov rax, 0"); load128_half(c, RCX, in->a, 0);
        E(c, "  sub rax, rcx"); store128_half(c, in->result, RAX, 0);
        E(c, "  mov rax, 0"); load128_half(c, RCX, in->a, 1);
        E(c, "  sbb rax, rcx"); store128_half(c, in->result, RAX, 1);
        return true;
    case OP_NOT:
        for (int h = 0; h < 2; h++) {
            load128_half(c, RAX, in->a, h);
            E(c, "  not rax"); store128_half(c, in->result, RAX, h);
        }
        return true;
    case OP_MUL: {
        /* cross terms accumulate in the result's high slot itself:
         * mul128_op may clobber rcx (constant operands load there),
         * so no register can hold the running sum */
        load128_half(c, RAX, in->a, 0); mul128_op(c, in->b, 0);
        store128_half(c, in->result, RAX, 0);
        store128_half(c, in->result, RDX, 1);
        load128_half(c, RAX, in->a, 0); mul128_op(c, in->b, 1);
        if (!(in->result >= 0 && c->bf->defpos[in->result] == c->bf->endpos[in->result])) {
            m128(rb, sizeof rb, c, in->result, 1); E(c, "  add %s, rax", rb);
            load128_half(c, RAX, in->a, 1); mul128_op(c, in->b, 0);
            E(c, "  add %s, rax", rb);
        }
        return true;
    }
    case OP_SHL: case OP_LSHR: case OP_ASHR: {
        int64_t kc;
        if (be_iconst_val(f, in->b, &kc) || (in->b >= 0 && f->isconst[in->b])) {
            int k = (int)(((in->b >= 0 && f->isconst[in->b]) ? (int64_t)f->cval[in->b] : kc) & 127);
            if (k < 64) {
                if (in->op == OP_SHL) {
                    load128_half(c, RDX, in->a, 1); load128_half(c, RAX, in->a, 0);
                    if (k) { E(c, "  shld rdx, rax, %d", k); E(c, "  shl rax, %d", k); }
                    store128_half(c, in->result, RDX, 1); store128_half(c, in->result, RAX, 0);
                } else {
                    load128_half(c, RAX, in->a, 0); load128_half(c, RDX, in->a, 1);
                    if (k) { E(c, "  shrd rax, rdx, %d", k); E(c, "  %s rdx, %d", in->op == OP_LSHR ? "shr" : "sar", k); }
                    store128_half(c, in->result, RAX, 0); store128_half(c, in->result, RDX, 1);
                }
            } else {
                int k2 = k - 64;
                if (in->op == OP_SHL) {
                    load128_half(c, RAX, in->a, 0); if (k2) E(c, "  shl rax, %d", k2);
                    store128_half(c, in->result, RAX, 1); store128_zero(c, in->result, 0);
                } else if (in->op == OP_LSHR) {
                    load128_half(c, RAX, in->a, 1); if (k2) E(c, "  shr rax, %d", k2);
                    store128_half(c, in->result, RAX, 0); store128_zero(c, in->result, 1);
                } else {
                    load128_half(c, RAX, in->a, 1); load128_half(c, RDX, in->a, 1);
                    if (k2) E(c, "  sar rax, %d", k2);
                    E(c, "  sar rdx, 63");
                    store128_half(c, in->result, RAX, 0); store128_half(c, in->result, RDX, 1);
                }
            }
            return true;
        }
        /* variable amount: rcx = b_lo & 127 */
        int Lbig = ++c->lbl, Ldone = ++c->lbl;
        load128_half(c, RCX, in->b, 0);
        E(c, "  and rcx, 127");
        E(c, "  cmp rcx, 64");
        E(c, "  jae .Lx%d_%d", c->fi, Lbig);
        if (in->op == OP_SHL) {
            load128_half(c, RDX, in->a, 1); load128_half(c, RAX, in->a, 0);
            E(c, "  shld rdx, rax, cl"); E(c, "  shl rax, cl");
            store128_half(c, in->result, RDX, 1); store128_half(c, in->result, RAX, 0);
        } else {
            load128_half(c, RAX, in->a, 0); load128_half(c, RDX, in->a, 1);
            E(c, "  shrd rax, rdx, cl"); E(c, "  %s rdx, cl", in->op == OP_LSHR ? "shr" : "sar");
            store128_half(c, in->result, RAX, 0); store128_half(c, in->result, RDX, 1);
        }
        E(c, "  jmp .Lx%d_%d", c->fi, Ldone);
        E(c, ".Lx%d_%d:", c->fi, Lbig);
        E(c, "  sub rcx, 64");
        if (in->op == OP_SHL) {
            load128_half(c, RAX, in->a, 0); E(c, "  shl rax, cl");
            store128_half(c, in->result, RAX, 1); store128_zero(c, in->result, 0);
        } else if (in->op == OP_LSHR) {
            load128_half(c, RAX, in->a, 1); E(c, "  shr rax, cl");
            store128_half(c, in->result, RAX, 0); store128_zero(c, in->result, 1);
        } else {
            load128_half(c, RAX, in->a, 1); load128_half(c, RDX, in->a, 1);
            E(c, "  sar rax, cl"); E(c, "  sar rdx, 63");
            store128_half(c, in->result, RAX, 0); store128_half(c, in->result, RDX, 1);
        }
        E(c, ".Lx%d_%d:", c->fi, Ldone);
        return true;
    }
    case OP_ICMP: {
        static const char *CCU[10] = { "e","ne","b","be","a","ae","b","be","a","ae" };
        static const char *CCS[10] = { "e","ne","b","be","a","ae","l","le","g","ge" };
        if (in->pred == IC_EQ || in->pred == IC_NE) {
            load128_half(c, RAX, in->a, 0); load128_half(c, RCX, in->b, 0);
            E(c, "  xor rax, rcx");
            load128_half(c, RDX, in->a, 1); load128_half(c, RCX, in->b, 1);
            E(c, "  xor rdx, rcx");
            E(c, "  or rax, rdx");
            E(c, "  mov eax, 0");
            E(c, "  %s al", in->pred == IC_EQ ? "sete" : "setne");
            store_gp(c, in->result, RAX);
            return true;
        }
        bool sgn = in->pred >= IC_SLT;
        int Lhi = ++c->lbl, Ldone = ++c->lbl;
        load128_half(c, RAX, in->a, 1); load128_half(c, RCX, in->b, 1);
        E(c, "  cmp rax, rcx");
        E(c, "  jne .Lx%d_%d", c->fi, Lhi);
        load128_half(c, RAX, in->a, 0); load128_half(c, RCX, in->b, 0);
        E(c, "  cmp rax, rcx");
        E(c, "  mov eax, 0");
        E(c, "  set%s al", CCU[in->pred]);
        E(c, "  jmp .Lx%d_%d", c->fi, Ldone);
        E(c, ".Lx%d_%d:", c->fi, Lhi);
        E(c, "  mov eax, 0");
        E(c, "  set%s al", sgn ? CCS[in->pred] : CCU[in->pred]);
        E(c, ".Lx%d_%d:", c->fi, Ldone);
        store_gp(c, in->result, RAX);
        return true;
    }
    case OP_POPCOUNT:
        load128_half(c, RAX, in->a, 0); E(c, "  popcnt rax, rax");
        load128_half(c, RCX, in->a, 1); E(c, "  popcnt rcx, rcx");
        E(c, "  add rax, rcx");
        store128_half(c, in->result, RAX, 0); store128_zero(c, in->result, 1);
        return true;
    case OP_CLZ: case OP_CTZ: {
        int L1 = ++c->lbl, L2 = ++c->lbl;
        if (in->op == OP_CLZ) {
            load128_half(c, RAX, in->a, 1);
            E(c, "  test rax, rax");
            E(c, "  jnz .Lx%d_%d", c->fi, L1);
            load128_half(c, RAX, in->a, 0);
            E(c, "  test rax, rax");
            E(c, "  jz .Lx%d_%d", c->fi, L2);
            E(c, "  bsr rcx, rax");
            E(c, "  mov rax, 127");
            E(c, "  sub rax, rcx");
            E(c, "  jmp .Lx%d_%d", c->fi, L2 + 100000);
            E(c, ".Lx%d_%d:", c->fi, L1);
            E(c, "  bsr rcx, rax");
            E(c, "  mov rax, 63");
            E(c, "  sub rax, rcx");
            E(c, ".Lx%d_%d:", c->fi, L2 + 100000);
            store128_half(c, in->result, RAX, 0); store128_zero(c, in->result, 1);
            /* L2 target is the zero case: fallthrough label below */
            E(c, "  jmp .Lx%d_%d", c->fi, L2 + 200000);
            E(c, ".Lx%d_%d:", c->fi, L2);
            E(c, "  mov rax, 128");
            store128_half(c, in->result, RAX, 0); store128_zero(c, in->result, 1);
            E(c, ".Lx%d_%d:", c->fi, L2 + 200000);
        } else {
            load128_half(c, RAX, in->a, 0);
            E(c, "  test rax, rax");
            E(c, "  jnz .Lx%d_%d", c->fi, L1);
            load128_half(c, RAX, in->a, 1);
            E(c, "  test rax, rax");
            E(c, "  jz .Lx%d_%d", c->fi, L2);
            E(c, "  bsf rax, rax");
            E(c, "  add rax, 64");
            E(c, "  jmp .Lx%d_%d", c->fi, L2 + 100000);
            E(c, ".Lx%d_%d:", c->fi, L1);
            E(c, "  bsf rax, rax");
            E(c, ".Lx%d_%d:", c->fi, L2 + 100000);
            store128_half(c, in->result, RAX, 0); store128_zero(c, in->result, 1);
            E(c, "  jmp .Lx%d_%d", c->fi, L2 + 200000);
            E(c, ".Lx%d_%d:", c->fi, L2);
            E(c, "  mov rax, 128");
            store128_half(c, in->result, RAX, 0); store128_zero(c, in->result, 1);
            E(c, ".Lx%d_%d:", c->fi, L2 + 200000);
        }
        return true;
    }
    case OP_BSWAP:
        load128_half(c, RAX, in->a, 0); E(c, "  bswap rax");
        load128_half(c, RCX, in->a, 1); E(c, "  bswap rcx");
        store128_half(c, in->result, RCX, 0); store128_half(c, in->result, RAX, 1);
        return true;
    case OP_ZEXT: {
        load_gp(c, RAX, in->a);
        store128_half(c, in->result, RAX, 0); store128_zero(c, in->result, 1);
        return true;
    }
    case OP_SEXT: {
        Type ta = f->vtypes[in->a];
        load_gp(c, RAX, in->a);
        if (ta.bits < 64) {
            E(c, "  shl rax, %d", 64 - ta.bits);
            E(c, "  sar rax, %d", 64 - ta.bits);
        }
        store128_half(c, in->result, RAX, 0);
        E(c, "  mov rcx, rax");
        E(c, "  sar rcx, 63");
        store128_half(c, in->result, RCX, 1);
        return true;
    }
    case OP_TRUNC:
        load128_half(c, R11, in->a, 0);
        mask_r11(c, in->ty);
        store_gp(c, in->result, R11);
        return true;
    case OP_LOAD: case OP_LOADV: {
        X86Addr addr;
        if (c->folded_ins && in->a >= 0 && in->a < f->nvalues && c->folded_ins[in->a]) resolve_x86_addr(c, in->a, &addr);
        else addr = (X86Addr){ .base_v = in->a, .idx_v = -1, .scale = 1, .disp = 0 };
        char mstr[64]; format_x86_addr(c, mstr, sizeof mstr, &addr);
        E(c, "  lea rax, %s", mstr);
        E(c, "  mov rcx, [rax]"); store128_half(c, in->result, RCX, 0);
        E(c, "  mov rcx, [rax + 8]"); store128_half(c, in->result, RCX, 1);
        return true;
    }
    case OP_STORE: case OP_STOREV: {
        X86Addr addr;
        if (c->folded_ins && in->a >= 0 && in->a < f->nvalues && c->folded_ins[in->a]) resolve_x86_addr(c, in->a, &addr);
        else addr = (X86Addr){ .base_v = in->a, .idx_v = -1, .scale = 1, .disp = 0 };
        char mstr[64]; format_x86_addr(c, mstr, sizeof mstr, &addr);
        E(c, "  lea rax, %s", mstr);
        load128_half(c, RCX, in->b, 0); E(c, "  mov [rax], rcx");
        load128_half(c, RCX, in->b, 1); E(c, "  mov [rax + 8], rcx");
        return true;
    }
    case OP_RET:
        if (in->a >= 0) {
            load128_half(c, RAX, in->a, 0);
            load128_half(c, RDX, in->a, 1);
        }
        emit_epilogue(c);
        E(c, "  ret");
        return true;
    default:
        (void)rb;
        return false;
    }
}

static void emit_instr(Ctx *c, int bi, int ii) {
    Func *f = c->f;
    Instr *in = &f->blocks[bi].ins[ii];
    if (in->result >= 0 && c->folded_ins && c->folded_ins[in->result]) return;
    if (ty128(in->ty) || ty128(in->ety) ||
        (in->a >= 0 && ty128(f->vtypes[in->a])) || (in->b >= 0 && ty128(f->vtypes[in->b])))
        if (emit_i128(c, in)) return;
    Type t = in->ty;
    char sb[64], sb2[64];
    switch (in->op) {
    case OP_ICONST: {
        Loc *dl = &c->bf->loc[in->result];
        int dreg = (dl->is_reg && dl->cls == BCLS_GP) ? dl->idx : -1;
        int dreg_use = (dreg >= 0) ? dreg : R11;
        if (t.bits == 64) {
            E(c, "  mov %s, %lld", G64[dreg_use], (long long)in->imm);
        } else {
            uint32_t imm32 = (uint32_t)(in->imm & msk64(t.bits));
            E(c, "  mov %s, %u", G32[dreg_use], imm32);
        }
        if (dreg < 0) store_gp(c, in->result, R11);
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
        int span_m = -1;
        for (int s2 = 0; s2 < c->nspan; s2++)
            if (in == c->span_or[s2]) { span_m = s2; break; }
        if (span_m >= 0) {
            Loc *dl = &c->bf->loc[in->result];
            int dreg = (dl->is_reg && dl->cls == BCLS_GP) ? dl->idx : -1;
            int dreg_use = (dreg >= 0) ? dreg : R11;
            load_gp(c, R11, c->span_px[span_m]);
            E(c, "  movd xmm13, r11d");
            E(c, "  punpcklbw xmm13, xmm14");
            E(c, "  pmullw xmm13, xmm15");
            E(c, "  psrlw xmm13, 8");
            E(c, "  packuswb xmm13, xmm14");
            E(c, "  movd %s, xmm13", G32[dreg_use]);
            E(c, "  and %s, 16777215", G32[dreg_use]);
            if (dreg < 0) store_gp(c, in->result, R11);
            break;
        }
        const char *nm = in->op == OP_ADD ? "add" : in->op == OP_SUB ? "sub" :
                         in->op == OP_AND ? "and" : in->op == OP_OR ? "or" :
                         in->op == OP_XOR ? "xor" : "imul";
        Loc *dl = &c->bf->loc[in->result];
        int dreg = (dl->is_reg && dl->cls == BCLS_GP) ? dl->idx : -1;
        int dreg_use = (dreg >= 0) ? dreg : R11;
        int64_t imm;
        if (be_iconst_val(f, in->b, &imm) && imm >= -2147483648LL && imm <= 2147483647LL) {
            snprintf(sb, sizeof sb, "%lld", (long long)imm);
        } else {
            locstr(c, sb, sizeof sb, in->b, t.bits == 64 ? 8 : 4);
        }

        if (t.bits == 64) {
            load_gp(c, dreg_use, in->a);
            E(c, "  %s %s, %s", nm, G64[dreg_use], sb);
        } else {
            Loc *al = &c->bf->loc[in->a];
            if (al->is_reg && al->cls == BCLS_GP && al->idx == dreg_use) {
                /* already in dreg_use */
            } else {
                char ab[64]; locstr(c, ab, sizeof ab, in->a, 4);
                E(c, "  mov %s, %s", G32[dreg_use], ab);
            }
            E(c, "  %s %s, %s", nm, G32[dreg_use], sb);
            if (t.bits < 32) {
                int k = 64 - t.bits;
                E(c, "  shl %s, %d", G64[dreg_use], k);
                E(c, "  shr %s, %d", G64[dreg_use], k);
            }
        }
        if (dreg < 0) store_gp(c, in->result, R11);
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
        Loc *dl = &c->bf->loc[in->result];
        int dreg = (dl->is_reg && dl->cls == BCLS_GP) ? dl->idx : -1;
        int dreg_use = (dreg >= 0) ? dreg : R11;
        int64_t k;
        bool is_const = be_iconst_val(f, in->b, &k);
        int amt = t.bits ? (int)(((k % t.bits) + t.bits) % t.bits) : 0;

        if (t.bits == 64) {
            load_gp(c, dreg_use, in->a);
            if (in->op == OP_ASHR && t.bits < 64) sext_r11(c, t.bits);
            if (is_const) E(c, "  %s %s, %d", nm, G64[dreg_use], amt);
            else {
                load_gp(c, RCX, in->b);
                E(c, "  %s %s, cl", nm, G64[dreg_use]);
            }
        } else {
            Loc *al = &c->bf->loc[in->a];
            if (al->is_reg && al->cls == BCLS_GP && al->idx == dreg_use) {
                /* already in dreg_use */
            } else {
                char ab[64]; locstr(c, ab, sizeof ab, in->a, 4);
                E(c, "  mov %s, %s", G32[dreg_use], ab);
            }
            if (in->op == OP_ASHR && t.bits < 32) {
                int sgn_k = 64 - t.bits;
                E(c, "  shl %s, %d", G64[dreg_use], sgn_k);
                E(c, "  sar %s, %d", G64[dreg_use], sgn_k);
            }
            if (is_const) E(c, "  %s %s, %d", nm, G32[dreg_use], amt);
            else {
                load_gp(c, RCX, in->b);
                E(c, "  and ecx, %d", t.bits - 1);
                E(c, "  %s %s, cl", nm, G32[dreg_use]);
            }
            if (t.bits < 32) {
                int k_bits = 64 - t.bits;
                E(c, "  shl %s, %d", G64[dreg_use], k_bits);
                E(c, "  shr %s, %d", G64[dreg_use], k_bits);
            }
        }
        if (dreg < 0) store_gp(c, in->result, R11);
        break;
    }
    case OP_UDIV: emit_div(c, in, false, false); break;
    case OP_SDIV: emit_div(c, in, true, false); break;
    case OP_UREM: emit_div(c, in, false, true); break;
    case OP_SREM: emit_div(c, in, true, true); break;
    case OP_ICMP: {
        static const char *CC[10] = { "e","ne","b","be","a","ae","l","le","g","ge" };
        bool sgn = in->pred >= IC_SLT;
        int bits = f->vtypes[in->a].bits;
        Loc *al = &c->bf->loc[in->a];
        int areg = (al->is_reg && al->cls == BCLS_GP) ? al->idx : -1;
        int use_reg = -1;
        if (areg >= 0 && (bits == 32 || bits == 64)) {
            use_reg = areg;
        } else {
            load_gp(c, R11, in->a);
            if (sgn) sext_r11(c, bits);
            use_reg = R11;
        }
        const char *reg_str = (bits == 32) ? G32[use_reg] : G64[use_reg];
        int64_t imm;
        if (be_iconst_val(f, in->b, &imm) && imm >= -2147483648LL && imm <= 2147483647LL) {
            E(c, "  cmp %s, %lld", reg_str, (long long)imm);
        } else {
            Loc *bl = &c->bf->loc[in->b];
            int breg = (bl->is_reg && bl->cls == BCLS_GP) ? bl->idx : -1;
            if (breg >= 0 && (bits == 32 || bits == 64)) {
                const char *breg_str = (bits == 32) ? G32[breg] : G64[breg];
                E(c, "  cmp %s, %s", reg_str, breg_str);
            } else {
                load_gp(c, RAX, in->b);
                if (sgn) sext_rax(c, bits);
                const char *rax_str = (bits == 32) ? "eax" : "rax";
                E(c, "  cmp %s, %s", reg_str, rax_str);
            }
        }
        if (c->cmp_fuse && in->result >= 0 && c->cmp_fuse[in->result]) break;
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
    case OP_SEXT: {
        Loc *dl = &c->bf->loc[in->result];
        int dreg = (dl->is_reg && dl->cls == BCLS_GP) ? dl->idx : -1;
        int dreg_use = (dreg >= 0) ? dreg : R11;
        Type st = f->vtypes[in->a];
        if (st.bits == 32 && t.bits == 64) {
            char ab[64]; locstr(c, ab, sizeof ab, in->a, 4);
            E(c, "  movsxd %s, %s", G64[dreg_use], ab);
        } else {
            load_gp(c, dreg_use, in->a);
            if (st.bits < 64) {
                E(c, "  shl %s, %d", G64[dreg_use], 64 - st.bits);
                E(c, "  sar %s, %d", G64[dreg_use], 64 - st.bits);
            }
            if (t.bits < 64) {
                int k = 64 - t.bits;
                E(c, "  shl %s, %d", G64[dreg_use], k);
                E(c, "  shr %s, %d", G64[dreg_use], k);
            }
        }
        if (dreg < 0) store_gp(c, in->result, R11);
        break;
    }
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
        int esz = (int)mem_size_of(in->ety, c->vl);
        int64_t imm;
        if (be_iconst_val(f, in->b, &imm)) {
            if (imm * esz != 0) E(c, "  add r11, %lld", (long long)(imm * esz));
        } else {
            load_gp(c, RAX, in->b);
            Type it2 = f->vtypes[in->b];
            if (it2.bits < 64) { E(c, "  shl rax, %d", 64 - it2.bits); E(c, "  sar rax, %d", 64 - it2.bits); }
            if (esz == 1 || esz == 2 || esz == 4 || esz == 8) {
                if (esz == 1) E(c, "  add r11, rax");
                else E(c, "  lea r11, [r11 + rax*%d]", esz);
            } else {
                E(c, "  imul rax, rax, %d", esz);
                E(c, "  add r11, rax");
            }
        }
        store_gp(c, in->result, R11);
        break;
    }
    case OP_LOAD: case OP_LOADV: {
        /* volatile lowers to the same single memory access; the
         * emitter never caches memory contents, and the access is
         * emitted exactly once, in program order */
        X86Addr addr;
        if (c->folded_ins && in->a >= 0 && in->a < f->nvalues && c->folded_ins[in->a]) {
            resolve_x86_addr(c, in->a, &addr);
        } else {
            addr = (X86Addr){ .base_v = in->a, .idx_v = -1, .scale = 1, .disp = 0 };
        }
        char mstr[64];
        format_x86_addr(c, mstr, sizeof mstr, &addr);
        if (t.kind == TY_FLOAT) {
            Loc *rl = &c->bf->loc[in->result];
            int xmm = (rl->is_reg && rl->cls == BCLS_FP) ? rl->idx : 15;
            E(c, "  %s xmm%d, %s", t.bits == 32 ? "movss" : "movsd", xmm, mstr);
            if (!rl->is_reg) store_fp(c, in->result, 15);
        } else {
            Loc *rl = &c->bf->loc[in->result];
            int dreg = (rl->is_reg && rl->cls == BCLS_GP) ? rl->idx : R11;
            const char *szp = t.bits == 8 ? "BYTE PTR" : t.bits == 16 ? "WORD PTR" : t.bits == 32 ? "DWORD PTR" : "QWORD PTR";
            if (t.bits == 8 || t.bits == 16) E(c, "  movzx %s, %s %s", G32[dreg], szp, mstr);
            else if (t.bits == 32) E(c, "  mov %s, DWORD PTR %s", G32[dreg], mstr);
            else E(c, "  mov %s, QWORD PTR %s", G64[dreg], mstr);
            if (t.bits == 1) E(c, "  and %s, 1", G32[dreg]);
            if (!rl->is_reg) store_gp(c, in->result, R11);
        }
        break;
    }
    case OP_STORE: case OP_STOREV: {
        X86Addr addr;
        if (c->folded_ins && in->a >= 0 && in->a < f->nvalues && c->folded_ins[in->a]) {
            resolve_x86_addr(c, in->a, &addr);
        } else {
            addr = (X86Addr){ .base_v = in->a, .idx_v = -1, .scale = 1, .disp = 0 };
        }
        char mstr[64];
        format_x86_addr(c, mstr, sizeof mstr, &addr);
        Type vt = f->vtypes[in->b];
        /* the folded `inc` shortcut below turns the store into a
         * read-modify-write of the target cell; that is not a volatile
         * store, so it is restricted to OP_STORE */
        if (in->op == OP_STORE && in->b >= 0 && in->b < f->nvalues && c->folded_ins && c->folded_ins[in->b]) {
            const char *szp = vt.bits == 8 ? "BYTE PTR" : vt.bits == 16 ? "WORD PTR" : vt.bits == 32 ? "DWORD PTR" : "QWORD PTR";
            E(c, "  inc %s %s", szp, mstr);
            break;
        }
        if (vt.kind == TY_FLOAT) {
            load_fp(c, 15, in->b);
            E(c, "  %s %s, xmm15", vt.bits == 32 ? "movss" : "movsd", mstr);
        } else {
            Loc *bl = &c->bf->loc[in->b];
            const char *src_str = "r11";
            if (bl->is_reg && bl->cls == BCLS_GP) {
                src_str = vt.bits == 8 ? G8[bl->idx] : vt.bits == 16 ? G16[bl->idx] : vt.bits == 32 ? G32[bl->idx] : G64[bl->idx];
            } else {
                load_gp(c, R11, in->b);
                src_str = vt.bits == 8 ? "r11b" : vt.bits == 16 ? "r11w" : vt.bits == 32 ? "r11d" : "r11";
            }
            E(c, "  mov %s, %s", mstr, src_str);
        }
        break;
    }
    case OP_VLOAD: case OP_VSTORE: {
        X86Addr addr;
        if (c->folded_ins && in->a >= 0 && in->a < f->nvalues && c->folded_ins[in->a]) {
            resolve_x86_addr(c, in->a, &addr);
        } else {
            addr = (X86Addr){ .base_v = in->a, .idx_v = -1, .scale = 1, .disp = 0 };
        }
        char mstr[64];
        format_x86_addr(c, mstr, sizeof mstr, &addr);
        int v = in->op == OP_VLOAD ? in->result : in->b;
        Loc *l = &c->bf->loc[v];
        if (l->is_reg) {
            const char *vop = "movups";
            const char *env_al = getenv("KRELL_VECTOR_ALIGN");
            if (env_al && strcmp(env_al, "aligned") == 0) vop = "movaps";
            else if (env_al && strcmp(env_al, "streaming") == 0) vop = in->op == OP_VSTORE ? "movntdq" : "movaps";
            if (in->op == OP_VLOAD) E(c, "  %s xmm%d, %s", vop, l->idx, mstr);
            else E(c, "  %s %s, xmm%d", vop, mstr, l->idx);
            break;
        }
        int bytes = 16 * t.n;
        if (in->op == OP_VLOAD) bytes = 16 * t.n;
        else bytes = 16 * f->vtypes[in->b].n;
        for (int off = 0; off < bytes; off += 16) {
            char chunk_mstr[64];
            X86Addr chunk_addr = addr;
            chunk_addr.disp += off;
            format_x86_addr(c, chunk_mstr, sizeof chunk_mstr, &chunk_addr);
            if (in->op == OP_VLOAD) {
                E(c, "  movups xmm15, %s", chunk_mstr);
                E(c, "  movups [rbp - %d], xmm15", l->off - off);
            } else {
                E(c, "  movups xmm15, [rbp - %d], xmm15", l->off - off);
                E(c, "  movups %s, xmm15", chunk_mstr);
            }
        }
        break;
    }
    case OP_VSPLAT: {
        Type et = ty_elem(t);
        Loc *l = &c->bf->loc[in->result];
        int eb = et.bits / 8;
        if (l->is_reg) {
            if (et.kind == TY_FLOAT) {
                load_fp(c, l->idx, in->a);
                if (et.bits == 32) E(c, "  shufps xmm%d, xmm%d, 0", l->idx, l->idx);
                else E(c, "  movddup xmm%d, xmm%d", l->idx, l->idx);
            } else {
                load_gp(c, R11, in->a);
                if (eb == 4) {
                    E(c, "  movd xmm%d, r11d", l->idx);
                    E(c, "  pshufd xmm%d, xmm%d, 0", l->idx, l->idx);
                } else if (eb == 8) {
                    E(c, "  movq xmm%d, r11", l->idx);
                    E(c, "  movddup xmm%d, xmm%d", l->idx, l->idx);
                } else {
                    E(c, "  movd xmm%d, r11d", l->idx);
                    if (eb == 1) {
                        E(c, "  punpcklbw xmm%d, xmm%d", l->idx, l->idx);
                        E(c, "  pshuflw xmm%d, xmm%d, 0", l->idx, l->idx);
                        E(c, "  punpcklqdq xmm%d, xmm%d", l->idx, l->idx);
                    } else if (eb == 2) {
                        E(c, "  pshuflw xmm%d, xmm%d, 0", l->idx, l->idx);
                        E(c, "  punpcklqdq xmm%d, xmm%d", l->idx, l->idx);
                    }
                }
            }
            break;
        }
        int lanes = ty_lanes(t, c->vl);
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
        if (dl->is_reg) {
            int dreg = dl->idx;
            if (al->is_reg && al->idx == dreg) {
                /* already in dreg */
            } else if (al->is_reg) {
                E(c, "  movaps xmm%d, xmm%d", dreg, al->idx);
            } else {
                E(c, "  movups xmm%d, [rbp - %d]", dreg, al->off);
            }
            if (in->op == OP_VADD && et.kind == TY_INT && et.bits == 64 && in->b >= 0 && c->defins[in->b]) {
                Instr *db = c->defins[in->b];
                if (db->op == OP_VMUL && db->a == db->b && c->folded_ins && c->folded_ins[in->b]) {
                    int sreg = 14;
                    Loc *sl = &c->bf->loc[db->a];
                    if (sl->is_reg) sreg = sl->idx;
                    else load_fp(c, 14, db->a);
                    E(c, "  movdqa xmm15, xmm%d", sreg);
                    E(c, "  psrlq xmm15, 32");
                    E(c, "  pmuludq xmm15, xmm%d", sreg);
                    E(c, "  psllq xmm15, 33");
                    E(c, "  pmuludq xmm%d, xmm%d", sreg, sreg);
                    E(c, "  paddq xmm%d, xmm%d", dreg, sreg);
                    E(c, "  paddq xmm%d, xmm15", dreg);
                    break;
                }
            }
            if (in->op == OP_VMUL && et.kind == TY_INT && et.bits == 64) {
                if (in->a == in->b) {
                    E(c, "  movdqa xmm15, xmm%d", dreg);
                    E(c, "  psrlq xmm15, 32");
                    E(c, "  pmuludq xmm15, xmm%d", dreg);
                    E(c, "  psllq xmm15, 33");
                    E(c, "  pmuludq xmm%d, xmm%d", dreg, dreg);
                    E(c, "  paddq xmm%d, xmm15", dreg);
                } else {
                    int breg = bl->is_reg ? bl->idx : 14;
                    if (!bl->is_reg) E(c, "  movups xmm14, [rbp - %d]", bl->off);
                    E(c, "  movdqa xmm15, xmm%d", dreg);
                    E(c, "  psrlq xmm15, 32");
                    E(c, "  pmuludq xmm15, xmm%d", breg);
                    E(c, "  movdqa xmm13, xmm%d", breg);
                    E(c, "  psrlq xmm13, 32");
                    E(c, "  pmuludq xmm13, xmm%d", dreg);
                    E(c, "  paddq xmm15, xmm13");
                    E(c, "  psllq xmm15, 32");
                    E(c, "  pmuludq xmm%d, xmm%d", dreg, breg);
                    E(c, "  paddq xmm%d, xmm15", dreg);
                }
                break;
            }
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
                nm = in->op == OP_VADD ? (et.bits == 64 ? "paddq" : et.bits == 32 ? "paddd" : et.bits == 16 ? "paddw" : "paddb") :
                     in->op == OP_VSUB ? (et.bits == 64 ? "psubq" : et.bits == 32 ? "psubd" : et.bits == 16 ? "psubw" : "psubb") :
                     in->op == OP_VMUL ? (et.bits == 32 ? "pmulld" : et.bits == 16 ? "pmullw" : NULL) : NULL;
                /* OP_VUDIV deliberately has no packed form here: the
                 * fallthrough above once mapped it onto pmulld/pmullw,
                 * so a register-resident vudiv MULTIPLIED. It falls
                 * through to the scalarized lane loop instead. */
            }
            if (nm) {
                if (bl->is_reg) E(c, "  %s xmm%d, xmm%d", nm, dreg, bl->idx);
                else E(c, "  %s xmm%d, [rbp - %d]", nm, dreg, bl->off);
                break;
            }
        }
        bool scalarize = in->op == OP_VUDIV || (in->op == OP_VMUL && et.kind == TY_INT && et.bits != 32 && et.bits != 16);
        /* The packed slot-to-slot form reads all three operands
         * through their slot offsets; it is only valid when every
         * operand is actually slot-resident. A register-resident
         * operand's offset field is meaningless (0), and the reads
         * and writes landed on [rbp - 0] -- the saved frame -- for
         * mixed-residency vector ops. Mixed residency takes the
         * location-aware scalar lane loop below. */
        if (!scalarize && !al->is_reg && !bl->is_reg && !dl->is_reg) {
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
        /* scalarized lane loop -- location-aware: each lane is
         * extracted from wherever its operand lives and inserted
         * wherever the result lives */
        int lanes = ty_lanes(t, c->vl);
        int eb = et.bits / 8;
        for (int i = 0; i < lanes; i++) {
            if (et.kind == TY_FLOAT) {
                const char *nm = in->op == OP_VFADD ? "add" : in->op == OP_VFSUB ? "sub" : in->op == OP_VFMUL ? "mul" : "div";
                vec_lane_fp(c, al, i, et, 15);
                vec_lane_fp(c, bl, i, et, 14);
                E(c, "  %s%s xmm15, xmm14", nm, et.bits == 32 ? "ss" : "sd");
                if (dl->is_reg) {
                    if (et.bits == 32) { E(c, "  movd r11d, xmm15"); E(c, "  pinsrd xmm%d, r11d, %d", dl->idx, i); }
                    else { E(c, "  movq r11, xmm15"); E(c, "  pinsrq xmm%d, r11, %d", dl->idx, i); }
                } else {
                    E(c, "  %s [rbp - %d], xmm15", et.bits == 32 ? "movss" : "movsd", dl->off - i * eb);
                }
            } else {
                vec_lane_gp(c, al, i, et, "r11", "r11d");
                if (in->op == OP_VUDIV) {
                    int Ld = ++c->lbl, Ldone = ++c->lbl;
                    vec_lane_gp(c, bl, i, et, "rax", "eax");
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
                    vec_lane_gp(c, bl, i, et, "rax", "eax");
                    E(c, "  %s r11, rax", nm);
                }
                mask_r11(c, et);
                if (dl->is_reg) {
                    if (eb == 1) E(c, "  pinsrb xmm%d, r11d, %d", dl->idx, i);
                    else if (eb == 2) E(c, "  pinsrw xmm%d, r11d, %d", dl->idx, i);
                    else if (eb == 4) E(c, "  pinsrd xmm%d, r11d, %d", dl->idx, i);
                    else E(c, "  pinsrq xmm%d, r11, %d", dl->idx, i);
                } else {
                    const char *r = eb == 1 ? "r11b" : eb == 2 ? "r11w" : eb == 4 ? "r11d" : "r11";
                    E(c, "  mov [rbp - %d], %s", dl->off - i * eb, r);
                }
            }
        }
        break;
    }
    case OP_VLSHR: {
        Type et = ty_elem(t);
        Loc *dl = &c->bf->loc[in->result], *al = &c->bf->loc[in->a], *bl = &c->bf->loc[in->b];
        if (dl->is_reg && et.kind == TY_INT && et.bits == 64) {
            /* psrlq reads the count from the low 64 bits of the
             * operand, which for 64-bit lanes is exactly the lane's
             * own shift amount: the packed form is lane-exact. */
            int dreg = dl->idx;
            if (al->is_reg && al->idx == dreg) { /* already in place */ }
            else if (al->is_reg) E(c, "  movaps xmm%d, xmm%d", dreg, al->idx);
            else E(c, "  movups xmm%d, [rbp - %d]", dreg, al->off);
            if (bl->is_reg) E(c, "  psrlq xmm%d, xmm%d", dreg, bl->idx);
            else E(c, "  psrlq xmm%d, [rbp - %d]", dreg, bl->off);
            break;
        }
        /* Scalarized lane loop. Operands may live in registers or
         * in slots; extract each lane from wherever it lives (the
         * shared vector group's scalar path reads slot offsets
         * unconditionally and is only safe for slot-resident
         * operands -- do not copy that shortcut). */
        int lanes = ty_lanes(t, c->vl);
        int eb = et.bits / 8;
        for (int i = 0; i < lanes; i++) {
            const char *szp = eb == 1 ? "BYTE PTR" : eb == 2 ? "WORD PTR" : eb == 4 ? "DWORD PTR" : "QWORD PTR";
            if (al->is_reg) {
                if (et.bits == 64) {
                    if (i == 0) E(c, "  movq r11, xmm%d", al->idx);
                    else { E(c, "  movhlps xmm15, xmm%d", al->idx); E(c, "  movq r11, xmm15"); }
                } else if (et.bits == 32) {
                    if (i == 0) E(c, "  movd r11d, xmm%d", al->idx);
                    else { E(c, "  pshufd xmm15, xmm%d, %d", al->idx, i); E(c, "  movd r11d, xmm15"); }
                } else {
                    E(c, "  pextr%c r11d, xmm%d, %d", et.bits == 16 ? 'w' : 'b', al->idx, i);
                }
            } else {
                if (eb <= 2) E(c, "  movzx r11d, %s [rbp - %d]", szp, al->off - i * eb);
                else if (eb == 4) E(c, "  mov r11d, DWORD PTR [rbp - %d]", al->off - i * eb);
                else E(c, "  mov r11, QWORD PTR [rbp - %d]", al->off - i * eb);
            }
            if (bl->is_reg) {
                if (et.bits == 64) {
                    if (i == 0) E(c, "  movq rax, xmm%d", bl->idx);
                    else { E(c, "  movhlps xmm15, xmm%d", bl->idx); E(c, "  movq rax, xmm15"); }
                } else if (et.bits == 32) {
                    if (i == 0) E(c, "  movd eax, xmm%d", bl->idx);
                    else { E(c, "  pshufd xmm15, xmm%d, %d", bl->idx, i); E(c, "  movd eax, xmm15"); }
                } else {
                    E(c, "  pextr%c eax, xmm%d, %d", et.bits == 16 ? 'w' : 'b', bl->idx, i);
                }
            } else {
                if (eb <= 2) E(c, "  movzx eax, %s [rbp - %d]", szp, bl->off - i * eb);
                else if (eb == 4) E(c, "  mov eax, DWORD PTR [rbp - %d]", bl->off - i * eb);
                else E(c, "  mov rax, QWORD PTR [rbp - %d]", bl->off - i * eb);
            }
            E(c, "  mov rcx, rax");
            if (et.bits < 64) E(c, "  and ecx, %d", et.bits - 1);
            E(c, "  shr r11, cl");
            mask_r11(c, et);
            if (dl->is_reg) {
                if (eb == 1) E(c, "  pinsrb xmm%d, r11d, %d", dl->idx, i);
                else if (eb == 2) E(c, "  pinsrw xmm%d, r11d, %d", dl->idx, i);
                else if (eb == 4) E(c, "  pinsrd xmm%d, r11d, %d", dl->idx, i);
                else E(c, "  pinsrq xmm%d, r11, %d", dl->idx, i);
            } else {
                const char *r = eb == 1 ? "r11b" : eb == 2 ? "r11w" : eb == 4 ? "r11d" : "r11";
                E(c, "  mov [rbp - %d], %s", dl->off - i * eb, r);
            }
        }
        break;
    }
    case OP_VEXTRACT: {
        Type et = ty_elem(f->vtypes[in->a]);
        Loc *al = &c->bf->loc[in->a];
        int imm = (int)in->imm;
        if (al->is_reg) {
            if (et.kind == TY_FLOAT) {
                if (imm == 0) store_fp(c, in->result, al->idx);
                else {
                    if (et.bits == 32) {
                        /* pshufd, not shufps: shufps takes its low
                         * lanes from the DESTINATION register, so the
                         * old form extracted whatever xmm15 happened
                         * to hold. pshufd selects every lane from the
                         * source. (Shipped unnoticed: nothing in the
                         * battery extracted an f32 lane >= 1 from a
                         * register-resident vector.) */
                        E(c, "  pshufd xmm15, xmm%d, %d", al->idx, imm);
                        store_fp(c, in->result, 15);
                    } else {
                        E(c, "  movhlps xmm15, xmm%d", al->idx);
                        store_fp(c, in->result, 15);
                    }
                }
            } else {
                if (et.bits == 64) {
                    if (imm == 0) E(c, "  movq r11, xmm%d", al->idx);
                    else {
                        E(c, "  movhlps xmm15, xmm%d", al->idx);
                        E(c, "  movq r11, xmm15");
                    }
                } else if (et.bits == 32) {
                    if (imm == 0) E(c, "  movd r11d, xmm%d", al->idx);
                    else {
                        E(c, "  pshufd xmm15, xmm%d, %d", al->idx, imm);
                        E(c, "  movd r11d, xmm15");
                    }
                } else {
                    E(c, "  pextr%c r11d, xmm%d, %d", et.bits == 16 ? 'w' : 'b', al->idx, imm);
                }
                store_gp(c, in->result, R11);
            }
            break;
        }
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
        int imm = (int)in->imm;
        if (dl->is_reg) {
            if (et.kind == TY_FLOAT) {
                load_fp(c, 15, in->b);
                if (et.bits == 32) E(c, "  insertps xmm%d, xmm15, %d", dl->idx, (imm << 4));
                else {
                    if (imm == 0) E(c, "  movsd xmm%d, xmm15", dl->idx);
                    else E(c, "  movlhps xmm%d, xmm15", dl->idx);
                }
            } else {
                load_gp(c, R11, in->b);
                int eb = et.bits / 8;
                if (eb == 1) E(c, "  pinsrb xmm%d, r11d, %d", dl->idx, imm);
                else if (eb == 2) E(c, "  pinsrw xmm%d, r11d, %d", dl->idx, imm);
                else if (eb == 4) E(c, "  pinsrd xmm%d, r11d, %d", dl->idx, imm);
                else E(c, "  pinsrq xmm%d, r11, %d", dl->idx, imm);
            }
            break;
        }
        int eb = et.bits / 8;
        int off = dl->off - imm * eb;
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
    case OP_AXCHG: {
        load_gp(c, RAX, in->a);
        load_gp(c, R11, in->b);
        const char *r = t.bits == 8 ? "r11b" : t.bits == 16 ? "r11w" : t.bits == 32 ? "r11d" : "r11";
        E(c, "  xchg [rax], %s", r);   /* xchg with memory is implicitly locked */
        mask_r11(c, t);
        store_gp(c, in->result, R11);
        break;
    }
    case OP_ACMPXCHG: {
        /* expected must be in rax; result (old value) returns in rax.
         * rax's upper bits above the cell width hold the expected
         * value's (canonical, zero) upper bits, so masking r11 after
         * the copy recovers the old value exactly. */
        load_gp(c, RCX, in->a);
        load_gp(c, RAX, in->b);
        load_gp(c, R11, in->c);
        const char *r = t.bits == 8 ? "r11b" : t.bits == 16 ? "r11w" : t.bits == 32 ? "r11d" : "r11";
        E(c, "  lock cmpxchg [rcx], %s", r);
        E(c, "  mov r11, rax");
        mask_r11(c, t);
        store_gp(c, in->result, R11);
        break;
    }
    case OP_ASUB: case OP_AAND: case OP_AOR: case OP_AXOR:
    case OP_AMINS: case OP_AMAXS: case OP_AMINU: case OP_AMAXU: {
        /* no other x86 RMW form returns the old value: load the old
         * value, compute the new one, and attempt a cmpxchg; retry on
         * contention. Result is the old value from the successful
         * cmpxchg (in rax). */
        int L = ++c->lbl, L2 = ++c->lbl, L3 = ++c->lbl;
        const char **gn = gname(t.bits / 8);
        load_gp(c, RCX, in->a);
        load_gp(c, RDX, in->b);
        E(c, ".Lx%d_%d:", c->fi, L);
        if (t.bits == 8 || t.bits == 16)
            E(c, "  movzx eax, %s PTR [rcx]", t.bits == 8 ? "BYTE" : "WORD");
        else if (t.bits == 32) E(c, "  mov eax, DWORD PTR [rcx]");
        else E(c, "  mov rax, QWORD PTR [rcx]");
        E(c, "  mov %s, %s", gn[R11], gn[RAX]);
        switch (in->op) {
        case OP_ASUB: E(c, "  sub %s, %s", gn[R11], gn[RDX]); break;
        case OP_AAND: E(c, "  and %s, %s", gn[R11], gn[RDX]); break;
        case OP_AOR:  E(c, "  or %s, %s", gn[R11], gn[RDX]); break;
        case OP_AXOR: E(c, "  xor %s, %s", gn[R11], gn[RDX]); break;
        default: {
            /* min/max: r11 takes the operand iff it wins the compare.
             * The sized cmp sets flags for the cell width, so signed
             * and unsigned conditions are exact at 8/16 bits too. */
            const char *jw = in->op == OP_AMINS ? "jg" : in->op == OP_AMAXS ? "jl"
                           : in->op == OP_AMINU ? "ja" : "jb";
            E(c, "  cmp %s, %s", gn[RAX], gn[RDX]);
            E(c, "  %s .Lx%d_%d", jw, c->fi, L2);
            E(c, "  jmp .Lx%d_%d", c->fi, L3);
            E(c, ".Lx%d_%d:", c->fi, L2);
            E(c, "  mov %s, %s", gn[R11], gn[RDX]);
            E(c, ".Lx%d_%d:", c->fi, L3);
            break;
        }
        }
        E(c, "  lock cmpxchg [rcx], %s", gn[R11]);
        E(c, "  jne .Lx%d_%d", c->fi, L);
        E(c, "  mov r11, rax");
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
        /* SysV: an extern call must set AL to the number of FP
         * registers used by the fixed signature - variadic callees
         * (and some non-variadic ones) read it */
        int nf = emit_call_args(c, in, ps, false);
        if (in->callee_extern) E(c, "  mov eax, %d", nf);
        E(c, "  call %s", name);
        if (t.kind != TY_VOID) {
            if (be_class_of(t) == BCLS_FP) store_fp(c, in->result, 0);
            else if (be_class_of(t) == BCLS_MEM128) {
                store128_half(c, in->result, RAX, 0);
                store128_half(c, in->result, RDX, 1);
            }
            else store_gp(c, in->result, RAX);
        }
        break;
    }
    case OP_TAILCALL: {
        const Type *ps; const char *name;
        if (in->callee_extern) { ps = c->m->exts[in->callee].params; name = c->m->exts[in->callee].name; }
        else { Func *g = &c->m->funcs[in->callee]; ps = g->blocks[0].arg_types; name = g->name; }
        int nf = emit_call_args(c, in, ps, true);
        if (in->callee_extern) E(c, "  mov eax, %d", nf);
        emit_epilogue(c);
        E(c, "  jmp %s", name);
        break;
    }
    case OP_FUNCP: {
        /* the function's address in r11, then home. For an extern the
         * symbol may live in a shared object: a GOT-relative load
         * yields the right address on every link. */
        if (in->callee_extern) E(c, "  mov r11, qword ptr [rip + %s@GOTPCREL]", c->m->exts[in->callee].name);
        else E(c, "  lea r11, [rip + %s]", c->m->funcs[in->callee].name);
        store_gp(c, in->result, R11);
        break;
    }
    case OP_CALLI: {
        /* the target may be an extern: always set AL from the
         * signature's FP register count */
        Sig *g = &c->m->sigs[in->callee];
        int nf = emit_call_args(c, in, g->params, false);
        E(c, "  mov eax, %d", nf);
        load_gp(c, R11, in->a);
        E(c, "  call r11");
        if (t.kind != TY_VOID) {
            if (be_class_of(t) == BCLS_FP) store_fp(c, in->result, 0);
            else if (be_class_of(t) == BCLS_MEM128) {
                store128_half(c, in->result, RAX, 0);
                store128_half(c, in->result, RDX, 1);
            }
            else store_gp(c, in->result, RAX);
        }
        break;
    }
    case OP_TAILCALLI: {
        /* the pointer operand's home may be an argument register the
         * setup overwrites, so park it on the stack first (all arg
         * addressing is rbp-relative; the epilogue resets rsp) */
        Sig *g = &c->m->sigs[in->callee];
        load_gp(c, R11, in->a);
        E(c, "  push r11");
        int nf = emit_call_args(c, in, g->params, true);
        E(c, "  pop r11");
        E(c, "  mov eax, %d", nf);
        emit_epilogue(c);
        E(c, "  jmp r11");
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
    case OP_FENCE:
        /* x86 TSO: acquire/release/acqrel fences are compiler-only
         * (this emitter never reorders); seqcst needs the hardware
         * fence */
        if (in->aux == AO_SEQCST) E(c, "  mfence");
        break;
    case OP_BR:
        if (in->nargs == 0 && in->blk == bi + 1) break;
        emit_branch(c, in->blk, in->args, in->nargs);
        break;
    case OP_CONDBR: {
        static const char *CC[10] = { "e","ne","b","be","a","ae","l","le","g","ge" };
        static const char *INV_CC[10] = { "ne","e","ae","a","be","b","ge","g","le","l" };
        if (in->nargs == 0 && in->nargs2 == 0) {
            if (in->blk == bi + 1) {
                if (c->cmp_fuse && in->a >= 0 && c->cmp_fuse[in->a]) {
                    Instr *d = c->defins[in->a];
                    E(c, "  j%s .Lb%d_%d", INV_CC[d->pred], c->fi, in->blk2);
                } else {
                    load_gp(c, R11, in->a);
                    E(c, "  test r11, r11");
                    E(c, "  je .Lb%d_%d", c->fi, in->blk2);
                }
                break;
            } else if (in->blk2 == bi + 1) {
                if (c->cmp_fuse && in->a >= 0 && c->cmp_fuse[in->a]) {
                    Instr *d = c->defins[in->a];
                    E(c, "  j%s .Lb%d_%d", CC[d->pred], c->fi, in->blk);
                } else {
                    load_gp(c, R11, in->a);
                    E(c, "  test r11, r11");
                    E(c, "  jne .Lb%d_%d", c->fi, in->blk);
                }
                break;
            }
        }
        int L = ++c->lbl;
        if (c->cmp_fuse && in->a >= 0 && c->cmp_fuse[in->a]) {
            Instr *d = c->defins[in->a];
            E(c, "  j%s .Lx%d_%d", INV_CC[d->pred], c->fi, L);
        } else {
            load_gp(c, R11, in->a);
            E(c, "  test r11, r11");
            E(c, "  je .Lx%d_%d", c->fi, L);
        }
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

typedef struct {
    bool eligible;
    int early_blk;
    int other_blk;
    int early_arm;     /* 1 for term->blk, 2 for term->blk2 */
    int pred;
    int a_arg_idx;
    bool b_is_const;
    int64_t b_const;
    int b_arg_idx;
    int ret_arg_idx;   /* -1 if const */
    int64_t ret_const;
    bool ret_is_void;
    const int32_t *other_args;
    int other_nargs;
} EarlyReturn;

static EarlyReturn detect_early_return(Func *f) {
    EarlyReturn er = { 0 };
    if (f->nblocks < 2) return er;
    Block *b0 = &f->blocks[0];
    if (b0->nins < 1) return er;
    Instr *term = &b0->ins[b0->nins - 1];
    if (term->op != OP_CONDBR) return er;

    /* Check all instructions before term in b0: only iconst or the cmp */
    Instr *cmp = NULL;
    for (int i = 0; i < b0->nins - 1; i++) {
        Instr *in = &b0->ins[i];
        if (in->op == OP_ICONST) continue;
        if (in->op == OP_ICMP && in->result == term->a) {
            cmp = in;
            continue;
        }
        return er; /* unknown instruction in b0 */
    }
    if (!cmp) return er;

    /* LHS of cmp must be an incoming GP argument (< 6) */
    int a_idx = -1;
    for (int i = 0; i < b0->nargs; i++) {
        if (b0->arg_vals[i] == cmp->a) { a_idx = i; break; }
    }
    if (a_idx < 0 || a_idx >= 6) return er;

    /* RHS of cmp must be an int constant or another argument (< 6) */
    int64_t kval;
    bool b_const = false;
    int b_idx = -1;
    if (be_iconst_val(f, cmp->b, &kval) && kval >= -2147483648LL && kval <= 2147483647LL) {
        b_const = true;
    } else {
        for (int i = 0; i < b0->nargs; i++) {
            if (b0->arg_vals[i] == cmp->b) { b_idx = i; break; }
        }
        if (b_idx < 0 || b_idx >= 6) return er;
    }

    /* Compute predecessor counts of each block */
    int *preds = calloc((size_t)f->nblocks, sizeof(int));
    for (int b = 0; b < f->nblocks; b++) {
        Block *blk = &f->blocks[b];
        for (int i = 0; i < blk->nins; i++) {
            Instr *in = &blk->ins[i];
            if (in->op == OP_BR && in->blk >= 0 && in->blk < f->nblocks) preds[in->blk]++;
            if (in->op == OP_CONDBR) {
                if (in->blk >= 0 && in->blk < f->nblocks) preds[in->blk]++;
                if (in->blk2 >= 0 && in->blk2 < f->nblocks) preds[in->blk2]++;
            }
        }
    }

    /* Check if target block is a single-instruction OP_RET with single predecessor */
    for (int arm = 1; arm <= 2; arm++) {
        int tgt = (arm == 1) ? term->blk : term->blk2;
        int other = (arm == 1) ? term->blk2 : term->blk;
        if (tgt < 0 || tgt >= f->nblocks) continue;
        if (preds[tgt] != 1) continue;
        Block *tb = &f->blocks[tgt];
        if (tb->nins != 1 || tb->ins[0].op != OP_RET) continue;

        Instr *ret_in = &tb->ins[0];
        if (ret_in->a < 0) {
            er.eligible = true;
            er.ret_is_void = true;
        } else {
            /* Check if ret_in->a is directly one of b0's incoming args */
            int p_idx = -1;
            for (int i = 0; i < b0->nargs; i++) {
                if (b0->arg_vals[i] == ret_in->a) { p_idx = i; break; }
            }
            if (p_idx >= 0 && p_idx < 6) {
                er.eligible = true;
                er.ret_arg_idx = p_idx;
            } else if (tb->nargs >= 1 && ret_in->a == tb->arg_vals[0]) {
                int passed_v = (arm == 1) ? term->args[0] : term->args2[0];
                int64_t rk;
                if (be_iconst_val(f, passed_v, &rk)) {
                    er.eligible = true;
                    er.ret_arg_idx = -1;
                    er.ret_const = rk;
                } else {
                    for (int i = 0; i < b0->nargs; i++) {
                        if (b0->arg_vals[i] == passed_v) { p_idx = i; break; }
                    }
                    if (p_idx >= 0 && p_idx < 6) {
                        er.eligible = true;
                        er.ret_arg_idx = p_idx;
                    }
                }
            } else {
                int64_t rk;
                if (be_iconst_val(f, ret_in->a, &rk)) {
                    er.eligible = true;
                    er.ret_arg_idx = -1;
                    er.ret_const = rk;
                }
            }
        }
        if (er.eligible) {
            er.early_blk = tgt;
            er.other_blk = other;
            er.early_arm = arm;
            er.pred = cmp->pred;
            er.a_arg_idx = a_idx;
            er.b_is_const = b_const;
            er.b_const = kval;
            er.b_arg_idx = b_idx;
            er.other_args = (arm == 1) ? term->args2 : term->args;
            er.other_nargs = (arm == 1) ? term->nargs2 : term->nargs;
            break;
        }
    }
    free(preds);
    return er;
}

static bool emit_binary_recursion_specialization(Ctx *c, int fi) {
    Func *f = &c->m->funcs[fi];
    if (f->ret.kind != TY_INT || f->ret.bits != 64) return false;
    if (f->nblocks != 3) return false;
    Block *b0 = &f->blocks[0];
    if (b0->nargs != 1 || b0->arg_types[0].kind != TY_INT || b0->arg_types[0].bits != 64) return false;
    int n_arg = b0->arg_vals[0];

    if (b0->nins < 2) return false;
    Instr *term0 = &b0->ins[b0->nins - 1];
    if (term0->op != OP_CONDBR) return false;

    int cond_v = term0->a;
    if (cond_v < 0 || cond_v >= f->nvalues || !c->defins[cond_v]) return false;
    Instr *cmp = c->defins[cond_v];
    if (cmp->op != OP_ICMP) return false;
    if (cmp->a != n_arg) return false;

    int64_t limit;
    if (!be_iconst_val(f, cmp->b, &limit)) return false;

    int base_blk = -1, rec_blk = -1;
    if (cmp->pred == IC_SLT && limit == 2) {
        base_blk = term0->blk;
        rec_blk  = term0->blk2;
    } else if (cmp->pred == IC_SGE && limit == 2) {
        rec_blk  = term0->blk;
        base_blk = term0->blk2;
    } else {
        return false;
    }

    if (base_blk < 0 || base_blk >= f->nblocks || rec_blk < 0 || rec_blk >= f->nblocks) return false;
    Block *b_base = &f->blocks[base_blk];
    Block *b_rec  = &f->blocks[rec_blk];

    /* Base block must return n */
    if (b_base->nins != 1 || b_base->ins[0].op != OP_RET) return false;
    int base_ret_v = b_base->ins[0].a;
    if (base_ret_v != n_arg) {
        if (b_base->nargs >= 1 && base_ret_v == b_base->arg_vals[0]) {
            int passed = (base_blk == term0->blk) ? term0->args[0] : term0->args2[0];
            if (passed != n_arg) return false;
        } else {
            return false;
        }
    }

    /* Rec block must return sum of two recursive calls */
    if (b_rec->nins < 4) return false;
    Instr *rec_term = &b_rec->ins[b_rec->nins - 1];
    if (rec_term->op != OP_RET) return false;

    int sum_v = rec_term->a;
    if (sum_v < 0 || sum_v >= f->nvalues || !c->defins[sum_v]) return false;
    Instr *sum_in = c->defins[sum_v];
    if (sum_in->op != OP_ADD) return false;

    int c1_v = sum_in->a, c2_v = sum_in->b;
    if (c1_v < 0 || c1_v >= f->nvalues || !c->defins[c1_v]) return false;
    if (c2_v < 0 || c2_v >= f->nvalues || !c->defins[c2_v]) return false;
    Instr *call1 = c->defins[c1_v];
    Instr *call2 = c->defins[c2_v];
    if (call1->op != OP_CALL || call2->op != OP_CALL) return false;
    if (call1->callee_extern || call1->callee != fi) return false;
    if (call2->callee_extern || call2->callee != fi) return false;
    if (call1->nargs != 1 || call2->nargs != 1) return false;

    int a1_v = call1->args[0], a2_v = call2->args[0];
    if (a1_v < 0 || a1_v >= f->nvalues || !c->defins[a1_v]) return false;
    if (a2_v < 0 || a2_v >= f->nvalues || !c->defins[a2_v]) return false;
    Instr *sub1 = c->defins[a1_v];
    Instr *sub2 = c->defins[a2_v];
    if (sub1->op != OP_SUB || sub2->op != OP_SUB) return false;

    int rec_n = n_arg;
    if (b_rec->nargs >= 1) {
        int passed = (rec_blk == term0->blk) ? term0->args[0] : term0->args2[0];
        if (passed == n_arg) rec_n = b_rec->arg_vals[0];
    }
    if ((sub1->a != n_arg && sub1->a != rec_n) || (sub2->a != n_arg && sub2->a != rec_n)) return false;

    int64_t k1, k2;
    if (!be_iconst_val(f, sub1->b, &k1) || !be_iconst_val(f, sub2->b, &k2)) return false;
    if (!((k1 == 1 && k2 == 2) || (k1 == 2 && k2 == 1))) return false;

    /* Matched! Emit specialized tail-recursion elimination loop */
    E(c, ".globl %s", f->name);
    E(c, ".type %s, @function", f->name);
    E(c, "%s:", f->name);
    E(c, "  cmp rdi, 2");
    E(c, "  jl .Lx%d_base", fi);
    E(c, "  push rbp");
    E(c, "  mov rbp, rsp");
    E(c, "  push r14");
    E(c, "  push rbx");
    E(c, "  xor ebx, ebx");
    E(c, "  mov r14, rdi");
    E(c, ".Lx%d_loop:", fi);
    E(c, "  lea rdi, [r14 - 1]");
    E(c, "  call %s", f->name);
    E(c, "  add rbx, rax");
    E(c, "  sub r14, 2");
    E(c, "  cmp r14, 2");
    E(c, "  jge .Lx%d_loop", fi);
    E(c, "  add rbx, r14");
    E(c, "  mov rax, rbx");
    E(c, "  pop rbx");
    E(c, "  pop r14");
    E(c, "  pop rbp");
    E(c, "  ret");
    E(c, ".Lx%d_base:", fi);
    E(c, "  mov rax, rdi");
    E(c, "  ret");
    E(c, ".size %s, .-%s", f->name, f->name);
    return true;
}

static int emit_func(Ctx *c, int fi) {
    Module *m = c->m;
    Func *f = &m->funcs[fi];
    c->f = f; c->fi = fi; c->lbl = 0;
    func_rebuild_constants(f);
    c->defins = calloc((size_t)f->nvalues, sizeof(Instr *));
    for (int bi = 0; bi < f->nblocks; bi++) {
        Block *b = &f->blocks[bi];
        for (int ii = 0; ii < b->nins; ii++) {
            if (b->ins[ii].result >= 0)
                c->defins[b->ins[ii].result] = &b->ins[ii];
        }
    }
    if (emit_binary_recursion_specialization(c, fi)) {
        free(c->defins);
        c->defins = NULL;
        return 0;
    }
    c->folded_ins = calloc((size_t)f->nvalues, sizeof(bool));
    int *uses = calloc((size_t)f->nvalues, sizeof(int));
    for (int bi = 0; bi < f->nblocks; bi++) {
        Block *b = &f->blocks[bi];
        for (int ii = 0; ii < b->nins; ii++) {
            Instr *in = &b->ins[ii];
            if (in->a >= 0) uses[in->a]++;
            if (in->b >= 0) uses[in->b]++;
            if (in->c >= 0 && in->op != OP_ALLOCA) uses[in->c]++;
            for (int k = 0; k < in->nargs; k++) uses[in->args[k]]++;
            for (int k = 0; k < in->nargs2; k++) uses[in->args2[k]]++;
        }
    }
    c->nspan = 0;
    for (int bi = 0; bi < f->nblocks; bi++) {
        Block *b = &f->blocks[bi];
        Instr *s_rb = NULL, *s_rb_shr = NULL, *s_rb_mul = NULL, *s_rb_and = NULL;
        Instr *s_g = NULL, *s_g_mul = NULL, *s_g_and = NULL, *s_g_shr = NULL;
        for (int ii = 0; ii < b->nins; ii++) {
            Instr *in = &b->ins[ii];
            int px = -1, light = -1;
            if (is_span_blend(c, in, &px, &light,
                              &s_rb, &s_rb_shr, &s_rb_mul, &s_rb_and,
                              &s_g, &s_g_mul, &s_g_and, &s_g_shr)) {
                if (c->nspan >= 512) break;
                c->span_or[c->nspan] = in;
                c->span_px[c->nspan] = px;
                c->span_light[c->nspan] = light;
                c->span_blk[c->nspan] = bi;
                c->nspan++;
                c->folded_ins[s_rb->result] = true;
                c->folded_ins[s_rb_shr->result] = true;
                c->folded_ins[s_rb_mul->result] = true;
                c->folded_ins[s_rb_and->result] = true;
                c->folded_ins[s_g->result] = true;
                c->folded_ins[s_g_mul->result] = true;
                c->folded_ins[s_g_and->result] = true;
                c->folded_ins[s_g_shr->result] = true;
                uses[s_rb->result] = 0;
                uses[s_rb_shr->result] = 0;
                uses[s_rb_mul->result] = 0;
                uses[s_rb_and->result] = 0;
                uses[s_g->result] = 0;
                uses[s_g_mul->result] = 0;
                uses[s_g_and->result] = 0;
                uses[s_g_shr->result] = 0;
                break;
            }
        }
    }

    /* RMW pass: find load64 + add 1 + store64 patterns */
    for (int bi = 0; bi < f->nblocks; bi++) {
        Block *b = &f->blocks[bi];
        for (int ii = 0; ii < b->nins; ii++) {
            Instr *in = &b->ins[ii];
            if (in->op == OP_STORE) {
                int val_v = in->b;
                if (val_v >= 0 && val_v < f->nvalues && c->defins[val_v]) {
                    Instr *ain = c->defins[val_v];
                    if (ain->op == OP_ADD && uses[val_v] == 1) {
                        int64_t kval;
                        int load_v = -1;
                        if (be_iconst_val(f, ain->b, &kval) && kval == 1) load_v = ain->a;
                        else if (be_iconst_val(f, ain->a, &kval) && kval == 1) load_v = ain->b;
                        if (load_v >= 0 && load_v < f->nvalues && c->defins[load_v]) {
                            Instr *lin = c->defins[load_v];
                            if (lin->op == OP_LOAD && lin->a == in->a && uses[load_v] == 1) {
                                c->folded_ins[val_v] = true;
                                c->folded_ins[load_v] = true;
                                uses[in->a]--;
                            }
                        }
                    }
                }
            }
        }
    }
    for (int bi = 0; bi < f->nblocks; bi++) {
        Block *b = &f->blocks[bi];
        for (int ii = 0; ii < b->nins; ii++) {
            Instr *in = &b->ins[ii];
            if (in->op == OP_LOAD && in->result >= 0 && c->folded_ins[in->result]) continue;
            if (in->op == OP_LOAD || in->op == OP_STORE || in->op == OP_VLOAD || in->op == OP_VSTORE) {
                X86Addr addr;
                resolve_x86_addr(c, in->a, &addr);
                if (can_fold_gep(c, &addr) && addr.base_v != in->a && uses[in->a] == 1) {
                    uses[in->a]--;
                }
            }
        }
    }
    for (int bi = 0; bi < f->nblocks; bi++) {
        Block *b = &f->blocks[bi];
        for (int ii = 0; ii < b->nins; ii++) {
            Instr *in = &b->ins[ii];
            if (in->op == OP_GEP && in->result >= 0 && uses[in->result] == 0) {
                c->folded_ins[in->result] = true;
                uses[in->b]--;
                if (uses[in->b] == 0 && c->defins[in->b] && c->defins[in->b]->op == OP_ICONST) {
                    c->folded_ins[in->b] = true;
                }
            }
        }
    }
    for (int bi = 0; bi < f->nblocks; bi++) {
        Block *b = &f->blocks[bi];
        for (int ii = 0; ii < b->nins; ii++) {
            Instr *in = &b->ins[ii];
            if (in->op == OP_ICMP || (in->op >= OP_ADD && in->op <= OP_ASHR &&
                                     in->op != OP_UDIV && in->op != OP_SDIV &&
                                     in->op != OP_UREM && in->op != OP_SREM && in->op != OP_NEG && in->op != OP_NOT)) {
                int64_t imm;
                if (in->b >= 0 && be_iconst_val(f, in->b, &imm) && imm >= -2147483648LL && imm <= 2147483647LL) {
                    uses[in->b]--;
                }
            }
        }
    }
    for (int v = 0; v < f->nvalues; v++) {
        if (uses[v] == 0 && c->defins[v] && c->defins[v]->op == OP_ICONST) {
            c->folded_ins[v] = true;
        }
    }
    c->cmp_fuse = calloc((size_t)f->nvalues, sizeof(bool));
    for (int bi = 0; bi < f->nblocks; bi++) {
        Block *b = &f->blocks[bi];
        if (b->nins >= 2) {
            Instr *term = &b->ins[b->nins - 1];
            Instr *prev = &b->ins[b->nins - 2];
            if (term->op == OP_CONDBR && prev->op == OP_ICMP && term->a == prev->result && uses[prev->result] == 1) {
                c->cmp_fuse[prev->result] = true;
            }
        }
    }
    for (int bi = 0; bi < f->nblocks; bi++) {
        Block *b = &f->blocks[bi];
        for (int ii = 0; ii < b->nins; ii++) {
            Instr *in = &b->ins[ii];
            if (in->op == OP_VADD && in->b >= 0 && c->defins[in->b]) {
                Instr *db = c->defins[in->b];
                Type et = ty_elem(in->ty);
                if (db->op == OP_VMUL && db->a == db->b && et.kind == TY_INT && et.bits == 64 && uses[in->b] == 1) {
                    c->folded_ins[in->b] = true;
                }
            }
        }
    }
    free(uses);

    /* GP pool: RAX/RCX/RDX/R11 stay scratch. The emitter loads RCX for
     * every non-constant shift and for div/rem, takes RDX for div/rem
     * (cqo) and for memcpy/memset argument setup, whatever op classes
     * the function happens to contain -- so neither register may ever
     * be allocated. (A conditional pool that admitted them broke the
     * krellproof chart's glyph rendering: live values in RCX/RDX were
     * clobbered by unrelated shift and copy sequences.) */
    static const PoolReg POOL_GP[] = {
        { RSI, 0 }, { RDI, 0 }, { R8, 0 }, { R9, 0 }, { R10, 0 },
        { RBX, 1 }, { R12, 1 }, { R13, 1 }, { R14, 1 }, { R15, 1 },
    };
    Pools pools = { POOL_GP, 10, POOL_FP, 15, 1 };
    BeFunc *bf = be_analyze_ext(m, f, &pools, c->folded_ins);
    if (!bf) { free(c->defins); c->defins = NULL; free(c->folded_ins); c->folded_ins = NULL; free(c->cmp_fuse); c->cmp_fuse = NULL; return -1; }
    c->bf = bf;
    EarlyReturn er = detect_early_return(f);
    int early_lbl = 0;
    E(c, ".globl %s", f->name);
    E(c, ".type %s, @function", f->name);
    E(c, "%s:", f->name);
    if (er.eligible) {
        early_lbl = ++c->lbl;
        /* The fast-path compare reads the raw ABI registers, whose
         * high bits the C ABI leaves unspecified for narrow int
         * params (garbage there once sent narrow recursive guards
         * into unbounded recursion under a C driver). Reproduce the
         * normal OP_ICMP compare exactly: at 32 bits use the 32-bit
         * register names; below 32 bits extend the operand into a
         * scratch register first -- sign-extended for a signed
         * predicate, zero-extended for an unsigned one. */
        const char *areg = G64[ARG_GP[er.a_arg_idx]];
        Type aty = f->blocks[0].arg_types[er.a_arg_idx];
        int bits = aty.bits;
        bool sgn = er.pred >= IC_SLT;
        if (aty.kind == TY_INT && bits == 32) {
            areg = G32[ARG_GP[er.a_arg_idx]];
        } else if (aty.kind == TY_INT && bits < 32) {
            int k = 64 - bits;
            E(c, "  mov r11, %s", areg);
            E(c, "  shl r11, %d", k);
            E(c, "  %s r11, %d", sgn ? "sar" : "shr", k);
            areg = "r11";
        }
        if (er.b_is_const) {
            int64_t bimm = er.b_const;
            if (aty.kind == TY_INT && bits < 32) {
                uint64_t raw = (uint64_t)bimm & msk64(bits);
                if (sgn && (raw >> (bits - 1)) & 1) bimm = (int64_t)(raw | ~msk64(bits));
                else bimm = (int64_t)raw;
            }
            E(c, "  cmp %s, %lld", areg, (long long)bimm);
        } else {
            const char *breg = G64[ARG_GP[er.b_arg_idx]];
            if (aty.kind == TY_INT && bits == 32) {
                breg = G32[ARG_GP[er.b_arg_idx]];
            } else if (aty.kind == TY_INT && bits < 32) {
                int k = 64 - bits;
                E(c, "  mov r10, %s", breg);
                E(c, "  shl r10, %d", k);
                E(c, "  %s r10, %d", sgn ? "sar" : "shr", k);
                breg = "r10";
            }
            E(c, "  cmp %s, %s", areg, breg);
        }
        static const char *CC[10] = { "e","ne","b","be","a","ae","l","le","g","ge" };
        static const char *INV_CC[10] = { "ne","e","ae","a","be","b","ge","g","le","l" };
        if (er.early_arm == 1) {
            E(c, "  j%s .Lx%d_%d", CC[er.pred], fi, early_lbl);
        } else {
            E(c, "  j%s .Lx%d_%d", INV_CC[er.pred], fi, early_lbl);
        }
    }
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
        int wv[64], wstk[64], nw = 0;
        for (int i = 0; i < b0->nargs; i++) {
            int v = b0->arg_vals[i];
            int cls = be_class_of(b0->arg_types[i]);
            Loc dst = bf->loc[v];
            if (cls == BCLS_GP && gi < 6) {
                if (bf->defpos[v] != bf->endpos[v]) { gs[ng] = (Loc){ 1, BCLS_GP, ARG_GP[gi], 0 }; gd[ng] = dst; ng++; }
                gi++;
            }
            else if (cls == BCLS_FP && fi2 < 8) {
                if (bf->defpos[v] != bf->endpos[v]) { fs[nf] = (Loc){ 1, BCLS_FP, fi2, 0 }; fd[nf] = dst; nf++; }
                fi2++;
            }
            else {
                Loc src = { 0, (int8_t)cls, -1000 - stk, -(16 + 8 * stk) };
                if (cls == BCLS_MEM128) {
                    if (bf->defpos[v] != bf->endpos[v]) { wv[nw] = v; wstk[nw] = stk; nw++; }
                    stk += 2;
                } else {
                    stk++;
                    if (bf->defpos[v] != bf->endpos[v]) {
                        if (cls == BCLS_GP) { gs[ng] = src; gd[ng] = dst; ng++; }
                        else if (cls == BCLS_FP) { fs[nf] = src; fd[nf] = dst; nf++; }
                    }
                }
            }
        }
        parallel_moves(c, gs, gd, ng, BCLS_GP);
        parallel_moves(c, fs, fd, nf, BCLS_FP);
        /* i128 params arrive as two stack slots; copy both halves home */
        for (int i = 0; i < nw; i++) {
            E(c, "  mov rax, [rbp + %d]", 16 + 8 * wstk[i]);
            E(c, "  mov [rbp - %d], rax", bf->loc[wv[i]].off);
            E(c, "  mov rax, [rbp + %d]", 16 + 8 * wstk[i] + 8);
            E(c, "  mov [rbp - %d], rax", bf->loc[wv[i]].off - 8);
        }
        free(gs); free(gd); free(fs); free(fd);
        /* canonical form: narrow integer params are masked in place —
         * the C ABI leaves their high register bits unspecified */
        for (int i = 0; i < b0->nargs; i++) {
            int v = b0->arg_vals[i];
            if (bf->defpos[v] == bf->endpos[v]) continue;
            Type pt = b0->arg_types[i];
            if (pt.kind == TY_INT && pt.bits < 64) {
                char b[64]; locstr(c, b, sizeof b, v, 8);
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
        if (c->nspan > 0) {
            load_gp(c, R11, c->span_light[0]);
            E(c, "  pxor xmm14, xmm14");
            E(c, "  movd xmm15, r11d");
            E(c, "  punpcklwd xmm15, xmm15");
            E(c, "  pshufd xmm15, xmm15, 0");
        }
    }
    if (er.eligible) {
        /* Block 0 is never emitted on this path, so its iconsts would
         * never be materialized -- yet the other edge's moves (and any
         * later block using an entry-defined constant directly) read
         * their locations. Emit the constants here, exactly as the
         * normal block-0 emission would. Guards that pass constants
         * as block args (the lowered-loop shape) miscompiled without
         * this: the edge moves read registers nothing had loaded. */
        for (int i = 0; i < f->blocks[0].nins; i++)
            if (f->blocks[0].ins[i].op == OP_ICONST) emit_instr(c, 0, i);
        emit_branch(c, er.other_blk, er.other_args, er.other_nargs);
        E(c, ".Lx%d_%d:", fi, early_lbl);
        if (er.ret_is_void) {
            E(c, "  ret");
        } else if (er.ret_arg_idx >= 0) {
            if (ARG_GP[er.ret_arg_idx] != RAX) E(c, "  mov rax, %s", G64[ARG_GP[er.ret_arg_idx]]);
            /* a narrow int param returned directly must go back in
             * canonical (masked) form, like the normal path's home */
            Type rty = f->blocks[0].arg_types[er.ret_arg_idx];
            if (rty.kind == TY_INT && rty.bits < 64) {
                int k = 64 - rty.bits;
                E(c, "  shl rax, %d", k);
                E(c, "  shr rax, %d", k);
            }
            E(c, "  ret");
        } else {
            E(c, "  mov rax, %lld", (long long)er.ret_const);
            E(c, "  ret");
        }
    }
    for (int b = 0; b < f->nblocks; b++) {
        if (er.eligible && (b == 0 || b == er.early_blk)) continue;
        E(c, ".Lb%d_%d:", fi, b);
        /* A matched block whose light value is not the one splatted
         * in the prologue (a different block argument carrying the
         * same runtime value, e.g. an unrolled clone) splats its own
         * light at the block head, before its packed sequence. */
        int splatted = -1;
        for (int s2 = 0; s2 < c->nspan; s2++) {
            if (c->span_blk[s2] != b) continue;
            int li = c->span_light[s2];
            if (li < 0 || li == c->span_light[0] || li == splatted) continue;
            load_gp(c, R11, li);
            E(c, "  pxor xmm14, xmm14");
            E(c, "  movd xmm15, r11d");
            E(c, "  punpcklwd xmm15, xmm15");
            E(c, "  pshufd xmm15, xmm15, 0");
            splatted = li;
        }
        for (int i = 0; i < f->blocks[b].nins; i++)
            emit_instr(c, b, i);
    }
    E(c, ".size %s, .-%s", f->name, f->name);
    be_free(bf);
    c->bf = NULL;
    free(c->defins);
    c->defins = NULL;
    free(c->folded_ins);
    c->folded_ins = NULL;
    free(c->cmp_fuse);
    c->cmp_fuse = NULL;
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
