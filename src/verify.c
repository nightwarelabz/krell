/* Krell-IR — verifier: structure, types, SSA dominance, target gate.
 * Returns NULL on success, else a static diagnostic string. */
#include "krell.h"

static char ERR[256];
static const char *fail(const char *msg) { snprintf(ERR, sizeof ERR, "%s", msg); return ERR; }
static const char *failf(const char *fmt, const char *a, int b) {
    snprintf(ERR, sizeof ERR, fmt, a, b); return ERR;
}

/* operand type expectations for the simple polymorphic ops */
static bool same_ty(Type a, Type b) { return ty_eq(a, b); }

static const char *check_instr(Module *m, Func *f, Block *b, Instr *in, int idx) {
    (void)b;
    int op = in->op;
    #define VT(v) (f->vtypes[(v)])
    #define NEED(cond, msg) do { if (!(cond)) return fail(msg); } while (0)
    switch (op) {
    case OP_ICONST: NEED(ty_is_int(in->ty), "iconst result must be integer"); break;
    case OP_FCONST: NEED(ty_is_float(in->ty), "fconst result must be float"); break;
    case OP_ADD: case OP_SUB: case OP_MUL: case OP_UDIV: case OP_SDIV:
    case OP_UREM: case OP_SREM: case OP_AND: case OP_OR: case OP_XOR:
    case OP_SHL: case OP_LSHR: case OP_ASHR:
        NEED(ty_is_int(in->ty), "int binop result must be integer");
        NEED(same_ty(VT(in->a), in->ty) && same_ty(VT(in->b), in->ty), "int binop operand type mismatch");
        break;
    case OP_NEG: case OP_NOT: case OP_POPCOUNT: case OP_CLZ: case OP_CTZ: case OP_BSWAP:
        NEED(ty_is_int(in->ty) && same_ty(VT(in->a), in->ty), "int unop type mismatch");
        break;
    case OP_ICMP:
        NEED(in->ty.kind == TY_INT && in->ty.bits == 1, "icmp result must be i1");
        NEED(ty_is_int(VT(in->a)) && same_ty(VT(in->a), VT(in->b)), "icmp operand mismatch");
        NEED(in->pred <= IC_SGE, "icmp predicate out of range");
        break;
    case OP_TRUNC: case OP_ZEXT: case OP_SEXT:
        NEED(ty_is_int(in->ty) && ty_is_int(VT(in->a)), "width conversion needs integers");
        if (op == OP_TRUNC) NEED(in->ty.bits < VT(in->a).bits, "trunc must narrow");
        else NEED(in->ty.bits > VT(in->a).bits, "ext must widen");
        break;
    case OP_FADD: case OP_FSUB: case OP_FMUL: case OP_FDIV:
        NEED(ty_is_float(in->ty) && same_ty(VT(in->a), in->ty) && same_ty(VT(in->b), in->ty), "float binop mismatch");
        break;
    case OP_FNEG: case OP_FABS:
        NEED(ty_is_float(in->ty) && same_ty(VT(in->a), in->ty), "float unop mismatch");
        break;
    case OP_FMA:
        NEED(ty_is_float(in->ty) && same_ty(VT(in->a), in->ty) && same_ty(VT(in->b), in->ty) && same_ty(VT(in->c), in->ty), "fma mismatch");
        break;
    case OP_FCMP:
        NEED(in->ty.kind == TY_INT && in->ty.bits == 1, "fcmp result must be i1");
        NEED(ty_is_float(VT(in->a)) && same_ty(VT(in->a), VT(in->b)), "fcmp operand mismatch");
        NEED(in->pred <= FC_UNO, "fcmp predicate out of range");
        break;
    case OP_FTRUNC: NEED(in->ty.bits == 32 && VT(in->a).bits == 64, "ftrunc must be f64->f32"); break;
    case OP_FEXT:   NEED(in->ty.bits == 64 && VT(in->a).bits == 32, "fext must be f32->f64"); break;
    case OP_FPTOSI: case OP_FPTOUI:
        NEED(ty_is_float(VT(in->a)) && ty_is_int(in->ty), "fptoi mismatch"); break;
    case OP_SITOFP: case OP_UITOFP:
        NEED(ty_is_int(VT(in->a)) && ty_is_float(in->ty), "itofp mismatch"); break;
    case OP_BITCAST: {
        Type s = VT(in->a);
        int sb = s.kind == TY_VEC ? 0 : ty_bytes(s), db = in->ty.kind == TY_VEC ? 0 : ty_bytes(in->ty);
        NEED(sb && db && sb == db, "bitcast size mismatch");
        break;
    }
    case OP_FREEZE: NEED(same_ty(VT(in->a), in->ty), "freeze type mismatch"); break;
    case OP_SELECT:
        NEED(VT(in->a).kind == TY_INT && VT(in->a).bits == 1, "select condition must be i1");
        NEED(same_ty(VT(in->b), in->ty) && same_ty(VT(in->c), in->ty), "select arm mismatch");
        break;
    case OP_ALLOCA:
        NEED(in->ty.kind == TY_PTR, "alloca result must be ptr");
        NEED(in->imm >= 0 && in->c >= 1 && in->c <= 4096, "alloca size/align invalid");
        break;
    case OP_LOAD:
        NEED(VT(in->a).kind == TY_PTR, "load address must be ptr");
        break;
    case OP_VLOAD:
        NEED(VT(in->a).kind == TY_PTR && ty_is_vec(in->ty), "vload mismatch");
        break;
    case OP_STORE:
        NEED(VT(in->a).kind == TY_PTR, "store address must be ptr");
        NEED(same_ty(VT(in->b), in->ty), "store value type mismatch");
        break;
    case OP_VSTORE:
        NEED(VT(in->a).kind == TY_PTR && ty_is_vec(VT(in->b)), "vstore mismatch");
        break;
    case OP_GEP:
        NEED(VT(in->a).kind == TY_PTR && ty_is_int(VT(in->b)) && in->ty.kind == TY_PTR, "gep mismatch");
        break;
    case OP_MEMCPY: case OP_MEMSET:
        NEED(VT(in->a).kind == TY_PTR, "mem op dst must be ptr");
        if (op == OP_MEMCPY) NEED(VT(in->b).kind == TY_PTR, "memcpy src must be ptr");
        else NEED(ty_is_int(VT(in->b)), "memset byte must be int");
        NEED(ty_is_int(VT(in->c)), "mem op length must be int");
        break;
    case OP_DATAPTR:
        NEED(in->ty.kind == TY_PTR, "dataptr result must be ptr");
        NEED(in->imm >= 0 && in->imm < m->ndata, "dataptr index out of range");
        break;
    case OP_VSPLAT:
        NEED(ty_is_vec(in->ty) && same_ty(VT(in->a), ty_elem(in->ty)), "vsplat element mismatch");
        break;
    case OP_VADD: case OP_VSUB: case OP_VMUL: case OP_VUDIV: case OP_VAND: case OP_VOR: case OP_VXOR:
        NEED(ty_is_vec(in->ty) && same_ty(VT(in->a), in->ty) && same_ty(VT(in->b), in->ty), "vec binop mismatch");
        NEED(ty_elem(in->ty).kind == TY_INT, "int vec op needs int elements");
        break;
    case OP_VFADD: case OP_VFSUB: case OP_VFMUL: case OP_VFDIV:
        NEED(ty_is_vec(in->ty) && same_ty(VT(in->a), in->ty) && same_ty(VT(in->b), in->ty), "vec binop mismatch");
        NEED(ty_elem(in->ty).kind == TY_FLOAT, "float vec op needs float elements");
        break;
    case OP_VEXTRACT:
        NEED(ty_is_vec(VT(in->a)) && same_ty(in->ty, ty_elem(VT(in->a))), "vextract mismatch");
        NEED(in->imm >= 0, "vextract lane negative");
        break;
    case OP_VINSERT:
        NEED(ty_is_vec(in->ty) && same_ty(VT(in->a), in->ty) && same_ty(VT(in->b), ty_elem(in->ty)), "vinsert mismatch");
        NEED(in->imm >= 0, "vinsert lane negative");
        break;
    case OP_ALOAD:
        NEED(VT(in->a).kind == TY_PTR && ty_is_int(in->ty), "aload mismatch");
        NEED(in->aux <= AO_SEQCST, "atomic ordering out of range");
        break;
    case OP_ASTORE:
        NEED(VT(in->a).kind == TY_PTR && ty_is_int(VT(in->b)), "astore mismatch");
        NEED(in->aux <= AO_SEQCST, "atomic ordering out of range");
        break;
    case OP_AADD:
        NEED(VT(in->a).kind == TY_PTR && ty_is_int(VT(in->b)) && ty_is_int(in->ty), "aadd mismatch");
        NEED(in->aux <= AO_SEQCST, "atomic ordering out of range");
        break;
    case OP_BR: case OP_CONDBR: {
        if (op == OP_CONDBR) NEED(VT(in->a).kind == TY_INT && VT(in->a).bits == 1, "condbr condition must be i1");
        int tgts[2] = { in->blk, in->blk2 };
        int32_t *aa[2] = { in->args, in->args2 };
        int nn[2] = { in->nargs, in->nargs2 };
        int lim = op == OP_BR ? 1 : 2;
        for (int k = 0; k < lim; k++) {
            NEED(tgts[k] >= 0 && tgts[k] < f->nblocks, "branch target out of range");
            Block *tb = &f->blocks[tgts[k]];
            NEED(nn[k] == tb->nargs, "branch argument count mismatch");
            for (int i = 0; i < nn[k]; i++)
                NEED(same_ty(VT(aa[k][i]), tb->arg_types[i]), "branch argument type mismatch");
        }
        break;
    }
    case OP_RET:
        if (f->ret.kind == TY_VOID) NEED(in->a == -1, "void function returns a value");
        else { NEED(in->a >= 0, "missing return value"); NEED(same_ty(VT(in->a), f->ret), "return type mismatch"); }
        break;
    case OP_CALL: case OP_TAILCALL: {
        const Type *ps; int np; Type rt;
        if (in->callee_extern) {
            NEED(in->callee >= 0 && in->callee < m->nexts, "extern index out of range");
            ps = m->exts[in->callee].params; np = m->exts[in->callee].nparams; rt = m->exts[in->callee].ret;
        } else {
            NEED(in->callee >= 0 && in->callee < m->nfuncs, "function index out of range");
            Func *g = &m->funcs[in->callee];
            NEED(g->nblocks > 0, "call to empty function");
            ps = g->blocks[0].arg_types; np = g->blocks[0].nargs; rt = g->ret;
        }
        NEED(in->nargs == np, "call argument count mismatch");
        for (int i = 0; i < np; i++)
            NEED(same_ty(VT(in->args[i]), ps[i]), "call argument type mismatch");
        NEED(same_ty(in->ty, rt), "call result type mismatch");
        if (op == OP_TAILCALL) {
            NEED(idx == (int)b->nins - 1, "tailcall must terminate its block");
            NEED(same_ty(rt, f->ret), "tailcall result must match function return type");
        }
        break;
    }
    case OP_ASSUME:
        NEED(VT(in->a).kind == TY_INT && VT(in->a).bits == 1, "assume needs i1");
        break;
    default:
        return failf("verifier: unknown opcode %s (%d)", op_name(op), op);
    }
    #undef NEED
    #undef VT
    return NULL;
}

const char *mod_verify(Module *m) {
    for (int fi = 0; fi < m->nfuncs; fi++) {
        Func *f = &m->funcs[fi];
        if (f->nblocks == 0) return failf("verifier: function %s has no blocks", f->name, 0);
        /* definition map: value -> (block, position) ; position -1 = block arg */
        int nv = f->nvalues;
        int *defblk = malloc(sizeof(int) * (size_t)nv);
        int *defpos = malloc(sizeof(int) * (size_t)nv);
        for (int i = 0; i < nv; i++) { defblk[i] = -1; defpos[i] = -1; }
        for (int bi = 0; bi < f->nblocks; bi++) {
            Block *b = &f->blocks[bi];
            for (int i = 0; i < b->nargs; i++) { defblk[b->arg_vals[i]] = bi; defpos[b->arg_vals[i]] = -1; }
            int terms = 0;
            for (int ii = 0; ii < b->nins; ii++) {
                Instr *in = &b->ins[ii];
                if (op_is_terminator(in->op)) {
                    terms++;
                    if (ii != b->nins - 1) { free(defblk); free(defpos); return fail("verifier: terminator before end of block"); }
                }
                if (in->result >= 0) { defblk[in->result] = bi; defpos[in->result] = ii; }
                const char *e = check_instr(m, f, b, in, ii);
                if (e) { free(defblk); free(defpos); return e; }
            }
            if (terms != 1) { free(defblk); free(defpos); return fail("verifier: block must end with exactly one terminator"); }
        }
        /* use-before-def within blocks + dominance via simple dataflow:
         * a use in block B of a value defined in block D is legal iff D == B
         * with an earlier position, or D dominates B. Compute dominators. */
        int nb = f->nblocks;
        if (nb < 1 || nb > 4096) return fail("verifier: block count out of range");
        size_t nnb = (size_t)nb;
        /* bitset dominators, word count */
        int W = (nb + 63) / 64;
        uint64_t *doms = calloc(nnb * (size_t)W, sizeof(uint64_t));
        for (int i = 0; i < nb; i++)
            for (int w = 0; w < W; w++) doms[(size_t)i * W + w] = ~0ull;
        for (int w = 0; w < W; w++) doms[w] = 0;
        doms[0] = 1ull;
        /* predecessors */
        int *npred = calloc(nnb, sizeof(int));
        int **preds = calloc(nnb, sizeof(int *));
        int *predcap = calloc(nnb, sizeof(int));
        for (int bi = 0; bi < nb; bi++) {
            Block *b = &f->blocks[bi];
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
                if (npred[i] == 0) continue; /* unreachable: leave all-ones */
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
        for (int bi = 0; bi < nb; bi++) {
            Block *b = &f->blocks[bi];
            for (int ii = 0; ii < b->nins; ii++) {
                Instr *in = &b->ins[ii];
                int32_t ops[64]; int nops = 0;
                if (in->a >= 0) ops[nops++] = in->a;
                if (in->b >= 0) ops[nops++] = in->b;
                if (in->c >= 0 && in->op != OP_ALLOCA) ops[nops++] = in->c; /* ALLOCA's c is the align immediate */
                for (int i = 0; i < in->nargs && nops < 64; i++) ops[nops++] = in->args[i];
                for (int i = 0; i < in->nargs2 && nops < 64; i++) ops[nops++] = in->args2[i];
                for (int i = 0; i < nops; i++) {
                    int v = ops[i];
                    if (v >= nv) { snprintf(ERR, sizeof ERR, "verifier: value id out of range (func %s block %d ins %d val %d nvals %d)", f->name, bi, ii, v, nv); free(defblk); free(defpos); free(doms); return ERR; }
                    int db = defblk[v];
                    if (db < 0) { snprintf(ERR, sizeof ERR, "verifier: use of undefined value (func %s block %d ins %d val %d)", f->name, bi, ii, v); free(defblk); free(defpos); free(doms); return ERR; }
                    bool okd = (db == bi) ? (defpos[v] < ii || defpos[v] == -1) : (DOM(db, bi) && db != bi);
                    if (db == bi) okd = defpos[v] == -1 || defpos[v] < ii;
                    else okd = DOM(db, bi) != 0;
                    if (!okd) { snprintf(ERR, sizeof ERR, "verifier: use not dominated by definition (func %s block %d ins %d val %d defblock %d)", f->name, bi, ii, v, db); free(defblk); free(defpos); free(doms); return ERR; }
                }
            }
        }
        #undef DOM
        for (int i = 0; i < nb; i++) free(preds[i]);
        free(preds); free(npred); free(predcap);
        free(doms); free(defblk); free(defpos);
    }
    return NULL;
}

const char *mod_verify_target(Module *m, const char *target) {
    const char *e = mod_verify(m);
    if (e) return e;
    Cost *c = cost_load(target);
    if (!c) return fail("verifier: cost file for target not found");
    for (int fi = 0; fi < m->nfuncs; fi++) {
        Func *f = &m->funcs[fi];
        for (int bi = 0; bi < f->nblocks; bi++) {
            Block *b = &f->blocks[bi];
            for (int ii = 0; ii < b->nins; ii++) {
                Instr *in = &b->ins[ii];
                switch (in->op) {
                case OP_BR: case OP_CONDBR: case OP_RET: case OP_CALL: case OP_TAILCALL:
                case OP_ICONST: case OP_FCONST: case OP_FREEZE: case OP_ASSUME: case OP_DATAPTR:
                    continue;
                default: break;
                }
                Type t = in->ty;
                if (in->op == OP_STORE || in->op == OP_VSTORE) t = f->vtypes[in->b];
                if (cost_lat(c, in->op, t) < 0)
                     { cost_free(c); return failf("verifier: op %s has no cost entry for target (no-cliff gate)", op_name(in->op), 0); }
                if (cost_cliff(c, in->op, t))
                     { cost_free(c); return failf("verifier: op %s is a cliff on this target (no-cliff gate)", op_name(in->op), 0); }
            }
        }
    }
    cost_free(c);
    return NULL;
}
