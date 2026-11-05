/* Krell backends — shared kit implementation. */
#include "be.h"
#include <limits.h>

void be_err(char *err, size_t cap, const char *msg) { if (err) snprintf(err, cap, "%s", msg); }

int be_class_of(Type t) {
    switch (t.kind) {
    case TY_INT: if (t.bits == 128) return BCLS_MEM128; /* memory-resident */
             /* fall through */
    case TY_PTR: return BCLS_GP;
    case TY_FLOAT: return BCLS_FP;
    case TY_VEC: return t.n == 1 ? BCLS_FP : BCLS_VEC;
    default: return -1;
    }
}

bool be_iconst_val(Func *f, int v, int64_t *out) {
    if (v < 0 || v >= f->nvalues || !f->isconst[v]) return false;
    Type t = f->vtypes[v];
    if (t.kind != TY_INT) return false;
    *out = (int64_t)f->cval[v];
    return true;
}

/* ---------- liveness / intervals ---------- */
typedef struct { int start, end, v; bool cross; } Iv;

static int cmp_iv(const void *a, const void *b) {
    const Iv *x = a, *y = b;
    /* Total order (start, end, value id): qsort leaves the order of
     * equal elements to the libc, and block arguments tie on start
     * by construction — without the tie-breaks the allocator walks
     * tied intervals in libc order and the same module compiles to
     * different (equivalent) code on different platforms. With a
     * total order the allocation, and therefore the generated code,
     * is identical everywhere. */
    if (x->start != y->start) return x->start < y->start ? -1 : 1;
    if (x->end != y->end) return x->end < y->end ? -1 : 1;
    return x->v < y->v ? -1 : x->v > y->v ? 1 : 0;
}

/* Next use of a value at or after position p, for the Belady spill
 * choice. Use positions are static (block start + instruction
 * index), so a loop-carried value whose remaining uses in this
 * iteration all sit before p would otherwise read as "never used
 * again" (INT_MAX) and be evicted ahead of genuinely cold values --
 * parse's buffer pointer was spilled exactly this way, adding a
 * stack reload to its per-byte loop. When no static use at or after
 * p exists but the value's first use and p both lie inside a loop
 * AND the value's interval spans the loop's back edge (it is live
 * across the latch, so the use really does recur), the next dynamic
 * use is the first use of the next iteration: report it as the
 * virtual position latch_end + (first_use - header_start), which
 * keeps wrapped distances comparable with plain ones. A body-local
 * value whose interval ends before the latch does not span the
 * edge: its early use is spent, not recurring, and it stays
 * INT_MAX -- the correct first victim. */
static int nu_next_use(const int *usepos, int lo, int hi, int p,
                       int istart, int iend,
                       const int *be_hp, const int *be_lp, int nbe) {
    for (int k = lo; k < hi; k++) if (usepos[k] >= p) return usepos[k];
    if (lo >= hi) return INT_MAX;
    int u0 = usepos[lo], best = INT_MAX;
    for (int e = 0; e < nbe; e++) {
        if (be_hp[e] <= u0 && u0 <= be_lp[e] && be_hp[e] <= p && p <= be_lp[e] &&
            istart <= be_lp[e] && iend >= be_lp[e]) {
            int w = be_lp[e] + (u0 - be_hp[e]);
            if (w < best) best = w;
        }
    }
    return best;
}

BeFunc *be_analyze(Module *m, Func *f, const Pools *pools) {
    return be_analyze_ext(m, f, pools, NULL, NULL);
}

/* Folded-consumption liveness: when a backend folds an instruction
 * into its consumer (a GEP into a load/store addressing mode, an
 * arithmetic chain into a select, ...), the folded value gets no
 * location, but its OPERANDS are read at the consumer, not at the
 * folded instruction. Every use of a folded value therefore also
 * counts as a use of its operands at the same position, recursively
 * through folded chains. Without this, the allocator believes an
 * operand dies at the folded instruction and hands its register to
 * a value defined between the two -- the optimized fuzz corpus
 * stored through a clobbered GEP index register this way (the
 * store's constant landed in the index register first).
 *
 * Root-redirected folds (fold_root[v] >= 0): some folds do NOT read
 * the folded value's defining operands at the consumer -- the x86
 * backend's skipped add chains (WP20) are materialized from the
 * chain's recorded ROOT plus an accumulated offset, reaching through
 * every intermediate add, including ones that execute. For those
 * values a use expands to the root alone. Expanding to the defining
 * operands instead leaves the root's interval ending at its last
 * direct use, so an in-place (2-address) definition between the two
 * can take the root's register and the materialization silently
 * reads the new value (WP36: a sub written into the argument's home
 * was read back as the argument by three chain materializations). */
static void endpos_use(BeFunc *bf, const bool *folded, const int *fold_root, Instr **defi, int v, int p, int depth) {
    if (v < 0) return;
    if (p > bf->endpos[v]) bf->endpos[v] = p;
    if (folded && folded[v] && depth < 32) {
        if (fold_root && fold_root[v] >= 0) {
            endpos_use(bf, folded, fold_root, defi, fold_root[v], p, depth + 1);
        } else if (defi && defi[v]) {
            Instr *d = defi[v];
            endpos_use(bf, folded, fold_root, defi, d->a, p, depth + 1);
            endpos_use(bf, folded, fold_root, defi, d->b, p, depth + 1);
            if (d->op != OP_ALLOCA) endpos_use(bf, folded, fold_root, defi, d->c, p, depth + 1);
        }
    }
}
static void buse_use(uint64_t *buse, const uint64_t *bdef, int W, int b, const bool *folded, const int *fold_root, Instr **defi, int v, int depth) {
    if (v < 0) return;
    if (!((bdef[(size_t)b * (size_t)W + (size_t)(v >> 6)] >> (v & 63)) & 1ull))
        buse[(size_t)b * (size_t)W + (size_t)(v >> 6)] |= (1ull << (v & 63));
    if (folded && folded[v] && depth < 32) {
        if (fold_root && fold_root[v] >= 0) {
            buse_use(buse, bdef, W, b, folded, fold_root, defi, fold_root[v], depth + 1);
        } else if (defi && defi[v]) {
            Instr *d = defi[v];
            buse_use(buse, bdef, W, b, folded, fold_root, defi, d->a, depth + 1);
            buse_use(buse, bdef, W, b, folded, fold_root, defi, d->b, depth + 1);
            if (d->op != OP_ALLOCA) buse_use(buse, bdef, W, b, folded, fold_root, defi, d->c, depth + 1);
        }
    }
}
static void count_use(const bool *folded, const int *fold_root, Instr **defi, int *usecnt, int v, int depth) {
    if (v < 0) return;
    usecnt[v]++;
    if (folded && folded[v] && depth < 32) {
        if (fold_root && fold_root[v] >= 0) {
            count_use(folded, fold_root, defi, usecnt, fold_root[v], depth + 1);
        } else if (defi && defi[v]) {
            Instr *d = defi[v];
            count_use(folded, fold_root, defi, usecnt, d->a, depth + 1);
            count_use(folded, fold_root, defi, usecnt, d->b, depth + 1);
            if (d->op != OP_ALLOCA) count_use(folded, fold_root, defi, usecnt, d->c, depth + 1);
        }
    }
}
static void fill_use(const bool *folded, const int *fold_root, Instr **defi, int *usepos, int *usecur, const int *useoff, int v, int p, int depth) {
    if (v < 0) return;
    if (usecur[v] < useoff[v + 1]) usepos[usecur[v]++] = p;
    if (folded && folded[v] && depth < 32) {
        if (fold_root && fold_root[v] >= 0) {
            fill_use(folded, fold_root, defi, usepos, usecur, useoff, fold_root[v], p, depth + 1);
        } else if (defi && defi[v]) {
            Instr *d = defi[v];
            fill_use(folded, fold_root, defi, usepos, usecur, useoff, d->a, p, depth + 1);
            fill_use(folded, fold_root, defi, usepos, usecur, useoff, d->b, p, depth + 1);
            if (d->op != OP_ALLOCA) fill_use(folded, fold_root, defi, usepos, usecur, useoff, d->c, p, depth + 1);
        }
    }
}

BeFunc *be_analyze_ext(Module *m, Func *f, const Pools *pools, const bool *folded, const int *fold_root) {
    (void)m;
    BeFunc *bf = calloc(1, sizeof(BeFunc));
    bf->f = f;
    int nv = f->nvalues > 0 ? f->nvalues : 1;
    bf->nvals = f->nvalues;
    bf->defpos = calloc((size_t)nv, sizeof(int));
    bf->endpos = calloc((size_t)nv, sizeof(int));
    bf->crosscall = calloc((size_t)nv, sizeof(bool));
    bf->vclass = malloc((size_t)nv);
    bf->loc = calloc((size_t)nv, sizeof(Loc));
    bf->vec_off = malloc(sizeof(int32_t) * (size_t)nv);
    bf->blkstart = calloc((size_t)(f->nblocks > 0 ? f->nblocks : 1), sizeof(int));
    for (int i = 0; i < f->nvalues; i++) {
        bf->loc[i].idx = -1;
        if (folded && folded[i]) bf->vclass[i] = -1;
        else if (!pools->vec_regs && f->vtypes[i].kind == TY_VEC) bf->vclass[i] = BCLS_VEC;
        else bf->vclass[i] = (int8_t)be_class_of(f->vtypes[i]);
        bf->vec_off[i] = -1;
    }
    /* positions */
    int pos = 0;
    for (int b = 0; b < f->nblocks; b++) {
        bf->blkstart[b] = pos;
        pos += 1 + f->blocks[b].nins;
    }
    bf->maxpos = pos;
    bf->allo_off = malloc(sizeof(int) * (size_t)(pos > 0 ? pos : 1));
    for (int i = 0; i < pos; i++) bf->allo_off[i] = -1;

    /* defs and direct uses */
    int *callpos = NULL; int ncall = 0, callcap = 0;
    for (int b = 0; b < f->nblocks; b++) {
        Block *bl = &f->blocks[b];
        for (int i = 0; i < bl->nargs; i++) {
            bf->defpos[bl->arg_vals[i]] = bf->blkstart[b];
            bf->endpos[bl->arg_vals[i]] = bf->blkstart[b];
        }
        for (int i = 0; i < bl->nins; i++) {
            Instr *in = &bl->ins[i];
            int p = be_pos(bf, b, i);
            if (in->result >= 0) { bf->defpos[in->result] = p; bf->endpos[in->result] = p; }
            if (in->op == OP_CALL || in->op == OP_CALLI || in->op == OP_FMA || in->op == OP_MEMCPY || in->op == OP_MEMSET) {
                /* FMA/memcpy/memset lower to libcalls on some targets: any
                 * value live across them must survive a call */
                if (ncall == callcap) { callcap = callcap ? callcap * 2 : 16; callpos = realloc(callpos, sizeof(int) * (size_t)callcap); }
                callpos[ncall++] = p;
            }
        }
    }
    /* defining instruction per value, for folded-use expansion */
    Instr **defi = calloc((size_t)nv, sizeof(Instr *));
    for (int b = 0; b < f->nblocks; b++) {
        Block *bl = &f->blocks[b];
        for (int i = 0; i < bl->nins; i++)
            if (bl->ins[i].result >= 0) defi[bl->ins[i].result] = &bl->ins[i];
    }
    for (int b = 0; b < f->nblocks; b++) {
        Block *bl = &f->blocks[b];
        for (int i = 0; i < bl->nins; i++) {
            Instr *in = &bl->ins[i];
            int p = be_pos(bf, b, i);
            endpos_use(bf, folded, fold_root, defi, in->a, p, 0);
            endpos_use(bf, folded, fold_root, defi, in->b, p, 0);
            if (in->op != OP_ALLOCA) endpos_use(bf, folded, fold_root, defi, in->c, p, 0);
            for (int k = 0; k < in->nargs; k++) endpos_use(bf, folded, fold_root, defi, in->args[k], p, 0);
            for (int k = 0; k < in->nargs2; k++) endpos_use(bf, folded, fold_root, defi, in->args2[k], p, 0);
        }
    }
    /* live-in / live-out per block (bitsets over values) */
    int nb = f->nblocks, W = (f->nvalues + 63) / 64;
    if (W < 1) W = 1;
    if (nb < 1 || nb > 65536 || f->nvalues < 0 || f->nvalues > (1 << 22)) return NULL;
    uint64_t *livein = calloc((size_t)nb * (size_t)W, sizeof(uint64_t));
    uint64_t *liveout = calloc((size_t)nb * (size_t)W, sizeof(uint64_t));
    uint64_t *buse = calloc((size_t)nb * (size_t)W, sizeof(uint64_t));
    uint64_t *bdef = calloc((size_t)nb * (size_t)W, sizeof(uint64_t));
    #define SET(bs, b, v) (bs)[(size_t)(b) * W + ((v) >> 6)] |= (1ull << ((v) & 63))
    #define GET(bs, b, v) (((bs)[(size_t)(b) * W + ((v) >> 6)] >> ((v) & 63)) & 1ull)
    for (int b = 0; b < nb; b++) {
        Block *bl = &f->blocks[b];
        for (int i = 0; i < bl->nargs; i++) SET(bdef, b, bl->arg_vals[i]);
        for (int i = 0; i < bl->nins; i++) {
            Instr *in = &bl->ins[i];
            int32_t ops[3] = { in->a, in->b, in->op == OP_ALLOCA ? -1 : in->c };
            for (int k = 0; k < 3; k++)
                buse_use(buse, bdef, W, b, folded, fold_root, defi, ops[k], 0);
            for (int k = 0; k < in->nargs; k++)
                buse_use(buse, bdef, W, b, folded, fold_root, defi, in->args[k], 0);
            for (int k = 0; k < in->nargs2; k++)
                buse_use(buse, bdef, W, b, folded, fold_root, defi, in->args2[k], 0);
            if (in->result >= 0) SET(bdef, b, in->result);
        }
    }
    bool changed = true;
    while (changed) {
        changed = false;
        for (int b = nb - 1; b >= 0; b--) {
            Block *bl = &f->blocks[b];
            Instr *t = &bl->ins[bl->nins - 1];
            int tg[2] = { -1, -1 };
            if (t->op == OP_BR) tg[0] = t->blk;
            if (t->op == OP_CONDBR) { tg[0] = t->blk; tg[1] = t->blk2; }
            for (int k = 0; k < 2; k++) {
                if (tg[k] < 0) continue;
                int s = tg[k];
                for (int w = 0; w < W; w++) {
                    uint64_t add = livein[(size_t)s * W + w] & ~liveout[(size_t)b * W + w];
                    if (add) { liveout[(size_t)b * W + w] |= livein[(size_t)s * W + w]; changed = true; }
                }
            }
            for (int w = 0; w < W; w++) {
                uint64_t nin = buse[(size_t)b * W + w] | (liveout[(size_t)b * W + w] & ~bdef[(size_t)b * W + w]);
                if (nin != livein[(size_t)b * W + w]) { livein[(size_t)b * W + w] = nin; changed = true; }
            }
        }
    }
    /* extend interval ends over blocks where the value is live-out */
    for (int b = 0; b < nb; b++) {
        int bend = bf->blkstart[b] + f->blocks[b].nins; /* position of last instr */
        for (int v = 0; v < f->nvalues; v++)
            if (GET(liveout, b, v) && bend > bf->endpos[v]) bf->endpos[v] = bend;
    }
    /* call crossing */
    for (int v = 0; v < f->nvalues; v++) {
        for (int i = 0; i < ncall; i++)
            if (callpos[i] > bf->defpos[v] && callpos[i] < bf->endpos[v]) { bf->crosscall[v] = true; break; }
    }
    free(callpos); free(livein); free(liveout); free(buse); free(bdef);
    #undef SET
    #undef GET
    #undef USE

    /* ---------- frame layout ----------
     * Order below the frame pointer (offsets grow downward):
     *   scalar spill slots (8B each), vector slots (16B x n each),
     *   alloca areas, outgoing stack-arg area (max 16 slots = 128B cap),
     * rounded up to 16. Offset of the first byte of the frame = 16 (we also
     * keep the saved frame pointer / return address above). */
    int scalar_slots = 0, vec_units = 0;
    /* first pass: count potential slots = number of GP/FP values + vec units */
    for (int v = 0; v < f->nvalues; v++) {
        if (bf->vclass[v] == BCLS_VEC) vec_units += f->vtypes[v].n;
        else if (bf->vclass[v] >= 0) scalar_slots++;
    }
    int out_slots = 0;
    for (int b = 0; b < f->nblocks; b++)
        for (int i = 0; i < f->blocks[b].nins; i++) {
            Instr *in = &f->blocks[b].ins[i];
            if ((in->op == OP_CALL || in->op == OP_TAILCALL || in->op == OP_CALLI || in->op == OP_TAILCALLI) && in->nargs > out_slots) out_slots = in->nargs;
        }
    /* layout intent: allocation below decides slot indices; offsets computed
     * after allocation once we know how many slots are actually used. To keep
     * one pass, reserve worst case and compute offsets from slot indices:
     *   scalar slot i  -> off = 16 + 8*i
     *   vec value slot -> off = 16 + 8*scalar_slots + 16*unit
     *   alloca j       -> follows vectors
     * We do allocation FIRST using abstract slot indices, then fix offsets. */
    (void)scalar_slots; (void)vec_units; (void)out_slots;

    /* ---------- linear scan per class ---------- */
    Instr **defins = calloc((size_t)nv, sizeof(Instr *));
    int *defblk = calloc((size_t)nv, sizeof(int));
    int *defidx = calloc((size_t)nv, sizeof(int));
    int *usecnt = calloc((size_t)nv, sizeof(int));
    int *use_tgt = malloc(sizeof(int) * (size_t)nv);
    int *use_slot = calloc((size_t)nv, sizeof(int));
    int *use_list = calloc((size_t)nv, sizeof(int));
    int *use_srcblk = calloc((size_t)nv, sizeof(int));
    for (int v = 0; v < nv; v++) { defblk[v] = -1; defidx[v] = -1; use_tgt[v] = -1; use_srcblk[v] = -1; }
    for (int b = 0; b < f->nblocks; b++) {
        Block *bl = &f->blocks[b];
        for (int i = 0; i < bl->nins; i++) {
            Instr *in = &bl->ins[i];
            if (in->result >= 0) { defins[in->result] = in; defblk[in->result] = b; defidx[in->result] = i; }
        }
    }
    /* use census: counts every operand use; a use as a branch argument
     * also records (source block, target block, slot, list) so the
     * allocator can recognize sole-use edge values */
    for (int b = 0; b < f->nblocks; b++) {
        Block *bl = &f->blocks[b];
        for (int i = 0; i < bl->nins; i++) {
            Instr *in = &bl->ins[i];
            count_use(folded, fold_root, defi, usecnt, in->a, 0);
            count_use(folded, fold_root, defi, usecnt, in->b, 0);
            if (in->op != OP_ALLOCA) count_use(folded, fold_root, defi, usecnt, in->c, 0);
            for (int k = 0; k < in->nargs; k++) {
                int v = in->args[k]; if (v < 0) continue; count_use(folded, fold_root, defi, usecnt, v, 0);
                if (in->op == OP_BR || in->op == OP_CONDBR) { use_tgt[v] = in->blk; use_slot[v] = k; use_list[v] = 0; use_srcblk[v] = b; }
            }
            for (int k = 0; k < in->nargs2; k++) {
                int v = in->args2[k]; if (v < 0) continue; count_use(folded, fold_root, defi, usecnt, v, 0);
                if (in->op == OP_CONDBR) { use_tgt[v] = in->blk2; use_slot[v] = k; use_list[v] = 1; use_srcblk[v] = b; }
            }
        }
    }

    /* ---------- clobber analysis for scratch-shared pool registers --
     * When the backend offers pool registers it also uses as emitter
     * scratch (PoolReg.clob != 0), compute per value the clobber
     * classes it may NOT be allocated into: a class forbids a value
     * when an instruction strictly inside the value's interval may
     * write that register, when the value's defining instruction
     * forbids it for its own result, when the value's last use is at
     * a clobbering instruction that does not bless this operand for
     * that class, or when a prologue sequence bans it for entry
     * arguments. Conservative by construction: an unrecognized
     * pattern forbids, never permits. */
    uint8_t *forbid = NULL;
    if (pools->clob_mask) {
        forbid = calloc((size_t)nv, 1);
        int mp = bf->maxpos > 0 ? bf->maxpos : 1;
        Instr **posins = calloc((size_t)mp, sizeof(Instr *));
        uint8_t *posmask = calloc((size_t)mp, 1);
        for (int b = 0; b < f->nblocks; b++) {
            Block *bl = &f->blocks[b];
            for (int i = 0; i < bl->nins; i++) {
                int p = be_pos(bf, b, i);
                posins[p] = &bl->ins[i];
                posmask[p] = pools->clob_mask(pools->clob_ctx, &bl->ins[i]);
            }
        }
        if (pools->clob_entrymask && f->nblocks > 0) {
            uint8_t em = pools->clob_entrymask(pools->clob_ctx, f);
            if (em) for (int i = 0; i < f->blocks[0].nargs; i++)
                forbid[f->blocks[0].arg_vals[i]] |= em;
        }
        /* cost guard, ported from the WP21-C eligibility scan: the
         * interval scan below is O(values x positions); on very
         * large functions leave the scratch-shared pool off (every
         * clobber class forbidden for every value) rather than pay
         * a quadratic pass. */
        uint8_t allclob = 0;
        for (int r = 0; r < pools->ngp; r++) allclob |= (uint8_t)pools->gp[r].clob;
        for (int r = 0; r < pools->nfp; r++) allclob |= (uint8_t)pools->fp[r].clob;
        bool scan = (int64_t)nv * (int64_t)bf->maxpos <= (int64_t)64 * 1000 * 1000;
        for (int v = 0; v < f->nvalues; v++) {
            if (bf->vclass[v] < 0) continue;
            if (!scan) { forbid[v] = allclob; continue; }
            if (defins[v] && pools->clob_defmask)
                forbid[v] |= pools->clob_defmask(pools->clob_ctx, defins[v]);
            int s = bf->defpos[v], e = bf->endpos[v];
            for (int p = s + 1; p <= e && p < bf->maxpos; p++) {
                uint8_t cm = posmask[p];
                if (!cm) continue;
                if (p < e) { forbid[v] |= cm; continue; }
                Instr *in = posins[p];
                if (!in) continue;
                for (int bit = 1; bit <= 4; bit <<= 1) {
                    if (!(cm & bit)) continue;
                    bool ok = pools->clob_bless &&
                              pools->clob_bless(pools->clob_ctx, in, v, (uint8_t)bit);
                    if (!ok) forbid[v] |= (uint8_t)bit;
                }
            }
        }
        free(posins); free(posmask);
    }
#define REG_FORBIDDEN(v, pe) ((pe).clob && forbid && (forbid[v] & (pe).clob))

    /* Per-value use positions in the allocator's global position
     * space -- be_pos (block start + 1 + instruction index), the
     * SAME space as defpos/endpos and the interval starts the spill
     * decision compares against. (A blkstart+i spelling here once
     * shifted every use one position early, which made an operand
     * of the very instruction being allocated for look already
     * spent and therefore evictable.) Appended in block
     * order, hence sorted per value. The spill decision below uses
     * them for a next-use (Belady) victim choice: evicting the
     * interval whose next use is farthest away is the locally
     * optimal trade, and it subsumes the older heuristics (evict
     * the interval that ends last, length and cross-block guards),
     * which could not see that a loop invariant's next use may be
     * nearer than a hot intermediate's, or vice versa. */
    int *useoff = malloc(sizeof(int) * (size_t)(nv + 1));
    int tot_uses = 0;
    for (int v = 0; v < nv; v++) { useoff[v] = tot_uses; tot_uses += usecnt[v]; }
    useoff[nv] = tot_uses;
    int *usepos = malloc(sizeof(int) * (size_t)(tot_uses > 0 ? tot_uses : 1));
    {
        int *usecur = malloc(sizeof(int) * (size_t)nv);
        for (int v = 0; v < nv; v++) usecur[v] = useoff[v];
        for (int b = 0; b < f->nblocks; b++) {
            Block *bl = &f->blocks[b];
            for (int i = 0; i < bl->nins; i++) {
                Instr *in = &bl->ins[i];
                int pos = be_pos(bf, b, i);
                fill_use(folded, fold_root, defi, usepos, usecur, useoff, in->a, pos, 0);
                fill_use(folded, fold_root, defi, usepos, usecur, useoff, in->b, pos, 0);
                if (in->op != OP_ALLOCA) fill_use(folded, fold_root, defi, usepos, usecur, useoff, in->c, pos, 0);
                for (int k = 0; k < in->nargs; k++) fill_use(folded, fold_root, defi, usepos, usecur, useoff, in->args[k], pos, 0);
                for (int k = 0; k < in->nargs2; k++) fill_use(folded, fold_root, defi, usepos, usecur, useoff, in->args2[k], pos, 0);
            }
        }
        free(usecur);
    }
    free(defi);

    /* Back edges in position space: a terminator target whose block
     * starts at or before the source block is a loop back edge; the
     * pair (header start, latch end) spans the loop for the
     * wrap-aware next-use computation in nu_next_use. */
    int *be_hp = malloc(sizeof(int) * (size_t)(2 * nb > 0 ? 2 * nb : 1));
    int *be_lp = malloc(sizeof(int) * (size_t)(2 * nb > 0 ? 2 * nb : 1));
    int nbe = 0;
    for (int b = 0; b < nb; b++) {
        Block *bl = &f->blocks[b];
        if (bl->nins < 1) continue;
        Instr *t = &bl->ins[bl->nins - 1];
        int tg[2] = { -1, -1 };
        if (t->op == OP_BR) tg[0] = t->blk;
        if (t->op == OP_CONDBR) { tg[0] = t->blk; tg[1] = t->blk2; }
        for (int k = 0; k < 2; k++) {
            int s = tg[k];
            if (s < 0 || s >= nb) continue;
            if (bf->blkstart[s] <= bf->blkstart[b]) {
                be_hp[nbe] = bf->blkstart[s];
                be_lp[nbe] = bf->blkstart[b] + bl->nins;
                nbe++;
            }
        }
    }

    /* Spill weights: an evicted interval pays a reload at EVERY
     * remaining use (this allocator does not split intervals), so the
     * victim choice must weigh total dynamic cost, not just the next
     * use. A use inside a loop span counts LOOPW times -- a
     * loop-carried pointer used four times per iteration outweighs a
     * burst of one-shot temporaries even though its next single use
     * is farther away than theirs (the failure mode of pure
     * next-use Belady on wide loop state: the regulars are evicted
     * one at a time, each at the moment its next use looks far).
     * Constants weigh 0: they are rematerializable, most emitter
     * sites fold them back into immediates, and the rest pay a
     * single load -- always the cheapest victims. */
    int *ivweight = malloc(sizeof(int) * (size_t)nv);
    for (int v = 0; v < nv; v++) {
        Instr *df = defins[v];
        if (df && (df->op == OP_ICONST || df->op == OP_FCONST)) { ivweight[v] = 0; continue; }
        int wsum = 0;
        for (int k = useoff[v]; k < useoff[v + 1]; k++) {
            int p = usepos[k], inl = 0;
            for (int e = 0; e < nbe; e++) if (be_hp[e] <= p && p <= be_lp[e]) { inl = 1; break; }
            wsum += inl ? 16 : 1;
        }
        ivweight[v] = wsum;
    }

    /* Spill weights, cycle form: a value on a def-use cycle -- the
     * loop-carried shape: block parameter -> update chain -> back-edge
     * argument -> the same parameter -- is one spill unit with its
     * fellow cycle members, not an independent value. The per-value
     * count above undercounts such chains: in an unrolled reduction
     * every link has exactly one in-loop use (weight 16, no better
     * than a one-shot temporary whose next use is two positions
     * away), so the victim choice picks the links off one at a time,
     * and a spilled link also breaks the register reuse (2-address
     * and back-edge coalescing) the rest of the chain depends on.
     * Give every member of a strongly connected component of the
     * def-use graph the component's total weight. Edges: an operand
     * value flows into the value its instruction defines; a branch
     * argument flows into the target block's parameter. Weights only
     * steer victim choice, so folded-value edges may be approximate. */
    {
        int *outdeg = calloc((size_t)nv, sizeof(int));
        int *indeg = calloc((size_t)nv, sizeof(int));
        for (int b = 0; b < f->nblocks; b++) {
            Block *bl = &f->blocks[b];
            for (int i = 0; i < bl->nins; i++) {
                Instr *in = &bl->ins[i];
                if (in->op == OP_BR || in->op == OP_CONDBR) {
                    int tg[2] = { in->blk, in->op == OP_CONDBR ? in->blk2 : -1 };
                    const int32_t *ea[2] = { in->args, in->args2 };
                    const uint16_t en[2] = { in->nargs, in->nargs2 };
                    for (int e = 0; e < 2; e++) {
                        if (tg[e] < 0 || tg[e] >= f->nblocks) continue;
                        Block *tb = &f->blocks[tg[e]];
                        for (int k = 0; k < en[e] && k < tb->nargs; k++) {
                            int x = ea[e][k];
                            if (x < 0 || x >= nv) continue;
                            outdeg[x]++; indeg[tb->arg_vals[k]]++;
                        }
                    }
                    continue;
                }
                int r = in->result;
                if (r < 0 || r >= nv) continue;
                int ops[3] = { in->a, in->b, in->op == OP_ALLOCA ? -1 : in->c };
                for (int k = 0; k < 3; k++) {
                    int x = ops[k];
                    if (x < 0 || x >= nv || x == r) continue;
                    outdeg[x]++; indeg[r]++;
                }
                for (int k = 0; k < in->nargs; k++) {
                    int x = in->args[k];
                    if (x < 0 || x >= nv || x == r) continue;
                    outdeg[x]++; indeg[r]++;
                }
            }
        }
        int ne2 = 0;
        for (int v = 0; v < nv; v++) ne2 += outdeg[v];
        int *eoff = malloc(sizeof(int) * (size_t)(nv + 1));
        int *roff = malloc(sizeof(int) * (size_t)(nv + 1));
        int *eadj = malloc(sizeof(int) * (size_t)(ne2 > 0 ? ne2 : 1));
        int *radj = malloc(sizeof(int) * (size_t)(ne2 > 0 ? ne2 : 1));
        eoff[0] = 0; roff[0] = 0;
        for (int v = 0; v < nv; v++) { eoff[v + 1] = eoff[v] + outdeg[v]; roff[v + 1] = roff[v] + indeg[v]; }
        {
            int *ecur = malloc(sizeof(int) * (size_t)nv);
            int *rcur = malloc(sizeof(int) * (size_t)nv);
            for (int v = 0; v < nv; v++) { ecur[v] = eoff[v]; rcur[v] = roff[v]; }
            for (int b = 0; b < f->nblocks; b++) {
                Block *bl = &f->blocks[b];
                for (int i = 0; i < bl->nins; i++) {
                    Instr *in = &bl->ins[i];
                    if (in->op == OP_BR || in->op == OP_CONDBR) {
                        int tg[2] = { in->blk, in->op == OP_CONDBR ? in->blk2 : -1 };
                        const int32_t *ea[2] = { in->args, in->args2 };
                        const uint16_t en[2] = { in->nargs, in->nargs2 };
                        for (int e = 0; e < 2; e++) {
                            if (tg[e] < 0 || tg[e] >= f->nblocks) continue;
                            Block *tb = &f->blocks[tg[e]];
                            for (int k = 0; k < en[e] && k < tb->nargs; k++) {
                                int x = ea[e][k];
                                if (x < 0 || x >= nv) continue;
                                int u = tb->arg_vals[k];
                                eadj[ecur[x]++] = u; radj[rcur[u]++] = x;
                            }
                        }
                        continue;
                    }
                    int r = in->result;
                    if (r < 0 || r >= nv) continue;
                    int ops[3] = { in->a, in->b, in->op == OP_ALLOCA ? -1 : in->c };
                    for (int k = 0; k < 3; k++) {
                        int x = ops[k];
                        if (x < 0 || x >= nv || x == r) continue;
                        eadj[ecur[x]++] = r; radj[rcur[r]++] = x;
                    }
                    for (int k = 0; k < in->nargs; k++) {
                        int x = in->args[k];
                        if (x < 0 || x >= nv || x == r) continue;
                        eadj[ecur[x]++] = r; radj[rcur[r]++] = x;
                    }
                }
            }
            free(ecur); free(rcur);
        }
        /* Kosaraju, iterative: finish order on the user graph, then
         * component assignment on the reversed graph. */
        char *vis = calloc((size_t)nv, 1);
        int *order = malloc(sizeof(int) * (size_t)(nv > 0 ? nv : 1));
        int norder = 0;
        int *dfs = malloc(sizeof(int) * (size_t)(nv > 0 ? nv : 1));
        int *dit = malloc(sizeof(int) * (size_t)(nv > 0 ? nv : 1));
        for (int s = 0; s < nv; s++) {
            if (vis[s]) continue;
            int sp = 0;
            vis[s] = 1; dfs[sp] = s; dit[s] = eoff[s]; sp++;
            while (sp > 0) {
                int v = dfs[sp - 1];
                if (dit[v] < eoff[v + 1]) {
                    int u = eadj[dit[v]++];
                    if (!vis[u]) { vis[u] = 1; dfs[sp++] = u; dit[u] = eoff[u]; }
                } else {
                    order[norder++] = v; sp--;
                }
            }
        }
        int *comp = malloc(sizeof(int) * (size_t)(nv > 0 ? nv : 1));
        for (int v = 0; v < nv; v++) comp[v] = -1;
        int ncomp = 0;
        for (int oi = norder - 1; oi >= 0; oi--) {
            int s = order[oi];
            if (comp[s] >= 0) continue;
            int sp = 0;
            comp[s] = ncomp; dfs[sp++] = s;
            while (sp > 0) {
                int v = dfs[--sp];
                for (int e = roff[v]; e < roff[v + 1]; e++) {
                    int x = radj[e];
                    if (comp[x] < 0) { comp[x] = ncomp; dfs[sp++] = x; }
                }
            }
            ncomp++;
        }
        int *csum = calloc((size_t)(ncomp > 0 ? ncomp : 1), sizeof(int));
        for (int v = 0; v < nv; v++) csum[comp[v]] += ivweight[v];
        for (int v = 0; v < nv; v++) ivweight[v] = csum[comp[v]];
        free(outdeg); free(indeg); free(eoff); free(roff); free(eadj); free(radj);
        free(vis); free(order); free(dfs); free(dit); free(comp); free(csum);
    }

    int maxslots = 0;
    for (int cls = 0; cls < 2; cls++) {
        const PoolReg *pool = cls == BCLS_GP ? pools->gp : pools->fp;
        int npool = cls == BCLS_GP ? pools->ngp : pools->nfp;
        if (!pool || npool == 0) continue;
        Iv *ivs = malloc(sizeof(Iv) * (size_t)nv);
        int ni = 0;
        for (int v = 0; v < f->nvalues; v++)
            if (bf->vclass[v] == cls) {
                if (bf->defpos[v] == bf->endpos[v]) continue;
                ivs[ni].start = bf->defpos[v]; ivs[ni].end = bf->endpos[v];
                ivs[ni].v = v; ivs[ni].cross = bf->crosscall[v]; ni++;
            }
        qsort(ivs, (size_t)ni, sizeof(Iv), cmp_iv);
        /* active list: (start, end, reg, v, callee) */
        typedef struct { int start, end, reg, v; bool callee; bool prot; } Act;
        Act *act = malloc(sizeof(Act) * (size_t)(ni > 0 ? ni : 1));
        /* (block, pool register) pairs already claimed by a coalesced
         * edge value in this class pass */
        typedef struct { int blk, reg; } Coal;
        Coal *coal = malloc(sizeof(Coal) * (size_t)(ni > 0 ? ni : 1));
        int ncoal = 0;
        int na = 0;
        bool *regused = calloc((size_t)npool, 1);
        int *regowner_end = calloc((size_t)npool, sizeof(int));
        (void)regowner_end;
        int spill_counter = 0;
        for (int i = 0; i < ni; i++) {
            Iv *iv = &ivs[i];
            /* expire: strictly-before only. An interval ending AT
             * the incoming start is still occupying its register at
             * that position: its last use is the instruction there,
             * which is the very instruction that defines the incoming
             * value, and an operand's register may be reused for a
             * result only through the emitter-aware 2-address path
             * below, never by freeing it here. (Freeing at == once
             * let a shift result take its shift-count operand's
             * register; the emitter read the count after the copy
             * and 679 battery cases miscompiled.) */
            int wn = 0;
            for (int j = 0; j < na; j++) {
                if (act[j].end < iv->start) { regused[act[j].reg] = false; }
                else act[wn++] = act[j];
            }
            na = wn;
            /* Back-edge coalescing: a value whose only use is as the
             * branch argument for parameter pv of the target block can
             * be computed directly into pv's register when pv is
             * already allocated there, pv has no use after the
             * definition inside the source block (the terminator's own
             * argument lists and condition included), and pv's active
             * entry still guards the register. The successor value
             * then lands in the parameter's register with no edge
             * move -- the loop-carried update shape (accumulators,
             * indices). pv's entry is marked protected so a later
             * spill decision cannot hand the register away under the
             * coalesced value, and at most one value per
             * (block, register) coalesces, so two edge values never
             * share a register in one block. */
            bool coalesced = false;
            if (defins[iv->v] && defblk[iv->v] >= 0) {
                Block *sb0 = &f->blocks[defblk[iv->v]];
                Instr *term0 = sb0->nins > 0 ? &sb0->ins[sb0->nins - 1] : NULL;
                /* Every terminator-arg occurrence of this value is a
                 * candidate target (WP16). A loop body's updated
                 * values are passed to BOTH the back edge and the
                 * exit edge of the same condbr, so the historical
                 * sole-use rule (usecnt == 1) never fired for them
                 * and the edge moves shuffled every loop-carried
                 * pointer through scratch registers each iteration.
                 * The census must account for exactly these
                 * occurrences -- no other use anywhere; the
                 * folded-use expansion keeps that conservative,
                 * since any folded involvement inflates the census
                 * past the occurrence count and skips the value. */
                int occ_lst[8], occ_slot[8], occ_tgt[8], nocc = 0;
                if (term0 && term0->op == OP_BR) {
                    for (int k = 0; k < term0->nargs; k++)
                        if (term0->args[k] == iv->v && nocc < 8) { occ_lst[nocc] = 0; occ_slot[nocc] = k; occ_tgt[nocc] = term0->blk; nocc++; }
                } else if (term0 && term0->op == OP_CONDBR) {
                    for (int k = 0; k < term0->nargs; k++)
                        if (term0->args[k] == iv->v && nocc < 8) { occ_lst[nocc] = 0; occ_slot[nocc] = k; occ_tgt[nocc] = term0->blk; nocc++; }
                    for (int k = 0; k < term0->nargs2; k++)
                        if (term0->args2[k] == iv->v && nocc < 8) { occ_lst[nocc] = 1; occ_slot[nocc] = k; occ_tgt[nocc] = term0->blk2; nocc++; }
                }
                if (nocc > 0 && usecnt[iv->v] == nocc) {
                for (int oi = 0; oi < nocc && !coalesced; oi++) {
                int tb = occ_tgt[oi], slot = occ_slot[oi], lst = occ_lst[oi];
                Block *tblk = &f->blocks[tb];
                int pv = slot < tblk->nargs ? tblk->arg_vals[slot] : -1;
                Instr *dd = defins[iv->v];
                if (pv >= 0 && pv != iv->v &&
                    bf->vclass[pv] == cls && bf->loc[pv].is_reg && bf->loc[pv].cls == cls &&
                    dd->op != OP_CALL && dd->op != OP_TAILCALL && dd->op != OP_CALLI && dd->op != OP_TAILCALLI && dd->op != OP_FMA &&
                    dd->op != OP_MEMCPY && dd->op != OP_MEMSET && dd->op != OP_ALLOCA) {
                    Block *sb = &f->blocks[defblk[iv->v]];
                    Instr *term = &sb->ins[sb->nins - 1];
                    bool ok = term->op == OP_BR || term->op == OP_CONDBR;
                    if (ok && lst == 0 && term->blk != tb) ok = false;
                    if (ok && lst == 1 && term->blk2 != tb) ok = false;
                    if (ok) {
                        const int *lp = lst == 0 ? term->args : term->args2;
                        int nl = lst == 0 ? term->nargs : term->nargs2;
                        if (slot >= nl || lp[slot] != iv->v) ok = false;
                        if (term->a == pv) ok = false;
                        for (int k = 0; k < term->nargs && ok; k++) if (term->args[k] == pv) ok = false;
                        for (int k = 0; k < term->nargs2 && ok; k++) if (term->args2[k] == pv) ok = false;
                    }
                    for (int i = defidx[iv->v] + 1; ok && i < sb->nins - 1; i++) {
                        Instr *u = &sb->ins[i];
                        if (u->a == pv || u->b == pv || (u->op != OP_ALLOCA && u->c == pv)) ok = false;
                        for (int k = 0; k < u->nargs && ok; k++) if (u->args[k] == pv) ok = false;
                        for (int k = 0; k < u->nargs2 && ok; k++) if (u->args2[k] == pv) ok = false;
                    }
                    if (ok) {
                        int pr = -1;
                        for (int r = 0; r < npool; r++) if (pool[r].reg == bf->loc[pv].idx) { pr = r; break; }
                        if (pr < 0) ok = false;
                        if (ok && REG_FORBIDDEN(iv->v, pool[pr])) ok = false;
                        if (ok && iv->cross && !pool[pr].callee_saved) ok = false;
                        int aj = -1;
                        for (int j = 0; ok && j < na; j++) if (act[j].v == pv && act[j].reg == pr) { aj = j; break; }
                        if (aj < 0) ok = false;
                        for (int j = 0; ok && j < ncoal; j++) if (coal[j].blk == defblk[iv->v] && coal[j].reg == pr) ok = false;
                        if (ok) {
                            bf->loc[iv->v] = bf->loc[pv];
                            act[aj].prot = true;
                            /* The coalesced value occupies pv's
                             * register from its own definition to
                             * its last use (the edge), but no Act
                             * entry of its own records that span --
                             * pv's entry ends at pv's last in-block
                             * use, which can be long before (an
                             * accumulator updated early in a wide
                             * unrolled body). Without this extension
                             * the register looks free in between and
                             * a later value is allocated into it,
                             * clobbering the edge value. */
                            if (iv->end > act[aj].end) act[aj].end = iv->end;
                            coal[ncoal].blk = defblk[iv->v]; coal[ncoal].reg = pr; ncoal++;
                            coalesced = true;
                        }
                    }
                }
                } /* for each occurrence */
                } /* census == occurrences */
                } /* defining block has a branch terminator */
            if (!coalesced) {
            /* choose a register: if crossing, callee-saved only;
             * prefer caller-saved for non-crossing (preserve callee regs) */
            int pick = -1;

            /* 2-address / accumulator reuse preference:
             * If iv->v is defined by an operation whose first operand a dies at iv->start,
             * and a is allocated to a register in this pool, reuse that register! */
            Instr *d = defins[iv->v];
            if (d && (d->op == OP_VADD || d->op == OP_VSUB || d->op == OP_VMUL || d->op == OP_VLSHR ||
                      d->op == OP_VWIDEN ||
                      d->op == OP_ADD || d->op == OP_SUB || d->op == OP_MUL ||
                      d->op == OP_AND || d->op == OP_OR || d->op == OP_XOR ||
                      d->op == OP_ZEXT || d->op == OP_TRUNC)) {
                int a = d->a;
                if (a >= 0 && bf->vclass[a] == cls && bf->loc[a].is_reg &&
                    bf->endpos[a] == iv->start) {
                    int r_id = bf->loc[a].idx;
                    for (int r = 0; r < npool; r++) {
                        if (pool[r].reg == r_id) {
                            bool cs = pool[r].callee_saved != 0;
                            if ((!iv->cross || cs) && !REG_FORBIDDEN(iv->v, pool[r])) {
                                for (int j = 0; j < na; j++) {
                                    if (act[j].reg == r) {
                                        act[j] = act[--na];
                                        break;
                                    }
                                }
                                regused[r] = false;
                                pick = r;
                            }
                            break;
                        }
                    }
                }
            }

            for (int pass = 0; pass < 2 && pick < 0; pass++) {
                for (int r = 0; r < npool; r++) {
                    if (regused[r]) continue;
                    if (REG_FORBIDDEN(iv->v, pool[r])) continue;
                    bool cs = pool[r].callee_saved != 0;
                    if (iv->cross && !cs) continue;
                    if (pass == 0 && !iv->cross && cs) continue; /* first pass: caller-saved */
                    if (pass == 0 && iv->cross) { /* only cs considered */ }
                    pick = r; break;
                }
            }
            if (pick >= 0) {
                regused[pick] = true;
                act[na].start = iv->start; act[na].end = iv->end; act[na].reg = pick; act[na].v = iv->v; act[na].callee = pool[pick].callee_saved != 0; act[na].prot = false; na++;
                bf->loc[iv->v].is_reg = 1;
                bf->loc[iv->v].cls = (int8_t)cls;
                bf->loc[iv->v].idx = pool[pick].reg;
            } else {
                /* SpillAtInterval, weight form: among the eligible
                 * active intervals, evict the one with the lowest
                 * spill weight (total dynamic use cost, loop uses
                 * counted 16x, constants 0); ties break by Belady
                 * next-use distance. If the incoming interval is
                 * itself the cheapest, spill it instead. A use at
                 * the current position (an operand of the defining
                 * instruction) is never chosen unless the candidate
                 * is a rematerializable constant. Coalesced (prot)
                 * intervals and the call-crossing callee rule remain
                 * hard constraints. */
                int furthest = -1;
                /* the incoming interval also counts the store its
                 * own spill would pay at its definition (an evicted
                 * interval pays only reloads), as one extra use at
                 * the incoming interval's own loop depth */
                int best_w = ivweight[iv->v];
                {
                    int inl = 0;
                    for (int e = 0; e < nbe; e++) if (be_hp[e] <= iv->start && iv->start <= be_lp[e]) { inl = 1; break; }
                    best_w += inl ? 16 : 1;
                }
                int best_next = nu_next_use(usepos, useoff[iv->v], useoff[iv->v + 1],
                                            iv->start, iv->start, iv->end,
                                            be_hp, be_lp, nbe);
                for (int j = 0; j < na; j++) {
                    if (act[j].prot) continue;
                    if (REG_FORBIDDEN(iv->v, pool[act[j].reg])) continue;
                    if (iv->cross && !act[j].callee) continue;
                    int nu = nu_next_use(usepos, useoff[act[j].v], useoff[act[j].v + 1],
                                         iv->start, act[j].start, act[j].end,
                                         be_hp, be_lp, nbe);
                    int wj = ivweight[act[j].v];
                    if (wj > 0 && nu <= iv->start) continue;  /* operand of this instruction */
                    if (wj < best_w || (wj == best_w && nu > best_next)) {
                        best_w = wj;
                        best_next = nu;
                        furthest = j;
                    }
                }
                if (furthest >= 0) {
                    int evict_val = act[furthest].v;
                    int r = act[furthest].reg;
                    bf->loc[evict_val].is_reg = 0;
                    bf->loc[evict_val].cls = (int8_t)cls;
                    bf->loc[evict_val].idx = spill_counter++;

                    act[furthest].start = iv->start;
                    act[furthest].end = iv->end;
                    act[furthest].v = iv->v;
                    act[furthest].callee = pool[r].callee_saved != 0;
                    act[furthest].prot = false;
                    bf->loc[iv->v].is_reg = 1;
                    bf->loc[iv->v].cls = (int8_t)cls;
                    bf->loc[iv->v].idx = pool[r].reg;
                } else {
                    bf->loc[iv->v].is_reg = 0;
                    bf->loc[iv->v].cls = (int8_t)cls;
                    bf->loc[iv->v].idx = spill_counter++;
                }
            }
            } /* if (!coalesced) */
        }
        if (spill_counter > maxslots) maxslots = spill_counter;
        free(ivs); free(act); free(coal); free(regused); free(regowner_end);
    }
    free(defins); free(defblk); free(defidx); free(usecnt);
    free(forbid);
    free(usepos); free(useoff); free(ivweight);
    free(be_hp); free(be_lp);
    free(use_tgt); free(use_slot); free(use_list); free(use_srcblk);
    bf->nspill_gp = 0; bf->nspill_fp = 0;
    for (int v = 0; v < f->nvalues; v++)
        if (!bf->loc[v].is_reg && bf->vclass[v] == BCLS_GP) bf->nspill_gp++;
        else if (!bf->loc[v].is_reg && bf->vclass[v] == BCLS_FP && f->vtypes[v].kind != TY_VEC) bf->nspill_fp++;
    /* vector values: stack-resident if not in register */
    {
        int unit = 0;
        /* units counted after scalar slots are known: defer offset fixup.
         * Units are 16 bytes; a vector value occupies
         * n * (pools->vec_bytes ? pools->vec_bytes : 16) bytes. */
        int vunits = (pools->vec_bytes ? pools->vec_bytes : 16) / 16;
        if (vunits < 1) vunits = 1;
        for (int v = 0; v < f->nvalues; v++)
            if (f->vtypes[v].kind == TY_VEC) {
                if (!bf->loc[v].is_reg) {
                    bf->loc[v].is_reg = 0; bf->loc[v].cls = BCLS_VEC; bf->loc[v].idx = unit;
                    unit += f->vtypes[v].n * vunits;
                }
            }
        /* i128 values (v3.0): always memory-resident, one 16-byte unit
         * each in the same area; emitters compute on the (lo, hi) pair
         * through scratch registers. */
        for (int v = 0; v < f->nvalues; v++)
            if (bf->vclass[v] == BCLS_MEM128 && bf->loc[v].idx < 0) {
                bf->loc[v].is_reg = 0; bf->loc[v].cls = BCLS_MEM128; bf->loc[v].idx = unit;
                unit += 1;
            }
        bf->nalloca = unit; /* temporarily stash unit count; fixed below */
    }
    /* Assign scalar slot indices uniquely (allocator used per-class counters;
     * merge GP+FP spills into one slot space) */
    {
        int next = 0;
        for (int cls = 0; cls < 2; cls++) {
            /* map old per-class slot idx -> new global idx, per class */
            int mx = 0;
            for (int v = 0; v < f->nvalues; v++)
                if (bf->vclass[v] == cls && !bf->loc[v].is_reg && bf->loc[v].idx >= 0 && f->vtypes[v].kind != TY_VEC && bf->loc[v].idx >= mx) mx = bf->loc[v].idx + 1;
            int *map = malloc(sizeof(int) * (size_t)(mx > 0 ? mx : 1));
            for (int i = 0; i < mx; i++) map[i] = next++;
            for (int v = 0; v < f->nvalues; v++)
                if (bf->vclass[v] == cls && !bf->loc[v].is_reg && bf->loc[v].idx >= 0 && f->vtypes[v].kind != TY_VEC) bf->loc[v].idx = map[bf->loc[v].idx];
            free(map);
        }
        int total_scalar_slots = next;
        /* callee-saved registers actually used get save slots ahead of the
         * spill area (offsets 16, 24, ... in list order) */
        bf->nsave_gp = 0; bf->nsave_fp = 0;
        for (int cls = 0; cls < 2; cls++) {
            const PoolReg *pool = cls == BCLS_GP ? pools->gp : pools->fp;
            int npool = cls == BCLS_GP ? pools->ngp : pools->nfp;
            if (!pool) continue;
            for (int r = 0; r < npool; r++) {
                if (!pool[r].callee_saved) continue;
                for (int v = 0; v < f->nvalues; v++) {
                    if (bf->vclass[v] == cls && bf->loc[v].is_reg && bf->loc[v].idx == pool[r].reg) {
                        if (cls == BCLS_GP && bf->nsave_gp < 24) bf->save_gp[bf->nsave_gp++] = pool[r].reg;
                        if (cls == BCLS_FP && bf->nsave_fp < 24) bf->save_fp[bf->nsave_fp++] = pool[r].reg;
                        break;
                    }
                }
            }
        }
        int slot_base = 16 + 8 * (bf->nsave_gp + bf->nsave_fp);
        bf->slot_base = slot_base;
        int vec_unit_total = bf->nalloca;
        int alloca_bytes = 0;
        for (int b = 0; b < f->nblocks; b++)
            for (int i = 0; i < f->blocks[b].nins; i++) {
                Instr *in = &f->blocks[b].ins[i];
                if (in->op == OP_ALLOCA) {
                    int al = in->c > 0 ? in->c : 1;
                    /* Base addressing (WP34): the alloca value is the
                     * region's LOWEST byte. Emitters form it as
                     * frame_base - allo_off and accesses run upward
                     * ([ptr + k] for k in [0, size)), so allo_off must
                     * be the offset of the region's far edge: the
                     * cumulative END of the region, rounded up to the
                     * requested alignment so the pointer itself is
                     * aligned (the interpreter's bump allocator
                     * guarantees the same). The historical form sampled
                     * the cumulative START — the region's top edge — so
                     * a store at byte k >= 1 landed outside the region,
                     * in whatever the frame keeps at smaller offsets:
                     * vector area, scalar slots, and for k in 8..32 the
                     * callee-save slots. A 64-byte alloca's stores at
                     * bytes 8/16/24 overwrote the saved r14/r13/r12 and
                     * the epilogue restored the stored values into
                     * those registers (WP34 repro). Bounded now: byte k
                     * of region j lands at allo_base + allo_off_j - k,
                     * which stays within (allo_base + prev_end,
                     * allo_base + allo_off_j] — inside region j. */
                    alloca_bytes += (int)in->imm;
                    alloca_bytes = (alloca_bytes + al - 1) & ~(al - 1);
                    bf->allo_off[be_pos(bf, b, i)] = alloca_bytes;
                }
            }
        /* max outgoing stack args (beyond the register file) — targets pass
         * up to 8 in regs here; overflow area: nargs beyond 6 GP/8 FP.
         * Reserve generously: nargs*8 capped at 256. */
        int outb = 0;
        for (int b = 0; b < f->nblocks; b++)
            for (int i = 0; i < f->blocks[b].nins; i++) {
                Instr *in = &f->blocks[b].ins[i];
                if ((in->op == OP_CALL || in->op == OP_TAILCALL || in->op == OP_CALLI || in->op == OP_TAILCALLI) && in->nargs * 8 > outb) outb = in->nargs * 8;
            }
        /* The vector area must begin at a 16-byte boundary from the
         * frame base: slot chunks are addressed in 16-byte units from
         * vec_base, and vector ops may fold a slot operand as an SSE
         * memory operand, which faults (#GP, delivered as SIGSEGV
         * with no fault address) unless 16-byte aligned. The frame
         * base register is 16-byte aligned (frame_bytes is a multiple
         * of 16 over an ABI-aligned entry stack), so aligning vec_base
         * here aligns every vector slot. slot_base + scalar slots is
         * a multiple of 8, so the pad is 0 or 8; with an odd
         * (nsave + scalar slots) count every vector slot used to sit
         * at offset 8 mod 16 and any folded vector op crashed. */
        int vec_base = slot_base + total_scalar_slots * 8;
        vec_base = (vec_base + 15) & ~15;
        int allo_base = vec_base + vec_unit_total * 16;
        int frame = vec_base + vec_unit_total * 16 + alloca_bytes + outb;
        frame = (frame + 15) & ~15;
        bf->frame_bytes = frame;
        bf->out_bytes = outb;
        bf->nalloca = alloca_bytes;
        /* now compute byte offsets */
        for (int v = 0; v < f->nvalues; v++) {
            if ((bf->loc[v].cls == BCLS_VEC || bf->loc[v].cls == BCLS_MEM128) && !bf->loc[v].is_reg) {
                /* Emitters address a vector value's bytes as
                 * [base - (off - chunk)] for chunk in [0, bytes):
                 * off is the distance from the frame base to the
                 * value's LOWEST byte, so the value's own units sit
                 * between its first unit and off. off = vec_base +
                 * (first unit + own units) * 16 — for a 16-byte value
                 * this is the historical (idx + 1) * 16; the old
                 * idx * 16 form put every wider value's top chunk
                 * across the frame base (WP21-B fix; n >= 2 slot
                 * vectors at vl 4 were already corrupt the same way). */
                int vunits = (pools->vec_bytes ? pools->vec_bytes : 16) / 16;
                if (vunits < 1) vunits = 1;
                int own = bf->loc[v].cls == BCLS_MEM128 ? 1 : f->vtypes[v].n * vunits;
                bf->vec_off[v] = vec_base + (bf->loc[v].idx + own) * 16;
                bf->loc[v].off = bf->vec_off[v];
            } else if (bf->vclass[v] >= 0 && !bf->loc[v].is_reg) {
                if (bf->loc[v].idx >= 0) bf->loc[v].off = slot_base + bf->loc[v].idx * 8;
            }
        }
        for (int i = 0; i < bf->maxpos; i++)
            if (bf->allo_off[i] >= 0) bf->allo_off[i] += allo_base;
        /* outgoing args live at the very bottom: offsets from frame base are
         * stored as (frame_bytes - outb + 8*k) relative to frame pointer —
         * emitters compute against their frame base register. We expose it
         * via allo_off-style accessor: store outb and let emitters use
         * (bf->frame_bytes - bf->out_bytes). */
    }
    return bf;
}

int be_loc_off(const BeFunc *bf, int v) { return bf->loc[v].off; }

void be_free(BeFunc *bf) {
    if (!bf) return;
    free(bf->defpos); free(bf->endpos); free(bf->crosscall);
    free(bf->vclass); free(bf->loc); free(bf->vec_off);
    free(bf->blkstart); free(bf->allo_off);
    free(bf);
}

/* ---------- parallel moves ---------- */
void be_parallel_move(void *ctx, MoveFn mv, const Loc *srcs, const Loc *dsts, int n, Loc scratch) {
    if (n <= 0) return;
    Loc *s = malloc(sizeof(Loc) * (size_t)n);
    Loc *d = malloc(sizeof(Loc) * (size_t)n);
    int m = 0;
    for (int i = 0; i < n; i++) {
        if (srcs[i].is_reg == dsts[i].is_reg && srcs[i].idx == dsts[i].idx && srcs[i].cls == dsts[i].cls) continue;
        s[m] = srcs[i]; d[m] = dsts[i]; m++;
    }
    /* repeatedly emit moves whose dst is not a pending source */
    int remaining = m;
    while (remaining > 0) {
        bool progress = false;
        for (int i = 0; i < m; i++) {
            if (d[i].idx == -2) continue; /* done marker */
            bool blocked = false;
            for (int j = 0; j < m; j++) {
                if (j == i || d[j].idx == -2) continue;
                if (s[j].is_reg == d[i].is_reg && s[j].idx == d[i].idx && s[j].cls == d[i].cls) { blocked = true; break; }
            }
            if (!blocked) {
                mv(ctx, d[i], s[i]);
                d[i].idx = -2;
                remaining--;
                progress = true;
            }
        }
        if (!progress) {
            /* cycle: stash the first pending source in scratch */
            for (int i = 0; i < m; i++) {
                if (d[i].idx == -2) continue;
                mv(ctx, scratch, s[i]);
                s[i] = scratch;
                break;
            }
        }
    }
    free(s); free(d);
}
