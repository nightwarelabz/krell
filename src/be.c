/* Krell backends — shared kit implementation. */
#include "be.h"
#include <limits.h>

void be_err(char *err, size_t cap, const char *msg) { if (err) snprintf(err, cap, "%s", msg); }

int be_class_of(Type t) {
    switch (t.kind) {
    case TY_INT: case TY_PTR: return BCLS_GP;
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
    return be_analyze_ext(m, f, pools, NULL);
}

BeFunc *be_analyze_ext(Module *m, Func *f, const Pools *pools, const bool *folded) {
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
            if (in->op == OP_CALL || in->op == OP_FMA || in->op == OP_MEMCPY || in->op == OP_MEMSET) {
                /* FMA/memcpy/memset lower to libcalls on some targets: any
                 * value live across them must survive a call */
                if (ncall == callcap) { callcap = callcap ? callcap * 2 : 16; callpos = realloc(callpos, sizeof(int) * (size_t)callcap); }
                callpos[ncall++] = p;
            }
        }
    }
    #define USE(v, p) do { if ((v) >= 0 && (p) > bf->endpos[v]) bf->endpos[v] = (p); } while (0)
    for (int b = 0; b < f->nblocks; b++) {
        Block *bl = &f->blocks[b];
        for (int i = 0; i < bl->nins; i++) {
            Instr *in = &bl->ins[i];
            int p = be_pos(bf, b, i);
            USE(in->a, p); USE(in->b, p);
            if (in->op != OP_ALLOCA) USE(in->c, p);
            for (int k = 0; k < in->nargs; k++) USE(in->args[k], p);
            for (int k = 0; k < in->nargs2; k++) USE(in->args2[k], p);
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
                if (ops[k] >= 0 && !GET(bdef, b, ops[k])) SET(buse, b, ops[k]);
            for (int k = 0; k < in->nargs; k++)
                if (!GET(bdef, b, in->args[k])) SET(buse, b, in->args[k]);
            for (int k = 0; k < in->nargs2; k++)
                if (!GET(bdef, b, in->args2[k])) SET(buse, b, in->args2[k]);
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
            if ((in->op == OP_CALL || in->op == OP_TAILCALL) && in->nargs > out_slots) out_slots = in->nargs;
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
            if (in->a >= 0) usecnt[in->a]++;
            if (in->b >= 0) usecnt[in->b]++;
            if (in->op != OP_ALLOCA && in->c >= 0) usecnt[in->c]++;
            for (int k = 0; k < in->nargs; k++) {
                int v = in->args[k]; if (v < 0) continue; usecnt[v]++;
                if (in->op == OP_BR || in->op == OP_CONDBR) { use_tgt[v] = in->blk; use_slot[v] = k; use_list[v] = 0; use_srcblk[v] = b; }
            }
            for (int k = 0; k < in->nargs2; k++) {
                int v = in->args2[k]; if (v < 0) continue; usecnt[v]++;
                if (in->op == OP_CONDBR) { use_tgt[v] = in->blk2; use_slot[v] = k; use_list[v] = 1; use_srcblk[v] = b; }
            }
        }
    }

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
                if (in->a >= 0 && usecur[in->a] < useoff[in->a + 1]) usepos[usecur[in->a]++] = pos;
                if (in->b >= 0 && usecur[in->b] < useoff[in->b + 1]) usepos[usecur[in->b]++] = pos;
                if (in->op != OP_ALLOCA && in->c >= 0 && usecur[in->c] < useoff[in->c + 1]) usepos[usecur[in->c]++] = pos;
                for (int k = 0; k < in->nargs; k++) { int v = in->args[k]; if (v >= 0 && usecur[v] < useoff[v + 1]) usepos[usecur[v]++] = pos; }
                for (int k = 0; k < in->nargs2; k++) { int v = in->args2[k]; if (v >= 0 && usecur[v] < useoff[v + 1]) usepos[usecur[v]++] = pos; }
            }
        }
        free(usecur);
    }

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
            if (usecnt[iv->v] == 1 && use_tgt[iv->v] >= 0 && defins[iv->v]) {
                int tb = use_tgt[iv->v], slot = use_slot[iv->v], lst = use_list[iv->v];
                Block *tblk = &f->blocks[tb];
                int pv = slot < tblk->nargs ? tblk->arg_vals[slot] : -1;
                Instr *dd = defins[iv->v];
                if (pv >= 0 && pv != iv->v && defblk[iv->v] == use_srcblk[iv->v] &&
                    bf->vclass[pv] == cls && bf->loc[pv].is_reg && bf->loc[pv].cls == cls &&
                    dd->op != OP_CALL && dd->op != OP_TAILCALL && dd->op != OP_FMA &&
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
                        if (ok && iv->cross && !pool[pr].callee_saved) ok = false;
                        int aj = -1;
                        for (int j = 0; ok && j < na; j++) if (act[j].v == pv && act[j].reg == pr) { aj = j; break; }
                        if (aj < 0) ok = false;
                        for (int j = 0; ok && j < ncoal; j++) if (coal[j].blk == defblk[iv->v] && coal[j].reg == pr) ok = false;
                        if (ok) {
                            bf->loc[iv->v] = bf->loc[pv];
                            act[aj].prot = true;
                            coal[ncoal].blk = defblk[iv->v]; coal[ncoal].reg = pr; ncoal++;
                            coalesced = true;
                        }
                    }
                }
            }
            if (!coalesced) {
            /* choose a register: if crossing, callee-saved only;
             * prefer caller-saved for non-crossing (preserve callee regs) */
            int pick = -1;

            /* 2-address / accumulator reuse preference:
             * If iv->v is defined by an operation whose first operand a dies at iv->start,
             * and a is allocated to a register in this pool, reuse that register! */
            Instr *d = defins[iv->v];
            if (d && (d->op == OP_VADD || d->op == OP_VSUB || d->op == OP_VMUL || d->op == OP_VLSHR ||
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
                            if (!iv->cross || cs) {
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
                /* SpillAtInterval, Belady form: among the eligible
                 * active intervals, evict the one whose next use is
                 * farthest from the current position; if the incoming
                 * interval's own next use is farthest of all, spill
                 * it instead. A use at the current position (an
                 * operand of the defining instruction) is the
                 * nearest possible and is never chosen. Coalesced
                 * (prot) intervals and the call-crossing callee rule
                 * remain hard constraints. */
                int furthest = -1;
                int best_next = nu_next_use(usepos, useoff[iv->v], useoff[iv->v + 1],
                                            iv->start, iv->start, iv->end,
                                            be_hp, be_lp, nbe);
                for (int j = 0; j < na; j++) {
                    if (act[j].prot) continue;
                    if (iv->cross && !act[j].callee) continue;
                    int nu = nu_next_use(usepos, useoff[act[j].v], useoff[act[j].v + 1],
                                         iv->start, act[j].start, act[j].end,
                                         be_hp, be_lp, nbe);
                    if (nu > best_next) {
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
    free(usepos); free(useoff);
    free(be_hp); free(be_lp);
    free(use_tgt); free(use_slot); free(use_list); free(use_srcblk);
    bf->nspill_gp = 0; bf->nspill_fp = 0;
    for (int v = 0; v < f->nvalues; v++)
        if (!bf->loc[v].is_reg && bf->vclass[v] == BCLS_GP) bf->nspill_gp++;
        else if (!bf->loc[v].is_reg && bf->vclass[v] == BCLS_FP && f->vtypes[v].kind != TY_VEC) bf->nspill_fp++;
    /* vector values: stack-resident if not in register */
    {
        int unit = 0;
        /* units counted after scalar slots are known: defer offset fixup */
        for (int v = 0; v < f->nvalues; v++)
            if (f->vtypes[v].kind == TY_VEC) {
                if (!bf->loc[v].is_reg) {
                    bf->loc[v].is_reg = 0; bf->loc[v].cls = BCLS_VEC; bf->loc[v].idx = unit;
                    unit += f->vtypes[v].n;
                }
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
                    alloca_bytes = (alloca_bytes + al - 1) & ~(al - 1);
                    bf->allo_off[be_pos(bf, b, i)] = alloca_bytes;
                    alloca_bytes += (int)in->imm;
                }
            }
        /* max outgoing stack args (beyond the register file) — targets pass
         * up to 8 in regs here; overflow area: nargs beyond 6 GP/8 FP.
         * Reserve generously: nargs*8 capped at 256. */
        int outb = 0;
        for (int b = 0; b < f->nblocks; b++)
            for (int i = 0; i < f->blocks[b].nins; i++) {
                Instr *in = &f->blocks[b].ins[i];
                if ((in->op == OP_CALL || in->op == OP_TAILCALL) && in->nargs * 8 > outb) outb = in->nargs * 8;
            }
        int frame = slot_base + total_scalar_slots * 8 + vec_unit_total * 16 + alloca_bytes + outb;
        frame = (frame + 15) & ~15;
        bf->frame_bytes = frame;
        bf->out_bytes = outb;
        bf->nalloca = alloca_bytes;
        /* now compute byte offsets */
        int vec_base = slot_base + total_scalar_slots * 8;
        int allo_base = vec_base + vec_unit_total * 16;
        for (int v = 0; v < f->nvalues; v++) {
            if (bf->loc[v].cls == BCLS_VEC && !bf->loc[v].is_reg) {
                bf->vec_off[v] = vec_base + bf->loc[v].idx * 16;
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
