/* Krell backends — shared kit implementation. */
#include "be.h"

void be_err(char *err, size_t cap, const char *msg) { if (err) snprintf(err, cap, "%s", msg); }

int be_class_of(Type t) {
    switch (t.kind) {
    case TY_INT: case TY_PTR: return BCLS_GP;
    case TY_FLOAT: return BCLS_FP;
    case TY_VEC: return BCLS_VEC;
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
    return x->start < y->start ? -1 : x->start > y->start ? 1 : 0;
}

BeFunc *be_analyze(Module *m, Func *f, const Pools *pools) {
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
        bf->vclass[i] = (int8_t)be_class_of(f->vtypes[i]);
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
            USE(in->a, p); USE(in->b, p); USE(in->c, p);
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
            int32_t ops[3] = { in->a, in->b, in->c };
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
    int maxslots = 0;
    for (int cls = 0; cls < 2; cls++) {
        const PoolReg *pool = cls == BCLS_GP ? pools->gp : pools->fp;
        int npool = cls == BCLS_GP ? pools->ngp : pools->nfp;
        if (!pool || npool == 0) continue;
        Iv *ivs = malloc(sizeof(Iv) * (size_t)nv);
        int ni = 0;
        for (int v = 0; v < f->nvalues; v++)
            if (bf->vclass[v] == cls) {
                ivs[ni].start = bf->defpos[v]; ivs[ni].end = bf->endpos[v];
                ivs[ni].v = v; ivs[ni].cross = bf->crosscall[v]; ni++;
            }
        qsort(ivs, (size_t)ni, sizeof(Iv), cmp_iv);
        /* active list: (end, reg, callee) */
        typedef struct { int end, reg; bool callee; } Act;
        Act *act = malloc(sizeof(Act) * (size_t)(ni > 0 ? ni : 1));
        int na = 0;
        bool *regused = calloc((size_t)npool, 1);
        int *regowner_end = calloc((size_t)npool, sizeof(int));
        (void)regowner_end;
        int spill_counter = 0;
        for (int i = 0; i < ni; i++) {
            Iv *iv = &ivs[i];
            /* expire */
            int wn = 0;
            for (int j = 0; j < na; j++) {
                if (act[j].end < iv->start) { regused[act[j].reg] = false; }
                else act[wn++] = act[j];
            }
            na = wn;
            /* choose a register: if crossing, callee-saved only;
             * prefer caller-saved for non-crossing (preserve callee regs) */
            int pick = -1;
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
                act[na].end = iv->end; act[na].reg = pick; act[na].callee = pool[pick].callee_saved != 0; na++;
                bf->loc[iv->v].is_reg = 1;
                bf->loc[iv->v].cls = (int8_t)cls;
                bf->loc[iv->v].idx = pool[pick].reg;
            } else {
                bf->loc[iv->v].is_reg = 0;
                bf->loc[iv->v].cls = (int8_t)cls;
                bf->loc[iv->v].idx = spill_counter++;
            }
        }
        if (spill_counter > maxslots) maxslots = spill_counter;
        free(ivs); free(act); free(regused); free(regowner_end);
    }
    bf->nspill_gp = 0; bf->nspill_fp = 0;
    for (int v = 0; v < f->nvalues; v++)
        if (!bf->loc[v].is_reg && bf->vclass[v] == BCLS_GP) bf->nspill_gp++;
        else if (!bf->loc[v].is_reg && bf->vclass[v] == BCLS_FP) bf->nspill_fp++;
    /* vector values: always stack-resident */
    {
        int unit = 0;
        /* units counted after scalar slots are known: defer offset fixup */
        for (int v = 0; v < f->nvalues; v++)
            if (bf->vclass[v] == BCLS_VEC) {
                bf->loc[v].is_reg = 0; bf->loc[v].cls = BCLS_VEC; bf->loc[v].idx = unit;
                unit += f->vtypes[v].n;
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
                if (bf->vclass[v] == cls && !bf->loc[v].is_reg && bf->loc[v].idx >= mx) mx = bf->loc[v].idx + 1;
            int *map = malloc(sizeof(int) * (size_t)(mx > 0 ? mx : 1));
            for (int i = 0; i < mx; i++) map[i] = next++;
            for (int v = 0; v < f->nvalues; v++)
                if (bf->vclass[v] == cls && !bf->loc[v].is_reg) bf->loc[v].idx = map[bf->loc[v].idx];
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
            if (bf->vclass[v] == BCLS_VEC) {
                bf->vec_off[v] = vec_base + bf->loc[v].idx * 16;
                bf->loc[v].off = bf->vec_off[v];
            } else if (bf->vclass[v] >= 0 && !bf->loc[v].is_reg) {
                bf->loc[v].off = slot_base + bf->loc[v].idx * 8;
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
