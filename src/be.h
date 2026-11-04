/* Krell backends — shared kit: liveness, live intervals, linear-scan
 * allocation, parallel-move resolution, frame layout. Target emitters
 * consume the analysis; they never re-derive it. */
#ifndef KRELL_BE_H
#define KRELL_BE_H

#include "krell.h"

/* value classes for allocation */
enum { BCLS_GP = 0, BCLS_FP = 1, BCLS_VEC = 2, BCLS_MEM128 = 3 };

/* a location: a register (target numbering) or a stack slot */
typedef struct {
    int8_t  is_reg;   /* 1 register, 0 stack */
    int8_t  cls;      /* BCLS_* */
    int32_t idx;      /* register id, or slot index */
    int32_t off;      /* stack: byte offset below the frame pointer */
} Loc;

typedef struct {
    int reg;
    int callee_saved;
} PoolReg;

typedef struct BeFunc {
    Func  *f;
    int    nvals;
    int   *defpos;      /* position of definition */
    int   *endpos;      /* last position the value is live */
    bool  *crosscall;   /* live across a call */
    int8_t *vclass;     /* BCLS_* per value, -1 for void */
    Loc   *loc;         /* allocation result per value */
    int   *blkstart;    /* position of each block's start */
    int   *allo_off;    /* per position: alloca byte offset (or -1) */
    int    frame_bytes; /* total local frame (16-aligned) */
    int    out_bytes;   /* outgoing stack-args area size */
    int    nalloca;     /* bytes of alloca area */
    int    maxpos;
    /* backend scratch usage flags */
    int    nspill_gp, nspill_fp;
    int32_t *vec_off;   /* per value: byte offset if vector-typed */
    /* callee-saved registers actually used (register ids), with their
     * save-slot byte offsets (16 + 8*i in list order, gp first then fp) */
    int    save_gp[24]; int nsave_gp;
    int    save_fp[24]; int nsave_fp;
    int    slot_base;   /* byte offset of spill slot 0 */
} BeFunc;

/* register pools a target offers, per class */
typedef struct {
    const PoolReg *gp;  int ngp;
    const PoolReg *fp;  int nfp;
    /* 1 if the backend's emission handles register-resident vector
     * values (x86_64); 0 if vectors must be memory-resident, as the
     * aarch64/riscv64 emitters assume -- they address every vector
     * through its slot offset, and a register-assigned vector keeps
     * offset 0, which made simultaneously live vectors collide on
     * one address and corrupted the frame (both qemu batteries
     * segfaulted on it once the allocator kept vectors in
     * registers). With vec_regs == 0 the allocator classes every
     * vector value BCLS_VEC and gives it a real slot. */
    int vec_regs;
} Pools;

/* position of instruction ii in block bi */
static inline int be_pos(const BeFunc *bf, int bi, int ii) { return bf->blkstart[bi] + 1 + ii; }

BeFunc *be_analyze(Module *m, Func *f, const Pools *pools);
BeFunc *be_analyze_ext(Module *m, Func *f, const Pools *pools, const bool *folded);
void    be_free(BeFunc *bf);
int     be_class_of(Type t);
/* byte offset (below frame ptr) for a stack Loc / vector value */
int     be_loc_off(const BeFunc *bf, int v);

/* parallel moves: emit elementary moves via callback, breaking cycles
 * with `scratch` (a register Loc of the same class). */
typedef void (*MoveFn)(void *ctx, Loc dst, Loc src);
void be_parallel_move(void *ctx, MoveFn mv, const Loc *srcs, const Loc *dsts, int n, Loc scratch);

/* shared helpers for emitters */
bool be_iconst_val(Func *f, int v, int64_t *out);  /* value is a known integer constant */
void be_err(char *err, size_t cap, const char *msg);

#endif /* KRELL_BE_H */
