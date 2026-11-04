/* Krell-IR — core data structures and APIs.
 * One header for the whole toolchain: IR, binary format, verifier,
 * interpreter, cost oracle, optimizer, backends. See docs/SPEC.md and
 * docs/SEMANTICS.md. */
#ifndef KRELL_H
#define KRELL_H

#include <stdint.h>
#include <stdbool.h>
#include <stddef.h>
#include <stdlib.h>
#include <string.h>
#include <stdio.h>

/* ---------------- types ---------------- */
enum { TY_VOID = 0, TY_INT = 1, TY_FLOAT = 2, TY_PTR = 3, TY_VEC = 4 };

typedef struct {
    uint8_t kind;      /* TY_* */
    uint8_t bits;      /* INT: 1,8,16,32,64 ; FLOAT: 32,64 */
    uint8_t elem_kind; /* VEC only: TY_INT or TY_FLOAT */
    uint8_t elem_bits; /* VEC only */
    uint8_t n;         /* VEC only: vscale count (lanes = n * VL) */
} Type;

static inline Type ty_void(void) { Type t = { TY_VOID, 0, 0, 0, 0 }; return t; }
static inline Type ty_int(int bits) { Type t = { TY_INT, (uint8_t)bits, 0, 0, 0 }; return t; }
static inline Type ty_i1(void) { return ty_int(1); }
static inline Type ty_i8(void) { return ty_int(8); }
static inline Type ty_i16(void) { return ty_int(16); }
static inline Type ty_i32(void) { return ty_int(32); }
static inline Type ty_i64(void) { return ty_int(64); }
static inline Type ty_f32(void) { Type t = { TY_FLOAT, 32, 0, 0, 0 }; return t; }
static inline Type ty_f64(void) { Type t = { TY_FLOAT, 64, 0, 0, 0 }; return t; }
static inline Type ty_ptr(void) { Type t = { TY_PTR, 64, 0, 0, 0 }; return t; }
static inline Type ty_vec(Type elem, int n) {
    Type t = { TY_VEC, 0, elem.kind, elem.bits, (uint8_t)n }; return t;
}
static inline bool ty_eq(Type a, Type b) { return memcmp(&a, &b, sizeof(Type)) == 0; }
static inline bool ty_is_int(Type t) { return t.kind == TY_INT; }
static inline bool ty_is_float(Type t) { return t.kind == TY_FLOAT; }
static inline bool ty_is_vec(Type t) { return t.kind == TY_VEC; }
static inline bool ty_is_scalar(Type t) { return t.kind == TY_INT || t.kind == TY_FLOAT || t.kind == TY_PTR; }
/* byte size of a scalar type (vectors handled separately) */
static inline int ty_bytes(Type t) {
    if (t.kind == TY_PTR) return 8;
    if (t.kind == TY_FLOAT) return t.bits / 8;
    if (t.kind == TY_INT) return t.bits <= 8 ? 1 : t.bits / 8;
    return 0;
}
/* element type of a vector */
static inline Type ty_elem(Type t) {
    Type e = { t.elem_kind, t.elem_bits, 0, 0, 0 }; return e;
}

/* ---------------- opcodes ---------------- */
enum {
    OP_ICONST = 1, OP_FCONST, OP_FREEZE,
    OP_ADD, OP_SUB, OP_MUL, OP_UDIV, OP_SDIV, OP_UREM, OP_SREM,
    OP_NEG, OP_AND, OP_OR, OP_XOR, OP_NOT, OP_SHL, OP_LSHR, OP_ASHR,
    OP_ICMP, OP_POPCOUNT, OP_CLZ, OP_CTZ, OP_BSWAP,
    OP_TRUNC, OP_ZEXT, OP_SEXT,
    OP_FADD, OP_FSUB, OP_FMUL, OP_FDIV, OP_FNEG, OP_FABS, OP_FMA, OP_FCMP,
    OP_FTRUNC, OP_FEXT, OP_FPTOSI, OP_FPTOUI, OP_SITOFP, OP_UITOFP, OP_BITCAST,
    OP_ALLOCA, OP_LOAD, OP_STORE, OP_GEP, OP_MEMCPY, OP_MEMSET, OP_DATAPTR,
    OP_VSPLAT, OP_VADD, OP_VSUB, OP_VMUL, OP_VUDIV,
    OP_VFADD, OP_VFSUB, OP_VFMUL, OP_VFDIV, OP_VAND, OP_VOR, OP_VXOR,
    OP_VLOAD, OP_VSTORE, OP_VEXTRACT, OP_VINSERT,
    OP_ALOAD, OP_ASTORE, OP_AADD,
    OP_BR, OP_CONDBR, OP_RET, OP_CALL, OP_TAILCALL, OP_SELECT, OP_ASSUME,
    OP_VLSHR,   /* appended: existing opcode numbers are binary-format */
    OP_COUNT
};
/* icmp predicates */
enum { IC_EQ, IC_NE, IC_ULT, IC_ULE, IC_UGT, IC_UGE, IC_SLT, IC_SLE, IC_SGT, IC_SGE };
/* fcmp predicates */
enum { FC_OEQ, FC_ONE, FC_OLT, FC_OLE, FC_OGT, FC_OGE,
       FC_UEQ, FC_UNE, FC_ULT, FC_ULE, FC_UGT, FC_UGE, FC_ORD, FC_UNO };
/* atomic orderings */
enum { AO_RELAXED = 0, AO_ACQREL = 1, AO_SEQCST = 2 };

const char *op_name(int op);
bool op_is_pure(int op);        /* no side effects, hash-consable */
bool op_is_terminator(int op);

/* ---------------- IR structures ---------------- */
typedef struct {
    uint8_t  op;
    Type     ty;          /* result type (TY_VOID if none) */
    int32_t  a, b, c;     /* value operands, -1 if unused */
    int64_t  imm;         /* iconst payload / fconst bits / size / lane / data idx */
    uint8_t  pred;        /* icmp/fcmp predicate */
    uint8_t  aux;         /* atomic ordering, call flags */
    int32_t  result;      /* value id of result, -1 if none */
    /* control / calls */
    Type     ety;                     /* GEP element type */
    int32_t  blk;                     /* br/condbr first target */
    int32_t  blk2;                    /* condbr second target */
    int32_t  callee;                  /* func or extern index */
    uint8_t  callee_extern;           /* callee indexes the extern table */
    int32_t *args;  uint16_t nargs;   /* call args / br args */
    int32_t *args2; uint16_t nargs2;  /* condbr false-branch args */
} Instr;

typedef struct {
    Type    *arg_types;
    int32_t *arg_vals;    /* value ids of the block's arguments */
    int      nargs;
    Instr   *ins;
    int      nins, cap;
} Block;

#define FUNC_PURE 1u

typedef struct Func {
    char    *name;
    Type     ret;
    uint8_t  flags;
    Block   *blocks;
    int      nblocks, capblocks;
    int      nvalues;         /* next value id */
    /* hash-cons table for pure ops (per function); opaque, owned by ir.c */
    void *cons;
    /* integer/float constant tracking per value (bit patterns) */
    uint64_t *cval; uint8_t *isconst; int cvalcap;
    /* per-value type table */
    Type    *vtypes; int vcap;
} Func;

typedef struct {
    char *name;
    Type *params; int nparams;
    Type  ret;
} Extern;

typedef struct {
    char    *name;
    uint32_t align;
    uint8_t *bytes;
    uint32_t len;
} DataBlob;

typedef struct Module {
    Func    *funcs;  int nfuncs,  capfuncs;
    Extern  *exts;   int nexts,   capexts;
    DataBlob *data;  int ndata,   capdata;
} Module;

/* ---------------- builder (ir.c) ---------------- */
Module *mod_new(void);
void    mod_free(Module *m);
int     mod_add_extern(Module *m, const char *name, const Type *params, int n, Type ret);
int     mod_add_data(Module *m, const char *name, uint32_t align, const void *bytes, uint32_t len);
Func   *mod_add_func(Module *m, const char *name, Type ret, uint8_t flags);
int     mod_find_func(Module *m, const char *name);
int     mod_find_extern(Module *m, const char *name);

int     func_add_block(Func *f, const Type *argtypes, int nargs);
Instr   ins_make(uint8_t op, Type ty);
int     emit(Func *f, int blk, Instr in);            /* returns result id or -1 */
int     emit_pure(Func *f, int blk, Instr in);       /* hash-consed + folded */
/* convenience constructors */
Instr   ins_iconst(Type ty, int64_t v);
Instr   ins_fconst(Type ty, uint64_t bits);
Instr   ins_bin(uint8_t op, Type ty, int a, int b);
Instr   ins_un(uint8_t op, Type ty, int a);
Instr   ins_br(int blk, int32_t *args, int n);
Instr   ins_condbr(int cond, int b1, int32_t *a1, int n1, int b2, int32_t *a2, int n2);
Instr   ins_ret(int v);          /* v = -1 for void */
Instr   ins_call(Type ret, int callee, bool ext, int32_t *args, int n, bool tail);
int32_t *ids_dup(const int32_t *src, int n);
Type     func_value_type(Func *f, int32_t v);
void     func_rebuild_constants(Func *f);

/* ---------------- binary format (binary.c) ---------------- */
uint8_t *mod_encode(Module *m, size_t *out_len);
Module  *mod_decode(const uint8_t *buf, size_t len, char *err, size_t errcap);
void     mod_hash(Module *m, uint8_t out[32]);   /* sha-256 of canonical encoding */

/* ---------------- text dump (print.c) ---------------- */
void     mod_dump(Module *m, FILE *out);
void     ty_dump(Type t, FILE *out);

/* ---------------- verifier (verify.c) ---------------- */
/* returns NULL on success, else a static error string */
const char *mod_verify(Module *m);
/* target gate: names must match the target ids in the cost files */
const char *mod_verify_target(Module *m, const char *target);

/* ---------------- cost oracle (cost.c) ---------------- */
typedef struct Cost Cost;
Cost *cost_load(const char *target);           /* searches targets/<t>.cost, ./<t>.cost */
void  cost_free(Cost *c);
int   cost_vl_i32(const Cost *c);              /* i32 lanes per vscale unit */
int   cost_lat(const Cost *c, int op, Type t); /* -1 = unknown */
int   cost_thr(const Cost *c, int op, Type t);
bool  cost_cliff(const Cost *c, int op, Type t);
const char *cost_target_name(const Cost *c);

/* ---------------- interpreter (interp.c) ---------------- */
typedef struct Interp Interp;
typedef struct { uint64_t *lanes; } IVal;      /* lanes[0] is the scalar value */
typedef uint64_t (*HostFn)(Interp *it, void *ctx, const IVal *args, int nargs, IVal *ret);

Interp *interp_new(Module *m);
void    interp_free(Interp *it);
void    interp_host(Interp *it, const char *name, HostFn fn, void *ctx);
uint8_t *interp_mem(Interp *it, size_t *size);            /* flat memory base */
uint64_t interp_alloc(Interp *it, size_t size, size_t align); /* bump region for tests */
int      interp_call(Interp *it, const char *funcname, const IVal *args, int nargs, IVal *ret);
int      interp_last_error(Interp *it, char *buf, size_t cap);
uint64_t ival_u64(IVal v);
IVal     ival_make(uint64_t x);
int      ty_lanes(Type t, int vl_i32);         /* lane count of a type given target VL */

/* ---------------- surface syntax (surface.c) ---------------- */
/* Parse the human-readable text form into a module (NULL on error). */
Module *surface_parse(const char *text, char *err, size_t errcap);

/* ---------------- optimizer (opt.c) ---------------- */
typedef struct { int folded, dce, rewritten, blocks_removed; } OptStats;
void opt_optimize(Module *m, const Cost *cost, OptStats *st);

/* ---------------- backends (be_*.c) ---------------- */
/* Emit GNU assembly text for a module to `out`. Returns 0 on success. */
int be_x86_64(Module *m, const Cost *cost, FILE *out, char *err, size_t errcap);
int be_aarch64(Module *m, const Cost *cost, FILE *out, char *err, size_t errcap);
int be_riscv64(Module *m, const Cost *cost, FILE *out, char *err, size_t errcap);
int be_llvm(Module *m, const Cost *cost, FILE *out, char *err, size_t errcap);

#endif /* KRELL_H */
