/* Krell-IR — module structures, builder, hash-consing, constant folding. */
#include "krell.h"

static void cons_free(Func *f);
static char *xstrdup(const char *s) {
    size_t n = strlen(s) + 1;
    char *p = malloc(n);
    memcpy(p, s, n);
    return p;
}

static const char *OPNAMES[OP_COUNT] = {
    [OP_ICONST]="iconst", [OP_FCONST]="fconst", [OP_FREEZE]="freeze",
    [OP_ADD]="add", [OP_SUB]="sub", [OP_MUL]="mul", [OP_UDIV]="udiv",
    [OP_SDIV]="sdiv", [OP_UREM]="urem", [OP_SREM]="srem", [OP_NEG]="neg",
    [OP_AND]="and", [OP_OR]="or", [OP_XOR]="xor", [OP_NOT]="not",
    [OP_SHL]="shl", [OP_LSHR]="lshr", [OP_ASHR]="ashr", [OP_ICMP]="icmp",
    [OP_POPCOUNT]="popcount", [OP_CLZ]="clz", [OP_CTZ]="ctz", [OP_BSWAP]="bswap",
    [OP_TRUNC]="trunc", [OP_ZEXT]="zext", [OP_SEXT]="sext",
    [OP_FADD]="fadd", [OP_FSUB]="fsub", [OP_FMUL]="fmul", [OP_FDIV]="fdiv",
    [OP_FNEG]="fneg", [OP_FABS]="fabs", [OP_FMA]="fma", [OP_FCMP]="fcmp",
    [OP_FTRUNC]="ftrunc", [OP_FEXT]="fext", [OP_FPTOSI]="fptosi",
    [OP_FPTOUI]="fptoui", [OP_SITOFP]="sitofp", [OP_UITOFP]="uitofp",
    [OP_BITCAST]="bitcast",
    [OP_ALLOCA]="alloca", [OP_LOAD]="load", [OP_STORE]="store", [OP_GEP]="gep",
    [OP_MEMCPY]="memcpy", [OP_MEMSET]="memset", [OP_DATAPTR]="dataptr",
    [OP_VSPLAT]="vsplat", [OP_VADD]="vadd", [OP_VSUB]="vsub", [OP_VMUL]="vmul",
    [OP_VUDIV]="vudiv", [OP_VFADD]="vfadd", [OP_VFSUB]="vfsub",
    [OP_VFMUL]="vfmul", [OP_VFDIV]="vfdiv", [OP_VAND]="vand", [OP_VOR]="vor",
    [OP_VXOR]="vxor", [OP_VLOAD]="vload", [OP_VSTORE]="vstore",
    [OP_VEXTRACT]="vextract", [OP_VINSERT]="vinsert",
    [OP_ALOAD]="aload", [OP_ASTORE]="astore", [OP_AADD]="aadd",
    [OP_BR]="br", [OP_CONDBR]="condbr", [OP_RET]="ret", [OP_CALL]="call",
    [OP_TAILCALL]="tailcall", [OP_SELECT]="select", [OP_ASSUME]="assume",
    [OP_VLSHR]="vlshr",
    [OP_LOADV]="loadv", [OP_STOREV]="storev",
    [OP_FENCE]="fence",
    [OP_ACMPXCHG]="acmpxchg", [OP_AXCHG]="axchg", [OP_ASUB]="asub",
    [OP_AAND]="aand", [OP_AOR]="aor", [OP_AXOR]="axor",
    [OP_AMINS]="amins", [OP_AMAXS]="amaxs", [OP_AMINU]="aminu", [OP_AMAXU]="amaxu",
    [OP_FUNCP]="funcptr", [OP_CALLI]="calli", [OP_TAILCALLI]="tailcalli",
    [OP_FSHL]="fshl", [OP_FSHR]="fshr",
};
const char *op_name(int op) {
    if (op <= 0 || op >= OP_COUNT || !OPNAMES[op]) return "?op";
    return OPNAMES[op];
}

bool op_is_terminator(int op) {
    return op == OP_BR || op == OP_CONDBR || op == OP_RET || op == OP_TAILCALL || op == OP_TAILCALLI;
}
bool op_is_rmw(int op) {
    switch (op) {
    case OP_AADD: case OP_AXCHG: case OP_ASUB: case OP_AAND: case OP_AOR:
    case OP_AXOR: case OP_AMINS: case OP_AMAXS: case OP_AMINU: case OP_AMAXU:
        return true;
    default:
        return false;
    }
}
bool op_is_pure(int op) {
    switch (op) {
    case OP_LOAD: case OP_STORE: case OP_ALOAD: case OP_ASTORE: case OP_AADD:
    case OP_MEMCPY: case OP_MEMSET: case OP_CALL: case OP_TAILCALL:
    case OP_BR: case OP_CONDBR: case OP_RET: case OP_ASSUME: case OP_VLOAD:
    case OP_VSTORE: case OP_ALLOCA: case OP_LOADV: case OP_STOREV: case OP_FENCE:
    case OP_ACMPXCHG: case OP_AXCHG: case OP_ASUB: case OP_AAND: case OP_AOR:
    case OP_AXOR: case OP_AMINS: case OP_AMAXS: case OP_AMINU: case OP_AMAXU:
    case OP_CALLI: case OP_TAILCALLI:
        return false;
    default:
        return true;
    }
}

/* ---------------- module ---------------- */
Module *mod_new(void) { return calloc(1, sizeof(Module)); }

static void func_clear(Func *f) {
    for (int i = 0; i < f->nblocks; i++) {
        Block *b = &f->blocks[i];
        free(b->arg_types); free(b->arg_vals);
        for (int j = 0; j < b->nins; j++) {
            free(b->ins[j].args); free(b->ins[j].args2);
        }
        free(b->ins);
    }
    free(f->blocks); free(f->name);
    cons_free(f);
    free(f->cval); free(f->cval_hi); free(f->isconst); free(f->vtypes);
    memset(f, 0, sizeof *f);
}

void mod_free(Module *m) {
    if (!m) return;
    for (int i = 0; i < m->nfuncs; i++) func_clear(&m->funcs[i]);
    free(m->funcs);
    for (int i = 0; i < m->nexts; i++) { free(m->exts[i].name); free(m->exts[i].params); }
    free(m->exts);
    for (int i = 0; i < m->ndata; i++) { free(m->data[i].name); free(m->data[i].bytes); }
    free(m->data);
    for (int i = 0; i < m->nsigs; i++) free(m->sigs[i].params);
    free(m->sigs);
    free(m);
}

int mod_add_extern(Module *m, const char *name, const Type *params, int n, Type ret) {
    if (m->nexts == m->capexts) {
        m->capexts = m->capexts ? m->capexts * 2 : 8;
        m->exts = realloc(m->exts, (size_t)m->capexts * sizeof(Extern));
    }
    Extern *e = &m->exts[m->nexts];
    e->name = xstrdup(name);
    e->params = malloc(sizeof(Type) * (size_t)(n > 0 ? n : 1));
    if (n > 0) memcpy(e->params, params, sizeof(Type) * (size_t)n);
    e->nparams = n;
    e->ret = ret;
    return m->nexts++;
}

int mod_add_sig(Module *m, const Type *params, int n, Type ret) {
    for (int i = 0; i < m->nsigs; i++) {
        Sig *g = &m->sigs[i];
        if (g->nparams == n && ty_eq(g->ret, ret)) {
            bool same = true;
            for (int j = 0; j < n; j++) if (!ty_eq(g->params[j], params[j])) { same = false; break; }
            if (same) return i;
        }
    }
    if (m->nsigs == m->capsigs) {
        m->capsigs = m->capsigs ? m->capsigs * 2 : 8;
        m->sigs = realloc(m->sigs, (size_t)m->capsigs * sizeof(Sig));
    }
    Sig *g = &m->sigs[m->nsigs];
    g->params = malloc(sizeof(Type) * (size_t)(n ? n : 1));
    for (int j = 0; j < n; j++) g->params[j] = params[j];
    g->nparams = n;
    g->ret = ret;
    return m->nsigs++;
}

int mod_add_data(Module *m, const char *name, uint32_t align, const void *bytes, uint32_t len) {
    if (m->ndata == m->capdata) {
        m->capdata = m->capdata ? m->capdata * 2 : 8;
        m->data = realloc(m->data, (size_t)m->capdata * sizeof(DataBlob));
    }
    DataBlob *d = &m->data[m->ndata];
    d->name = xstrdup(name);
    d->align = align;
    d->bytes = malloc(len ? len : 1);
    if (len) memcpy(d->bytes, bytes, len);
    d->len = len;
    return m->ndata++;
}

Func *mod_add_func(Module *m, const char *name, Type ret, uint8_t flags) {
    if (m->nfuncs == m->capfuncs) {
        m->capfuncs = m->capfuncs ? m->capfuncs * 2 : 8;
        m->funcs = realloc(m->funcs, (size_t)m->capfuncs * sizeof(Func));
    }
    Func *f = &m->funcs[m->nfuncs++];
    memset(f, 0, sizeof *f);
    f->name = xstrdup(name);
    f->ret = ret;
    f->flags = flags;
    return f;
}

int mod_find_func(Module *m, const char *name) {
    for (int i = 0; i < m->nfuncs; i++)
        if (strcmp(m->funcs[i].name, name) == 0) return i;
    return -1;
}
int mod_find_extern(Module *m, const char *name) {
    for (int i = 0; i < m->nexts; i++)
        if (strcmp(m->exts[i].name, name) == 0) return i;
    return -1;
}

/* ---------------- values ---------------- */
static void func_reserve_value(Func *f, Type t) {
    if (f->nvalues >= f->vcap) {
        f->vcap = f->vcap ? f->vcap * 2 : 32;
        f->vtypes  = realloc(f->vtypes,  (size_t)f->vcap * sizeof(Type));
        f->cval    = realloc(f->cval,    (size_t)f->vcap * sizeof(uint64_t));
        f->cval_hi = realloc(f->cval_hi, (size_t)f->vcap * sizeof(uint64_t));
        f->isconst = realloc(f->isconst, (size_t)f->vcap);
    }
    f->vtypes[f->nvalues] = t;
    f->cval[f->nvalues] = 0;
    f->cval_hi[f->nvalues] = 0;
    f->isconst[f->nvalues] = 0;
    f->nvalues++;
}

Type func_value_type(Func *f, int32_t v) {
    if (v < 0 || v >= f->nvalues) return ty_void();
    return f->vtypes[v];
}

int func_add_block(Func *f, const Type *argtypes, int nargs) {
    if (f->nblocks == f->capblocks) {
        f->capblocks = f->capblocks ? f->capblocks * 2 : 8;
        f->blocks = realloc(f->blocks, (size_t)f->capblocks * sizeof(Block));
    }
    Block *b = &f->blocks[f->nblocks];
    memset(b, 0, sizeof *b);
    b->arg_types = malloc(sizeof(Type) * (size_t)(nargs > 0 ? nargs : 1));
    b->arg_vals  = malloc(sizeof(int32_t) * (size_t)(nargs > 0 ? nargs : 1));
    b->nargs = nargs;
    for (int i = 0; i < nargs; i++) {
        b->arg_types[i] = argtypes[i];
        func_reserve_value(f, argtypes[i]);
        b->arg_vals[i] = f->nvalues - 1;
    }
    return f->nblocks++;
}

/* ---------------- emit ---------------- */
Instr ins_make(uint8_t op, Type ty) {
    Instr in;
    memset(&in, 0, sizeof in);
    in.op = op; in.ty = ty;
    in.a = in.b = in.c = -1;
    in.result = -1;
    in.blk = in.blk2 = -1; in.callee = -1;
    return in;
}
Instr ins_iconst(Type ty, int64_t v) { Instr in = ins_make(OP_ICONST, ty); in.imm = v; return in; }
Instr ins_iconst128(int64_t lo, int64_t hi) { Instr in = ins_make(OP_ICONST, ty_i128()); in.imm = lo; in.imm2 = hi; return in; }
Instr ins_fconst(Type ty, uint64_t bits) { Instr in = ins_make(OP_FCONST, ty); in.imm = (int64_t)bits; return in; }
Instr ins_bin(uint8_t op, Type ty, int a, int b) { Instr in = ins_make(op, ty); in.a = a; in.b = b; return in; }
Instr ins_un(uint8_t op, Type ty, int a) { Instr in = ins_make(op, ty); in.a = a; return in; }
Instr ins_br(int blk, int32_t *args, int n) {
    Instr in = ins_make(OP_BR, ty_void()); in.blk = blk; in.args = args; in.nargs = (uint16_t)n; return in;
}
Instr ins_condbr(int cond, int b1, int32_t *a1, int n1, int b2, int32_t *a2, int n2) {
    Instr in = ins_make(OP_CONDBR, ty_void());
    in.a = cond; in.blk = b1; in.args = a1; in.nargs = (uint16_t)n1;
    in.blk2 = b2; in.args2 = a2; in.nargs2 = (uint16_t)n2; return in;
}
Instr ins_ret(int v) { Instr in = ins_make(OP_RET, ty_void()); in.a = v; return in; }
Instr ins_call(Type ret, int callee, bool ext, int32_t *args, int n, bool tail) {
    Instr in = ins_make(tail ? OP_TAILCALL : OP_CALL, ret);
    in.callee = callee; in.callee_extern = ext ? 1 : 0;
    in.args = args; in.nargs = (uint16_t)n; return in;
}
Instr ins_funcptr(int callee, bool ext) {
    Instr in = ins_make(OP_FUNCP, ty_ptr());
    in.callee = callee; in.callee_extern = ext ? 1 : 0;
    return in;
}
Instr ins_calli(Type ret, int sig, int fp, int32_t *args, int n, bool tail) {
    Instr in = ins_make(tail ? OP_TAILCALLI : OP_CALLI, ret);
    in.callee = sig; in.a = fp;
    in.args = args; in.nargs = (uint16_t)n; return in;
}
int32_t *ids_dup(const int32_t *src, int n) {
    if (n <= 0) return NULL;
    int32_t *p = malloc(sizeof(int32_t) * (size_t)n);
    memcpy(p, src, sizeof(int32_t) * (size_t)n);
    return p;
}

static bool ins_has_result(const Instr *in) {
    switch (in->op) {
    case OP_STORE: case OP_VSTORE: case OP_BR: case OP_CONDBR: case OP_RET:
    case OP_ASSUME: case OP_ASTORE: case OP_MEMCPY: case OP_MEMSET: case OP_STOREV:
    case OP_FENCE:
        return false;
    case OP_CALL:
        return in->ty.kind != TY_VOID;
    default:
        return true;
    }
}

/* integer constant helpers */
static uint64_t mask_for(int bits) { return bits >= 64 ? ~0ull : ((1ull << bits) - 1ull); }
static uint64_t sext_u64(uint64_t v, int bits) {
    if (bits >= 64) return v;
    uint64_t m = 1ull << (bits - 1);
    return ((v & mask_for(bits)) ^ m) - m;
}

static int emit_at(Func *f, int blk, int pos, Instr in) {
    Block *b = &f->blocks[blk];
    if (b->nins == b->cap) {
        b->cap = b->cap ? b->cap * 2 : 16;
        b->ins = realloc(b->ins, (size_t)b->cap * sizeof(Instr));
    }
    if (ins_has_result(&in)) {
        func_reserve_value(f, in.ty);
        in.result = f->nvalues - 1;
    }
    if (pos < 0 || pos > b->nins) pos = b->nins;
    memmove(&b->ins[pos + 1], &b->ins[pos], sizeof(Instr) * (size_t)(b->nins - pos));
    b->ins[pos] = in;
    b->nins++;
    return in.result;
}

static int emit_raw(Func *f, int blk, Instr in) { return emit_at(f, blk, -1, in); }

/* v3: constants are function-scoped. A constant requested in any block is
 * materialized in the entry block (inserted before its terminator if it
 * already has one), which dominates every block in the function, so the
 * single hash-consed definition is a legal use everywhere. This removes
 * the v1/v2 trap in which a literal first materialized in a non-dominating
 * branch block was reused for a sibling block and failed verification. */
static int emit_entry_const(Func *f, Instr in) {
    Block *b0 = &f->blocks[0];
    int pos = b0->nins;
    if (pos > 0 && op_is_terminator(b0->ins[pos - 1].op)) pos--;
    return emit_at(f, 0, pos, in);
}

int emit(Func *f, int blk, Instr in) { return emit_pure(f, blk, in); }

/* ---------------- hash-consing + folding ---------------- */
typedef struct {
    Instr   key;      /* the pure instruction (result field ignored) */
    int32_t value;    /* value id it produced */
    int32_t defblk;   /* block the value was defined in (v3: dominance-aware reuse) */
    int     used;
} ConsEnt;

typedef struct { ConsEnt *e; int cap, n; } ConsTab;

static uint32_t ty_pack(Type t) {
    return (uint32_t)t.kind | ((uint32_t)t.bits << 4) | ((uint32_t)t.elem_kind << 12) |
           ((uint32_t)t.elem_bits << 16) | ((uint32_t)t.n << 24);
}
static uint64_t hash_ins(const Instr *in) {
    uint64_t h = 1469598103934665603ull;
    h = (h ^ (uint64_t)in->op) * 1099511628211ull;
    h = (h ^ (uint64_t)ty_pack(in->ty)) * 1099511628211ull;
    h = (h ^ (uint64_t)(uint32_t)in->a) * 1099511628211ull;
    h = (h ^ (uint64_t)(uint32_t)in->b) * 1099511628211ull;
    h = (h ^ (uint64_t)(uint32_t)in->c) * 1099511628211ull;
    h = (h ^ (uint64_t)in->imm) * 1099511628211ull;
    h = (h ^ (uint64_t)in->imm2) * 1099511628211ull;
    h = (h ^ (uint64_t)in->pred) * 1099511628211ull;
    h = (h ^ (uint64_t)in->aux) * 1099511628211ull;
    h = (h ^ (uint64_t)(uint32_t)in->callee) * 1099511628211ull;
    h = (h ^ (uint64_t)in->callee_extern) * 1099511628211ull;
    return h;
}
static bool ins_eq(const Instr *x, const Instr *y) {
    return x->op == y->op && ty_pack(x->ty) == ty_pack(y->ty) &&
           x->a == y->a && x->b == y->b && x->c == y->c &&
           x->imm == y->imm && x->imm2 == y->imm2 && x->pred == y->pred && x->aux == y->aux &&
           x->callee == y->callee && x->callee_extern == y->callee_extern;
}
static ConsTab *cons_tab(Func *f) {
    if (!f->cons) {
        ConsTab *t = calloc(1, sizeof(ConsTab));
        t->cap = 64;
        t->e = calloc((size_t)t->cap, sizeof(ConsEnt));
        f->cons = t;
    }
    return f->cons;
}
static void cons_free(Func *f) {
    ConsTab *t = f->cons;
    if (t) { free(t->e); free(t); f->cons = NULL; }
}
static int cons_find(Func *f, const Instr *in) {
    ConsTab *t = cons_tab(f);
    uint64_t h = hash_ins(in);
    for (int i = 0; i < t->cap; i++) {
        ConsEnt *e = &t->e[(h + (uint64_t)i) & (uint64_t)(t->cap - 1)];
        if (!e->used) return -1;
        if (ins_eq(&e->key, in)) return e->value;
    }
    return -1;
}
/* block in which the hash-consed value for `in` was defined, or -2 */
static int cons_defblk(Func *f, const Instr *in) {
    ConsTab *t = cons_tab(f);
    uint64_t h = hash_ins(in);
    for (int i = 0; i < t->cap; i++) {
        ConsEnt *e = &t->e[(h + (uint64_t)i) & (uint64_t)(t->cap - 1)];
        if (!e->used) return -2;
        if (ins_eq(&e->key, in)) return e->defblk;
    }
    return -2;
}
static void cons_put(Func *f, const Instr *in, int32_t value, int32_t defblk) {
    ConsTab *t = cons_tab(f);
    if ((t->n + 1) * 2 >= t->cap) {
        ConsEnt *old = t->e; int ocap = t->cap;
        t->cap *= 2;
        t->e = calloc((size_t)t->cap, sizeof(ConsEnt));
        t->n = 0;
        for (int i = 0; i < ocap; i++) if (old[i].used) {
            ConsEnt *src = &old[i];
            uint64_t h = hash_ins(&src->key);
            for (int j = 0; j < t->cap; j++) {
                ConsEnt *e = &t->e[(h + (uint64_t)j) & (uint64_t)(t->cap - 1)];
                if (!e->used) { *e = *src; t->n++; break; }
            }
        }
        free(old);
    }
    uint64_t h = hash_ins(in);
    for (int i = 0; i < t->cap; i++) {
        ConsEnt *e = &t->e[(h + (uint64_t)i) & (uint64_t)(t->cap - 1)];
        if (!e->used) { e->key = *in; e->value = value; e->defblk = defblk; e->used = 1; t->n++; return; }
        if (ins_eq(&e->key, in)) { e->value = value; e->defblk = defblk; return; }
    }
}

/* try to fold `in` to an existing value or a constant; returns value id or -1 */
static int try_fold(Func *f, int blk, Instr *in) {
    int op = in->op;
    Type t = in->ty;
    bool ac = in->a >= 0 && f->isconst[in->a];
    bool bc = in->b >= 0 && f->isconst[in->b];
    uint64_t av = ac ? f->cval[in->a] : 0, bv = bc ? f->cval[in->b] : 0;

    if (op == OP_SELECT && ac) return f->cval[in->a] ? in->b : in->c;

    if (t.kind == TY_INT && t.bits == 128 && op != OP_ICONST) {
        /* i128 constants live in (cval, cval_hi); fold on the full pair.
         * Nothing below this block may see a 128-bit result: the generic
         * folder tracks only the low word and would fold e.g. x + 2^64
         * (low word 0) to x. */
        unsigned __int128 A  = ((unsigned __int128)(ac ? f->cval_hi[in->a] : 0) << 64) | av;
        unsigned __int128 Bv = ((unsigned __int128)(bc ? f->cval_hi[in->b] : 0) << 64) | bv;
        #define K128(x) emit_pure(f, blk, ins_iconst128((int64_t)(uint64_t)(unsigned __int128)(x), (int64_t)(uint64_t)((unsigned __int128)(x) >> 64)))
        if (bc) {
            switch (op) {
            case OP_ADD: case OP_OR: case OP_XOR: if (Bv == 0) return in->a; break;
            case OP_SUB: if (Bv == 0) return in->a; if (in->a == in->b) return K128(0); break;
            case OP_MUL: if (Bv == 0) return K128(0); if (Bv == 1) return in->a; break;
            case OP_AND: if (Bv == 0) return K128(0); if (Bv == ~(unsigned __int128)0) return in->a; break;
            case OP_SHL: case OP_LSHR: case OP_ASHR: if ((Bv % 128) == 0) return in->a; break;
            default: break;
            }
        }
        if (ac) {
            switch (op) {
            case OP_ADD: case OP_OR: case OP_XOR: if (A == 0) return in->b; break;
            case OP_MUL: if (A == 0) return K128(0); if (A == 1) return in->b; break;
            case OP_AND: if (A == 0) return K128(0); break;
            default: break;
            }
        }
        if (ac && bc) {
            unsigned __int128 r = 0; bool ok = true;
            switch (op) {
            case OP_ADD: r = A + Bv; break;
            case OP_SUB: r = A - Bv; break;
            case OP_MUL: r = A * Bv; break;
            case OP_AND: r = A & Bv; break;
            case OP_OR:  r = A | Bv; break;
            case OP_XOR: r = A ^ Bv; break;
            case OP_UDIV: r = Bv ? A / Bv : 0; break;
            case OP_UREM: r = Bv ? A % Bv : 0; break;
            case OP_SDIV: case OP_SREM: {
                if (Bv == 0) { r = 0; break; }
                __int128 sa = (__int128)A, sb = (__int128)Bv;
                unsigned __int128 ua = sa < 0 ? (unsigned __int128)0 - (unsigned __int128)A : A;
                unsigned __int128 ub = sb < 0 ? (unsigned __int128)0 - (unsigned __int128)Bv : Bv;
                unsigned __int128 q = (op == OP_SDIV) ? ua / ub : ua % ub;
                bool neg = (op == OP_SDIV) ? ((sa < 0) != (sb < 0)) : (sa < 0);
                r = neg ? (unsigned __int128)0 - q : q;
                break;
            }
            case OP_SHL:  r = A << (unsigned)(Bv % 128); break;
            case OP_LSHR: r = A >> (unsigned)(Bv % 128); break;
            case OP_ASHR: r = (unsigned __int128)((__int128)A >> (unsigned)(Bv % 128)); break;
            default: ok = false; break;
            }
            if (ok) return K128(r);
        }
        if (ac) {
            switch (op) {
            case OP_NEG: return K128((unsigned __int128)0 - A);
            case OP_NOT: return K128(~A);
            case OP_POPCOUNT: return emit_pure(f, blk, ins_iconst(t, __builtin_popcountll((unsigned long long)A) + __builtin_popcountll((unsigned long long)(A >> 64))));
            case OP_CLZ: {
                unsigned long long hi = (unsigned long long)(A >> 64), lo = (unsigned long long)A;
                return emit_pure(f, blk, ins_iconst(t, hi ? __builtin_clzll(hi) : 64 + (lo ? __builtin_clzll(lo) : 64)));
            }
            case OP_CTZ: {
                unsigned long long hi = (unsigned long long)(A >> 64), lo = (unsigned long long)A;
                return emit_pure(f, blk, ins_iconst(t, lo ? __builtin_ctzll(lo) : 64 + (hi ? __builtin_ctzll(hi) : 64)));
            }
            case OP_BSWAP: return K128(((unsigned __int128)__builtin_bswap64((unsigned long long)A) << 64) | __builtin_bswap64((unsigned long long)(A >> 64)));
            case OP_ZEXT: return K128((unsigned __int128)av);
            case OP_SEXT: {
                int sb = func_value_type(f, in->a).bits;
                uint64_t lo = sext_u64(av, sb);
                return K128(((unsigned __int128)(lo >> 63 ? ~0ull : 0) << 64) | lo);
            }
            default: break;
            }
        }
        #undef K128
        return -1;
    }

    if (op == OP_ICMP && ac && bc && func_value_type(f, in->a).bits == 128) {
        unsigned __int128 A  = ((unsigned __int128)f->cval_hi[in->a] << 64) | av;
        unsigned __int128 Bv = ((unsigned __int128)f->cval_hi[in->b] << 64) | bv;
        __int128 sa = (__int128)A, sb = (__int128)Bv;
        bool r = false;
        switch (in->pred) {
        case IC_EQ: r = A == Bv; break; case IC_NE: r = A != Bv; break;
        case IC_ULT: r = A < Bv; break; case IC_ULE: r = A <= Bv; break;
        case IC_UGT: r = A > Bv; break; case IC_UGE: r = A >= Bv; break;
        case IC_SLT: r = sa < sb; break; case IC_SLE: r = sa <= sb; break;
        case IC_SGT: r = sa > sb; break; case IC_SGE: r = sa >= sb; break;
        }
        return emit_pure(f, blk, ins_iconst(ty_i1(), r ? 1 : 0));
    }

    if (t.kind == TY_INT && op != OP_ICONST) {
        int bits = t.bits;
        uint64_t m = mask_for(bits);
        /* identities with one constant */
        if (bc) {
            switch (op) {
            case OP_ADD: if ((bv & m) == 0) return in->a; break;
            case OP_SUB: if ((bv & m) == 0) return in->a; if (in->a == in->b) return emit_pure(f, blk, ins_iconst(t, 0)); break;
            case OP_MUL: if ((bv & m) == 0) return emit_pure(f, blk, ins_iconst(t, 0));
                         if ((bv & m) == 1) return in->a;
                         break;
            case OP_AND: if ((bv & m) == 0) return emit_pure(f, blk, ins_iconst(t, 0));
                         if ((bv & m) == m) return in->a;
                         break;
            case OP_OR:  if ((bv & m) == 0) return in->a;
                         if ((bv & m) == m) return emit_pure(f, blk, ins_iconst(t, -1));
                         break;
            case OP_XOR: if ((bv & m) == 0) return in->a;
                         if (in->a == in->b) return emit_pure(f, blk, ins_iconst(t, 0));
                         break;
            case OP_SHL: case OP_LSHR: case OP_ASHR:
                         if ((bv % (uint64_t)bits) == 0) return in->a;
                         break;
            default: break;
            }
        }
        if (ac) {
            switch (op) {
            case OP_ADD: if ((av & m) == 0) return in->b; break;
            case OP_MUL: if ((av & m) == 0) return emit_pure(f, blk, ins_iconst(t, 0));
                         if ((av & m) == 1) return in->b;
                         break;
            case OP_AND: if ((av & m) == 0) return emit_pure(f, blk, ins_iconst(t, 0)); break;
            case OP_OR:  if ((av & m) == 0) return in->b; break;
            case OP_XOR: if ((av & m) == 0) return in->b; break;
            default: break;
            }
        }
        if (op == OP_FSHL || op == OP_FSHR) {
            bool cc = in->c >= 0 && f->isconst[in->c];
            uint64_t cv = cc ? f->cval[in->c] : 0;
            if (cc && (cv % (uint64_t)bits) == 0) return op == OP_FSHL ? in->a : in->b;
            if (ac && bc && cc) {
                uint64_t s = cv % (uint64_t)bits;
                uint64_t ua = av & m, ub = bv & m, r;
                if (op == OP_FSHL) r = s ? ((ua << s) | (ub >> ((uint64_t)bits - s))) : ua;
                else               r = s ? ((ua << ((uint64_t)bits - s)) | (ub >> s)) : ub;
                return emit_pure(f, blk, ins_iconst(t, (int64_t)(r & m)));
            }
        }
        if (ac && bc) {
            int64_t sa = (int64_t)sext_u64(av, bits), sb = (int64_t)sext_u64(bv, bits);
            uint64_t ua = av & m, ub = bv & m;
            uint64_t r = 0; bool ok = true;
            switch (op) {
            case OP_ADD: r = ua + ub; break;
            case OP_SUB: r = ua - ub; break;
            case OP_MUL: r = ua * ub; break;
            case OP_UDIV: r = ub ? ua / ub : 0; break;
            case OP_SDIV: if (sb == 0) r = 0; else if (bits < 64 && sa == -(1ll << (bits - 1)) && sb == -1) r = (uint64_t)sa; else if (bits == 64 && sa == INT64_MIN && sb == -1) r = (uint64_t)sa; else r = (uint64_t)(sa / sb); break;
            case OP_UREM: r = ub ? ua % ub : 0; break;
            case OP_SREM: if (sb == 0) r = 0; else if (bits < 64 && sa == -(1ll << (bits - 1)) && sb == -1) r = 0; else if (bits == 64 && sa == INT64_MIN && sb == -1) r = 0; else r = (uint64_t)(sa % sb); break;
            case OP_AND: r = ua & ub; break;
            case OP_OR:  r = ua | ub; break;
            case OP_XOR: r = ua ^ ub; break;
            case OP_SHL: r = ua << (ub % (uint64_t)bits); break;
            case OP_LSHR: r = ua >> (ub % (uint64_t)bits); break;
            case OP_ASHR: r = (uint64_t)(sa >> (ub % (uint64_t)bits)); break;
            default: ok = false; break;
            }
            if (ok) return emit_pure(f, blk, ins_iconst(t, (int64_t)(r & m)));
        }
        if (ac) {
            uint64_t ua = av & m;
            switch (op) {
            case OP_NEG: return emit_pure(f, blk, ins_iconst(t, (int64_t)((0 - ua) & m)));
            case OP_NOT: return emit_pure(f, blk, ins_iconst(t, (int64_t)((~ua) & m)));
            case OP_POPCOUNT: { int c = 0; for (uint64_t x = ua; x; x &= x - 1) c++; return emit_pure(f, blk, ins_iconst(t, c)); }
            case OP_CLZ: { int c = 0; for (int i = bits - 1; i >= 0; i--) { if ((ua >> i) & 1) break; c++; } return emit_pure(f, blk, ins_iconst(t, c)); }
            case OP_CTZ: { int c = 0; for (int i = 0; i < bits; i++) { if ((ua >> i) & 1) break; c++; } return emit_pure(f, blk, ins_iconst(t, c)); }
            case OP_TRUNC: case OP_ZEXT: return emit_pure(f, blk, ins_iconst(t, (int64_t)(ua & m)));
            case OP_SEXT: return emit_pure(f, blk, ins_iconst(t, (int64_t)sext_u64(ua, func_value_type(f, in->a).bits)));
            default: break;
            }
        }
    }
    if (op == OP_ICMP && ac && bc) {
        Type at = func_value_type(f, in->a);
        int bits = at.bits;
        uint64_t ua = av & mask_for(bits), ub = bv & mask_for(bits);
        int64_t sa = (int64_t)sext_u64(ua, bits), sb = (int64_t)sext_u64(ub, bits);
        bool r = false;
        switch (in->pred) {
        case IC_EQ: r = ua == ub; break; case IC_NE: r = ua != ub; break;
        case IC_ULT: r = ua < ub; break; case IC_ULE: r = ua <= ub; break;
        case IC_UGT: r = ua > ub; break; case IC_UGE: r = ua >= ub; break;
        case IC_SLT: r = sa < sb; break; case IC_SLE: r = sa <= sb; break;
        case IC_SGT: r = sa > sb; break; case IC_SGE: r = sa >= sb; break;
        }
        return emit_pure(f, blk, ins_iconst(ty_i1(), r ? 1 : 0));
    }
    (void)op;
    return -1;
}

int emit_pure(Func *f, int blk, Instr in) {
    if (!op_is_pure(in.op) || op_is_terminator(in.op)) return emit_raw(f, blk, in);
    int folded = try_fold(f, blk, &in);
    if (folded >= 0) return folded;
    int found = cons_find(f, &in);
    if (found >= 0) {
        /* Dominance-aware reuse (v3): a hash-consed value may only be
         * reused where its definition dominates the use. The entry block
         * dominates every block, and a definition earlier in the same
         * block dominates by position. Any other hit (the classic case:
         * first materialized in one arm of a branch, requested again in
         * the sibling arm) must be re-emitted in the requesting block;
         * for constants the re-emission is hoisted to the entry block
         * below, after which the shared definition dominates all uses. */
        int db = cons_defblk(f, &in);
        if (db == blk || db == 0) return found;
    }
    int eblk = blk;
    int r;
    if ((in.op == OP_ICONST || in.op == OP_FCONST) && blk != 0 && f->nblocks > 0) {
        r = emit_entry_const(f, in);
        eblk = 0;
    } else {
        r = emit_raw(f, blk, in);
    }
    if (r >= 0) {
        if (in.op == OP_ICONST) {
            Type t = in.ty;
            f->isconst[r] = 1;
            f->cval[r] = (uint64_t)in.imm & mask_for(t.bits);
            f->cval_hi[r] = (uint64_t)in.imm2;
        } else if (in.op == OP_FCONST) {
            f->isconst[r] = 1;
            f->cval[r] = (uint64_t)in.imm;
        }
        cons_put(f, &in, r, eblk);
    }
    return r;
}

void func_rebuild_constants(Func *f) {
    if (!f || !f->isconst || !f->cval) return;
    for (int i = 0; i < f->nvalues; i++) f->isconst[i] = 0;
    for (int bi = 0; bi < f->nblocks; bi++) {
        Block *b = &f->blocks[bi];
        for (int ii = 0; ii < b->nins; ii++) {
            Instr *in = &b->ins[ii];
            if (in->op == OP_ICONST && in->result >= 0 && in->result < f->nvalues) {
                f->isconst[in->result] = 1;
                f->cval[in->result] = (uint64_t)in->imm & mask_for(in->ty.bits);
                f->cval_hi[in->result] = (uint64_t)in->imm2;
            } else if (in->op == OP_FCONST && in->result >= 0 && in->result < f->nvalues) {
                f->isconst[in->result] = 1;
                f->cval[in->result] = (uint64_t)in->imm;
            }
        }
    }
}
