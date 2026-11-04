/* Krell-IR — canonical binary encoding/decoding + SHA-256 module identity.
 * Format: docs/SPEC.md §5 (names inline in their sections in v1). */
#include "krell.h"

/* ---------------- growable buffer ---------------- */
typedef struct { uint8_t *p; size_t n, cap; } Buf;
static void bput(Buf *b, uint8_t x) {
    if (b->n == b->cap) { b->cap = b->cap ? b->cap * 2 : 256; b->p = realloc(b->p, b->cap); }
    b->p[b->n++] = x;
}
static void bputn(Buf *b, const void *src, size_t n) { for (size_t i = 0; i < n; i++) bput(b, ((const uint8_t *)src)[i]); }
static void buleb(Buf *b, uint64_t v) {
    do { uint8_t x = (uint8_t)(v & 0x7f); v >>= 7; if (v) x |= 0x80; bput(b, x); } while (v);
}
static void bsleb(Buf *b, int64_t v) {
    for (;;) {
        uint8_t x = (uint8_t)(v & 0x7f);
        v >>= 7;
        bool done = (v == 0 && !(x & 0x40)) || (v == -1 && (x & 0x40));
        if (!done) x |= 0x80;
        bput(b, x);
        if (done) break;
    }
}
static void btype(Buf *b, Type t) {
    bput(b, t.kind);
    if (t.kind == TY_INT || t.kind == TY_FLOAT) bput(b, t.bits);
    else if (t.kind == TY_VEC) { bput(b, t.elem_kind); bput(b, t.elem_bits); bput(b, t.n); }
}
static void bname(Buf *b, const char *s) { size_t n = strlen(s); buleb(b, n); bputn(b, s, n); }
static void bval(Buf *b, int32_t v) { buleb(b, (uint64_t)(v + 1)); }

/* format version of the module currently being encoded/decoded:
 * v2 differs from v1 only in the i128 iconst payload (16-byte
 * little-endian) and, once indirect calls land, the signature section.
 * Everything else is byte-identical, so a module that needs no v2
 * feature encodes as v1 and stays readable by v2.x toolchains. */
static int fmt_ver = 1;

static bool ty_is_i128(Type t) { return t.kind == TY_INT && t.bits == 128; }
static bool mod_needs_v2(Module *m) {
    for (int i = 0; i < m->nexts; i++) {
        for (int j = 0; j < m->exts[i].nparams; j++) if (ty_is_i128(m->exts[i].params[j])) return true;
        if (ty_is_i128(m->exts[i].ret)) return true;
    }
    for (int i = 0; i < m->nfuncs; i++) {
        Func *f = &m->funcs[i];
        if (ty_is_i128(f->ret)) return true;
        for (int j = 0; j < f->nvalues; j++) if (ty_is_i128(f->vtypes[j])) return true;
        for (int bi = 0; bi < f->nblocks; bi++)
            for (int ii = 0; ii < f->blocks[bi].nins; ii++)
                if (ty_is_i128(f->blocks[bi].ins[ii].ety)) return true;
    }
    return false;
}

static void bins(Buf *b, const Instr *in) {
    bput(b, in->op);
    buleb(b, (uint64_t)(in->result + 1));
    btype(b, in->ty);
    int op = in->op;
    if (op == OP_ICONST) {
        if (fmt_ver >= 2 && ty_is_i128(in->ty)) {
            uint64_t lo = (uint64_t)in->imm, hi = (uint64_t)in->imm2;
            for (int i = 0; i < 8; i++) bput(b, (uint8_t)(lo >> (8 * i)));
            for (int i = 0; i < 8; i++) bput(b, (uint8_t)(hi >> (8 * i)));
        } else bsleb(b, in->imm);
        return;
    }
    if (op == OP_FCONST) { buleb(b, (uint64_t)in->imm); return; }
    if (op == OP_BR) {
        buleb(b, (uint64_t)in->blk); buleb(b, in->nargs);
        for (int i = 0; i < in->nargs; i++) bval(b, in->args[i]);
        return;
    }
    if (op == OP_CONDBR) {
        bval(b, in->a);
        buleb(b, (uint64_t)in->blk); buleb(b, in->nargs);
        for (int i = 0; i < in->nargs; i++) bval(b, in->args[i]);
        buleb(b, (uint64_t)in->blk2); buleb(b, in->nargs2);
        for (int i = 0; i < in->nargs2; i++) bval(b, in->args2[i]);
        return;
    }
    if (op == OP_CALL || op == OP_TAILCALL) {
        buleb(b, (uint64_t)in->callee); bput(b, in->callee_extern);
        buleb(b, in->nargs);
        for (int i = 0; i < in->nargs; i++) bval(b, in->args[i]);
        return;
    }
    if (op == OP_RET) { bval(b, in->a); return; }
    if (op == OP_ICMP || op == OP_FCMP) {
        bput(b, in->pred); bval(b, in->a); bval(b, in->b); return;
    }
    if (op == OP_ALLOCA) { buleb(b, (uint64_t)in->imm); buleb(b, (uint64_t)in->c); return; }
    if (op == OP_DATAPTR) { buleb(b, (uint64_t)in->imm); return; }
    if (op == OP_GEP) { bval(b, in->a); bval(b, in->b); btype(b, in->ety); return; }
    if (op == OP_VEXTRACT) { bval(b, in->a); buleb(b, (uint64_t)in->imm); return; }
    if (op == OP_VINSERT) { bval(b, in->a); bval(b, in->b); buleb(b, (uint64_t)in->imm); return; }
    if (op == OP_FENCE) { bput(b, in->aux); return; }
    if (op == OP_ALOAD || op == OP_ASTORE || op == OP_AADD || op_is_rmw(op)) {
        bput(b, in->aux); bval(b, in->a); if (in->op != OP_ALOAD) bval(b, in->b);
        return;
    }
    if (op == OP_ACMPXCHG) {
        bput(b, in->aux); bval(b, in->a); bval(b, in->b); bval(b, in->c);
        return;
    }
    /* generic: a, b, c value slots */
    bval(b, in->a); bval(b, in->b); bval(b, in->c);
}

uint8_t *mod_encode(Module *m, size_t *out_len) {
    Buf b = { 0 };
    fmt_ver = mod_needs_v2(m) ? 2 : 1;
    bputn(&b, "KREL", 4);
    bput(&b, (uint8_t)fmt_ver); bput(&b, 0); /* version u16 LE */
    /* section 2: externs */
    {
        Buf s = { 0 };
        buleb(&s, (uint64_t)m->nexts);
        for (int i = 0; i < m->nexts; i++) {
            Extern *e = &m->exts[i];
            bname(&s, e->name);
            buleb(&s, (uint64_t)e->nparams);
            for (int j = 0; j < e->nparams; j++) btype(&s, e->params[j]);
            btype(&s, e->ret);
        }
        bput(&b, 2); buleb(&b, s.n); bputn(&b, s.p, s.n); free(s.p);
    }
    /* section 3: data */
    {
        Buf s = { 0 };
        buleb(&s, (uint64_t)m->ndata);
        for (int i = 0; i < m->ndata; i++) {
            DataBlob *d = &m->data[i];
            bname(&s, d->name);
            buleb(&s, d->align);
            buleb(&s, d->len);
            bputn(&s, d->bytes, d->len);
        }
        bput(&b, 3); buleb(&b, s.n); bputn(&b, s.p, s.n); free(s.p);
    }
    /* section 4: functions */
    {
        Buf s = { 0 };
        buleb(&s, (uint64_t)m->nfuncs);
        for (int i = 0; i < m->nfuncs; i++) {
            Func *f = &m->funcs[i];
            bname(&s, f->name);
            bput(&s, f->flags);
            btype(&s, f->ret);
            buleb(&s, (uint64_t)f->nblocks);
            for (int j = 0; j < f->nblocks; j++) {
                Block *bl = &f->blocks[j];
                buleb(&s, (uint64_t)bl->nargs);
                for (int k = 0; k < bl->nargs; k++) { buleb(&s, (uint64_t)bl->arg_vals[k]); btype(&s, bl->arg_types[k]); }
                buleb(&s, (uint64_t)bl->nins);
                for (int k = 0; k < bl->nins; k++) bins(&s, &bl->ins[k]);
            }
        }
        bput(&b, 4); buleb(&b, s.n); bputn(&b, s.p, s.n); free(s.p);
    }
    *out_len = b.n;
    return b.p;
}

/* ---------------- decoding ---------------- */
typedef struct { const uint8_t *p, *end; int bad; } Rd;
static uint8_t rbyte(Rd *r) {
    if (r->p >= r->end) { r->bad = 1; return 0; }
    return *r->p++;
}
static uint64_t ruleb(Rd *r) {
    uint64_t v = 0; int sh = 0;
    for (;;) {
        uint8_t x = rbyte(r);
        v |= (uint64_t)(x & 0x7f) << sh;
        if (!(x & 0x80)) break;
        sh += 7;
        if (sh > 63) { r->bad = 1; break; }
    }
    return v;
}
static int64_t rsleb(Rd *r) {
    uint64_t v = 0; int sh = 0; uint8_t x = 0;
    for (;;) {
        x = rbyte(r);
        v |= (uint64_t)(x & 0x7f) << sh;
        sh += 7;
        if (!(x & 0x80)) break;
        if (sh > 63) { r->bad = 1; break; }
    }
    if (sh < 64 && (x & 0x40)) v |= (~0ull << sh);
    return (int64_t)v;
}
static Type rtype(Rd *r) {
    Type t; memset(&t, 0, sizeof t);
    t.kind = rbyte(r);
    if (t.kind == TY_INT || t.kind == TY_FLOAT) t.bits = rbyte(r);
    else if (t.kind == TY_VEC) { t.elem_kind = rbyte(r); t.elem_bits = rbyte(r); t.n = rbyte(r); }
    return t;
}
static char *rname(Rd *r) {
    uint64_t n = ruleb(r);
    if (r->p + n > r->end) { r->bad = 1; n = 0; }
    char *s = malloc(n + 1);
    memcpy(s, r->p, n); s[n] = 0; r->p += n;
    return s;
}
static int32_t rval(Rd *r) { return (int32_t)ruleb(r) - 1; }

static void rins(Rd *r, Instr *in) {
    memset(in, 0, sizeof *in);
    in->a = in->b = in->c = -1; in->result = -1; in->blk = in->blk2 = -1; in->callee = -1;
    in->op = rbyte(r);
    in->result = (int32_t)ruleb(r) - 1;
    in->ty = rtype(r);
    int op = in->op;
    if (op == OP_ICONST) {
        if (fmt_ver >= 2 && ty_is_i128(in->ty)) {
            uint64_t lo = 0, hi = 0;
            for (int i = 0; i < 8; i++) lo |= (uint64_t)rbyte(r) << (8 * i);
            for (int i = 0; i < 8; i++) hi |= (uint64_t)rbyte(r) << (8 * i);
            in->imm = (int64_t)lo; in->imm2 = (int64_t)hi;
        } else in->imm = rsleb(r);
        return;
    }
    if (op == OP_FCONST) { in->imm = (int64_t)ruleb(r); return; }
    if (op == OP_BR) {
        in->blk = (int32_t)ruleb(r); in->nargs = (uint16_t)ruleb(r);
        in->args = malloc(sizeof(int32_t) * (in->nargs ? in->nargs : 1));
        for (int i = 0; i < in->nargs; i++) in->args[i] = rval(r);
        return;
    }
    if (op == OP_CONDBR) {
        in->a = rval(r);
        in->blk = (int32_t)ruleb(r); in->nargs = (uint16_t)ruleb(r);
        in->args = malloc(sizeof(int32_t) * (in->nargs ? in->nargs : 1));
        for (int i = 0; i < in->nargs; i++) in->args[i] = rval(r);
        in->blk2 = (int32_t)ruleb(r); in->nargs2 = (uint16_t)ruleb(r);
        in->args2 = malloc(sizeof(int32_t) * (in->nargs2 ? in->nargs2 : 1));
        for (int i = 0; i < in->nargs2; i++) in->args2[i] = rval(r);
        return;
    }
    if (op == OP_CALL || op == OP_TAILCALL) {
        in->callee = (int32_t)ruleb(r); in->callee_extern = rbyte(r);
        in->nargs = (uint16_t)ruleb(r);
        in->args = malloc(sizeof(int32_t) * (in->nargs ? in->nargs : 1));
        for (int i = 0; i < in->nargs; i++) in->args[i] = rval(r);
        return;
    }
    if (op == OP_RET) { in->a = rval(r); return; }
    if (op == OP_ICMP || op == OP_FCMP) { in->pred = rbyte(r); in->a = rval(r); in->b = rval(r); return; }
    if (op == OP_ALLOCA) { in->imm = (int64_t)ruleb(r); in->c = (int32_t)ruleb(r); return; }
    if (op == OP_DATAPTR) { in->imm = (int64_t)ruleb(r); return; }
    if (op == OP_GEP) { in->a = rval(r); in->b = rval(r); in->ety = rtype(r); return; }
    if (op == OP_VEXTRACT) { in->a = rval(r); in->imm = (int64_t)ruleb(r); return; }
    if (op == OP_VINSERT) { in->a = rval(r); in->b = rval(r); in->imm = (int64_t)ruleb(r); return; }
    if (op == OP_FENCE) { in->aux = rbyte(r); return; }
    if (op == OP_ALOAD || op == OP_ASTORE || op == OP_AADD || op_is_rmw(op)) {
        in->aux = rbyte(r); in->a = rval(r); if (op != OP_ALOAD) in->b = rval(r);
        return;
    }
    if (op == OP_ACMPXCHG) {
        in->aux = rbyte(r); in->a = rval(r); in->b = rval(r); in->c = rval(r);
        return;
    }
    in->a = rval(r); in->b = rval(r); in->c = rval(r);
}

/* register an explicit value id with its type (decode keeps the
 * producer's numbering; the format carries ids for exactly this reason) */
static void reg_value(Func *f, int32_t id, Type t) {
    if (id < 0 || id >= (1 << 24)) return;
    if (id >= f->vcap) {
        int nc = f->vcap ? f->vcap : 32;
        while (nc <= id) nc *= 2;
        f->vtypes  = realloc(f->vtypes,  (size_t)nc * sizeof(Type));
        f->cval    = realloc(f->cval,    (size_t)nc * sizeof(uint64_t));
        f->cval_hi = realloc(f->cval_hi, (size_t)nc * sizeof(uint64_t));
        f->isconst = realloc(f->isconst, (size_t)nc);
        for (int i = f->vcap; i < nc; i++) { f->cval[i] = 0; f->cval_hi[i] = 0; f->isconst[i] = 0; }
        f->vcap = nc;
    }
    f->vtypes[id] = t;
    if (id >= f->nvalues) f->nvalues = id + 1;
}

Module *mod_decode(const uint8_t *buf, size_t len, char *err, size_t errcap) {
    Rd r = { buf, buf + len, 0 };
    if (len < 6 || memcmp(buf, "KREL", 4) != 0) { snprintf(err, errcap, "bad magic"); return NULL; }
    r.p += 4;
    int ver = rbyte(&r) | (rbyte(&r) << 8);
    if (ver != 1 && ver != 2) { snprintf(err, errcap, "bad version %d", ver); return NULL; }
    fmt_ver = ver;
    Module *m = mod_new();
    while (r.p < r.end && !r.bad) {
        int id = rbyte(&r);
        uint64_t slen = ruleb(&r);
        const uint8_t *send = r.p + slen;
        if (send > r.end) { r.bad = 1; break; }
        if (id == 2) {
            int n = (int)ruleb(&r);
            for (int i = 0; i < n && !r.bad; i++) {
                char *name = rname(&r);
                int np = (int)ruleb(&r);
                Type *ps = malloc(sizeof(Type) * (size_t)(np ? np : 1));
                for (int j = 0; j < np; j++) ps[j] = rtype(&r);
                Type ret = rtype(&r);
                mod_add_extern(m, name, ps, np, ret);
                free(name); free(ps);
            }
        } else if (id == 3) {
            int n = (int)ruleb(&r);
            for (int i = 0; i < n && !r.bad; i++) {
                char *name = rname(&r);
                uint32_t al = (uint32_t)ruleb(&r);
                uint32_t ln = (uint32_t)ruleb(&r);
                if (r.p + ln > r.end) { r.bad = 1; free(name); break; }
                mod_add_data(m, name, al, r.p, ln);
                r.p += ln;
                free(name);
            }
        } else if (id == 4) {
            int n = (int)ruleb(&r);
            for (int i = 0; i < n && !r.bad; i++) {
                char *name = rname(&r);
                uint8_t flags = rbyte(&r);
                Type ret = rtype(&r);
                Func *f = mod_add_func(m, name, ret, flags);
                free(name);
                int nb = (int)ruleb(&r);
                for (int j = 0; j < nb && !r.bad; j++) {
                    int na = (int)ruleb(&r);
                    if (f->nblocks == f->capblocks) {
                        f->capblocks = f->capblocks ? f->capblocks * 2 : 8;
                        f->blocks = realloc(f->blocks, (size_t)f->capblocks * sizeof(Block));
                    }
                    Block *b = &f->blocks[f->nblocks++];
                    memset(b, 0, sizeof *b);
                    b->arg_types = malloc(sizeof(Type) * (size_t)(na ? na : 1));
                    b->arg_vals  = malloc(sizeof(int32_t) * (size_t)(na ? na : 1));
                    b->nargs = na;
                    for (int k = 0; k < na; k++) {
                        int32_t avid = (int32_t)ruleb(&r);
                        Type at = rtype(&r);
                        b->arg_vals[k] = avid;
                        b->arg_types[k] = at;
                        reg_value(f, avid, at);
                    }
                    int ni = (int)ruleb(&r);
                    for (int k = 0; k < ni && !r.bad; k++) {
                        Instr in;
                        rins(&r, &in);
                        if (b->nins == b->cap) {
                            b->cap = b->cap ? b->cap * 2 : 16;
                            b->ins = realloc(b->ins, (size_t)b->cap * sizeof(Instr));
                        }
                        if (in.result >= 0) {
                            reg_value(f, in.result, in.ty);
                            if (in.op == OP_ICONST && in.ty.kind == TY_INT &&
                                (in.ty.bits == 1 || in.ty.bits == 8 || in.ty.bits == 16 || in.ty.bits == 32 || in.ty.bits == 64)) {
                                f->isconst[in.result] = 1;
                                f->cval[in.result] = (uint64_t)in.imm & (in.ty.bits >= 64 ? ~0ull : ((1ull << in.ty.bits) - 1ull));
                            } else if (in.op == OP_ICONST && ty_is_i128(in.ty)) {
                                f->isconst[in.result] = 1;
                                f->cval[in.result] = (uint64_t)in.imm;
                                f->cval_hi[in.result] = (uint64_t)in.imm2;
                            } else if (in.op == OP_FCONST) {
                                f->isconst[in.result] = 1;
                                f->cval[in.result] = (uint64_t)in.imm;
                            }
                        }
                        b->ins[b->nins++] = in;
                    }
                }
            }
        }
        if (r.p != send) r.p = send;
    }
    if (r.bad) { snprintf(err, errcap, "truncated or corrupt module"); mod_free(m); return NULL; }
    return m;
}

/* ---------------- SHA-256 ---------------- */
typedef struct { uint32_t h[8]; uint64_t len; uint8_t buf[64]; size_t bufn; } Sha256;
static const uint32_t K256[64] = {
    0x428a2f98,0x71374491,0xb5c0fbcf,0xe9b5dba5,0x3956c25b,0x59f111f1,0x923f82a4,0xab1c5ed5,
    0xd807aa98,0x12835b01,0x243185be,0x550c7dc3,0x72be5d74,0x80deb1fe,0x9bdc06a7,0xc19bf174,
    0xe49b69c1,0xefbe4786,0x0fc19dc6,0x240ca1cc,0x2de92c6f,0x4a7484aa,0x5cb0a9dc,0x76f988da,
    0x983e5152,0xa831c66d,0xb00327c8,0xbf597fc7,0xc6e00bf3,0xd5a79147,0x06ca6351,0x14292967,
    0x27b70a85,0x2e1b2138,0x4d2c6dfc,0x53380d13,0x650a7354,0x766a0abb,0x81c2c92e,0x92722c85,
    0xa2bfe8a1,0xa81a664b,0xc24b8b70,0xc76c51a3,0xd192e819,0xd6990624,0xf40e3585,0x106aa070,
    0x19a4c116,0x1e376c08,0x2748774c,0x34b0bcb5,0x391c0cb3,0x4ed8aa4a,0x5b9cca4f,0x682e6ff3,
    0x748f82ee,0x78a5636f,0x84c87814,0x8cc70208,0x90befffa,0xa4506ceb,0xbef9a3f7,0xc67178f2 };
#define RR(x,n) (((x) >> (n)) | ((x) << (32 - (n))))
static void sha_block(Sha256 *s, const uint8_t *p) {
    uint32_t w[64];
    for (int i = 0; i < 16; i++) w[i] = ((uint32_t)p[i*4] << 24) | ((uint32_t)p[i*4+1] << 16) | ((uint32_t)p[i*4+2] << 8) | p[i*4+3];
    for (int i = 16; i < 64; i++) {
        uint32_t s0 = RR(w[i-15],7) ^ RR(w[i-15],18) ^ (w[i-15] >> 3);
        uint32_t s1 = RR(w[i-2],17) ^ RR(w[i-2],19) ^ (w[i-2] >> 10);
        w[i] = w[i-16] + s0 + w[i-7] + s1;
    }
    uint32_t a=s->h[0],b=s->h[1],c=s->h[2],d=s->h[3],e=s->h[4],f=s->h[5],g=s->h[6],h=s->h[7];
    for (int i = 0; i < 64; i++) {
        uint32_t S1 = RR(e,6) ^ RR(e,11) ^ RR(e,25);
        uint32_t ch = (e & f) ^ (~e & g);
        uint32_t t1 = h + S1 + ch + K256[i] + w[i];
        uint32_t S0 = RR(a,2) ^ RR(a,13) ^ RR(a,22);
        uint32_t mj = (a & b) ^ (a & c) ^ (b & c);
        uint32_t t2 = S0 + mj;
        h=g; g=f; f=e; e=d+t1; d=c; c=b; b=a; a=t1+t2;
    }
    s->h[0]+=a; s->h[1]+=b; s->h[2]+=c; s->h[3]+=d; s->h[4]+=e; s->h[5]+=f; s->h[6]+=g; s->h[7]+=h;
}
static void sha_init(Sha256 *s) {
    static const uint32_t H0[8] = { 0x6a09e667,0xbb67ae85,0x3c6ef372,0xa54ff53a,0x510e527f,0x9b05688c,0x1f83d9ab,0x5be0cd19 };
    memcpy(s->h, H0, sizeof H0); s->len = 0; s->bufn = 0;
}
static void sha_upd(Sha256 *s, const uint8_t *p, size_t n) {
    s->len += n;
    while (n) {
        size_t take = 64 - s->bufn; if (take > n) take = n;
        memcpy(s->buf + s->bufn, p, take); s->bufn += take; p += take; n -= take;
        if (s->bufn == 64) { sha_block(s, s->buf); s->bufn = 0; }
    }
}
static void sha_fin(Sha256 *s, uint8_t out[32]) {
    uint64_t bits = s->len * 8;
    uint8_t pad = 0x80; sha_upd(s, &pad, 1);
    uint8_t z = 0; while (s->bufn != 56) sha_upd(s, &z, 1);
    uint8_t lb[8]; for (int i = 0; i < 8; i++) lb[i] = (uint8_t)(bits >> (56 - 8 * i));
    /* write length directly: bypass len counting */
    memcpy(s->buf + 56, lb, 8); sha_block(s, s->buf);
    for (int i = 0; i < 8; i++) {
        out[i*4] = (uint8_t)(s->h[i] >> 24); out[i*4+1] = (uint8_t)(s->h[i] >> 16);
        out[i*4+2] = (uint8_t)(s->h[i] >> 8); out[i*4+3] = (uint8_t)(s->h[i]);
    }
}
void mod_hash(Module *m, uint8_t out[32]) {
    size_t n; uint8_t *enc = mod_encode(m, &n);
    Sha256 s; sha_init(&s); sha_upd(&s, enc, n); sha_fin(&s, out);
    free(enc);
}
