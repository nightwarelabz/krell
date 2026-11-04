/* Krell — reference interpreter: docs/SEMANTICS.md made executable.
 * Single flat little-endian memory; data blobs low, bump region above.
 * The interpreter's vector length is fixed at 128 bits (vl_i32 = 4). */
#include "krell.h"
#include <math.h>

#define MEM_SIZE (64ull << 20)
#define MAX_HOSTS 64
#define MAX_DEPTH 4096

struct Interp {
    Module *m;
    uint8_t *mem;
    uint64_t bump;
    uint64_t *data_addr;
    struct { char name[64]; HostFn fn; void *ctx; } hosts[MAX_HOSTS];
    int nhosts;
    char err[256];
    long fuel;
    int depth;
};

int ty_lanes(Type t, int vl_i32) {
    if (t.kind == TY_INT && t.bits == 128) return 2;   /* i128 scalar: (lo, hi) lanes */
    if (t.kind != TY_VEC) return 1;
    int per = (vl_i32 * 32) / t.elem_bits;   /* lanes per vscale unit */
    return per * t.n;
}

IVal ival_make(uint64_t x) {
    IVal v; v.lanes = malloc(sizeof(uint64_t)); v.lanes[0] = x; return v;
}
uint64_t ival_u64(IVal v) { return v.lanes[0]; }

Interp *interp_new(Module *m) {
    Interp *it = calloc(1, sizeof(Interp));
    it->m = m;
    it->mem = calloc(1, MEM_SIZE);
    it->fuel = 2000000000L;
    it->data_addr = malloc(sizeof(uint64_t) * (size_t)(m->ndata ? m->ndata : 1));
    uint64_t cur = 0x1000;
    for (int i = 0; i < m->ndata; i++) {
        uint64_t al = m->data[i].align ? m->data[i].align : 1;
        cur = (cur + al - 1) & ~(al - 1);
        it->data_addr[i] = cur;
        memcpy(it->mem + cur, m->data[i].bytes, m->data[i].len);
        cur += m->data[i].len;
    }
    it->bump = (cur + 4095) & ~4095ull;
    return it;
}
void interp_free(Interp *it) {
    if (!it) return;
    free(it->mem); free(it->data_addr); free(it);
}
void interp_host(Interp *it, const char *name, HostFn fn, void *ctx) {
    if (it->nhosts >= MAX_HOSTS) return;
    snprintf(it->hosts[it->nhosts].name, 64, "%s", name);
    it->hosts[it->nhosts].fn = fn;
    it->hosts[it->nhosts].ctx = ctx;
    it->nhosts++;
}
uint8_t *interp_mem(Interp *it, size_t *size) { if (size) *size = MEM_SIZE; return it->mem; }
uint64_t interp_alloc(Interp *it, size_t size, size_t align) {
    if (align < 1) align = 1;
    it->bump = (it->bump + align - 1) & ~(uint64_t)(align - 1);
    uint64_t a = it->bump;
    it->bump += size;
    return a;
}
int interp_last_error(Interp *it, char *buf, size_t cap) {
    snprintf(buf, cap, "%s", it->err);
    return it->err[0] ? -1 : 0;
}
static int ierr(Interp *it, const char *msg) { snprintf(it->err, sizeof it->err, "%s", msg); return -1; }

/* ---------- scalar helpers ---------- */
static uint64_t msk(int bits) { return bits >= 64 ? ~0ull : ((1ull << bits) - 1ull); }
static unsigned __int128 val128(const uint64_t *L) { return ((unsigned __int128)L[1] << 64) | (unsigned __int128)L[0]; }
static void put128(uint64_t *L, unsigned __int128 v) { L[0] = (uint64_t)v; L[1] = (uint64_t)(v >> 64); }
static int64_t sx(uint64_t v, int bits) {
    if (bits >= 64) return (int64_t)v;
    uint64_t m = 1ull << (bits - 1);
    return (int64_t)(((v & msk(bits)) ^ m) - m);
}
static float  as_f32(uint64_t b) { uint32_t u = (uint32_t)b; float f; memcpy(&f, &u, 4); return f; }
static double as_f64(uint64_t b) { double d; memcpy(&d, &b, 8); return d; }
static uint64_t bits_f32(float f) { uint32_t u; memcpy(&u, &f, 4); return u; }
static uint64_t bits_f64(double d) { uint64_t u; memcpy(&u, &d, 8); return u; }

static int64_t f2i(double d, int bits, bool unsig) {
    if (isnan(d)) return 0;
    if (!unsig) {
        int64_t lo = bits == 64 ? INT64_MIN : -(1ll << (bits - 1));
        int64_t hi = bits == 64 ? INT64_MAX : ((1ll << (bits - 1)) - 1);
        if (bits == 64) {
            if (d >= 9223372036854775808.0) return INT64_MAX;
            if (d <= -9223372036854775808.0) return INT64_MIN;
            return (int64_t)d;
        }
        int64_t v = (d >= 9223372036854775808.0) ? INT64_MAX :
                    (d <= -9223372036854775808.0) ? INT64_MIN : (int64_t)d;
        if (v > hi) v = hi;
        if (v < lo) v = lo;
        return v;
    }
    uint64_t hi = bits == 64 ? UINT64_MAX : ((1ull << bits) - 1ull);
    if (d <= 0.0) return 0;
    if (d >= 18446744073709551616.0) return (int64_t)hi;
    uint64_t v = (uint64_t)d;
    if (v > hi) v = hi;
    return (int64_t)v;
}

/* ---------- frame execution ---------- */
typedef struct { uint64_t **lanes; uint64_t *arena; int n; } Frame;

/* One zeroed arena per frame, values at fixed offsets: frame setup
 * is two allocations regardless of value count, and operand lanes
 * sit in one cache-friendly block instead of one calloc per value. */
static void frame_alloc(Interp *it, Func *f, Frame *fr) {
    (void)it;
    fr->n = f->nvalues;
    fr->lanes = malloc(sizeof(uint64_t *) * (size_t)(fr->n ? fr->n : 1));
    size_t total = 0;
    for (int i = 0; i < fr->n; i++) total += (size_t)ty_lanes(f->vtypes[i], 4);
    fr->arena = calloc(total ? total : 1, sizeof(uint64_t));
    size_t off = 0;
    for (int i = 0; i < fr->n; i++) {
        fr->lanes[i] = fr->arena + off;
        off += (size_t)ty_lanes(f->vtypes[i], 4);
    }
}
static void frame_free(Frame *fr) {
    free(fr->arena);
    free(fr->lanes);
}
static void val_copy(Func *f, Frame *fr, int dst, int src) {
    int ln = ty_lanes(f->vtypes[dst], 4);
    memcpy(fr->lanes[dst], fr->lanes[src], sizeof(uint64_t) * (size_t)ln);
}

static size_t mem_ty_size(Type t) {
    if (t.kind == TY_VEC) return (size_t)ty_lanes(t, 4) * (size_t)(t.elem_bits / 8);
    return (size_t)ty_bytes(t);
}

static int run_func(Interp *it, int fi, const IVal *args, int nargs, IVal *ret);

static int exec_block(Interp *it, Func *f, Frame *fr, int bi, int *next_blk,
                      int32_t **pend, int *npend, IVal *ret, bool *done) {
    Block *b = &f->blocks[bi];
    for (int ii = 0; ii < b->nins; ii++) {
        if (--it->fuel < 0) return ierr(it, "interp: fuel exhausted");
        Instr *in = &b->ins[ii];
        int op = in->op;
        uint64_t *R = in->result >= 0 ? fr->lanes[in->result] : NULL;
        uint64_t *A = in->a >= 0 ? fr->lanes[in->a] : NULL;
        uint64_t *B = in->b >= 0 ? fr->lanes[in->b] : NULL;
        uint64_t *C = in->c >= 0 ? fr->lanes[in->c] : NULL;
        Type ta = in->a >= 0 ? f->vtypes[in->a] : ty_void();
        switch (op) {
        case OP_ICONST: R[0] = (uint64_t)in->imm & msk(in->ty.bits); if (in->ty.bits == 128) R[1] = (uint64_t)in->imm2; break;
        case OP_FCONST: R[0] = (uint64_t)in->imm; break;
        case OP_FREEZE: val_copy(f, fr, in->result, in->a); break;
        case OP_ADD: if (in->ty.bits == 128) put128(R, val128(A) + val128(B)); else R[0] = (A[0] + B[0]) & msk(in->ty.bits); break;
        case OP_SUB: if (in->ty.bits == 128) put128(R, val128(A) - val128(B)); else R[0] = (A[0] - B[0]) & msk(in->ty.bits); break;
        case OP_MUL: if (in->ty.bits == 128) put128(R, val128(A) * val128(B)); else R[0] = (A[0] * B[0]) & msk(in->ty.bits); break;
        case OP_NEG: if (in->ty.bits == 128) put128(R, (unsigned __int128)0 - val128(A)); else R[0] = (0 - A[0]) & msk(in->ty.bits); break;
        case OP_AND: R[0] = A[0] & B[0]; if (in->ty.bits == 128) R[1] = A[1] & B[1]; break;
        case OP_OR:  R[0] = A[0] | B[0]; if (in->ty.bits == 128) R[1] = A[1] | B[1]; break;
        case OP_XOR: R[0] = A[0] ^ B[0]; if (in->ty.bits == 128) R[1] = A[1] ^ B[1]; break;
        case OP_NOT: R[0] = ~A[0] & msk(in->ty.bits); if (in->ty.bits == 128) R[1] = ~A[1]; break;
        case OP_UDIV: if (in->ty.bits == 128) { unsigned __int128 d = val128(B); put128(R, d ? val128(A) / d : 0); } else R[0] = B[0] ? (A[0] / B[0]) & msk(in->ty.bits) : 0; break;
        case OP_UREM: if (in->ty.bits == 128) { unsigned __int128 d = val128(B); put128(R, d ? val128(A) % d : 0); } else R[0] = B[0] ? (A[0] % B[0]) & msk(in->ty.bits) : 0; break;
        case OP_SDIV: {
            int bits = in->ty.bits;
            if (bits == 128) {
                /* unsigned magnitudes: INT_MIN / -1 wraps, /0 yields 0 */
                __int128 sa = (__int128)val128(A), sb = (__int128)val128(B);
                unsigned __int128 r = 0;
                if (sb != 0) {
                    unsigned __int128 ua = sa < 0 ? (unsigned __int128)0 - val128(A) : val128(A);
                    unsigned __int128 ub = sb < 0 ? (unsigned __int128)0 - val128(B) : val128(B);
                    unsigned __int128 q = ua / ub;
                    r = ((sa < 0) != (sb < 0)) ? (unsigned __int128)0 - q : q;
                }
                put128(R, r); break;
            }
            int64_t sa = sx(A[0], bits), sb = sx(B[0], bits);
            int64_t r = 0;
            if (sb != 0) r = (sb == -1 && sa == (bits == 64 ? INT64_MIN : -(1ll << (bits - 1)))) ? sa : sa / sb;
            R[0] = (uint64_t)r & msk(bits); break;
        }
        case OP_SREM: {
            int bits = in->ty.bits;
            if (bits == 128) {
                __int128 sa = (__int128)val128(A), sb = (__int128)val128(B);
                unsigned __int128 r = 0;
                if (sb != 0) {
                    unsigned __int128 ua = sa < 0 ? (unsigned __int128)0 - val128(A) : val128(A);
                    unsigned __int128 ub = sb < 0 ? (unsigned __int128)0 - val128(B) : val128(B);
                    unsigned __int128 q = ua % ub;
                    r = sa < 0 ? (unsigned __int128)0 - q : q;
                }
                put128(R, r); break;
            }
            int64_t sa = sx(A[0], bits), sb = sx(B[0], bits);
            int64_t r = 0;
            if (sb != 0) r = (sb == -1 && sa == (bits == 64 ? INT64_MIN : -(1ll << (bits - 1)))) ? 0 : sa % sb;
            R[0] = (uint64_t)r & msk(bits); break;
        }
        case OP_SHL: if (in->ty.bits == 128) put128(R, val128(A) << (unsigned)(val128(B) % 128)); else R[0] = (A[0] << (B[0] % (uint64_t)in->ty.bits)) & msk(in->ty.bits); break;
        case OP_LSHR: if (in->ty.bits == 128) put128(R, val128(A) >> (unsigned)(val128(B) % 128)); else R[0] = (A[0] & msk(in->ty.bits)) >> (B[0] % (uint64_t)in->ty.bits); break;
        case OP_ASHR: if (in->ty.bits == 128) put128(R, (unsigned __int128)((__int128)val128(A) >> (unsigned)(val128(B) % 128))); else R[0] = (uint64_t)(sx(A[0], in->ty.bits) >> (B[0] % (uint64_t)in->ty.bits)) & msk(in->ty.bits); break;
        case OP_ICMP: {
            int bits = ta.bits;
            bool r = false;
            if (bits == 128) {
                unsigned __int128 ua = val128(A), ub = val128(B);
                __int128 sa = (__int128)ua, sb = (__int128)ub;
                switch (in->pred) {
                case IC_EQ: r = ua == ub; break; case IC_NE: r = ua != ub; break;
                case IC_ULT: r = ua < ub; break; case IC_ULE: r = ua <= ub; break;
                case IC_UGT: r = ua > ub; break; case IC_UGE: r = ua >= ub; break;
                case IC_SLT: r = sa < sb; break; case IC_SLE: r = sa <= sb; break;
                case IC_SGT: r = sa > sb; break; case IC_SGE: r = sa >= sb; break;
                }
                R[0] = r ? 1 : 0; break;
            }
            uint64_t ua = A[0] & msk(bits), ub = B[0] & msk(bits);
            int64_t sa = sx(ua, bits), sb = sx(ub, bits);
            switch (in->pred) {
            case IC_EQ: r = ua == ub; break; case IC_NE: r = ua != ub; break;
            case IC_ULT: r = ua < ub; break; case IC_ULE: r = ua <= ub; break;
            case IC_UGT: r = ua > ub; break; case IC_UGE: r = ua >= ub; break;
            case IC_SLT: r = sa < sb; break; case IC_SLE: r = sa <= sb; break;
            case IC_SGT: r = sa > sb; break; case IC_SGE: r = sa >= sb; break;
            }
            R[0] = r ? 1 : 0; break;
        }
        case OP_POPCOUNT: { int c = 0; if (in->ty.bits == 128) { uint64_t x0 = A[0], x1 = A[1]; while (x0) { x0 &= x0 - 1; c++; } while (x1) { x1 &= x1 - 1; c++; } } else { uint64_t x = A[0] & msk(in->ty.bits); while (x) { x &= x - 1; c++; } } R[0] = (uint64_t)c; if (in->ty.bits == 128) R[1] = 0; break; }
        case OP_CLZ: { int bits = in->ty.bits, c = 0;
                       if (bits == 128) { if (A[1]) { uint64_t x = A[1]; for (int i = 63; i >= 0; i--) { if ((x >> i) & 1) break; c++; } } else { c = 64; uint64_t x = A[0]; for (int i = 63; i >= 0; i--) { if ((x >> i) & 1) break; c++; } } }
                       else { uint64_t x = A[0] & msk(bits); for (int i = bits - 1; i >= 0; i--) { if ((x >> i) & 1) break; c++; } } R[0] = (uint64_t)c; if (bits == 128) R[1] = 0; break; }
        case OP_CTZ: { int bits = in->ty.bits, c = 0;
                       if (bits == 128) { if (A[0]) { uint64_t x = A[0]; for (int i = 0; i < 64; i++) { if ((x >> i) & 1) break; c++; } } else { c = 64; uint64_t x = A[1]; for (int i = 0; i < 64; i++) { if ((x >> i) & 1) break; c++; } } }
                       else { uint64_t x = A[0] & msk(bits); for (int i = 0; i < bits; i++) { if ((x >> i) & 1) break; c++; } } R[0] = (uint64_t)c; if (bits == 128) R[1] = 0; break; }
        case OP_BSWAP: {
            if (in->ty.bits == 128) {
                put128(R, ((unsigned __int128)__builtin_bswap64(A[0]) << 64) | (unsigned __int128)__builtin_bswap64(A[1]));
                break;
            }
            uint64_t x = A[0]; int n = in->ty.bits / 8; uint64_t r = 0;
            for (int i = 0; i < n; i++) r = (r << 8) | ((x >> (8 * i)) & 0xff);
            R[0] = r; break;
        }
        case OP_TRUNC: case OP_ZEXT: R[0] = A[0] & msk(in->ty.bits); if (in->ty.bits == 128) R[1] = 0; break;
        case OP_SEXT: R[0] = (uint64_t)sx(A[0], ta.bits) & msk(in->ty.bits); if (in->ty.bits == 128) R[1] = sx(A[0], ta.bits) < 0 ? ~0ull : 0; break;
        case OP_FADD: case OP_FSUB: case OP_FMUL: case OP_FDIV: {
            if (in->ty.bits == 32) {
                float x = as_f32(A[0]), y = as_f32(B[0]), r = 0;
                r = op == OP_FADD ? x + y : op == OP_FSUB ? x - y : op == OP_FMUL ? x * y : x / y;
                R[0] = bits_f32(r);
            } else {
                double x = as_f64(A[0]), y = as_f64(B[0]), r = 0;
                r = op == OP_FADD ? x + y : op == OP_FSUB ? x - y : op == OP_FMUL ? x * y : x / y;
                R[0] = bits_f64(r);
            }
            break;
        }
        case OP_FNEG: R[0] = in->ty.bits == 32 ? bits_f32(-as_f32(A[0])) : bits_f64(-as_f64(A[0])); break;
        case OP_FABS: R[0] = in->ty.bits == 32 ? bits_f32(fabsf(as_f32(A[0]))) : bits_f64(fabs(as_f64(A[0]))); break;
        case OP_FMA:
            R[0] = in->ty.bits == 32 ? bits_f32(fmaf(as_f32(A[0]), as_f32(B[0]), as_f32(C[0])))
                                     : bits_f64(fma(as_f64(A[0]), as_f64(B[0]), as_f64(C[0])));
            break;
        case OP_FCMP: {
            bool r = false;
            if (ta.bits == 32) {
                float x = as_f32(A[0]), y = as_f32(B[0]);
                bool un = isnan(x) || isnan(y);
                switch (in->pred) {
                case FC_OEQ: r = !un && x == y; break; case FC_ONE: r = !un && x != y; break;
                case FC_OLT: r = !un && x < y; break;  case FC_OLE: r = !un && x <= y; break;
                case FC_OGT: r = !un && x > y; break;  case FC_OGE: r = !un && x >= y; break;
                case FC_UEQ: r = un || x == y; break;  case FC_UNE: r = un || x != y; break;
                case FC_ULT: r = un || x < y; break;   case FC_ULE: r = un || x <= y; break;
                case FC_UGT: r = un || x > y; break;   case FC_UGE: r = un || x >= y; break;
                case FC_ORD: r = !un; break;           case FC_UNO: r = un; break;
                }
            } else {
                double x = as_f64(A[0]), y = as_f64(B[0]);
                bool un = isnan(x) || isnan(y);
                switch (in->pred) {
                case FC_OEQ: r = !un && x == y; break; case FC_ONE: r = !un && x != y; break;
                case FC_OLT: r = !un && x < y; break;  case FC_OLE: r = !un && x <= y; break;
                case FC_OGT: r = !un && x > y; break;  case FC_OGE: r = !un && x >= y; break;
                case FC_UEQ: r = un || x == y; break;  case FC_UNE: r = un || x != y; break;
                case FC_ULT: r = un || x < y; break;   case FC_ULE: r = un || x <= y; break;
                case FC_UGT: r = un || x > y; break;   case FC_UGE: r = un || x >= y; break;
                case FC_ORD: r = !un; break;           case FC_UNO: r = un; break;
                }
            }
            R[0] = r ? 1 : 0; break;
        }
        case OP_FTRUNC: R[0] = bits_f32((float)as_f64(A[0])); break;
        case OP_FEXT:   R[0] = bits_f64((double)as_f32(A[0])); break;
        case OP_FPTOSI: case OP_FPTOUI: {
            double d = ta.bits == 32 ? (double)as_f32(A[0]) : as_f64(A[0]);
            R[0] = (uint64_t)f2i(d, in->ty.bits, op == OP_FPTOUI) & msk(in->ty.bits);
            break;
        }
        case OP_SITOFP: case OP_UITOFP: {
            if (in->ty.bits == 32) {
                float v = op == OP_SITOFP ? (float)sx(A[0], ta.bits) : (float)(A[0] & msk(ta.bits));
                R[0] = bits_f32(v);
            } else {
                double v = op == OP_SITOFP ? (double)sx(A[0], ta.bits) : (double)(A[0] & msk(ta.bits));
                R[0] = bits_f64(v);
            }
            break;
        }
        case OP_BITCAST: R[0] = A[0]; break;
        case OP_SELECT: {
            int src = A[0] ? in->b : in->c;
            val_copy(f, fr, in->result, src);
            break;
        }
        case OP_ASSUME: break;
        case OP_FENCE: break;   /* ordering barrier; no value semantics on one thread */
        case OP_ALLOCA: {
            uint64_t al = in->c > 0 ? (uint64_t)in->c : 1;
            it->bump = (it->bump + al - 1) & ~(al - 1);
            R[0] = it->bump;
            it->bump += (uint64_t)in->imm;
            if (it->bump >= MEM_SIZE) return ierr(it, "interp: memory exhausted");
            break;
        }
        case OP_DATAPTR: R[0] = it->data_addr[in->imm]; break;
        case OP_GEP: {
            int64_t i2 = sx(B[0], f->vtypes[in->b].bits);
            R[0] = A[0] + (uint64_t)(i2 * (int64_t)mem_ty_size(in->ety));
            break;
        }
        case OP_LOAD: case OP_LOADV: {
            /* volatile: in the single-threaded reference interpreter a
             * volatile access has the same value semantics as a plain
             * one; its ordering/non-elimination force applies to the
             * optimizer and the backends, which treat it as opaque. */
            uint64_t addr = A[0];
            size_t n = mem_ty_size(in->ty);
            if (addr + n > MEM_SIZE) return ierr(it, "interp: load out of range");
            if (in->ty.kind == TY_VEC) {
                int ln = ty_lanes(in->ty, 4), eb = in->ty.elem_bits / 8;
                for (int i = 0; i < ln; i++) {
                    uint64_t v = 0; memcpy(&v, it->mem + addr + (size_t)i * eb, (size_t)eb);
                    R[i] = v;
                }
            } else if (n > 8) {
                /* wide scalar (i128): copy lane-wise; a single u64
                 * temporary would overflow (and did, latently) */
                memcpy(R, it->mem + addr, n);
            } else {
                uint64_t v = 0; memcpy(&v, it->mem + addr, n);
                R[0] = in->ty.kind == TY_INT ? v & msk(in->ty.bits) : v;
            }
            break;
        }
        case OP_STORE: case OP_STOREV: {
            uint64_t addr = A[0];
            size_t n = mem_ty_size(in->ty);
            if (addr + n > MEM_SIZE) return ierr(it, "interp: store out of range");
            if (n > 8) memcpy(it->mem + addr, B, n);
            else { uint64_t v = B[0]; memcpy(it->mem + addr, &v, n); }
            break;
        }
        case OP_VLOAD: {
            uint64_t addr = A[0];
            int ln = ty_lanes(in->ty, 4), eb = in->ty.elem_bits / 8;
            if (addr + (size_t)ln * eb > MEM_SIZE) return ierr(it, "interp: vload out of range");
            for (int i = 0; i < ln; i++) { uint64_t v = 0; memcpy(&v, it->mem + addr + (size_t)i * eb, (size_t)eb); R[i] = v; }
            break;
        }
        case OP_VSTORE: {
            uint64_t addr = A[0];
            int ln = ty_lanes(f->vtypes[in->b], 4), eb = f->vtypes[in->b].elem_bits / 8;
            if (addr + (size_t)ln * eb > MEM_SIZE) return ierr(it, "interp: vstore out of range");
            for (int i = 0; i < ln; i++) memcpy(it->mem + addr + (size_t)i * eb, &B[i], (size_t)eb);
            break;
        }
        case OP_MEMCPY: memmove(it->mem + A[0], it->mem + B[0], (size_t)C[0]); break;
        case OP_MEMSET: memset(it->mem + A[0], (int)(B[0] & 0xff), (size_t)C[0]); break;
        case OP_VSPLAT: {
            int ln = ty_lanes(in->ty, 4);
            for (int i = 0; i < ln; i++) R[i] = A[0];
            break;
        }
        case OP_VADD: case OP_VSUB: case OP_VMUL: case OP_VUDIV:
        case OP_VAND: case OP_VOR: case OP_VXOR: case OP_VLSHR:
        case OP_VFADD: case OP_VFSUB: case OP_VFMUL: case OP_VFDIV: {
            Type et = ty_elem(in->ty);
            int ln = ty_lanes(in->ty, 4);
            for (int i = 0; i < ln; i++) {
                uint64_t x = A[i], y = B[i], r = 0;
                if (et.kind == TY_FLOAT) {
                    if (et.bits == 32) {
                        float fx = as_f32(x), fy = as_f32(y), fr2 = 0;
                        fr2 = op == OP_VFADD ? fx + fy : op == OP_VFSUB ? fx - fy : op == OP_VFMUL ? fx * fy : fx / fy;
                        r = bits_f32(fr2);
                    } else {
                        double fx = as_f64(x), fy = as_f64(y), fr2 = 0;
                        fr2 = op == OP_VFADD ? fx + fy : op == OP_VFSUB ? fx - fy : op == OP_VFMUL ? fx * fy : fx / fy;
                        r = bits_f64(fr2);
                    }
                } else {
                    uint64_t m = msk(et.bits);
                    switch (op) {
                    case OP_VADD: r = (x + y) & m; break;
                    case OP_VSUB: r = (x - y) & m; break;
                    case OP_VMUL: r = (x * y) & m; break;
                    case OP_VUDIV: r = y ? (x / y) & m : 0; break;
                    case OP_VAND: r = x & y; break;
                    case OP_VOR:  r = x | y; break;
                    case OP_VXOR: r = x ^ y; break;
                    case OP_VLSHR: r = ((x & m) >> (y % (uint64_t)et.bits)) & m; break;
                    default: r = 0; break;
                    }
                }
                R[i] = r;
            }
            break;
        }
        case OP_VEXTRACT: R[0] = A[in->imm]; break;
        case OP_VINSERT: val_copy(f, fr, in->result, in->a); R[in->imm] = B[0]; break;
        case OP_ALOAD: {
            uint64_t v = 0; size_t n = mem_ty_size(in->ty);
            if (A[0] + n > MEM_SIZE) return ierr(it, "interp: aload out of range");
            memcpy(&v, it->mem + A[0], n); R[0] = v & msk(in->ty.bits);
            break;
        }
        case OP_ASTORE: {
            size_t n = mem_ty_size(f->vtypes[in->b]);
            if (A[0] + n > MEM_SIZE) return ierr(it, "interp: astore out of range");
            uint64_t v = B[0]; memcpy(it->mem + A[0], &v, n);
            break;
        }
        case OP_AADD: {
            size_t n = mem_ty_size(in->ty);
            uint64_t v = 0; memcpy(&v, it->mem + A[0], n);
            R[0] = v & msk(in->ty.bits);
            uint64_t nv = (v + B[0]) & msk(in->ty.bits);
            memcpy(it->mem + A[0], &nv, n);
            break;
        }
        case OP_ACMPXCHG: {
            /* strong cmpxchg: result is the old value; the cell takes
             * the desired value iff old == expected (no spurious failure) */
            size_t n = mem_ty_size(in->ty);
            if (A[0] + n > MEM_SIZE) return ierr(it, "interp: acmpxchg out of range");
            uint64_t v = 0; memcpy(&v, it->mem + A[0], n);
            R[0] = v & msk(in->ty.bits);
            if (R[0] == (B[0] & msk(in->ty.bits))) {
                uint64_t nv = C[0] & msk(in->ty.bits);
                memcpy(it->mem + A[0], &nv, n);
            }
            break;
        }
        case OP_AXCHG: case OP_ASUB: case OP_AAND: case OP_AOR: case OP_AXOR:
        case OP_AMINS: case OP_AMAXS: case OP_AMINU: case OP_AMAXU: {
            size_t n = mem_ty_size(in->ty);
            if (A[0] + n > MEM_SIZE) return ierr(it, "interp: atomic rmw out of range");
            uint64_t v = 0; memcpy(&v, it->mem + A[0], n);
            uint64_t old = v & msk(in->ty.bits);
            R[0] = old;
            uint64_t b = B[0] & msk(in->ty.bits);
            uint64_t nv;
            switch (in->op) {
            case OP_AXCHG: nv = b; break;
            case OP_ASUB:  nv = (old - b) & msk(in->ty.bits); break;
            case OP_AAND:  nv = old & b; break;
            case OP_AOR:   nv = old | b; break;
            case OP_AXOR:  nv = old ^ b; break;
            case OP_AMINS: nv = sx(old, in->ty.bits) < sx(b, in->ty.bits) ? old : b; break;
            case OP_AMAXS: nv = sx(old, in->ty.bits) > sx(b, in->ty.bits) ? old : b; break;
            case OP_AMINU: nv = old < b ? old : b; break;
            default:       nv = old > b ? old : b; break;   /* OP_AMAXU */
            }
            memcpy(it->mem + A[0], &nv, n);
            break;
        }
        case OP_CALL: {
            IVal *cargs = malloc(sizeof(IVal) * (size_t)(in->nargs ? in->nargs : 1));
            for (int i = 0; i < in->nargs; i++) cargs[i].lanes = fr->lanes[in->args[i]];
            int rc;
            if (in->callee_extern) {
                Extern *e = &it->m->exts[in->callee];
                HostFn hf = NULL; void *ctx = NULL;
                for (int h = 0; h < it->nhosts; h++)
                    if (strcmp(it->hosts[h].name, e->name) == 0) { hf = it->hosts[h].fn; ctx = it->hosts[h].ctx; break; }
                if (!hf) { free(cargs); return ierr(it, "interp: unresolved extern"); }
                IVal rv; rv.lanes = R;
                hf(it, ctx, cargs, in->nargs, &rv);
                rc = 0;
            } else {
                IVal rv; rv.lanes = R;
                rc = run_func(it, in->callee, cargs, in->nargs, in->ty.kind == TY_VOID ? NULL : &rv);
            }
            free(cargs);
            if (rc) return rc;
            break;
        }
        case OP_BR: case OP_CONDBR: {
            int tgt; const int32_t *targs; int tn;
            if (op == OP_BR) { tgt = in->blk; targs = in->args; tn = in->nargs; }
            else if (A[0])   { tgt = in->blk; targs = in->args; tn = in->nargs; }
            else             { tgt = in->blk2; targs = in->args2; tn = in->nargs2; }
            /* snapshot then bind (parallel copy) */
            int maxl = 1;
            for (int i = 0; i < tn; i++) { int l = ty_lanes(f->vtypes[targs[i]], 4); if (l > maxl) maxl = l; }
            uint64_t *snap = malloc(sizeof(uint64_t) * (size_t)maxl * (size_t)(tn ? tn : 1));
            for (int i = 0; i < tn; i++)
                memcpy(snap + (size_t)i * maxl, fr->lanes[targs[i]], sizeof(uint64_t) * (size_t)ty_lanes(f->vtypes[targs[i]], 4));
            Block *tb = &f->blocks[tgt];
            for (int i = 0; i < tn; i++)
                memcpy(fr->lanes[tb->arg_vals[i]], snap + (size_t)i * maxl, sizeof(uint64_t) * (size_t)ty_lanes(f->vtypes[targs[i]], 4));
            free(snap);
            *next_blk = tgt; *pend = NULL; *npend = 0;
            return 0;
        }
        case OP_RET: {
            if (in->a >= 0 && ret) {
                int ln = ty_lanes(f->vtypes[in->a], 4);
                memcpy(ret->lanes, fr->lanes[in->a], sizeof(uint64_t) * (size_t)ln);
            }
            *done = true;
            return 0;
        }
        case OP_TAILCALL: {
            /* handled by run_func loop: signal via special state */
            *next_blk = -2;
            /* stash call info in pend: encode callee/args into static slots */
            *pend = (int32_t *)in;   /* borrowed; run_func reads it */
            *npend = 1;
            return 0;
        }
        default:
            return ierr(it, "interp: unimplemented opcode");
        }
    }
    return ierr(it, "interp: block without terminator");
}

static void args_free(IVal *a, int n) {
    if (!a) return;
    for (int i = 0; i < n; i++) free(a[i].lanes);
    free(a);
}
/* deep-copy args using the callee's parameter types for lane counts */
static IVal *args_copy(Func *callee, const IVal *args, int nargs) {
    IVal *out = malloc(sizeof(IVal) * (size_t)(nargs ? nargs : 1));
    for (int i = 0; i < nargs; i++) {
        int ln = ty_lanes(callee->blocks[0].arg_types[i], 4);
        out[i].lanes = malloc(sizeof(uint64_t) * (size_t)ln);
        memcpy(out[i].lanes, args[i].lanes, sizeof(uint64_t) * (size_t)ln);
    }
    return out;
}

static int run_func(Interp *it, int fi, const IVal *args, int nargs, IVal *ret) {
    if (++it->depth > MAX_DEPTH) { it->depth--; return ierr(it, "interp: call depth exceeded"); }
    uint64_t saved_bump = it->bump;
    int cur_fi = fi;
    IVal *cur_args = args_copy(&it->m->funcs[fi], args, nargs);   /* owned */
    int cur_nargs = nargs;
    int rc = 0;
    for (;;) {
        Func *cf = &it->m->funcs[cur_fi];
        Frame fr;
        frame_alloc(it, cf, &fr);
        Block *b0 = &cf->blocks[0];
        if (cur_nargs != b0->nargs) { frame_free(&fr); rc = ierr(it, "interp: argument count mismatch"); break; }
        for (int i = 0; i < cur_nargs; i++) {
            int ln = ty_lanes(cf->vtypes[b0->arg_vals[i]], 4);
            memcpy(fr.lanes[b0->arg_vals[i]], cur_args[i].lanes, sizeof(uint64_t) * (size_t)ln);
            /* canonical form: integer arguments are masked to their width
             * at the function boundary (mirrors the backends' entry mask) */
            Type pt = b0->arg_types[i];
            if (pt.kind == TY_INT) fr.lanes[b0->arg_vals[i]][0] &= msk(pt.bits);
        }
        int blk = 0; bool done = false; bool tailed = false;
        while (!done) {
            int next_blk = -1, npend = 0; int32_t *pend = NULL;
            rc = exec_block(it, cf, &fr, blk, &next_blk, &pend, &npend, ret, &done);
            if (rc || done) break;
            if (next_blk == -2) {
                Instr *in = (Instr *)pend;   /* the TAILCALL instruction */
                if (in->callee_extern) {
                    Extern *e = &it->m->exts[in->callee];
                    HostFn hf = NULL; void *ctx = NULL;
                    for (int h = 0; h < it->nhosts; h++)
                        if (strcmp(it->hosts[h].name, e->name) == 0) { hf = it->hosts[h].fn; ctx = it->hosts[h].ctx; break; }
                    if (!hf) rc = ierr(it, "interp: unresolved extern");
                    else {
                        IVal *cargs = malloc(sizeof(IVal) * (size_t)(in->nargs ? in->nargs : 1));
                        for (int i = 0; i < in->nargs; i++) cargs[i].lanes = fr.lanes[in->args[i]];
                        IVal rv; rv.lanes = ret ? ret->lanes : NULL;
                        hf(it, ctx, cargs, in->nargs, &rv);
                        free(cargs);
                    }
                    frame_free(&fr);
                    tailed = true; cur_fi = -1;
                    break;
                }
                /* snapshot the callee's arguments, release the frame, loop */
                IVal *snap = malloc(sizeof(IVal) * (size_t)(in->nargs ? in->nargs : 1));
                for (int i = 0; i < in->nargs; i++) snap[i].lanes = fr.lanes[in->args[i]];
                IVal *na = args_copy(&it->m->funcs[in->callee], snap, in->nargs);
                free(snap);
                frame_free(&fr);
                args_free(cur_args, cur_nargs);
                cur_args = na; cur_nargs = in->nargs; cur_fi = in->callee;
                tailed = true;
                break;
            }
            blk = next_blk;
        }
        if (!tailed) { frame_free(&fr); break; }
        if (cur_fi < 0) break;
        /* loop: execute the tail-called function in this same frame budget */
    }
    args_free(cur_args, cur_nargs);
    it->bump = saved_bump;
    it->depth--;
    return rc;
}

int interp_call(Interp *it, const char *funcname, const IVal *args, int nargs, IVal *ret) {
    int fi = mod_find_func(it->m, funcname);
    if (fi < 0) return ierr(it, "interp: no such function");
    it->err[0] = 0;
    return run_func(it, fi, args, nargs, ret);
}
