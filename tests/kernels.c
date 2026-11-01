/* Acceptance kernels, shared by every phase's gate:
 *   fill32(dst, n, val)              — CASM's ps15_fill32 shape
 *   span(dst, tex, w, u0,v0, du,dv, light) — one textured, lit span
 * Built once here, consumed by the interpreter test and the backend tests.
 * The C reference implementations define the expected bytes. */
#include "krell.h"
#include <stdio.h>
#include <string.h>

/* ---------------- C references ---------------- */
void ref_fill32(uint32_t *dst, int64_t n, uint32_t val) {
    for (int64_t i = 0; i < n; i++) dst[i] = val;
}
void ref_span(uint32_t *dst, const uint32_t *tex, int64_t w,
              int32_t u0, int32_t v0, int32_t du, int32_t dv, int32_t light) {
    int32_t u = u0, v = v0;
    for (int64_t x = 0; x < w; x++) {
        int tx = (u >> 16) & 63, ty = (v >> 16) & 63;
        uint32_t px = tex[ty * 64 + tx];
        uint32_t r = (((px >> 16) & 0xff) * (uint32_t)light) >> 8;
        uint32_t g = (((px >> 8) & 0xff) * (uint32_t)light) >> 8;
        uint32_t b = ((px & 0xff) * (uint32_t)light) >> 8;
        dst[x] = (r << 16) | (g << 8) | b;
        u += du; v += dv;
    }
}

/* ---------------- Krell builders ---------------- */
/* fill32(ptr dst, i64 n, i32 val) -> void
 *   b0(dst, n, val) -> b1(0)
 *   b1(i): cmp i<n; condbr b2(i) / b3()
 *   b2(i): store val at dst + i*4; br b1(i+1)
 *   b3(): ret */
Module *build_kernels(void) {
    Module *m = mod_new();
    /* ---- fill32 ---- */
    {
        Func *f = mod_add_func(m, "fill32", ty_void(), 0);
        Type pa[3] = { ty_ptr(), ty_i64(), ty_i32() };
        int b0 = func_add_block(f, pa, 3);
        int b1 = func_add_block(f, (Type[]){ ty_i64() }, 1);
        int b2 = func_add_block(f, (Type[]){ ty_i64() }, 1);
        int b3 = func_add_block(f, NULL, 0);
        int dst = f->blocks[b0].arg_vals[0];
        int n   = f->blocks[b0].arg_vals[1];
        int val = f->blocks[b0].arg_vals[2];
        int zero = emit(f, b0, ins_iconst(ty_i64(), 0));
        emit(f, b0, ins_br(b1, ids_dup((int32_t[]){ zero }, 1), 1));
        int i1 = f->blocks[b1].arg_vals[0];
        Instr cmp = ins_make(OP_ICMP, ty_i1()); cmp.a = i1; cmp.b = n; cmp.pred = IC_SLT;
        int c = emit(f, b1, cmp);
        emit(f, b1, ins_condbr(c, b2, ids_dup((int32_t[]){ i1 }, 1), 1, b3, NULL, 0));
        int i2 = f->blocks[b2].arg_vals[0];
        Instr gep = ins_make(OP_GEP, ty_ptr()); gep.a = dst; gep.b = i2; gep.ety = ty_i32();
        int p = emit(f, b2, gep);
        Instr st = ins_make(OP_STORE, ty_i32()); st.a = p; st.b = val;
        emit(f, b2, st);
        int one = emit(f, b2, ins_iconst(ty_i64(), 1));
        int inext = emit(f, b2, ins_bin(OP_ADD, ty_i64(), i2, one));
        emit(f, b2, ins_br(b1, ids_dup((int32_t[]){ inext }, 1), 1));
        emit(f, b3, ins_ret(-1));
    }
    /* ---- span(ptr dst, ptr tex, i64 w, i32 u0, i32 v0, i32 du, i32 dv, i32 light) -> void
     * loop block carries (x, u, v) */
    {
        Func *f = mod_add_func(m, "span", ty_void(), 0);
        Type pa[8] = { ty_ptr(), ty_ptr(), ty_i64(), ty_i32(), ty_i32(), ty_i32(), ty_i32(), ty_i32() };
        int b0 = func_add_block(f, pa, 8);
        int b1 = func_add_block(f, (Type[]){ ty_i64(), ty_i32(), ty_i32() }, 3);
        int b2 = func_add_block(f, (Type[]){ ty_i64(), ty_i32(), ty_i32() }, 3);
        int b3 = func_add_block(f, NULL, 0);
        int dst = f->blocks[b0].arg_vals[0];
        int tex = f->blocks[b0].arg_vals[1];
        int w   = f->blocks[b0].arg_vals[2];
        int u0  = f->blocks[b0].arg_vals[3];
        int v0  = f->blocks[b0].arg_vals[4];
        int du  = f->blocks[b0].arg_vals[5];
        int dv  = f->blocks[b0].arg_vals[6];
        int light = f->blocks[b0].arg_vals[7];
        int zero = emit(f, b0, ins_iconst(ty_i64(), 0));
        emit(f, b0, ins_br(b1, ids_dup((int32_t[]){ zero, u0, v0 }, 3), 3));
        int x1 = f->blocks[b1].arg_vals[0];
        Instr cmp = ins_make(OP_ICMP, ty_i1()); cmp.a = x1; cmp.b = w; cmp.pred = IC_SLT;
        int c = emit(f, b1, cmp);
        int u1 = f->blocks[b1].arg_vals[1], v1 = f->blocks[b1].arg_vals[2];
        emit(f, b1, ins_condbr(c, b2, ids_dup((int32_t[]){ x1, u1, v1 }, 3), 3, b3, NULL, 0));
        int x = f->blocks[b2].arg_vals[0], u = f->blocks[b2].arg_vals[1], v = f->blocks[b2].arg_vals[2];
        int c16 = emit(f, b2, ins_iconst(ty_i32(), 16));
        int c63 = emit(f, b2, ins_iconst(ty_i32(), 63));
        int c6  = emit(f, b2, ins_iconst(ty_i32(), 6));
        int tx = emit(f, b2, ins_bin(OP_AND, ty_i32(),
                        emit(f, b2, ins_bin(OP_ASHR, ty_i32(), u, c16)), c63));
        int tyv = emit(f, b2, ins_bin(OP_AND, ty_i32(),
                        emit(f, b2, ins_bin(OP_ASHR, ty_i32(), v, c16)), c63));
        int trow = emit(f, b2, ins_bin(OP_SHL, ty_i32(), tyv, c6));
        int tidx32 = emit(f, b2, ins_bin(OP_ADD, ty_i32(), trow, tx));
        int tidx = emit(f, b2, ins_un(OP_SEXT, ty_i64(), tidx32));
        Instr gep = ins_make(OP_GEP, ty_ptr()); gep.a = tex; gep.b = tidx; gep.ety = ty_i32();
        int tp = emit(f, b2, gep);
        Instr ld = ins_make(OP_LOAD, ty_i32()); ld.a = tp;
        int px = emit(f, b2, ld);
        int c255 = emit(f, b2, ins_iconst(ty_i32(), 255));
        int c8 = emit(f, b2, ins_iconst(ty_i32(), 8));
        /* channel(px, shift) = ((px >> shift) & 255) * light >> 8 */
        #define CHAN(shift) ({ \
            int s_ = emit(f, b2, ins_iconst(ty_i32(), (shift))); \
            int sh_ = (shift) ? emit(f, b2, ins_bin(OP_LSHR, ty_i32(), px, s_)) : px; \
            int m_ = emit(f, b2, ins_bin(OP_AND, ty_i32(), sh_, c255)); \
            int ml_ = emit(f, b2, ins_bin(OP_MUL, ty_i32(), m_, light)); \
            emit(f, b2, ins_bin(OP_LSHR, ty_i32(), ml_, c8)); })
        int r = CHAN(16), g = CHAN(8), bch = CHAN(0);
        #undef CHAN
        int rsh = emit(f, b2, ins_bin(OP_SHL, ty_i32(), r, c16));
        int gsh = emit(f, b2, ins_bin(OP_SHL, ty_i32(), g, c8));
        int packed = emit(f, b2, ins_bin(OP_OR, ty_i32(),
                        emit(f, b2, ins_bin(OP_OR, ty_i32(), rsh, gsh)), bch));
        Instr gep2 = ins_make(OP_GEP, ty_ptr()); gep2.a = dst; gep2.b = x; gep2.ety = ty_i32();
        int dp = emit(f, b2, gep2);
        Instr st = ins_make(OP_STORE, ty_i32()); st.a = dp; st.b = packed;
        emit(f, b2, st);
        int one = emit(f, b2, ins_iconst(ty_i64(), 1));
        int xn = emit(f, b2, ins_bin(OP_ADD, ty_i64(), x, one));
        int un = emit(f, b2, ins_bin(OP_ADD, ty_i32(), u, du));
        int vn = emit(f, b2, ins_bin(OP_ADD, ty_i32(), v, dv));
        emit(f, b2, ins_br(b1, ids_dup((int32_t[]){ xn, un, vn }, 3), 3));
        emit(f, b3, ins_ret(-1));
    }
    return m;
}

/* ---------------- interpreter-side test ---------------- */
#ifndef KERNELS_NO_MAIN
static int failures = 0;
#define CHECK(cond, msg) do { if (!(cond)) { printf("FAIL: %s\n", msg); failures++; } } while (0)

int main(void) {
    Module *m = build_kernels();
    const char *e = mod_verify(m);
    CHECK(e == NULL, e ? e : "verify");
    if (e) { printf("verify error: %s\n", e); return 1; }

    Interp *it = interp_new(m);
    size_t memsz; uint8_t *mem = interp_mem(it, &memsz);
    (void)memsz;
    /* fill32 in interp memory */
    uint64_t dst = interp_alloc(it, 4096, 8);
    IVal a_dst = ival_make(dst), a_n = ival_make(257), a_val = ival_make(0xdeadbeef);
    IVal args1[3] = { a_dst, a_n, a_val };
    int rc = interp_call(it, "fill32", args1, 3, NULL);
    CHECK(rc == 0, "fill32 interp run");
    uint32_t *got = (uint32_t *)(mem + dst);
    uint32_t want[257];
    ref_fill32(want, 257, 0xdeadbeef);
    CHECK(memcmp(got, want, sizeof want) == 0, "fill32 bytes match reference");
    free(a_dst.lanes); free(a_n.lanes); free(a_val.lanes);

    /* span in interp memory */
    uint64_t texp = interp_alloc(it, 64 * 64 * 4, 8);
    uint64_t dstp = interp_alloc(it, 1024 * 4, 8);
    uint32_t *tex = (uint32_t *)(mem + texp);
    for (int i = 0; i < 64 * 64; i++) tex[i] = (uint32_t)(i * 2654435761u) >> 8;
    int32_t U0 = 3 << 16, V0 = 5 << 16, DU = 70000, DV = -30000, LIGHT = 200;
    IVal args2[8] = { ival_make(dstp), ival_make(texp), ival_make(1024), ival_make((uint64_t)(uint32_t)U0),
                      ival_make((uint64_t)(uint32_t)V0), ival_make((uint64_t)(uint32_t)DU),
                      ival_make((uint64_t)(uint32_t)DV), ival_make((uint64_t)(uint32_t)LIGHT) };
    rc = interp_call(it, "span", args2, 8, NULL);
    CHECK(rc == 0, "span interp run");
    if (rc) { char eb[256]; interp_last_error(it, eb, sizeof eb); printf("err: %s\n", eb); }
    uint32_t want2[1024];
    ref_span(want2, tex, 1024, U0, V0, DU, DV, LIGHT);
    CHECK(memcmp(mem + dstp, want2, sizeof want2) == 0, "span bytes match reference");
    for (int i = 0; i < 8; i++) free(args2[i].lanes);

    interp_free(it);
    mod_free(m);
    if (!failures) printf("KERNELS_INTERP_OK\n");
    return failures ? 1 : 0;
}
#endif
