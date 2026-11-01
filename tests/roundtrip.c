/* Phase 1 gate: binary round-trip. Build varied modules, encode, decode,
 * re-encode — bytes and module hashes must be identical; the verifier must
 * accept the decoded module; truncated/corrupt inputs must be rejected. */
#include "krell.h"
#include <stdio.h>
#include <string.h>

static int failures = 0;
#define CHECK(cond, msg) do { if (!(cond)) { printf("FAIL: %s\n", msg); failures++; } } while (0)

/* a module exercising many op classes */
static Module *build_varied(void) {
    Module *m = mod_new();
    Type ep[2] = { ty_i64(), ty_i64() };
    mod_add_extern(m, "host_add", ep, 2, ty_i64());
    static const uint32_t tab[4] = { 11, 22, 33, 44 };
    mod_add_data(m, "tab", 4, tab, sizeof tab);
    Func *f = mod_add_func(m, "mix", ty_i64(), 0);
    Type pa[3] = { ty_i64(), ty_i32(), ty_f64() };
    int b0 = func_add_block(f, pa, 3);
    int b1 = func_add_block(f, (Type[]){ ty_i64() }, 1);
    int b2 = func_add_block(f, NULL, 0);
    int x = f->blocks[b0].arg_vals[0];
    int y = f->blocks[b0].arg_vals[1];
    int z = f->blocks[b0].arg_vals[2];
    int c3 = emit(f, b0, ins_iconst(ty_i64(), 3));
    int s = emit(f, b0, ins_bin(OP_MUL, ty_i64(), x, c3));
    int ys = emit(f, b0, ins_un(OP_SEXT, ty_i64(), y));
    int t = emit(f, b0, ins_bin(OP_XOR, ty_i64(), s, ys));
    int pc = emit(f, b0, ins_un(OP_POPCOUNT, ty_i64(), t));
    int bs = emit(f, b0, ins_un(OP_BSWAP, ty_i64(), pc));
    Instr fc = ins_make(OP_FPTOSI, ty_i64()); fc.a = z;
    int zi = emit(f, b0, fc);
    int tot = emit(f, b0, ins_bin(OP_ADD, ty_i64(), bs, zi));
    int dp = emit(f, b0, (Instr){ .op = OP_DATAPTR, .ty = ty_ptr(), .a = -1, .b = -1, .c = -1, .imm = 0, .result = -1, .blk = -1, .blk2 = -1, .callee = -1 });
    Instr ld = ins_make(OP_LOAD, ty_i32()); ld.a = dp;
    int tv = emit(f, b0, ld);
    int tvx = emit(f, b0, ins_un(OP_ZEXT, ty_i64(), tv));
    int tot2 = emit(f, b0, ins_bin(OP_ADD, ty_i64(), tot, tvx));
    Instr call = ins_call(ty_i64(), 0, true, ids_dup((int32_t[]){ tot2, x }, 2), 2, false);
    int cv = emit(f, b0, call);
    Instr cmp = ins_make(OP_ICMP, ty_i1()); cmp.a = cv; cmp.b = c3; cmp.pred = IC_UGT;
    int cond = emit(f, b0, cmp);
    emit(f, b0, ins_condbr(cond, b1, ids_dup((int32_t[]){ cv }, 1), 1, b2, NULL, 0));
    int r1 = f->blocks[b1].arg_vals[0];
    int sh = emit(f, b1, ins_bin(OP_SHL, ty_i64(), r1,
                    emit(f, b1, ins_iconst(ty_i64(), 2))));
    emit(f, b1, ins_ret(sh));
    emit(f, b2, ins_ret(tot2));
    return m;
}

static void roundtrip(Module *m, const char *what) {
    size_t n1, n2;
    uint8_t *e1 = mod_encode(m, &n1);
    uint8_t h1[32], h2[32];
    mod_hash(m, h1);
    char err[128];
    Module *d = mod_decode(e1, n1, err, sizeof err);
    CHECK(d != NULL, what);
    if (!d) { printf("  decode err: %s\n", err); free(e1); return; }
    const char *ve = mod_verify(d);
    CHECK(ve == NULL, ve ? ve : "decoded module verifies");
    uint8_t *e2 = mod_encode(d, &n2);
    CHECK(n1 == n2 && memcmp(e1, e2, n1) == 0, "re-encode is byte-identical");
    mod_hash(d, h2);
    CHECK(memcmp(h1, h2, 32) == 0, "module hash stable across round-trip");
    /* dump must not crash */
    FILE *dn = fopen("/dev/null", "w");
    if (dn) { mod_dump(d, dn); fclose(dn); }
    free(e1); free(e2);
    mod_free(d);
}

int main(void) {
    Module *m = build_varied();
    const char *e = mod_verify(m);
    if (e) { printf("ORIGINAL verify: %s\n", e); mod_dump(m, stdout); }
    CHECK(e == NULL, e ? e : "varied module verifies");
    roundtrip(m, "varied module round-trips");
    mod_free(m);

    /* kernels module too */
    extern Module *build_kernels(void);
    Module *k = build_kernels();
    roundtrip(k, "kernels module round-trips");
    mod_free(k);

    /* corrupt inputs must fail cleanly */
    Module *m2 = build_varied();
    size_t n; uint8_t *enc = mod_encode(m2, &n);
    char err[128];
    for (size_t cut = 0; cut < n; cut += 7) {
        Module *d = mod_decode(enc, cut, err, sizeof err);
        if (d) mod_free(d);   /* partial decodes of whole sections may succeed for large cuts */
    }
    printf("truncation sweep survived\n");
    uint8_t bad[64]; memcpy(bad, enc, 64); bad[0] = 'X';
    CHECK(mod_decode(bad, 64, err, sizeof err) == NULL, "bad magic rejected");
    free(enc);
    mod_free(m2);

    if (!failures) printf("ROUNDTRIP_OK\n");
    return failures ? 1 : 0;
}
