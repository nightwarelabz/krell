/* Surface syntax gate: parse a program in the human text form, verify
 * it, run it in the interpreter against hand-computed answers, and
 * round-trip it through the binary encoding. */
#include "krell.h"
#include <stdio.h>
#include <string.h>

static const char *PROG =
"data tab: i32 = { 11, 22, 33, 44 }\n"
"extern shout(i64) -> i64\n"
"\n"
"fn sumsq(i64) -> i64 {\n"
"  entry(n: i64):\n"
"    br loop(1, 0, n)\n"
"  loop(i: i64, acc: i64, n: i64):\n"
"    %c = icmp.sle i64 i, n\n"
"    condbr %c, body(i, acc, n), exit(acc)\n"
"  body(i: i64, acc: i64, n: i64):\n"
"    %sq = mul i64 i, i\n"
"    %a2 = add i64 acc, %sq\n"
"    %i2 = add i64 i, 1\n"
"    br loop(%i2, %a2, n)\n"
"  exit(acc: i64):\n"
"    ret acc\n"
"}\n"
"\n"
"fn fact(i64) -> i64 {\n"
"  entry(n: i64):\n"
"    %c = icmp.sle i64 n, 1\n"
"    condbr %c, base(n), rec(n)\n"
"  base(n: i64):\n"
"    ret 1\n"
"  rec(n: i64):\n"
"    %m = sub i64 n, 1\n"
"    %r = call i64 fact(%m)\n"
"    %p = mul i64 n, %r\n"
"    ret %p\n"
"}\n"
"\n"
"fn tabval(i64) -> i64 {\n"
"  entry(i: i64):\n"
"    %p = dataptr 0\n"
"    %g = gep i32 %p, i\n"
"    %v = load i32, %g\n"
"    %e = zext i64 %v\n"
"    ret %e\n"
"}\n"
"\n"
"fn fill(ptr, i64, i32) -> void {\n"
"  entry(dst: ptr, n: i64, val: i32):\n"
"    br loop(0, dst, n, val)\n"
"  loop(i: i64, dst: ptr, n: i64, val: i32):\n"
"    %c = icmp.slt i64 i, n\n"
"    condbr %c, body(i, dst, n, val), exit()\n"
"  body(i: i64, dst: ptr, n: i64, val: i32):\n"
"    %g = gep i32 dst, i\n"
"    store i32 %g, val\n"
"    %i2 = add i64 i, 1\n"
"    br loop(%i2, dst, n, val)\n"
"  exit():\n"
"    ret\n"
"}\n"
"\n"
"fn loadsum(ptr, i64) -> i64 {\n"
"  entry(src: ptr, n: i64):\n"
"    br loop(0, 0, src, n)\n"
"  loop(i: i64, acc: i64, src: ptr, n: i64):\n"
"    %c = icmp.slt i64 i, n\n"
"    condbr %c, body(i, acc, src, n), exit(acc)\n"
"  body(i: i64, acc: i64, src: ptr, n: i64):\n"
"    %g = gep i32 src, i\n"
"    %v = load i32, %g\n"
"    %e = sext i64 %v\n"
"    %a2 = add i64 acc, %e\n"
"    %i2 = add i64 i, 1\n"
"    br loop(%i2, %a2, src, n)\n"
"  exit(acc: i64):\n"
"    ret acc\n"
"}\n"
"\n"
"fn vfirst(ptr) -> i32 {\n"
"  entry(src: ptr):\n"
"    %v = vload v4i32, src\n"
"    %s = vsplat v4i32 3\n"
"    %r = vadd v4i32 %v, %s\n"
"    %x = vextract i32 %r, 2\n"
"    ret %x\n"
"}\n"
"\n"
"fn maybe_set(ptr, i32, i1) -> void {\n"
"  entry(dst: ptr, val: i32, flag: i1):\n"
"    condbr flag, set(dst, val), skip()\n"
"  set(dst: ptr, val: i32):\n"
"    store i32 dst, val\n"
"    ret\n"
"  skip():\n"
"    ret\n"
"}\n";

static int failures = 0;
static void check(Interp *it, const char *fn, const uint64_t *args, int na, uint64_t want) {
    IVal av[8], rv;
    uint64_t lb[8][256];
    for (int i = 0; i < na; i++) { av[i].lanes = lb[i]; av[i].lanes[0] = args[i]; }
    rv.lanes = lb[0] + 16;
    int rc = interp_call(it, fn, av, na, &rv);
    if (rc != 0) { char eb[256]; interp_last_error(it, eb, sizeof eb); printf("FAIL %s: interp %s\n", fn, eb); failures++; return; }
    if (rv.lanes[0] != want) { printf("FAIL %s: got %llu want %llu\n", fn, (unsigned long long)rv.lanes[0], (unsigned long long)want); failures++; }
}

int main(void) {
    char err[512];
    Module *m = surface_parse(PROG, err, sizeof err);
    if (!m) { printf("PARSE FAIL: %s\n", err); return 1; }
    const char *ve = mod_verify(m);
    if (ve) { printf("VERIFY FAIL: %s\n", ve); return 1; }
    Interp *it = interp_new(m);
    check(it, "sumsq", (uint64_t[]){ 10 }, 1, 385);
    check(it, "sumsq", (uint64_t[]){ 0 }, 1, 0);
    check(it, "sumsq", (uint64_t[]){ 100 }, 1, 338350);
    check(it, "fact", (uint64_t[]){ 10 }, 1, 3628800);
    check(it, "fact", (uint64_t[]){ 0 }, 1, 1);
    check(it, "tabval", (uint64_t[]){ 2 }, 1, 33);
    check(it, "tabval", (uint64_t[]){ 0 }, 1, 11);
    /* fill + loadsum over the interpreter's memory */
    {
        size_t ms; uint8_t *mem = interp_mem(it, &ms);
        uint64_t base = interp_alloc(it, 256, 16);
        IVal av[3], rv; uint64_t lb[3][256];
        for (int i = 0; i < 3; i++) av[i].lanes = lb[i];
        av[0].lanes[0] = base; av[1].lanes[0] = 64; av[2].lanes[0] = (uint64_t)(uint32_t)-7;
        if (interp_call(it, "fill", av, 3, NULL) != 0) { printf("FAIL fill\n"); failures++; }
        av[0].lanes[0] = base; av[1].lanes[0] = 64;
        rv.lanes = lb[0] + 16;
        if (interp_call(it, "loadsum", av, 2, &rv) != 0) { printf("FAIL loadsum\n"); failures++; }
        else if (rv.lanes[0] != (uint64_t)(64 * -7)) { printf("FAIL loadsum: got %lld want -448\n", (long long)rv.lanes[0]); failures++; }
        (void)mem; (void)ms;
        /* vfirst: src = {100, 200, 300, 400} -> lane2 + 3 = 303 */
        uint32_t *img = (uint32_t *)(mem + base);
        img[0] = 100; img[1] = 200; img[2] = 300; img[3] = 400;
        av[0].lanes[0] = base;
        rv.lanes = lb[0] + 16;
        if (interp_call(it, "vfirst", av, 1, &rv) != 0) { printf("FAIL vfirst\n"); failures++; }
        else if (rv.lanes[0] != 303) { printf("FAIL vfirst: got %llu want 303\n", (unsigned long long)rv.lanes[0]); failures++; }
        /* maybe_set: its set block ends in a bare ret with another
         * block after it (regression: that ret once swallowed the
         * following block's label and the parse failed) */
        img[0] = 7;
        av[0].lanes[0] = base; av[1].lanes[0] = 123; av[2].lanes[0] = 1;
        if (interp_call(it, "maybe_set", av, 3, NULL) != 0) { printf("FAIL maybe_set interp\n"); failures++; }
        else if (img[0] != 123) { printf("FAIL maybe_set set: got %u want 123\n", img[0]); failures++; }
        av[0].lanes[0] = base; av[1].lanes[0] = 999; av[2].lanes[0] = 0;
        if (interp_call(it, "maybe_set", av, 3, NULL) != 0) { printf("FAIL maybe_set interp 2\n"); failures++; }
        else if (img[0] != 123) { printf("FAIL maybe_set skip: got %u want 123\n", img[0]); failures++; }
    }
    interp_free(it);
    /* a condbr to a block that does not exist is a parse error,
     * never a crash (regression: the target block was dereferenced
     * before the lookup was checked) */
    {
        static const char *BAD =
        "fn f(i32) -> i32 {\n"
        "  entry(n: i32):\n"
        "    %c = icmp.sgt i32 n, 0\n"
        "    condbr %c, nowhere(n), done(n)\n"
        "  done(n: i32):\n"
        "    ret n\n"
        "}\n";
        Module *bm = surface_parse(BAD, err, sizeof err);
        if (bm) { printf("FAIL badcondbr: missing block accepted\n"); failures++; mod_free(bm); }
    }
    /* binary round-trip */
    size_t blen; uint8_t *bytes = mod_encode(m, &blen);
    Module *m2 = mod_decode(bytes, blen, err, sizeof err);
    if (!m2) { printf("FAIL decode: %s\n", err); failures++; }
    else {
        ve = mod_verify(m2);
        if (ve) { printf("FAIL verify decoded: %s\n", ve); failures++; }
        mod_free(m2);
    }
    free(bytes);
    mod_free(m);
    printf(failures ? "SURFACE FAILURES=%d\n" : "SURFACE_OK\n", failures);
    return failures ? 1 : 0;
}
