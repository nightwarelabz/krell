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
"fn vround(ptr, i32) -> i32 {\n"
"  entry(dst: ptr, val: i32):\n"
"    storev i32 dst, val\n"
"    fence.seqcst\n"
"    %a = loadv i32, dst\n"
"    %b = loadv i32, dst\n"
"    %s = add i32 %a, %b\n"
"    ret %s\n"
"}\n"
"\n"
"fn armw(ptr, i64) -> i64 {\n"
"  entry(dst: ptr, val: i64):\n"
"    %o1 = axchg.seqcst i64 dst, val\n"
"    %o2 = asub.acqrel i64 dst, 5\n"
"    %cur = sub i64 %o2, 5\n"
"    %o3 = acmpxchg.seqcst i64 dst, %cur, 9\n"
"    %o4 = aminu.relaxed i64 dst, 100\n"
"    %r = add i64 %o3, %o4\n"
"    ret %r\n"
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
        /* vround: volatile store then two volatile loads of the same
         * cell; both loads must observe the stored value (77 + 77) */
        av[0].lanes[0] = base; av[1].lanes[0] = 77;
        rv.lanes = lb[0] + 16;
        if (interp_call(it, "vround", av, 2, &rv) != 0) { printf("FAIL vround interp\n"); failures++; }
        else if (rv.lanes[0] != 154 || img[0] != 77) { printf("FAIL vround: got %llu cell %u want 154/77\n", (unsigned long long)rv.lanes[0], img[0]); failures++; }
        /* armw: axchg (old=77, cell=50), asub 5 (old=50, cell=45),
         * acmpxchg expecting 45 -> 9 (old=45), aminu 100 (old=9, cell=9);
         * returns 45 + 9 = 54 and leaves 9 in the cell */
        uint64_t *cell = (uint64_t *)(mem + base + 16);
        *cell = 77;
        av[0].lanes[0] = base + 16; av[1].lanes[0] = 50;
        rv.lanes = lb[0] + 16;
        if (interp_call(it, "armw", av, 2, &rv) != 0) { printf("FAIL armw interp\n"); failures++; }
        else if (rv.lanes[0] != 54 || *cell != 9) { printf("FAIL armw: got %llu cell %llu want 54/9\n", (unsigned long long)rv.lanes[0], (unsigned long long)*cell); failures++; }
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
    /* a call to a function defined later in the module resolves
     * (regression: the callee's signature was read from its entry
     * block, which does not exist until its body is parsed, and a
     * forward reference segfaulted the parser). Mutual recursion
     * exercises it in both directions. */
    {
        static const char *FWD =
        "fn is_even(i32) -> i32 {\n"
        "  entry(n: i32):\n"
        "    %one = iconst i32 1\n"
        "    %z = icmp.eq i32 n, 0\n"
        "    condbr %z, yes(), no(n)\n"
        "  yes():\n"
        "    ret 1\n"
        "  no(n: i32):\n"
        "    %m = sub i32 n, 1\n"
        "    %r = call i32 is_odd(%m)\n"
        "    ret %r\n"
        "}\n"
        "fn is_odd(i32) -> i32 {\n"
        "  entry(n: i32):\n"
        "    %one = iconst i32 1\n"
        "    %z = icmp.eq i32 n, 0\n"
        "    condbr %z, no2(), yes2(n)\n"
        "  no2():\n"
        "    ret 0\n"
        "  yes2(n: i32):\n"
        "    %m = sub i32 n, 1\n"
        "    %r = call i32 is_even(%m)\n"
        "    ret %r\n"
        "}\n";
        Module *fm = surface_parse(FWD, err, sizeof err);
        if (!fm) { printf("FAIL fwdref parse: %s\n", err); failures++; }
        else {
            const char *fve = mod_verify(fm);
            if (fve) { printf("FAIL fwdref verify: %s\n", fve); failures++; }
            else {
                Interp *fit = interp_new(fm);
                check(fit, "is_even", (uint64_t[]){ 10 }, 1, 1);
                check(fit, "is_even", (uint64_t[]){ 7 }, 1, 0);
                check(fit, "is_odd", (uint64_t[]){ 7 }, 1, 1);
                check(fit, "is_odd", (uint64_t[]){ 10 }, 1, 0);
                interp_free(fit);
            }
            mod_free(fm);
        }
    }
    /* i128 (v3.0): arithmetic with cross-word carries, shifts,
     * signed/unsigned compares, and a memory round trip, in the
     * interpreter (backends gate i128 until the lowering step).
     * The module must encode as format v2, the main PROG as v1. */
    {
        static const char *W128 =
        "fn add128(i128, i128) -> i128 {\n"
        "  entry(a: i128, b: i128):\n"
        "    %s = add i128 a, b\n"
        "    ret %s\n"
        "}\n"
        "fn shl128(i128) -> i128 {\n"
        "  entry(a: i128):\n"
        "    %s = shl i128 a, 100\n"
        "    ret %s\n"
        "}\n"
        "fn lt128(i128, i128) -> i1 {\n"
        "  entry(a: i128, b: i128):\n"
        "    %c = icmp.slt i128 a, b\n"
        "    ret %c\n"
        "}\n"
        "fn mem128(ptr, i128) -> i128 {\n"
        "  entry(p: ptr, v: i128):\n"
        "    store i128 p, v\n"
        "    %l = load i128, p\n"
        "    %o = add i128 %l, 1\n"
        "    ret %o\n"
        "}\n";
        Module *wm = surface_parse(W128, err, sizeof err);
        if (!wm) { printf("FAIL w128 parse: %s\n", err); failures++; }
        else {
            const char *wve = mod_verify(wm);
            if (wve) { printf("FAIL w128 verify: %s\n", wve); failures++; }
            /* target gate: the admitted i128 ops carry cost rows on
             * every target, so this module verifies everywhere */
            const char *tg = mod_verify_target(wm, "x86_64");
            if (tg) { printf("FAIL w128 gate: x86_64 rejected i128: %s\n", tg); failures++; }
            tg = mod_verify_target(wm, "aarch64");
            if (tg) { printf("FAIL w128 gate: aarch64 rejected i128: %s\n", tg); failures++; }
            tg = mod_verify_target(wm, "riscv64");
            if (tg) { printf("FAIL w128 gate: riscv64 rejected i128: %s\n", tg); failures++; }
            size_t wl; uint8_t *wb = mod_encode(wm, &wl);
            if (!wb || wb[4] != 2) { printf("FAIL w128: encoding version is not 2\n"); failures++; }
            Module *wm2 = wb ? mod_decode(wb, wl, err, sizeof err) : NULL;
            if (!wm2) { printf("FAIL w128 decode: %s\n", err); failures++; }
            Interp *wit = interp_new(wm2 ? wm2 : wm);
            uint64_t ab[2][2], rb[2];
            IVal av[2], rv; av[0].lanes = ab[0]; av[1].lanes = ab[1]; rv.lanes = rb;
            /* (2^64-1) + 1 = 2^64: lo 0, hi 1 (carry across the seam) */
            ab[0][0] = ~0ull; ab[0][1] = 0; ab[1][0] = 1; ab[1][1] = 0; rb[0] = rb[1] = 0;
            if (interp_call(wit, "add128", av, 2, &rv) != 0 || rb[0] != 0 || rb[1] != 1)
                { printf("FAIL w128 add carry: got %llx:%llx want 1:0\n", (unsigned long long)rb[1], (unsigned long long)rb[0]); failures++; }
            /* (2^64-1) * 2 via add of the value to itself: hi 1, lo 2^64-2 */
            ab[1][0] = ~0ull; ab[1][1] = 0; rb[0] = rb[1] = 0;
            if (interp_call(wit, "add128", av, 2, &rv) != 0 || rb[0] != ~0ull - 1 || rb[1] != 1)
                { printf("FAIL w128 add2: got %llx:%llx\n", (unsigned long long)rb[1], (unsigned long long)rb[0]); failures++; }
            /* 1 << 100 = hi 2^36, lo 0 */
            ab[0][0] = 1; ab[0][1] = 0; rb[0] = rb[1] = 0;
            if (interp_call(wit, "shl128", av, 1, &rv) != 0 || rb[0] != 0 || rb[1] != (1ull << 36))
                { printf("FAIL w128 shl: got %llx:%llx\n", (unsigned long long)rb[1], (unsigned long long)rb[0]); failures++; }
            /* signed: -1 < 1; the same bits unsigned-compare the other way
             * is covered by the icmp fold tests in kernels; here slt only */
            ab[0][0] = ~0ull; ab[0][1] = ~0ull; ab[1][0] = 1; ab[1][1] = 0; rb[0] = 0;
            if (interp_call(wit, "lt128", av, 2, &rv) != 0 || rb[0] != 1)
                { printf("FAIL w128 slt: got %llx want 1\n", (unsigned long long)rb[0]); failures++; }
            /* memory round trip: store (5,7), load, add 1 -> (6,7) */
            size_t msz; interp_mem(wit, &msz);
            uint64_t cell = interp_alloc(wit, 16, 16);
            ab[0][0] = cell; ab[0][1] = 0; ab[1][0] = 5; ab[1][1] = 7; rb[0] = rb[1] = 0;
            if (interp_call(wit, "mem128", av, 2, &rv) != 0 || rb[0] != 6 || rb[1] != 7)
                { printf("FAIL w128 mem: got %llx:%llx want 7:6\n", (unsigned long long)rb[1], (unsigned long long)rb[0]); failures++; }
            interp_free(wit);
            if (wm2) mod_free(wm2);
            free(wb);
            mod_free(wm);
        }
    }
    /* indirect calls (v3.0): a function-pointer table dispatch and a
     * tail dispatch in the interpreter, signature-mismatch and
     * not-a-function-pointer detection, and v2 encoding (the module
     * carries a signature table) */
    {
        static const char *VT =
        "sig bin(i64, i64) -> i64\n"
        "fn oadd(i64, i64) -> i64 {\n"
        "  entry(a: i64, b: i64):\n"
        "    %s = add i64 a, b\n"
        "    ret %s\n"
        "}\n"
        "fn omul(i64, i64) -> i64 {\n"
        "  entry(a: i64, b: i64):\n"
        "    %s = mul i64 a, b\n"
        "    ret %s\n"
        "}\n"
        "fn apply(i64, i64, i64) -> i64 {\n"
        "  entry(sel: i64, x: i64, y: i64):\n"
        "    %cell = alloca 16, 8\n"
        "    %p0 = funcptr oadd\n"
        "    store ptr %cell, %p0\n"
        "    %s1 = gep ptr %cell, 1\n"
        "    %p1 = funcptr omul\n"
        "    store ptr %s1, %p1\n"
        "    %idx = and i64 sel, 1\n"
        "    %slot = gep ptr %cell, %idx\n"
        "    %fp = load ptr, %slot\n"
        "    %r = calli i64 bin %fp(%x, %y)\n"
        "    ret %r\n"
        "}\n"
        "fn tappy(i64, i64, i64) -> i64 {\n"
        "  entry(sel: i64, x: i64, y: i64):\n"
        "    %p0 = funcptr oadd\n"
        "    %p1 = funcptr omul\n"
        "    %bit = and i64 sel, 1\n"
        "    %c = icmp.ne i64 %bit, 0\n"
        "    %fp = select ptr %c, %p1, %p0\n"
        "    tailcalli i64 bin %fp(%x, %y)\n"
        "}\n";
        Module *vm = surface_parse(VT, err, sizeof err);
        if (!vm) { printf("FAIL vt parse: %s\n", err); failures++; }
        else {
            const char *vve = mod_verify(vm);
            if (vve) { printf("FAIL vt verify: %s\n", vve); failures++; }
            size_t vl2; uint8_t *vb = mod_encode(vm, &vl2);
            if (!vb || vb[4] != 2) { printf("FAIL vt: encoding version is not 2\n"); failures++; }
            Module *vm2 = vb ? mod_decode(vb, vl2, err, sizeof err) : NULL;
            if (!vm2) { printf("FAIL vt decode: %s\n", err); failures++; }
            Interp *vit = interp_new(vm2 ? vm2 : vm);
            check(vit, "apply", (uint64_t[]){ 0, 5, 10 }, 3, 15);
            check(vit, "apply", (uint64_t[]){ 1, 5, 10 }, 3, 50);
            check(vit, "apply", (uint64_t[]){ 3, 6, 7 }, 3, 42);
            check(vit, "tappy", (uint64_t[]){ 0, 5, 10 }, 3, 15);
            check(vit, "tappy", (uint64_t[]){ 1, 5, 10 }, 3, 50);
            interp_free(vit);
            if (vm2) mod_free(vm2);
            free(vb);
            mod_free(vm);
        }
        /* mismatch: the pointer target's own signature differs from
         * the call site's table entry - a producer contract breach
         * the interpreter must report, not misexecute */
        static const char *BAD =
        "sig bin(i64, i64) -> i64\n"
        "fn oth(i64) -> i64 {\n"
        "  entry(a: i64):\n"
        "    ret a\n"
        "}\n"
        "fn boom(i64, i64) -> i64 {\n"
        "  entry(x: i64, y: i64):\n"
        "    %p = funcptr oth\n"
        "    %r = calli i64 bin %p(%x, %y)\n"
        "    ret %r\n"
        "}\n"
        "fn boom2(ptr, i64, i64) -> i64 {\n"
        "  entry(p: ptr, x: i64, y: i64):\n"
        "    %r = calli i64 bin %p(%x, %y)\n"
        "    ret %r\n"
        "}\n";
        Module *bm = surface_parse(BAD, err, sizeof err);
        if (!bm) { printf("FAIL bad parse: %s\n", err); failures++; }
        else {
            Interp *bit2 = interp_new(bm);
            uint64_t la[3][256]; IVal av[3], rv; uint64_t rb[256];
            for (int i = 0; i < 3; i++) av[i].lanes = la[i];
            rv.lanes = rb;
            av[0].lanes[0] = 5; av[1].lanes[0] = 6;
            if (interp_call(bit2, "boom", av, 2, &rv) == 0)
                { printf("FAIL bad: signature mismatch not detected\n"); failures++; }
            /* boom2 with a data pointer (not a function address) */
            size_t msz2; interp_mem(bit2, &msz2);
            uint64_t cell2 = interp_alloc(bit2, 64, 8);
            av[0].lanes[0] = cell2; av[1].lanes[0] = 5; av[2].lanes[0] = 6;
            if (interp_call(bit2, "boom2", av, 3, &rv) == 0)
                { printf("FAIL bad: non-function pointer not detected\n"); failures++; }
            interp_free(bit2);
            mod_free(bm);
        }
    }
    /* i128 division is cliff-gated on every target in v3.0 */
    {
        static const char *D128 =
        "fn div128(i128, i128) -> i128 {\n"
        "  entry(a: i128, b: i128):\n"
        "    %q = udiv i128 a, b\n"
        "    ret %q\n"
        "}\n";
        Module *dm = surface_parse(D128, err, sizeof err);
        if (!dm) { printf("FAIL div128 parse: %s\n", err); failures++; }
        else {
            if (mod_verify(dm)) { printf("FAIL div128 structural verify\n"); failures++; }
            const char *tg = mod_verify_target(dm, "x86_64");
            if (!tg) { printf("FAIL div128 gate: x86_64 accepted i128 udiv\n"); failures++; }
            tg = mod_verify_target(dm, "riscv64");
            if (!tg) { printf("FAIL div128 gate: riscv64 accepted i128 udiv\n"); failures++; }
            mod_free(dm);
        }
    }
    /* binary round-trip (the main PROG uses no v2 feature: version 1) */
    size_t blen; uint8_t *bytes = mod_encode(m, &blen);
    if (!bytes || bytes[4] != 1) { printf("FAIL: v1 module encoded as version %d\n", bytes ? bytes[4] : -1); failures++; }
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
