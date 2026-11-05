/* Battery generator: builds the battery + kernels modules, emits code for
 * the requested backend, and records interpreter-expected results to a
 * binary case file that tests/driver.c replays against native code.
 * Usage: gen <x86|arm|rv|llvm> <asm-out> <expected-out> */
#include "krell.h"
#include <stdio.h>
#include <string.h>
#include <math.h>

extern Module *build_battery(void);
extern Module *build_kernels(void);

static uint64_t rs = 0x9e3779b97f4a7c15ull;
static uint64_t rnd(void) { rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17; return rs; }
static double rnd_double(void) {
    uint64_t b = rnd();
    double d; memcpy(&d, &b, 8);
    if (isnan(d) || isinf(d)) d = (double)(int64_t)rnd() / 1000.0;
    return d;
}

enum { AK_GP, AK_F64, AK_F32, AK_PTR };
enum { RK_GP, RK_F64, RK_F32, RK_VOID };

typedef struct { const char *name; int nargs; uint8_t ak[10]; uint8_t rk; } FSpec;
static const FSpec FUNCS[] = {
    { "arith64", 2, { AK_GP, AK_GP }, RK_GP },
    { "divs",    2, { AK_GP, AK_GP }, RK_GP },
    { "divu",    2, { AK_GP, AK_GP }, RK_GP },
    { "narrow",  2, { AK_GP, AK_GP }, RK_GP },
    { "fcalc",   2, { AK_F64, AK_F64 }, RK_F64 },
    { "fcalc32", 2, { AK_F32, AK_F32 }, RK_F32 },
    { "cvt_i",   1, { AK_F64 }, RK_GP },
    { "cvt_u",   1, { AK_F64 }, RK_GP },
    { "cvt_f",   1, { AK_GP }, RK_F64 },
    { "cvt_uf",  1, { AK_GP }, RK_F64 },
    { "cvt_f32i",1, { AK_F32 }, RK_GP },
    { "cmp64",   2, { AK_GP, AK_GP }, RK_GP },
    { "fcmp64",  2, { AK_F64, AK_F64 }, RK_GP },
    { "sel",     3, { AK_GP, AK_GP, AK_GP }, RK_GP },
    { "branch",  1, { AK_GP }, RK_GP },
    { "loop",    1, { AK_GP }, RK_GP },
    { "caller",  2, { AK_GP, AK_GP }, RK_GP },
    { "fact",    1, { AK_GP }, RK_GP },
    { "tail",    2, { AK_GP, AK_GP }, RK_GP },
    { "alloca",  1, { AK_GP }, RK_GP },
    { "allocsave", 1, { AK_GP }, RK_GP },
    { "chainpress", 2, { AK_GP, AK_GP }, RK_GP },
    { "data_load", 0, { 0 }, RK_GP },
    { "bitcast_df", 1, { AK_F64 }, RK_GP },
    { "bitcast_id", 1, { AK_GP }, RK_F64 },
    { "fround",  1, { AK_F32 }, RK_F64 },
    { "fround2", 1, { AK_F64 }, RK_F32 },
    { "manyargs", 10, { AK_GP, AK_GP, AK_GP, AK_GP, AK_GP, AK_GP, AK_GP, AK_GP, AK_F64, AK_F64 }, RK_GP },
    { "spills",  1, { AK_GP }, RK_GP },
    { "clobx",   1, { AK_GP }, RK_GP },
    { "clobcall", 1, { AK_GP }, RK_GP },
    { "selx",    1, { AK_GP }, RK_GP },
    { "rotw",    2, { AK_GP, AK_GP }, RK_GP },
    /* memory functions (B cases) */
    { "mem",     3, { AK_PTR, AK_GP, AK_GP }, RK_GP },
    { "stx",     3, { AK_PTR, AK_PTR, AK_GP }, RK_GP },
    { "atomic",  2, { AK_PTR, AK_GP }, RK_GP },
    { "rmw",     2, { AK_PTR, AK_GP }, RK_GP },
    { "rmw32",   2, { AK_PTR, AK_GP }, RK_GP },
    { "rmw8",    2, { AK_PTR, AK_GP }, RK_GP },
    { "vecadd",  2, { AK_PTR, AK_PTR }, RK_VOID },
    { "vecstage", 2, { AK_PTR, AK_PTR }, RK_VOID },
    { "vecstageu", 2, { AK_PTR, AK_PTR }, RK_VOID },
    { "vecf",    3, { AK_PTR, AK_PTR, AK_F32 }, RK_VOID },
    { "vecins",  3, { AK_PTR, AK_PTR, AK_GP }, RK_VOID },
    { "memcpy_", 3, { AK_PTR, AK_PTR, AK_GP }, RK_VOID },
    { "memset_", 3, { AK_PTR, AK_GP, AK_GP }, RK_VOID },
    { "vecext",  1, { AK_PTR }, RK_GP },
    { "gepneg",  1, { AK_PTR }, RK_GP },
    { "w128",    2, { AK_GP, AK_GP }, RK_GP },
    { "vtable",  2, { AK_GP, AK_GP }, RK_GP },
    { "alchk",   2, { AK_F64, AK_F64 }, RK_GP },
    { "alchk1",  1, { AK_F64 }, RK_GP },
    { "vtail",   2, { AK_GP, AK_GP }, RK_GP },
    { "asmchk",  2, { AK_GP, AK_GP }, RK_GP },
    { "extch",   2, { AK_GP, AK_GP }, RK_GP },
    { "fsh64",   3, { AK_GP, AK_GP, AK_GP }, RK_GP },
    { "fsh32",   3, { AK_GP, AK_GP, AK_GP }, RK_GP },
    { "fsh16",   3, { AK_GP, AK_GP, AK_GP }, RK_GP },
};
#define NFUNC (sizeof(FUNCS) / sizeof(FUNCS[0]))
static int func_index(const char *name) {
    for (size_t i = 0; i < NFUNC; i++) if (strcmp(FUNCS[i].name, name) == 0) return (int)i;
    return -1;
}


/* case file writer */
static FILE *cf;
static void w8(uint8_t v) { fputc(v, cf); }
static void w32(uint32_t v) { fwrite(&v, 4, 1, cf); }
static void w64(uint64_t v) { fwrite(&v, 8, 1, cf); }

static Interp *it;
static Module *mod;
static int nscalar = 0, nbcases = 0;
static long scalar_pos = 0, bcase_pos = 0;   /* patched counts: we buffer cases in memory instead */
typedef struct { uint32_t func; uint64_t args[10]; uint64_t expected; } SCase;
static SCase *scases; static int nsc, sccap;
typedef struct { uint32_t func; uint64_t args[10]; uint64_t expected; int has_ret;
                 uint8_t img_in[256], img_exp[256]; } BCase;
static BCase *bcases; static int nbc, bccap;

static void push_scalar(const char *name, const uint64_t *args) {
    if (nsc == sccap) { sccap = sccap ? sccap * 2 : 1024; scases = realloc(scases, sizeof(SCase) * (size_t)sccap); }
    SCase *cs = &scases[nsc];
    cs->func = (uint32_t)func_index(name);
    const FSpec *fs = &FUNCS[cs->func];
    IVal av[10], rv;
    uint64_t lanesbuf[10][256];
    for (int i = 0; i < fs->nargs; i++) { av[i].lanes = lanesbuf[i]; av[i].lanes[0] = args[i]; cs->args[i] = args[i]; }
    for (int i = fs->nargs; i < 10; i++) cs->args[i] = 0;
    rv.lanes = lanesbuf[9];
    int rc = interp_call(it, name, av, fs->nargs, &rv);
    if (rc != 0) { char eb[256]; interp_last_error(it, eb, sizeof eb); fprintf(stderr, "interp failed %s: %s\n", name, eb); exit(1); }
    cs->expected = rv.lanes[0];
    /* skip cases whose float result is NaN (payload is target-defined) */
    if (fs->rk == RK_F64) { double d; uint64_t b = cs->expected; memcpy(&d, &b, 8); if (isnan(d)) return; }
    if (fs->rk == RK_F32) { float f; uint32_t b = (uint32_t)cs->expected; memcpy(&f, &b, 4); if (isnan(f)) return; }
    nsc++;
}

static void push_bcase(const char *name, const uint64_t *args) {
    if (nbc == bccap) { bccap = bccap ? bccap * 2 : 256; bcases = realloc(bcases, sizeof(BCase) * (size_t)bccap); }
    BCase *cs = &bcases[nbc];
    cs->func = (uint32_t)func_index(name);
    const FSpec *fs = &FUNCS[cs->func];
    for (int i = 0; i < 256; i++) cs->img_in[i] = (uint8_t)rnd();
    /* deterministic per-function image fixups happen in the caller via img_in tweaks:
     * here we just run with the random image */
    size_t memsz; uint8_t *mem = interp_mem(it, &memsz);
    uint64_t base = interp_alloc(it, 256, 16);
    memcpy(mem + base, cs->img_in, 256);
    IVal av[10], rv;
    uint64_t lanesbuf[10][256];
    for (int i = 0; i < fs->nargs; i++) {
        av[i].lanes = lanesbuf[i];
        av[i].lanes[0] = fs->ak[i] == AK_PTR ? base + args[i] : args[i];
        cs->args[i] = args[i];
    }
    for (int i = fs->nargs; i < 10; i++) cs->args[i] = 0;
    rv.lanes = lanesbuf[9];
    int rc = interp_call(it, name, av, fs->nargs, fs->rk == RK_VOID ? NULL : &rv);
    if (rc != 0) { char eb[256]; interp_last_error(it, eb, sizeof eb); fprintf(stderr, "interp failed %s: %s\n", name, eb); exit(1); }
    cs->has_ret = fs->rk != RK_VOID;
    cs->expected = cs->has_ret ? rv.lanes[0] : 0;
    memcpy(cs->img_exp, mem + base, 256);
    nbc++;
}

static const uint64_t IPOOL[] = { 0, 1, (uint64_t)-1, 2, 3, 7, 10, 63, 64, 100,
    (uint64_t)-100, 1000000, (uint64_t)-1000000, 0x7fffffffffffffffULL,
    0x8000000000000000ULL, 0x7ffffffffffffffeULL, 0x100000000ULL,
    0x7fffffffULL, 0xffffffff80000000ULL, 123456789012345ULL, (uint64_t)-987654321 };
#define NIP (sizeof(IPOOL) / sizeof(IPOOL[0]))
static const double DPOOL[] = { 0.0, -0.0, 1.0, -1.0, 1.5, -2.75, 0.1, 123456.789,
    -987.654, 1e10, 1e-10, 1e300, -1e300, 2147483647.0, 2147483648.0, -2147483648.0,
    4294967295.0, 4294967296.0, 9223372036854775808.0, 18446744073709551616.0,
    -9223372036854775808.0, 3.999999, -0.5, INFINITY, -INFINITY, NAN };
#define NDP (sizeof(DPOOL) / sizeof(DPOOL[0]))
static uint64_t dbits(double d) { uint64_t b; memcpy(&b, &d, 8); return b; }
static uint64_t fbits(float f) { uint32_t b; memcpy(&b, &f, 4); return b; }

static void gen_cases(void) {
    /* integer pairs: cross of a subset + randoms */
    const char *pairfns[] = { "arith64", "divs", "divu", "cmp64", "caller" };
    for (size_t fi = 0; fi < sizeof(pairfns) / sizeof(char *); fi++) {
        for (int i = 0; i < 10; i++)
            for (int j = 0; j < 10; j++) {
                uint64_t a[2] = { IPOOL[i], IPOOL[j] };
                push_scalar(pairfns[fi], a);
            }
        for (int i = 0; i < 150; i++) {
            uint64_t a[2] = { rnd(), rnd() };
            push_scalar(pairfns[fi], a);
        }
    }
    for (int i = 0; i < 10; i++)
        for (int j = 0; j < 10; j++) {
            uint64_t a[2] = { (uint64_t)(uint32_t)IPOOL[i], (uint64_t)(uint32_t)IPOOL[j] };
            push_scalar("narrow", a);
        }
    for (int i = 0; i < 150; i++) {
        uint64_t a[2] = { (uint64_t)(uint32_t)rnd(), (uint64_t)(uint32_t)rnd() };
        push_scalar("narrow", a);
    }
    /* fcalc pairs (b != 0), skipping NaN results inside push_scalar */
    for (size_t i = 0; i < NDP; i++)
        for (size_t j = 0; j < NDP; j++) {
            if (DPOOL[j] == 0.0) continue;
            uint64_t a[2] = { dbits(DPOOL[i]), dbits(DPOOL[j]) };
            push_scalar("fcalc", a);
        }
    for (int i = 0; i < 150; i++) {
        double x = rnd_double(), y = rnd_double();
        if (y == 0.0) y = 1.0;
        uint64_t a[2] = { dbits(x), dbits(y) };
        push_scalar("fcalc", a);
    }
    static const float FPOOL[] = { 0.0f, -0.0f, 1.0f, -1.0f, 1.5f, -2.75f, 0.1f, 12345.678f,
        1e10f, 1e-10f, 1e38f, -1e38f, 2147483648.0f, 16777217.0f, -0.5f, INFINITY, -INFINITY, NAN };
    for (size_t i = 0; i < sizeof(FPOOL) / sizeof(float); i++)
        for (size_t j = 0; j < sizeof(FPOOL) / sizeof(float); j++) {
            if (FPOOL[j] == 0.0f) continue;
            uint64_t a[2] = { fbits(FPOOL[i]), fbits(FPOOL[j]) };
            push_scalar("fcalc32", a);
        }
    /* conversions: full pools + random bit patterns */
    for (size_t i = 0; i < NDP; i++) {
        uint64_t a[1] = { dbits(DPOOL[i]) };
        push_scalar("cvt_i", a); push_scalar("cvt_u", a);
        push_scalar("fcmp64", (uint64_t[]){ dbits(DPOOL[i]), dbits(DPOOL[(i + 7) % NDP]) });
        push_scalar("bitcast_df", a);
        push_scalar("fround2", a);
    }
    for (int i = 0; i < 200; i++) {
        uint64_t a[1] = { rnd() };
        push_scalar("cvt_i", a); push_scalar("cvt_u", a);
    }
    for (int i = 0; i < 300; i++) {
        uint64_t a[1] = { rnd() };
        push_scalar("cvt_f", a); push_scalar("cvt_uf", a); push_scalar("bitcast_id", a);
    }
    for (size_t i = 0; i < sizeof(FPOOL) / sizeof(float); i++) {
        uint64_t a[1] = { fbits(FPOOL[i]) };
        push_scalar("cvt_f32i", a); push_scalar("fround", a);
    }
    for (int i = 0; i < 200; i++) {
        uint64_t a[1] = { (uint64_t)(uint32_t)rnd() };
        push_scalar("cvt_f32i", a);
    }
    /* fcmp64 cross with nasties */
    for (int i = 0; i < 8; i++)
        for (int j = 0; j < 8; j++)
            push_scalar("fcmp64", (uint64_t[]){ dbits(DPOOL[i * 3]), dbits(DPOOL[j * 3 + 1]) });
    /* asmchk pairs */
    for (int i = 0; i < 120; i++)
        push_scalar("asmchk", (uint64_t[]){ rnd(), rnd() });
    /* extch pairs (32-bit inputs) */
    for (int i = 0; i < 10; i++)
        for (int j = 0; j < 10; j++)
            push_scalar("extch", (uint64_t[]){ (uint64_t)(uint32_t)IPOOL[i], (uint64_t)(uint32_t)IPOOL[j] });
    for (int i = 0; i < 100; i++)
        push_scalar("extch", (uint64_t[]){ (uint64_t)(uint32_t)rnd(), (uint64_t)(uint32_t)rnd() });
    /* funnel shifts: edge amounts (0, width-1, width, width+1, huge)
     * crossed with pool parts, plus random triples */
    { static const uint64_t ss[] = { 0, 1, 2, 7, 15, 16, 31, 32, 33, 63, 64, 65, 127, (uint64_t)-1 };
      for (size_t i = 0; i < 8; i++)
          for (size_t j = 0; j < 8; j++)
              for (size_t k = 0; k < sizeof(ss) / 8; k++)
                  push_scalar("fsh64", (uint64_t[]){ IPOOL[i], IPOOL[j], ss[k] });
      for (int i = 0; i < 150; i++)
          push_scalar("fsh64", (uint64_t[]){ rnd(), rnd(), rnd() });
      for (size_t i = 0; i < 6; i++)
          for (size_t j = 0; j < 6; j++)
              for (size_t k = 0; k < sizeof(ss) / 8; k++) {
                  push_scalar("fsh32", (uint64_t[]){ (uint64_t)(uint32_t)IPOOL[i], (uint64_t)(uint32_t)IPOOL[j], ss[k] });
                  push_scalar("fsh16", (uint64_t[]){ (uint64_t)(uint16_t)IPOOL[i], (uint64_t)(uint16_t)IPOOL[j], ss[k] });
              }
      for (int i = 0; i < 100; i++) {
          push_scalar("fsh32", (uint64_t[]){ (uint64_t)(uint32_t)rnd(), (uint64_t)(uint32_t)rnd(), rnd() });
          push_scalar("fsh16", (uint64_t[]){ (uint64_t)(uint16_t)rnd(), (uint64_t)(uint16_t)rnd(), rnd() });
      } }
    /* sel / branch / loops / recursion */
    for (int i = 0; i < 60; i++)
        push_scalar("sel", (uint64_t[]){ (uint64_t)(i % 3) - 1, rnd(), rnd() });
    for (size_t i = 0; i < NIP; i++) push_scalar("branch", (uint64_t[]){ IPOOL[i] });
    for (int i = 0; i < 60; i++) push_scalar("branch", (uint64_t[]){ rnd() });
    { static const uint64_t ns[] = { 0, 1, 2, 10, 100, 5000 };
      for (size_t i = 0; i < sizeof(ns) / 8; i++) push_scalar("loop", (uint64_t[]){ ns[i] }); }
    for (uint64_t n = 0; n <= 20; n++) push_scalar("fact", (uint64_t[]){ n });
    push_scalar("tail", (uint64_t[]){ 0, 5 });
    push_scalar("tail", (uint64_t[]){ 1, 0 });
    push_scalar("tail", (uint64_t[]){ 10, 0 });
    push_scalar("tail", (uint64_t[]){ 100000, 7 });
    push_scalar("tail", (uint64_t[]){ 500000, 0 });
    for (int i = 0; i < 40; i++) push_scalar("alloca", (uint64_t[]){ (uint64_t)(uint32_t)rnd() });
    push_scalar("data_load", (uint64_t[]){ 0 });
    for (int i = 0; i < 40; i++) push_scalar("spills", (uint64_t[]){ rnd() });
    for (int i = 0; i < 40; i++) push_scalar("clobx", (uint64_t[]){ rnd() });
    for (int i = 0; i < 40; i++) push_scalar("clobcall", (uint64_t[]){ rnd() });
    for (int i = 0; i < 30; i++) push_scalar("selx", (uint64_t[]){ rnd() });
    for (int i = 0; i < 40; i++) push_scalar("rotw", (uint64_t[]){ (uint64_t)(rnd() % 40), rnd() });
    for (int i = 0; i < 30; i++) {
        uint64_t a[10];
        for (int k = 0; k < 8; k++) a[k] = (uint64_t)(int64_t)(int32_t)rnd();
        a[8] = dbits((double)(int32_t)rnd() / 7.0);
        a[9] = dbits((double)(int32_t)rnd() / 13.0);
        push_scalar("manyargs", a);
    }
    /* B cases */
    for (int i = 0; i < 12; i++)
        push_bcase("mem", (uint64_t[]){ 32, (uint64_t)(rnd() % 41), (uint64_t)(uint32_t)rnd() });
    for (int i = 0; i < 12; i++)
        push_bcase("stx", (uint64_t[]){ 32, 128, (uint64_t)(i % 7) * 4 });
    for (int i = 0; i < 12; i++)
        push_bcase("atomic", (uint64_t[]){ 0, rnd() });
    for (int i = 0; i < 12; i++)
        push_bcase("rmw", (uint64_t[]){ 0, rnd() });
    for (int i = 0; i < 12; i++)
        push_bcase("rmw32", (uint64_t[]){ 0, (uint64_t)(uint32_t)rnd() });
    for (int i = 0; i < 12; i++)
        push_bcase("rmw8", (uint64_t[]){ 0, rnd() });
    for (int i = 0; i < 12; i++)
        push_scalar("allocsave", (uint64_t[]){ (uint64_t)(uint32_t)rnd() });
    for (int i = 0; i < 12; i++)
        push_scalar("chainpress", (uint64_t[]){ (uint64_t)(int64_t)(int32_t)rnd(), (uint64_t)(rnd() % 64) });
    for (int i = 0; i < 12; i++)
        push_scalar("w128", (uint64_t[]){ rnd(), rnd() });
    for (int i = 0; i < 12; i++)
        push_scalar("vtable", (uint64_t[]){ (uint64_t)i, rnd() });
    for (int i = 0; i < 12; i++)
        push_scalar("vtail", (uint64_t[]){ (uint64_t)i, rnd() });
    for (int i = 0; i < 4; i++) {
        double d1 = (double)(int)(rnd() % 2000) / 8.0, d2 = (double)(int)(rnd() % 2000) / 8.0;
        uint64_t u1, u2; memcpy(&u1, &d1, 8); memcpy(&u2, &d2, 8);
        push_scalar("alchk", (uint64_t[]){ u1, u2 });
        push_scalar("alchk1", (uint64_t[]){ u1 });
    }
    for (int i = 0; i < 12; i++)
        push_bcase("vecadd", (uint64_t[]){ 128, 0 });
    for (int i = 0; i < 12; i++)
        push_bcase("vecstage", (uint64_t[]){ 96, 0 });
    for (int i = 0; i < 12; i++)
        push_bcase("vecstageu", (uint64_t[]){ 96, 0 });
    for (int i = 0; i < 12; i++)
        push_bcase("vecf", (uint64_t[]){ 128, 0, fbits(1.5f + (float)(i % 5)) });
    for (int i = 0; i < 12; i++)
        push_bcase("vecins", (uint64_t[]){ 128, 0, (uint64_t)(uint32_t)rnd() });
    for (int i = 0; i < 6; i++)
        push_bcase("memcpy_", (uint64_t[]){ 128, 0, 100 });
    for (int i = 0; i < 6; i++)
        push_bcase("memset_", (uint64_t[]){ 64, (uint64_t)(rnd() & 0xff), 100 });
    for (int i = 0; i < 12; i++)
        push_bcase("vecext", (uint64_t[]){ 64 });
    for (int i = 0; i < 12; i++)
        push_bcase("gepneg", (uint64_t[]){ 64 });
    (void)nscalar; (void)nbcases; (void)scalar_pos; (void)bcase_pos;
}

/* the AL probes' reference semantics: report the FP-register count
 * of their own fixed signature (1 and 2 respectively) */
static uint64_t host_alprobe(Interp *it, void *ctx, const IVal *args, int nargs, IVal *ret) {
    (void)it; (void)ctx; (void)args; (void)nargs; ret->lanes[0] = 1; return 0;
}
static uint64_t host_alprobe2(Interp *it, void *ctx, const IVal *args, int nargs, IVal *ret) {
    (void)it; (void)ctx; (void)args; (void)nargs; ret->lanes[0] = 2; return 0;
}
int main(int argc, char **argv) {
    if (argc < 4) { fprintf(stderr, "usage: gen <x86|arm|rv|llvm> <asm-out> <expected-out>\n"); return 2; }
    const char *be = argv[1];
    Module *bat = build_battery();
    Module *ker = build_kernels();
    const char *e;
    if ((e = mod_verify(bat))) { fprintf(stderr, "battery verify: %s\n", e); return 1; }
    if ((e = mod_verify(ker))) { fprintf(stderr, "kernels verify: %s\n", e); return 1; }
    if (getenv("KRELL_OPT")) {
        Cost *oc = cost_load("x86_64");
        OptStats st = { 0, 0, 0, 0 };
        opt_optimize(bat, oc, &st);
        opt_optimize(ker, oc, &st);
        printf("OPT folded=%d dce=%d rewritten=%d\n", st.folded, st.dce, st.rewritten);
        if ((e = mod_verify(bat))) { fprintf(stderr, "battery verify after opt: %s\n", e); return 1; }
        if ((e = mod_verify(ker))) { fprintf(stderr, "kernels verify after opt: %s\n", e); return 1; }
    }
    Cost *cost = cost_load(strcmp(be, "arm") == 0 ? "aarch64" : strcmp(be, "rv") == 0 ? "riscv64" : "x86_64");
    /* battery and kernels go to separate outputs: one module per object,
     * like a real toolchain (argv[2] is a prefix: <prefix>.bat, <prefix>.ker) */
    const char *ext = strcmp(be, "llvm") == 0 ? "ll" : "s";
    char p1[512], p2[512];
    snprintf(p1, sizeof p1, "%s.bat.%s", argv[2], ext);
    snprintf(p2, sizeof p2, "%s.ker.%s", argv[2], ext);
    FILE *out1 = fopen(p1, "w"), *out2 = fopen(p2, "w");
    if (!out1 || !out2) { perror("asm out"); return 1; }
    char err[256];
    int rc = -99;
#ifdef KRELL_BE_X86
    if (strcmp(be, "x86") == 0) { rc = be_x86_64(bat, cost, out1, err, sizeof err); if (!rc) rc = be_x86_64(ker, cost, out2, err, sizeof err); }
    else
#endif
#ifdef KRELL_BE_ARM
    if (strcmp(be, "arm") == 0) { rc = be_aarch64(bat, cost, out1, err, sizeof err); if (!rc) rc = be_aarch64(ker, cost, out2, err, sizeof err); }
    else
#endif
#ifdef KRELL_BE_RV
    if (strcmp(be, "rv") == 0) { rc = be_riscv64(bat, cost, out1, err, sizeof err); if (!rc) rc = be_riscv64(ker, cost, out2, err, sizeof err); }
    else
#endif
#ifdef KRELL_BE_LLVM
    if (strcmp(be, "llvm") == 0) { rc = be_llvm(bat, cost, out1, err, sizeof err); if (!rc) rc = be_llvm(ker, cost, out2, err, sizeof err); }
    else
#endif
    { rc = -99; }
    fclose(out1); fclose(out2);
    if (rc == -99) { fprintf(stderr, "unknown backend %s\n", be); return 2; }
    if (rc) { fprintf(stderr, "backend: %s\n", err); return 1; }

    /* merge battery is what the interpreter runs (kernels tested natively vs C refs) */
    mod = bat;
    it = interp_new(mod);
    interp_host(it, "alprobe", host_alprobe, NULL);
    interp_host(it, "alprobe2", host_alprobe2, NULL);
    gen_cases();
    interp_free(it);

    cf = fopen(argv[3], "wb");
    if (!cf) { perror("expected out"); return 1; }
    fwrite("RBAT", 1, 4, cf);
    w32(1);
    w32((uint32_t)NFUNC);
    for (size_t i = 0; i < NFUNC; i++) {
        w8((uint8_t)strlen(FUNCS[i].name));
        fwrite(FUNCS[i].name, 1, strlen(FUNCS[i].name), cf);
        w8((uint8_t)FUNCS[i].nargs);
        for (int k = 0; k < FUNCS[i].nargs; k++) w8(FUNCS[i].ak[k]);
        w8(FUNCS[i].rk);
    }
    w32((uint32_t)nsc);
    for (int i = 0; i < nsc; i++) {
        w32(scases[i].func);
        for (int k = 0; k < 10; k++) w64(scases[i].args[k]);
        w64(scases[i].expected);
    }
    w32((uint32_t)nbc);
    for (int i = 0; i < nbc; i++) {
        w32(bcases[i].func);
        for (int k = 0; k < 10; k++) w64(bcases[i].args[k]);
        w64(bcases[i].expected);
        w8((uint8_t)bcases[i].has_ret);
        w32(256);
        fwrite(bcases[i].img_in, 1, 256, cf);
        fwrite(bcases[i].img_exp, 1, 256, cf);
    }
    fclose(cf);
    printf("GEN_OK backend=%s scalar=%d bcases=%d\n", be, nsc, nbc);
    mod_free(bat);
    mod_free(ker);
    return 0;
}
