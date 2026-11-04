/* Battery driver: replays tests/gen.c's case file against natively
 * compiled backend code and checks every result. Also runs the two
 * acceptance kernels (fill32, span) against their C references.
 * Usage: driver <expected.bin> */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>

extern void ref_fill32(uint32_t *, int64_t, uint32_t);
extern void ref_span(uint32_t *, const uint32_t *, int64_t, int32_t, int32_t, int32_t, int32_t, int32_t);
extern void fill32(void *, int64_t, int32_t);
extern void span(void *, const void *, int64_t, int32_t, int32_t, int32_t, int32_t, int32_t);

/* ---- native battery functions (from the emitted code) ---- */
extern uint64_t arith64(uint64_t, uint64_t);
extern uint64_t divs(uint64_t, uint64_t);
extern uint64_t divu(uint64_t, uint64_t);
extern int32_t narrow(int32_t, int32_t);
extern double fcalc(double, double);
extern float fcalc32(float, float);
extern uint64_t cvt_i(double);
extern uint64_t cvt_u(double);
extern double cvt_f(uint64_t);
extern double cvt_uf(uint64_t);
extern int32_t cvt_f32i(float);
extern uint64_t cmp64(uint64_t, uint64_t);
extern uint64_t fcmp64(double, double);
extern uint64_t sel(uint64_t, uint64_t, uint64_t);
extern uint64_t branch(uint64_t);
extern uint64_t loop(uint64_t);
extern uint64_t caller(uint64_t, uint64_t);
extern uint64_t fact(uint64_t);
extern uint64_t tail(uint64_t, uint64_t);
extern int32_t data_load(void);
extern uint64_t bitcast_df(double);
extern double bitcast_id(uint64_t);
extern double fround(float);
extern float fround2(double);
extern uint64_t manyargs(uint64_t, uint64_t, uint64_t, uint64_t, uint64_t, uint64_t, uint64_t, uint64_t, double, double);
extern uint64_t spills(uint64_t);
/* battery name "alloca" collides with libc's; the IR function is emitted
 * under its module name "alloca" — see note in the build script: the
 * emitted symbol is renamed there. We declare the renamed symbol. */
extern int32_t krell_alloca(int32_t);
/* memory functions */
extern int32_t mem(void *, int64_t, int32_t);
extern uint64_t atomic(void *, uint64_t);
extern uint64_t rmw(void *, uint64_t);
extern uint32_t rmw32(void *, uint32_t);
extern uint64_t rmw8(void *, uint64_t);
extern void vecadd(void *, const void *);
extern void vecf(void *, const void *, float);
extern void vecins(void *, const void *, int32_t);
extern void memcpy_(void *, const void *, uint64_t);
extern void memset_(void *, int32_t, uint64_t);
extern int32_t vecext(const void *);
extern int32_t gepneg(const void *);

static uint64_t dbits(double d) { uint64_t b; memcpy(&b, &d, 8); return b; }
static uint64_t fbits(float f) { uint32_t b; memcpy(&b, &f, 4); return b; }
static double dfrom(uint64_t b) { double d; memcpy(&d, &b, 8); return d; }
static float ffrom(uint64_t b) { uint32_t u = (uint32_t)b; float f; memcpy(&f, &u, 4); return f; }

typedef uint64_t (*Shim)(const uint64_t *);
static uint64_t sh_arith64(const uint64_t *a) { return arith64(a[0], a[1]); }
static uint64_t sh_divs(const uint64_t *a) { return divs(a[0], a[1]); }
static uint64_t sh_divu(const uint64_t *a) { return divu(a[0], a[1]); }
static uint64_t sh_narrow(const uint64_t *a) { return (uint64_t)(uint32_t)narrow((int32_t)a[0], (int32_t)a[1]); }
static uint64_t sh_fcalc(const uint64_t *a) { return dbits(fcalc(dfrom(a[0]), dfrom(a[1]))); }
static uint64_t sh_fcalc32(const uint64_t *a) { return fbits(fcalc32(ffrom(a[0]), ffrom(a[1]))); }
static uint64_t sh_cvt_i(const uint64_t *a) { return cvt_i(dfrom(a[0])); }
static uint64_t sh_cvt_u(const uint64_t *a) { return cvt_u(dfrom(a[0])); }
static uint64_t sh_cvt_f(const uint64_t *a) { return dbits(cvt_f(a[0])); }
static uint64_t sh_cvt_uf(const uint64_t *a) { return dbits(cvt_uf(a[0])); }
static uint64_t sh_cvt_f32i(const uint64_t *a) { return (uint64_t)(uint32_t)cvt_f32i(ffrom(a[0])); }
static uint64_t sh_cmp64(const uint64_t *a) { return cmp64(a[0], a[1]); }
static uint64_t sh_fcmp64(const uint64_t *a) { return fcmp64(dfrom(a[0]), dfrom(a[1])); }
static uint64_t sh_sel(const uint64_t *a) { return sel(a[0], a[1], a[2]); }
static uint64_t sh_branch(const uint64_t *a) { return branch(a[0]); }
static uint64_t sh_loop(const uint64_t *a) { return loop(a[0]); }
static uint64_t sh_caller(const uint64_t *a) { return caller(a[0], a[1]); }
static uint64_t sh_fact(const uint64_t *a) { return fact(a[0]); }
static uint64_t sh_tail(const uint64_t *a) { return tail(a[0], a[1]); }
static uint64_t sh_alloca(const uint64_t *a) { return (uint64_t)(uint32_t)krell_alloca((int32_t)a[0]); }
static uint64_t sh_data_load(const uint64_t *a) { (void)a; return (uint64_t)(uint32_t)data_load(); }
static uint64_t sh_bitcast_df(const uint64_t *a) { return bitcast_df(dfrom(a[0])); }
static uint64_t sh_bitcast_id(const uint64_t *a) { return dbits(bitcast_id(a[0])); }
static uint64_t sh_fround(const uint64_t *a) { return dbits(fround(ffrom(a[0]))); }
static uint64_t sh_fround2(const uint64_t *a) { return fbits(fround2(dfrom(a[0]))); }
static uint64_t sh_manyargs(const uint64_t *a) {
    return manyargs(a[0], a[1], a[2], a[3], a[4], a[5], a[6], a[7], dfrom(a[8]), dfrom(a[9]));
}
static uint64_t sh_spills(const uint64_t *a) { return spills(a[0]); }

typedef struct { const char *name; Shim shim; } SEntry;
static const SEntry SCALARS[] = {
    { "arith64", sh_arith64 }, { "divs", sh_divs }, { "divu", sh_divu },
    { "narrow", sh_narrow }, { "fcalc", sh_fcalc }, { "fcalc32", sh_fcalc32 },
    { "cvt_i", sh_cvt_i }, { "cvt_u", sh_cvt_u }, { "cvt_f", sh_cvt_f },
    { "cvt_uf", sh_cvt_uf }, { "cvt_f32i", sh_cvt_f32i }, { "cmp64", sh_cmp64 },
    { "fcmp64", sh_fcmp64 }, { "sel", sh_sel }, { "branch", sh_branch },
    { "loop", sh_loop }, { "caller", sh_caller }, { "fact", sh_fact },
    { "tail", sh_tail }, { "alloca", sh_alloca }, { "data_load", sh_data_load },
    { "bitcast_df", sh_bitcast_df }, { "bitcast_id", sh_bitcast_id },
    { "fround", sh_fround }, { "fround2", sh_fround2 },
    { "manyargs", sh_manyargs }, { "spills", sh_spills },
};

static int failures = 0, total = 0;
static char fail_names[64][32]; static int fail_counts[64], nfail_names = 0;
static void note_fail(const char *fn) {
    for (int i = 0; i < nfail_names; i++) if (strcmp(fail_names[i], fn) == 0) { fail_counts[i]++; return; }
    if (nfail_names < 64) { snprintf(fail_names[nfail_names], 32, "%s", fn); fail_counts[nfail_names++] = 1; }
}
static void expect_u64(const char *fn, int idx, uint64_t got, uint64_t want) {
    total++;
    if (got != want) {
        if (failures < 20)
            printf("MISMATCH %s case %d: got 0x%llx want 0x%llx\n", fn, idx,
                   (unsigned long long)got, (unsigned long long)want);
        failures++;
        note_fail(fn);
    }
}

/* case file */
static FILE *cf;
static uint8_t r8(void) { int c = fgetc(cf); return (uint8_t)c; }
static uint32_t r32(void) { uint32_t v; if (fread(&v, 4, 1, cf) != 1) v = 0; return v; }
static uint64_t r64(void) { uint64_t v; if (fread(&v, 8, 1, cf) != 1) v = 0; return v; }

typedef struct { char name[32]; int nargs; uint8_t ak[10]; uint8_t rk; } FInfo;

static uint64_t run_bcase(const FInfo *fi, uint8_t *img, const uint64_t *args) {
    void *base = img;
    if (strcmp(fi->name, "mem") == 0) return (uint64_t)(uint32_t)mem(base + args[0], (int64_t)args[1], (int32_t)args[2]);
    if (strcmp(fi->name, "atomic") == 0) return atomic(base + args[0], args[1]);
    if (strcmp(fi->name, "rmw") == 0) return rmw(base + args[0], args[1]);
    if (strcmp(fi->name, "rmw32") == 0) return (uint64_t)(uint32_t)rmw32(base + args[0], (uint32_t)args[1]);
    if (strcmp(fi->name, "rmw8") == 0) return rmw8(base + args[0], args[1]);
    if (strcmp(fi->name, "vecadd") == 0) { vecadd(base + args[0], base + args[1]); return 0; }
    if (strcmp(fi->name, "vecf") == 0) { vecf(base + args[0], base + args[1], ffrom(args[2])); return 0; }
    if (strcmp(fi->name, "vecins") == 0) { vecins(base + args[0], base + args[1], (int32_t)args[2]); return 0; }
    if (strcmp(fi->name, "memcpy_") == 0) { memcpy_(base + args[0], base + args[1], args[2]); return 0; }
    if (strcmp(fi->name, "memset_") == 0) { memset_(base + args[0], (int32_t)args[1], args[2]); return 0; }
    if (strcmp(fi->name, "vecext") == 0) return (uint64_t)(uint32_t)vecext(base + args[0]);
    if (strcmp(fi->name, "gepneg") == 0) return (uint64_t)(uint32_t)gepneg(base + args[0]);
    printf("unknown B function %s\n", fi->name);
    failures++;
    return 0;
}

int main(int argc, char **argv) {
    if (argc < 2) { fprintf(stderr, "usage: driver <expected.bin>\n"); return 2; }
    cf = fopen(argv[1], "rb");
    if (!cf) { perror("open cases"); return 1; }
    char magic[4]; if (fread(magic, 1, 4, cf) != 4 || memcmp(magic, "RBAT", 4) != 0) { printf("bad case file\n"); return 1; }
    (void)r32();
    int nf = (int)r32();
    FInfo *fis = calloc((size_t)nf, sizeof(FInfo));
    for (int i = 0; i < nf; i++) {
        int nl = r8();
        if (fread(fis[i].name, 1, (size_t)nl, cf) != (size_t)nl) return 1;
        fis[i].name[nl] = 0;
        fis[i].nargs = r8();
        for (int k = 0; k < fis[i].nargs; k++) fis[i].ak[k] = r8();
        fis[i].rk = r8();
    }
    int nsc = (int)r32();
    for (int i = 0; i < nsc; i++) {
        uint32_t fi = r32();
        uint64_t args[10];
        for (int k = 0; k < 10; k++) args[k] = r64();
        uint64_t want = r64();
        Shim shim = NULL;
        for (size_t s = 0; s < sizeof(SCALARS) / sizeof(SCALARS[0]); s++)
            if (strcmp(SCALARS[s].name, fis[fi].name) == 0) shim = SCALARS[s].shim;
        if (!shim) { printf("no shim for %s\n", fis[fi].name); failures++; continue; }
        uint64_t got = shim(args);
        expect_u64(fis[fi].name, i, got, want);
    }
    int nbc = (int)r32();
    for (int i = 0; i < nbc; i++) {
        uint32_t fi = r32();
        uint64_t args[10];
        for (int k = 0; k < 10; k++) args[k] = r64();
        uint64_t want_ret = r64();
        int has_ret = r8();
        uint32_t imglen = r32();
        uint8_t *img = malloc(imglen), *exp = malloc(imglen);
        if (fread(img, 1, imglen, cf) != imglen) return 1;
        if (fread(exp, 1, imglen, cf) != imglen) return 1;
        uint64_t got_ret = run_bcase(&fis[fi], img, args);
        if (has_ret) expect_u64(fis[fi].name, i, got_ret, want_ret);
        total++;
        if (memcmp(img, exp, imglen) != 0) {
            if (failures < 20) {
                printf("MISMATCH %s bcase %d: image differs\n", fis[fi].name, i);
                for (uint32_t k = 0; k < imglen; k++)
                    if (img[k] != exp[k]) { printf("  first diff at %u: got %02x want %02x\n", k, img[k], exp[k]); break; }
            }
            failures++;
            note_fail(fis[fi].name);
        }
        free(img); free(exp);
    }
    fclose(cf);
    /* kernels vs C references */
    {
        uint32_t dst[300], want[300];
        fill32(dst, 257, (int32_t)0xdeadbeef);
        ref_fill32(want, 257, 0xdeadbeef);
        total++;
        if (memcmp(dst, want, 257 * 4) != 0) { printf("MISMATCH fill32\n"); failures++; }
        static uint32_t tex[4096], d2[1024], w2[1024];
        for (int i = 0; i < 4096; i++) tex[i] = (uint32_t)(i * 2654435761u) >> 8;
        span(d2, tex, 1024, 3 << 16, 5 << 16, 70000, -30000, 200);
        ref_span(w2, tex, 1024, 3 << 16, 5 << 16, 70000, -30000, 200);
        total++;
        if (memcmp(d2, w2, sizeof d2) != 0) { printf("MISMATCH span\n"); failures++; }
    }
    for (int i = 0; i < nfail_names; i++) printf("FAILCOUNT %s %d\n", fail_names[i], fail_counts[i]);
    printf("DRIVER cases=%d failures=%d\n", total, failures);
    if (!failures) printf("DRIVER_OK\n");
    return failures ? 1 : 0;
}
