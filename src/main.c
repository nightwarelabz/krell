/* krellc — the Krell toolchain driver.
 *
 *   krellc parse  <in.txt> -o <out.krel>          surface syntax -> binary
 *   krellc dump   <module>                        text dump (debug form)
 *   krellc verify <module> [--target <t>]         verify (+ target gate)
 *   krellc hash   <module>                        canonical encoding hash
 *   krellc run    <module> <func> [i64 args...]   interpret, print result
 *   krellc opt    <module> -o <out.krel>          optimize
 *   krellc build  <module> --target <t> [-O] -o <out.s|.ll>
 *
 * A <module> is a binary module file, or a surface-syntax text file
 * (sniffed by content). Targets: x86_64, aarch64, riscv64, llvm. */
#define _POSIX_C_SOURCE 200809L
#define _DEFAULT_SOURCE 1
#define _DARWIN_C_SOURCE 1
#include "krell.h"
#include <stdio.h>
#include <string.h>
#include <stdlib.h>
#include <unistd.h>
#include <math.h>
#include <sys/ioctl.h>

/* Host externs for `krellc run`: the standard set the example
 * programs link against when compiled ahead of time, provided
 * by the interpreter's host table. Interpreter pointers are
 * offsets into the flat interpreter memory (interp_mem). */
static uint8_t *host_ptr(Interp *it, const IVal *v, size_t len, int *ok) {
    size_t size; uint8_t *mem = interp_mem(it, &size);
    uint64_t off = v->lanes[0];
    if (off > size || len > size - (size_t)off) { *ok = 0; return NULL; }
    *ok = 1; return mem + off;
}

/* The interpreter passes ret->lanes == NULL for void calls,
 * so hosts must never write a result unconditionally. */
static void ret_u64(IVal *ret, uint64_t v) { if (ret->lanes) ret->lanes[0] = v; }

static uint64_t host_write(Interp *it, void *ctx, const IVal *args, int nargs, IVal *ret) {
    (void)ctx; ret_u64(ret, (uint64_t)-1);
    if (nargs < 3) return 0;
    int ok; uint8_t *p = host_ptr(it, &args[1], (size_t)args[2].lanes[0], &ok);
    if (!ok) return 0;
    ret_u64(ret, (uint64_t)write((int)args[0].lanes[0], p, (size_t)args[2].lanes[0]));
    return 0;
}

static uint64_t host_read(Interp *it, void *ctx, const IVal *args, int nargs, IVal *ret) {
    (void)ctx; ret_u64(ret, (uint64_t)-1);
    if (nargs < 3) return 0;
    int ok; uint8_t *p = host_ptr(it, &args[1], (size_t)args[2].lanes[0], &ok);
    if (!ok) return 0;
    ret_u64(ret, (uint64_t)read((int)args[0].lanes[0], p, (size_t)args[2].lanes[0]));
    return 0;
}

static uint64_t host_malloc(Interp *it, void *ctx, const IVal *args, int nargs, IVal *ret) {
    (void)ctx;
    ret_u64(ret, nargs >= 1 ? interp_alloc(it, (size_t)args[0].lanes[0], 16) : 0);
    return 0;
}

static uint64_t host_free(Interp *it, void *ctx, const IVal *args, int nargs, IVal *ret) {
    (void)it; (void)ctx; (void)args; (void)nargs;
    ret_u64(ret, 0);   /* bump region: free is a no-op */
    return 0;
}

static uint64_t host_atoi(Interp *it, void *ctx, const IVal *args, int nargs, IVal *ret) {
    (void)ctx; ret_u64(ret, 0);
    if (nargs < 1) return 0;
    size_t size; uint8_t *mem = interp_mem(it, &size);
    uint64_t off = args[0].lanes[0];
    if (off >= size) return 0;
    const char *s = (const char *)mem + off; size_t max = size - (size_t)off;
    size_t i = 0; int neg = 0; long v = 0;
    while (i < max && (s[i] == ' ' || s[i] == '\t' || s[i] == '\n')) i++;
    if (i < max && (s[i] == '-' || s[i] == '+')) { neg = s[i] == '-'; i++; }
    while (i < max && s[i] >= '0' && s[i] <= '9') { v = v * 10 + (s[i] - '0'); i++; }
    ret_u64(ret, (uint64_t)(neg ? -v : v));
    return 0;
}

static double ival_f64(const IVal *v) { double d; memcpy(&d, &v->lanes[0], 8); return d; }
static void ret_f64(IVal *ret, double d) { if (ret->lanes) memcpy(&ret->lanes[0], &d, 8); }

static uint64_t host_sin(Interp *it, void *ctx, const IVal *args, int nargs, IVal *ret) {
    (void)it; (void)ctx; ret_f64(ret, nargs >= 1 ? sin(ival_f64(&args[0])) : 0.0); return 0;
}
static uint64_t host_cos(Interp *it, void *ctx, const IVal *args, int nargs, IVal *ret) {
    (void)it; (void)ctx; ret_f64(ret, nargs >= 1 ? cos(ival_f64(&args[0])) : 0.0); return 0;
}
static uint64_t host_sqrt(Interp *it, void *ctx, const IVal *args, int nargs, IVal *ret) {
    (void)it; (void)ctx; ret_f64(ret, nargs >= 1 ? sqrt(ival_f64(&args[0])) : 0.0); return 0;
}

static uint64_t host_usleep(Interp *it, void *ctx, const IVal *args, int nargs, IVal *ret) {
    (void)it; (void)ctx;
    if (nargs >= 1) usleep((useconds_t)args[0].lanes[0]);
    ret_u64(ret, 0);
    return 0;
}

/* Same contract as the examples' kc_winsize shim: fill the
 * winsize struct (row, col, xpixel, ypixel as u16s), seeded
 * with 80x24 so a failed query leaves a sane default. */
static uint64_t host_kc_winsize(Interp *it, void *ctx, const IVal *args, int nargs, IVal *ret) {
    (void)ctx; ret_u64(ret, (uint64_t)-1);
    if (nargs < 2) return 0;
    int ok; uint8_t *p = host_ptr(it, &args[1], 8, &ok);
    if (!ok) return 0;
    struct winsize ws; memset(&ws, 0, sizeof ws);
    ws.ws_row = 24; ws.ws_col = 80;
    int rc = ioctl((int)args[0].lanes[0], TIOCGWINSZ, &ws);
    if (ws.ws_row == 0 || ws.ws_col == 0) { ws.ws_row = 24; ws.ws_col = 80; }
    uint16_t v[4] = { ws.ws_row, ws.ws_col, ws.ws_xpixel, ws.ws_ypixel };
    memcpy(p, v, 8);
    ret_u64(ret, (uint64_t)(int64_t)rc);
    return 0;
}

static void register_std_hosts(Interp *it) {
    interp_host(it, "write", host_write, NULL);
    interp_host(it, "read", host_read, NULL);
    interp_host(it, "malloc", host_malloc, NULL);
    interp_host(it, "free", host_free, NULL);
    interp_host(it, "atoi", host_atoi, NULL);
    interp_host(it, "sin", host_sin, NULL);
    interp_host(it, "cos", host_cos, NULL);
    interp_host(it, "sqrt", host_sqrt, NULL);
    interp_host(it, "usleep", host_usleep, NULL);
    interp_host(it, "kc_winsize", host_kc_winsize, NULL);
}

static uint8_t *slurp(const char *path, size_t *len) {
    FILE *f = fopen(path, "rb");
    if (!f) return NULL;
    fseek(f, 0, SEEK_END);
    long n = ftell(f);
    fseek(f, 0, SEEK_SET);
    uint8_t *buf = malloc((size_t)n + 1);
    if (n > 0 && fread(buf, 1, (size_t)n, f) != (size_t)n) { fclose(f); free(buf); return NULL; }
    fclose(f);
    buf[n] = 0;
    *len = (size_t)n;
    return buf;
}

static Module *load_module(const char *path) {
    size_t len;
    uint8_t *buf = slurp(path, &len);
    if (!buf) { fprintf(stderr, "krellc: cannot read %s\n", path); return NULL; }
    Module *m = NULL;
    if (len >= 4 && memcmp(buf, "KREL", 4) == 0) {
        char err[256];
        m = mod_decode(buf, len, err, sizeof err);
        if (!m) fprintf(stderr, "krellc: decode: %s\n", err);
    } else {
        char err[512];
        m = surface_parse((const char *)buf, err, sizeof err);
        if (!m) fprintf(stderr, "krellc: %s\n", err);
    }
    free(buf);
    return m;
}

static int write_file(const char *path, const void *data, size_t len) {
    FILE *f = fopen(path, "wb");
    if (!f) { perror("krellc: output"); return -1; }
    if (len && fwrite(data, 1, len, f) != len) { fclose(f); return -1; }
    fclose(f);
    return 0;
}

static const char *argval(int argc, char **argv, const char *flag) {
    for (int i = 0; i + 1 < argc; i++)
        if (strcmp(argv[i], flag) == 0) return argv[i + 1];
    return NULL;
}
static bool hasflag(int argc, char **argv, const char *flag) {
    for (int i = 0; i < argc; i++) if (strcmp(argv[i], flag) == 0) return true;
    return false;
}

int main(int argc, char **argv) {
    if (argc < 3) {
        fprintf(stderr, "usage: krellc <parse|dump|verify|hash|run|opt|build> <module> [opts]\n");
        return 2;
    }
    const char *cmd = argv[1];
    const char *path = argv[2];

    if (strcmp(cmd, "parse") == 0) {
        size_t len; uint8_t *buf = slurp(path, &len);
        if (!buf) { fprintf(stderr, "krellc: cannot read %s\n", path); return 1; }
        char err[512];
        Module *m = surface_parse((const char *)buf, err, sizeof err);
        free(buf);
        if (!m) { fprintf(stderr, "krellc: %s\n", err); return 1; }
        const char *ve = mod_verify(m);
        if (ve) { fprintf(stderr, "krellc: verify: %s\n", ve); return 1; }
        const char *out = argval(argc, argv, "-o");
        if (!out) { fprintf(stderr, "krellc: parse needs -o\n"); return 2; }
        size_t blen; uint8_t *bytes = mod_encode(m, &blen);
        int rc = write_file(out, bytes, blen);
        free(bytes);
        mod_free(m);
        return rc ? 1 : 0;
    }

    Module *m = load_module(path);
    if (!m) return 1;

    if (strcmp(cmd, "dump") == 0) {
        mod_dump(m, stdout);
    } else if (strcmp(cmd, "verify") == 0) {
        const char *tgt = argval(argc, argv, "--target");
        const char *e = tgt ? mod_verify_target(m, tgt) : mod_verify(m);
        if (e) { fprintf(stderr, "krellc: %s\n", e); return 1; }
        printf("verify OK%s%s\n", tgt ? " target " : "", tgt ? tgt : "");
    } else if (strcmp(cmd, "hash") == 0) {
        uint8_t h[32];
        mod_hash(m, h);
        for (int i = 0; i < 32; i++) printf("%02x", h[i]);
        printf("\n");
    } else if (strcmp(cmd, "run") == 0) {
        if (argc < 4) { fprintf(stderr, "krellc: run needs a function name\n"); return 2; }
        Interp *it = interp_new(m);
        register_std_hosts(it);
        int fi = mod_find_func(m, argv[3]);
        if (fi < 0) { fprintf(stderr, "krellc: no such function\n"); return 1; }
        Func *f = &m->funcs[fi];
        int na = f->blocks[0].nargs;
        if (argc - 4 < na) { fprintf(stderr, "krellc: function takes %d args\n", na); return 2; }
        IVal av[16]; uint64_t lanes[16][256];
        uint64_t scratch = interp_alloc(it, 1 << 20, 16);
        for (int i = 0; i < na; i++) {
            av[i].lanes = lanes[i];
            Type pt = f->blocks[0].arg_types[i];
            av[i].lanes[0] = pt.kind == TY_PTR ? scratch : strtoull(argv[4 + i], NULL, 0);
        }
        IVal rv; uint64_t rl[256]; rv.lanes = rl;
        int rc = interp_call(it, argv[3], av, na, f->ret.kind == TY_VOID ? NULL : &rv);
        if (rc != 0) {
            char eb[256]; interp_last_error(it, eb, sizeof eb);
            fprintf(stderr, "krellc: run: %s\n", eb);
            return 1;
        }
        if (f->ret.kind != TY_VOID) {
            if (f->ret.kind == TY_FLOAT) {
                if (f->ret.bits == 32) { float fv; uint32_t u = (uint32_t)rv.lanes[0]; memcpy(&fv, &u, 4); printf("%g\n", fv); }
                else { double dv; memcpy(&dv, &rv.lanes[0], 8); printf("%g\n", dv); }
            } else printf("%lld (0x%llx)\n", (long long)rv.lanes[0], (unsigned long long)rv.lanes[0]);
        }
        interp_free(it);
    } else if (strcmp(cmd, "opt") == 0) {
        const char *out = argval(argc, argv, "-o");
        if (!out) { fprintf(stderr, "krellc: opt needs -o\n"); return 2; }
        Cost *cost = cost_load(argval(argc, argv, "--target") ? argval(argc, argv, "--target") : "x86_64");
        OptStats st = { 0, 0, 0, 0 };
        opt_optimize(m, cost, &st);
        const char *ve = mod_verify(m);
        if (ve) { fprintf(stderr, "krellc: verify after opt: %s\n", ve); return 1; }
        printf("opt: folded=%d dce=%d rewritten=%d blocks_removed=%d\n", st.folded, st.dce, st.rewritten, st.blocks_removed);
        size_t blen; uint8_t *bytes = mod_encode(m, &blen);
        int rc = write_file(out, bytes, blen);
        free(bytes);
        return rc ? 1 : 0;
    } else if (strcmp(cmd, "build") == 0) {
        const char *tgt = argval(argc, argv, "--target");
        const char *out = argval(argc, argv, "-o");
        if (!tgt || !out) { fprintf(stderr, "krellc: build needs --target and -o\n"); return 2; }
        if (hasflag(argc, argv, "-O")) {
            Cost *oc = cost_load(tgt);
            OptStats st = { 0, 0, 0, 0 };
            opt_optimize(m, oc, &st);
        }
        Cost *cost = cost_load(tgt);
        FILE *o = fopen(out, "w");
        if (!o) { perror("krellc: output"); return 1; }
        char err[512]; int rc;
        if (strcmp(tgt, "x86_64") == 0) rc = be_x86_64(m, cost, o, err, sizeof err);
        else if (strcmp(tgt, "aarch64") == 0) rc = be_aarch64(m, cost, o, err, sizeof err);
        else if (strcmp(tgt, "riscv64") == 0) rc = be_riscv64(m, cost, o, err, sizeof err);
        else if (strcmp(tgt, "llvm") == 0) rc = be_llvm(m, cost, o, err, sizeof err);
        else { fprintf(stderr, "krellc: unknown target %s\n", tgt); fclose(o); return 2; }
        fclose(o);
        if (rc) { fprintf(stderr, "krellc: backend: %s\n", err); return 1; }
    } else {
        fprintf(stderr, "krellc: unknown command %s\n", cmd);
        return 2;
    }
    mod_free(m);
    return 0;
}
