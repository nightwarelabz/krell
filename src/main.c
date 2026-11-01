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
#include "krell.h"
#include <stdio.h>
#include <string.h>

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
