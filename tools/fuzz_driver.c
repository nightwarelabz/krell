/* fuzz_driver — replays fuzz_gen's case file against natively compiled
 * random functions. The symbol table header is generated per run:
 * compile with -DFTAB_H='"path/to.ftab.h"'.
 * Usage: fuzz_driver <cases.fcases> */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>

#ifndef FTAB_H
#error "define FTAB_H to the generated table header"
#endif
#include FTAB_H

enum { FK_S, FK_M, FK_B, FK_L };

typedef uint64_t (*FnS)(uint64_t, uint64_t, uint64_t);
typedef uint64_t (*FnM)(void *, uint64_t, uint64_t);
typedef uint64_t (*FnL)(uint64_t);

static FILE *cf;
static uint8_t r8(void) { int c = fgetc(cf); return (uint8_t)c; }
static uint32_t r32(void) { uint32_t v; if (fread(&v, 4, 1, cf) != 1) v = 0; return v; }
static uint64_t r64(void) { uint64_t v; if (fread(&v, 8, 1, cf) != 1) v = 0; return v; }

int main(int argc, char **argv) {
    if (argc < 2) { fprintf(stderr, "usage: fuzz_driver <cases>\n"); return 2; }
    cf = fopen(argv[1], "rb");
    if (!cf) { perror("cases"); return 1; }
    char magic[4];
    if (fread(magic, 1, 4, cf) != 4 || memcmp(magic, "RFUZ", 4) != 0) { printf("bad case file\n"); return 1; }
    (void)r32();
    int nf = (int)r32();
    if (nf != (int)NFTAB) { printf("func table mismatch: file %d driver %d\n", nf, (int)NFTAB); return 1; }
    for (int i = 0; i < nf; i++) {
        int nl = r8();
        char nm[32]; if (fread(nm, 1, (size_t)nl, cf) != (size_t)nl) return 1;
        nm[nl] = 0;
        int kind = r8();
        if (strcmp(nm, FTAB[i].name) != 0 || kind != FTAB[i].kind) { printf("func %d mismatch\n", i); return 1; }
    }
    int nc = (int)r32();
    int failures = 0, total = 0;
    for (int i = 0; i < nc; i++) {
        uint32_t fi = r32();
        uint64_t a0 = r64(), a1 = r64(), a2 = r64(), exp = r64();
        const FTabEnt *fe = &FTAB[fi];
        uint64_t got = 0;
        if (fe->kind == FK_M) {
            uint8_t img[256], expi[256];
            if (fread(img, 1, 256, cf) != 256) return 1;
            if (fread(expi, 1, 256, cf) != 256) return 1;
            got = ((FnM)fe->fn)(img, a1, a2);
            total++;
            if (got != exp || memcmp(img, expi, 256) != 0) {
                if (failures < 20) printf("MISMATCH %s case %d: got 0x%llx want 0x%llx imgdiff %d\n",
                    fe->name, i, (unsigned long long)got, (unsigned long long)exp, memcmp(img, expi, 256) != 0);
                failures++;
            }
        } else if (fe->kind == FK_L) {
            got = ((FnL)fe->fn)(a0);
            total++;
            if (got != exp) {
                if (failures < 20) printf("MISMATCH %s case %d: got 0x%llx want 0x%llx\n",
                    fe->name, i, (unsigned long long)got, (unsigned long long)exp);
                failures++;
            }
        } else {
            got = ((FnS)fe->fn)(a0, a1, a2);
            total++;
            if (got != exp) {
                if (failures < 20) printf("MISMATCH %s case %d: got 0x%llx want 0x%llx\n",
                    fe->name, i, (unsigned long long)got, (unsigned long long)exp);
                failures++;
            }
        }
    }
    fclose(cf);
    printf("FUZZ_DRIVER cases=%d failures=%d\n", total, failures);
    if (!failures) printf("FUZZ_OK\n");
    return failures ? 1 : 0;
}
