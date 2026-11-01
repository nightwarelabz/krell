/* Kernel timing: Krell-compiled fill32/span vs the C references at -O2.
 * Best-of-7 wall times over large buffers; prints ns per call. */
#define _POSIX_C_SOURCE 199309L
#include <stdio.h>
#include <stdint.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>

extern void ref_fill32(uint32_t *, int64_t, uint32_t);
extern void ref_span(uint32_t *, const uint32_t *, int64_t, int32_t, int32_t, int32_t, int32_t, int32_t);
extern void fill32(void *, int64_t, int32_t);
extern void span(void *, const void *, int64_t, int32_t, int32_t, int32_t, int32_t, int32_t);

static double now_s(void) {
    struct timespec ts; clock_gettime(CLOCK_MONOTONIC, &ts);
    return ts.tv_sec + ts.tv_nsec * 1e-9;
}

int main(void) {
    const int64_t N = 1 << 20;
    uint32_t *buf = malloc((size_t)N * 4);
    static uint32_t tex[4096];
    for (int i = 0; i < 4096; i++) tex[i] = (uint32_t)(i * 2654435761u) >> 8;
    /* fill32 */
    double best_krell = 1e30, best_ref = 1e30;
    for (int r = 0; r < 7; r++) {
        double t0 = now_s();
        for (int i = 0; i < 20; i++) fill32(buf, N, 0x12345678);
        double dt = (now_s() - t0) / 20;
        if (dt < best_krell) best_krell = dt;
        t0 = now_s();
        for (int i = 0; i < 20; i++) ref_fill32(buf, N, 0x12345678);
        dt = (now_s() - t0) / 20;
        if (dt < best_ref) best_ref = dt;
    }
    printf("fill32 1M px: krell %.1f ns  C-O2 %.1f ns  ratio %.2f\n",
           best_krell * 1e9, best_ref * 1e9, best_krell / best_ref);
    /* span: 4096-wide rows */
    double bs_krell = 1e30, bs_ref = 1e30;
    for (int r = 0; r < 7; r++) {
        double t0 = now_s();
        for (int i = 0; i < 200; i++) span(buf, tex, 4096, 3 << 16, 5 << 16, 70000, -30000, 200);
        double dt = (now_s() - t0) / 200;
        if (dt < bs_krell) bs_krell = dt;
        t0 = now_s();
        for (int i = 0; i < 200; i++) ref_span(buf, tex, 4096, 3 << 16, 5 << 16, 70000, -30000, 200);
        dt = (now_s() - t0) / 200;
        if (dt < bs_ref) bs_ref = dt;
    }
    printf("span 4096 px: krell %.1f ns  C-O2 %.1f ns  ratio %.2f\n",
           bs_krell * 1e9, bs_ref * 1e9, bs_krell / bs_ref);
    free(buf);
    return 0;
}
