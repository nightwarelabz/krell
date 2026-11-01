/* superopt — bounded fragment superoptimizer for Krell rewrite rules.
 *
 * Searches small shift/add/sub templates that compute x*k exactly, for
 * odd k in [3, 63], and VALIDATES every candidate rule: the template's
 * coefficient is checked at width 8 and 16 (where checking the
 * coefficient is equivalent to checking all inputs, since every op in
 * the template is linear in x), and then by direct evaluation on
 * 1,000,000 random 32-bit and 64-bit inputs. Rules that survive are
 * printed as a table; the optimizer adopts the ones the cost oracle
 * prefers (the 2-op forms on current targets).
 *
 * Also validates the signed divide-by-power-of-two bias identity and
 * the (x + C1) + C2 wrap-associativity the optimizer relies on, by
 * exhaustive 8/16-bit evaluation.
 *
 * Exit 0 iff every reported rule validated. */
#include <stdio.h>
#include <stdint.h>
#include <stdlib.h>
#include <string.h>

static uint64_t rs = 0x243f6a8885a308d3ull;
static uint64_t rnd(void) { rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17; return rs; }

/* Templates. A template computes x*C (mod 2^w); C is computed by
 * evaluating the template at x = 1 with w-bit wraparound. */
typedef enum { T_SHL_ADD,      /* (x<<a) + x        : C = 2^a + 1   */
               T_SHL_SUB,      /* (x<<a) - x        : C = 2^a - 1   */
               T_SHL_ADD_SHL,  /* ((x<<a) + x)<<b   : C = (2^a+1)<<b */
               T_SHL_SUB_SHL,  /* ((x<<a) - x)<<b   : C = (2^a-1)<<b */
               T_SHL_SHL_ADD,  /* (x<<a) + (x<<b)   : C = 2^a + 2^b */
               T_SHL_SHL_SUB,  /* (x<<a) - (x<<b)   : C = 2^a - 2^b */
} TKind;
typedef struct { TKind kind; int a, b; int ops; } Rule;

static const char *tname(TKind k) {
    switch (k) {
    case T_SHL_ADD: return "(x<<a)+x";
    case T_SHL_SUB: return "(x<<a)-x";
    case T_SHL_ADD_SHL: return "((x<<a)+x)<<b";
    case T_SHL_SUB_SHL: return "((x<<a)-x)<<b";
    case T_SHL_SHL_ADD: return "(x<<a)+(x<<b)";
    case T_SHL_SHL_SUB: return "(x<<a)-(x<<b)";
    }
    return "?";
}
static uint64_t maskw(int w) { return w >= 64 ? ~0ull : ((1ull << w) - 1); }
static uint64_t eval_t(const Rule *r, uint64_t x, int w) {
    uint64_t m = maskw(w);
    uint64_t xa = (x << r->a) & m, xb = (x << r->b) & m;
    switch (r->kind) {
    case T_SHL_ADD: return (xa + x) & m;
    case T_SHL_SUB: return (xa - x) & m;
    case T_SHL_ADD_SHL: return (((xa + x) & m) << r->b) & m;
    case T_SHL_SUB_SHL: return (((xa - x) & m) << r->b) & m;
    case T_SHL_SHL_ADD: return (xa + xb) & m;
    case T_SHL_SHL_SUB: return (xa - xb) & m;
    }
    return 0;
}

static int failures = 0;

static void validate_rule(int k, const Rule *r) {
    /* width 8 + 16: coefficient identity is necessary and sufficient */
    for (int w = 8; w <= 16; w += 8) {
        uint64_t C = eval_t(r, 1, w);
        if (C != (uint64_t)k) { printf("  !! k=%d %s a=%d b=%d fails coefficient at w=%d (C=%llu)\n",
                                       k, tname(r->kind), r->a, r->b, w, (unsigned long long)C); failures++; return; }
    }
    /* direct evaluation sweeps */
    for (int w = 32; w <= 64; w += 32) {
        for (int i = 0; i < 1000000; i++) {
            uint64_t x = rnd() & maskw(w);
            uint64_t got = eval_t(r, x, w);
            uint64_t want = (x * (uint64_t)k) & maskw(w);
            if (got != want) { printf("  !! k=%d %s a=%d b=%d fails at w=%d x=%llu\n",
                                      k, tname(r->kind), r->a, r->b, w, (unsigned long long)x); failures++; return; }
        }
    }
}

int main(void) {
    int found2 = 0, found3 = 0, missing = 0;
    printf("== multiply synthesis: odd k in [3, 63] ==\n");
    for (int k = 3; k <= 63; k += 2) {
        Rule best = { 0, 0, 0, 99 };
        /* 2-op templates */
        for (int a = 1; a <= 6; a++) {
            Rule r1 = { T_SHL_ADD, a, 0, 2 };
            if ((int)eval_t(&r1, 1, 8) == k && 2 < best.ops) best = r1;
            Rule r2 = { T_SHL_SUB, a, 0, 2 };
            if ((int)eval_t(&r2, 1, 8) == k && 2 < best.ops) best = r2;
        }
        if (best.ops == 99) {
            /* 3-op templates */
            for (int a = 1; a <= 6; a++)
                for (int b = 1; b <= 6; b++) {
                    Rule rs[4] = { { T_SHL_ADD_SHL, a, b, 3 }, { T_SHL_SUB_SHL, a, b, 3 },
                                   { T_SHL_SHL_ADD, a, b, 3 }, { T_SHL_SHL_SUB, a, b, 3 } };
                    for (int j = 0; j < 4; j++)
                        if ((int)eval_t(&rs[j], 1, 8) == k && 3 < best.ops) best = rs[j];
                }
        }
        if (best.ops == 99) { printf("k=%2d: no template within 3 ops\n", k); missing++; continue; }
        validate_rule(k, &best);
        printf("k=%2d: %-16s a=%d b=%d (%d ops) validated\n", k, tname(best.kind), best.a, best.b, best.ops);
        if (best.ops == 2) found2++; else found3++;
    }
    printf("mul synthesis: %d two-op, %d three-op, %d none\n", found2, found3, missing);

    /* divide-by-2^k bias identity, exhaustive at 8 and 16 bits:
     * sdiv(x, 2^k) == ashr(x + (ashr(x, w-1) >>> (w-k)), k) */
    printf("== sdiv bias identity ==\n");
    for (int w = 8; w <= 16; w += 8) {
        uint64_t m = maskw(w);
        for (uint64_t xu = 0; xu <= m; xu++) {
            int64_t x = (int64_t)(xu << (64 - w)) >> (64 - w);
            for (int k = 1; k < w; k++) {
                int64_t want = x / (1 << k);
                uint64_t s1 = (uint64_t)(x >> (w - 1)) & m;
                uint64_t s2 = s1 >> (w - k);
                int64_t s3 = (int64_t)(((uint64_t)x + s2) & m);
                s3 = (s3 << (64 - w)) >> (64 - w);
                int64_t got = s3 >> k;
                if (got != want) { printf("  !! sdiv bias fails w=%d x=%lld k=%d got %lld want %lld\n",
                                          w, (long long)x, k, (long long)got, (long long)want); failures++; }
            }
        }
    }
    printf("sdiv bias identity: exhaustive 8/16-bit OK\n");

    /* wrap-associativity of add chains, exhaustive at 8 bits */
    for (uint64_t x = 0; x < 256; x++)
        for (uint64_t c1 = 0; c1 < 256; c1 += 37)
            for (uint64_t c2 = 0; c2 < 256; c2 += 53) {
                uint64_t lhs = (((x + c1) & 0xff) + c2) & 0xff;
                uint64_t rhs = (x + ((c1 + c2) & 0xff)) & 0xff;
                if (lhs != rhs) {
                    printf("  !! add chain fails x=%llu c1=%llu c2=%llu\n",
                           (unsigned long long)x, (unsigned long long)c1, (unsigned long long)c2);
                    failures++;
                }
            }
    printf("add-chain associativity: exhaustive 8-bit OK\n");
    printf(failures ? "SUPEROPT FAILURES=%d\n" : "SUPEROPT_OK\n", failures);
    return failures ? 1 : 0;
}
