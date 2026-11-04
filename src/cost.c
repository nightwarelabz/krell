/* Krell — per-target cost oracle: parses targets/<target>.cost files.
 * Format: see docs/SPEC.md §6. Unknown ops report lat -1 (the verifier's
 * target gate treats unknown core ops and cliff=1 ops as rejections). */
#include "krell.h"

#define COST_MAXFN 32
struct Cost {
    char target[64];
    int  vl_i32;
    /* per-op rows per class: 0 int, 1 float, 2 vec, 3 i128 (v3.0) */
    int  lat[OP_COUNT][4];
    int  thr[OP_COUNT][4];
    int  cliff[OP_COUNT][4];
    char fnname[COST_MAXFN][32];
    int  fncost[COST_MAXFN];
    int  nfn;
};

static int cls_of(Type t) {
    if (t.kind == TY_VEC) return 2;
    if (t.kind == TY_FLOAT) return 1;
    if (t.kind == TY_INT && t.bits == 128) return 3;
    return 0;
}

Cost *cost_load(const char *target) {
    char path[512];
    FILE *fp = NULL;
    const char *dirs[3];
    char env[512];
    const char *e = getenv("KRELL_TARGETS");
    snprintf(env, sizeof env, "%s", e ? e : "");
    dirs[0] = env[0] ? env : NULL;
    dirs[1] = "targets";
    dirs[2] = "../targets";
    for (int i = 0; i < 3 && !fp; i++) {
        if (!dirs[i]) continue;
        snprintf(path, sizeof path, "%s/%s.cost", dirs[i], target);
        fp = fopen(path, "r");
    }
    if (!fp) return NULL;
    Cost *c = calloc(1, sizeof(Cost));
    snprintf(c->target, sizeof c->target, "%s", target);
    c->vl_i32 = 4;
    for (int i = 0; i < OP_COUNT; i++)
        for (int j = 0; j < 4; j++) { c->lat[i][j] = -1; c->thr[i][j] = -1; }
    char line[256];
    while (fgets(line, sizeof line, fp)) {
        char w1[64], w2[64];
        if (line[0] == '#' || line[0] == '\n') continue;
        if (sscanf(line, "vl %d", &c->vl_i32) == 1) continue;
        if (sscanf(line, "op %63[^.].%63s", w1, w2) == 2) {
            int op = -1;
            for (int i = 1; i < OP_COUNT; i++)
                if (op_name(i) && strcmp(op_name(i), w1) == 0) { op = i; break; }
            if (op < 0) continue;
            int cls = 0;
            if (strcmp(w2, "i128") == 0) cls = 3;
            else if (w2[0] == 'f') cls = 1; else if (w2[0] == 'v') cls = 2; else cls = 0;
            int lat = -2, thr = -2, cliff = -1;
            char *p;
            if ((p = strstr(line, "lat "))) lat = atoi(p + 4);
            if ((p = strstr(line, "thr "))) thr = atoi(p + 4);
            if ((p = strstr(line, "cliff "))) cliff = atoi(p + 6);
            if (lat != -2) c->lat[op][cls] = lat;
            if (thr != -2) c->thr[op][cls] = thr;
            if (cliff >= 0) c->cliff[op][cls] = cliff;
            continue;
        }
        char fname[32]; int fc;
        if (sscanf(line, "fn %31s cost %d", fname, &fc) == 2 && c->nfn < COST_MAXFN) {
            snprintf(c->fnname[c->nfn], 32, "%s", fname);
            c->fncost[c->nfn] = fc;
            c->nfn++;
        }
    }
    fclose(fp);
    return c;
}

void cost_free(Cost *c) { free(c); }
int cost_vl_i32(const Cost *c) { return c ? c->vl_i32 : 4; }
int cost_lat(const Cost *c, int op, Type t) {
    if (!c || op <= 0 || op >= OP_COUNT) return -1;
    int v = c->lat[op][cls_of(t)];
    if (v < 0) v = c->lat[op][0];
    return v;
}
int cost_thr(const Cost *c, int op, Type t) {
    if (!c || op <= 0 || op >= OP_COUNT) return -1;
    int v = c->thr[op][cls_of(t)];
    if (v < 0) v = c->thr[op][0];
    return v;
}
bool cost_cliff(const Cost *c, int op, Type t) {
    if (!c || op <= 0 || op >= OP_COUNT) return false;
    int cl = cls_of(t);
    if (c->cliff[op][cl]) return true;
    return c->cliff[op][0] != 0;
}
const char *cost_target_name(const Cost *c) { return c ? c->target : "?"; }
