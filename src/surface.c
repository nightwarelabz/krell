/* Krell — human surface syntax: a small readable text form that parses
 * into the same IR the builder API produces. Deliberately a debugging /
 * authoring surface, not the interchange format (that is the binary).
 *
 * Grammar sketch:
 *   module   := (func | data | extern)*
 *   data     := "data" name ":" type "=" "{" int,... "}"
 *   extern   := "extern" name "(" types ")" "->" type
 *   func     := "fn" name "(" args ")" "->" type "{" block+ "}"
 *   block    := label "(" (name ":" type, ...) ")" ":" instr*
 *   instr    := "%"name "=" op ... | op ... | terminator
 *   op       := binop type a, b | unop type a | "icmp."pred type a, b
 *             | "fcmp."pred type a, b | "load" type, a | "store" type a, b
 *             | "gep" type a, b | "call" type name, (args) | "select" ...
 *             | "iconst" type imm | "fconst" type num | "alloca" size, align
 *             | "dataptr" int | "freeze" type a | conversions type a
 *             | "aload"/"astore"/"aadd" ["." order] type ...
 *             | "memcpy" a, b, c | "memset" a, b, c | vec ops ...
 *   terminator := "ret" [value] | "br" label "(" args ")"
 *             | "condbr" cond, label "(" args "), label "(" args ")"
 *             | "tailcall" type name, (args)
 * Values are named with %name or bare identifiers; integer and float
 * literals may appear wherever a value of a known type is expected.
 * Comments start with ';' or '#'. */
#include "krell.h"
#include <ctype.h>

typedef struct {
    const char *p;
    char err[256];
    Module *m;
    /* per-function symbol table */
    struct { char name[64]; int val; } syms[4096];
    int nsyms;
    struct { char name[64]; int idx; } blocks[256];
    int nblocks;
    /* block arg names (phase A), in an arena of 64-byte slots */
    int barg_off[256];
    int bnargs[256];
    char argarena[1 << 16];
    int argarena_len;
    /* queued function bodies, parsed after all shells exist */
    struct { int fi; const char *start, *end; } bodies[1024];
    int nbodies;
    /* function signatures captured at shell (header) parse time, so a call
       can be typed before the callee's body has been parsed (forward refs) */
    Type fsig_params[1024][16];
    int fsig_nparams[1024];
} P;

static void perr(P *p, const char *msg) {
    if (!p->err[0]) snprintf(p->err, sizeof p->err, "surface: %s (near: %.24s)", msg, p->p);
}
static void skip_ws(P *p) {
    for (;;) {
        while (*p->p && isspace((uint8_t)*p->p)) p->p++;
        if (*p->p == ';' || *p->p == '#') { while (*p->p && *p->p != '\n') p->p++; continue; }
        break;
    }
}
static bool is_id0(char ch) { return isalpha((uint8_t)ch) || ch == '_' || ch == '.' || ch == '%'; }
static bool is_idc(char ch) { return isalnum((uint8_t)ch) || ch == '_' || ch == '.'; }
static bool word(P *p, char *out, size_t cap) {
    skip_ws(p);
    if (!is_id0(*p->p)) return false;
    size_t n = 0;
    if (*p->p == '%') p->p++;
    while (is_idc(*p->p) && n + 1 < cap) out[n++] = *p->p++;
    out[n] = 0;
    return n > 0;
}
static bool eat(P *p, const char *tok) {
    skip_ws(p);
    size_t n = strlen(tok);
    if (strncmp(p->p, tok, n) == 0 && !is_idc(p->p[n])) { p->p += n; return true; }
    if (strncmp(p->p, tok, n) == 0 && (tok[n - 1] == '(' || tok[n - 1] == ',' || tok[n - 1] == ':' || tok[n - 1] == '=')) { p->p += n; return true; }
    return false;
}
static bool eat_ch(P *p, char ch) {
    skip_ws(p);
    if (*p->p == ch) { p->p++; return true; }
    return false;
}
static bool is_number_start(P *p) {
    skip_ws(p);
    return isdigit((uint8_t)*p->p) || (*p->p == '-' && isdigit((uint8_t)p->p[1]));
}
static int64_t parse_int(P *p) {
    skip_ws(p);
    char *end;
    long long v = strtoll(p->p, &end, 0);
    if (end == p->p) { perr(p, "expected integer"); return 0; }
    p->p = end;
    return (int64_t)v;
}
static double parse_double(P *p) {
    skip_ws(p);
    char *end;
    double d = strtod(p->p, &end);
    if (end == p->p) { perr(p, "expected number"); return 0; }
    p->p = end;
    return d;
}

static bool parse_type(P *p, Type *t) {
    char w[64];
    if (!word(p, w, sizeof w)) { perr(p, "expected type"); return false; }
    if (strcmp(w, "void") == 0) { *t = ty_void(); return true; }
    if (strcmp(w, "ptr") == 0) { *t = ty_ptr(); return true; }
    if (strcmp(w, "f32") == 0) { *t = ty_f32(); return true; }
    if (strcmp(w, "f64") == 0) { *t = ty_f64(); return true; }
    if (w[0] == 'i' && isdigit((uint8_t)w[1])) {
        int bits = atoi(w + 1);
        if (bits < 1 || bits > 64) { perr(p, "bad int width"); return false; }
        *t = ty_int(bits); return true;
    }
    if (w[0] == 'v') {   /* v<lanes><elem> e.g. v4i32, v2f64 */
        char *q = w + 1;
        int lanes = 0;
        while (isdigit((uint8_t)*q)) { lanes = lanes * 10 + (*q - '0'); q++; }
        Type e;
        if (q[0] == 'i' && isdigit((uint8_t)q[1])) e = ty_int(atoi(q + 1));
        else if (strcmp(q, "f32") == 0) e = ty_f32();
        else if (strcmp(q, "f64") == 0) e = ty_f64();
        else { perr(p, "bad vector element"); return false; }
        /* units n: total bits / 128 with the default VL of 4 i32 lanes */
        int total = lanes * (e.kind == TY_FLOAT ? e.bits : e.bits);
        int n = total / 128;
        if (n < 1 || total % 128) { perr(p, "vector size must be a multiple of 128 bits"); return false; }
        *t = ty_vec(e, n);
        return true;
    }
    perr(p, "unknown type");
    return false;
}

static int sym_find(P *p, const char *name) {
    for (int i = 0; i < p->nsyms; i++)
        if (strcmp(p->syms[i].name, name) == 0) return p->syms[i].val;
    return -1;
}
static void sym_add(P *p, const char *name, int val) {
    for (int i = 0; i < p->nsyms; i++)
        if (strcmp(p->syms[i].name, name) == 0) { p->syms[i].val = val; return; }
    if (p->nsyms >= 4096) return;
    snprintf(p->syms[p->nsyms].name, 64, "%s", name);
    p->syms[p->nsyms].val = val;
    p->nsyms++;
}
static int block_find(P *p, const char *name) {
    for (int i = 0; i < p->nblocks; i++)
        if (strcmp(p->blocks[i].name, name) == 0) return p->blocks[i].idx;
    return -1;
}

/* a value: %name | identifier | literal (typed by the caller) */
static int parse_value(P *p, Func *f, int blk, Type ty) {
    skip_ws(p);
    if (is_number_start(p)) {
        if (ty.kind == TY_FLOAT) {
            double d = parse_double(p);
            if (ty.bits == 32) { float fv = (float)d; uint32_t u; memcpy(&u, &fv, 4); return emit(f, blk, ins_fconst(ty, u)); }
            uint64_t u; memcpy(&u, &d, 8);
            return emit(f, blk, ins_fconst(ty, u));
        }
        return emit(f, blk, ins_iconst(ty, parse_int(p)));
    }
    char w[64];
    if (!word(p, w, sizeof w)) { perr(p, "expected value"); return -1; }
    int v = sym_find(p, w);
    if (v < 0) { perr(p, "unknown value name"); return -1; }
    return v;
}

static int parse_order(P *p, const char *w) {
    (void)p;
    const char *dot = strrchr(w, '.');
    if (!dot) return AO_RELAXED;
    if (strcmp(dot, ".acqrel") == 0) return AO_ACQREL;
    if (strcmp(dot, ".seqcst") == 0) return AO_SEQCST;
    if (strcmp(dot, ".acquire") == 0) return AO_ACQUIRE;
    if (strcmp(dot, ".release") == 0) return AO_RELEASE;
    return AO_RELAXED;
}

/* parse a branch argument list "(" v, v, ... ")" into a fresh array */
static int32_t *parse_branch_args(P *p, Func *f, int blk, Block *tgtblk, int *n_out) {
    int32_t *arr = NULL;
    int n = 0;
    if (!eat_ch(p, '(')) { perr(p, "expected ("); return NULL; }
    skip_ws(p);
    if (*p->p != ')') {
        for (;;) {
            if (n >= tgtblk->nargs) { perr(p, "too many branch args"); free(arr); return NULL; }
            Type at = tgtblk->arg_types[n];
            int v = parse_value(p, f, blk, at);
            if (v < 0) { free(arr); return NULL; }
            arr = realloc(arr, sizeof(int32_t) * (size_t)(n + 1));
            arr[n++] = (int32_t)v;
            if (!eat_ch(p, ',')) break;
        }
    }
    if (!eat_ch(p, ')')) { perr(p, "expected )"); free(arr); return NULL; }
    *n_out = n;
    return arr;
}

static bool parse_instr(P *p, Func *f, int blk) {
    skip_ws(p);
    const char *save = p->p;
    char w[64];
    /* result binding? "%name =" or "name =" */
    char resname[64] = "";
    {
        const char *q = p->p;
        char nm[64]; size_t nn = 0;
        if (*q == '%') q++;
        const char *r = q;
        while (is_idc(*r)) r++;
        if (r > q && (size_t)(r - q) < sizeof nm) {
            memcpy(nm, q, (size_t)(r - q)); nm[r - q] = 0; nn = (size_t)(r - q);
            const char *s = r;
            while (*s && isspace((uint8_t)*s)) s++;
            if (*s == '=' && nn > 0) {
                snprintf(resname, sizeof resname, "%s", nm);
                p->p = s + 1;
            }
        }
        if (!resname[0]) p->p = save;
    }
    if (!word(p, w, sizeof w)) { perr(p, "expected instruction"); return false; }
    int result = -2;   /* -2: no result handling yet */
    Type ty;
    /* terminators first */
    if (strcmp(w, "ret") == 0) {
        /* a bare ret ends at the end of its line: skip blanks only.
         * a newline-crossing skip would consume the next block's
         * label as a would-be return value. a comment also closes
         * the line, so it closes the ret as well. */
        while (*p->p == ' ' || *p->p == '\t') p->p++;
        if (*p->p == '\n' || *p->p == '\r' || *p->p == '}' || *p->p == 0 ||
            *p->p == ';' || *p->p == '#') { emit(f, blk, ins_ret(-1)); return true; }
        /* value type: the function's return type */
        int v = parse_value(p, f, blk, f->ret);
        emit(f, blk, ins_ret(v));
        return true;
    }
    if (strcmp(w, "br") == 0) {
        char lb[64];
        if (!word(p, lb, sizeof lb)) { perr(p, "br target"); return false; }
        int tg = block_find(p, lb);
        if (tg < 0) { perr(p, "unknown block"); return false; }
        int n; int32_t *args = parse_branch_args(p, f, blk, &f->blocks[tg], &n);
        if (!args && f->blocks[tg].nargs) return false;
        emit(f, blk, ins_br(tg, args, n));
        return true;
    }
    if (strcmp(w, "condbr") == 0) {
        int cond = parse_value(p, f, blk, ty_i1());
        if (!eat_ch(p, ',')) { perr(p, "condbr ,"); return false; }
        char l1[64], l2[64];
        if (!word(p, l1, sizeof l1)) return false;
        int t1 = block_find(p, l1);
        if (t1 < 0) { perr(p, "condbr target"); return false; }
        int n1; int32_t *a1 = parse_branch_args(p, f, blk, &f->blocks[t1], &n1);
        if (!eat_ch(p, ',')) { perr(p, "condbr ,"); return false; }
        if (!word(p, l2, sizeof l2)) return false;
        int t2 = block_find(p, l2);
        if (t2 < 0) { perr(p, "condbr target"); return false; }
        int n2; int32_t *a2 = parse_branch_args(p, f, blk, &f->blocks[t2], &n2);
        emit(f, blk, ins_condbr(cond, t1, a1, n1, t2, a2, n2));
        return true;
    }
    if (strcmp(w, "tailcall") == 0) {
        if (!parse_type(p, &ty)) return false;
        char nm[64];
        if (!word(p, nm, sizeof nm)) return false;
        bool ext = false; int ci = mod_find_func(p->m, nm);
        if (ci < 0) { ci = mod_find_extern(p->m, nm); ext = true; }
        if (ci < 0) { perr(p, "unknown callee"); return false; }
        /* args */
        const Type *ps; int np;
        if (ext) { ps = p->m->exts[ci].params; np = p->m->exts[ci].nparams; }
        else { ps = p->fsig_params[ci]; np = p->fsig_nparams[ci]; }
        if (!eat_ch(p, '(')) { perr(p, "call ("); return false; }
        int32_t *args = NULL; int n = 0;
        skip_ws(p);
        if (*p->p != ')') {
            for (;;) {
                int v = parse_value(p, f, blk, ps[n < np ? n : 0]);
                args = realloc(args, sizeof(int32_t) * (size_t)(n + 1));
                args[n++] = (int32_t)v;
                if (!eat_ch(p, ',')) break;
            }
        }
        if (!eat_ch(p, ')')) { perr(p, "call )"); return false; }
        emit(f, blk, ins_call(ty, ci, ext, args, n, true));
        return true;
    }
    /* everything else makes a value or a statement */
    int op = -1;
    for (int i = 1; i < OP_COUNT; i++) {
        const char *nm = op_name(i);
        if (nm && strcmp(w, nm) == 0) { op = i; break; }
        /* icmp.<pred> / fcmp.<pred> / atomic orders */
        if (nm && strncmp(w, nm, strlen(nm)) == 0 && w[strlen(nm)] == '.') { op = i; break; }
    }
    if (op < 0) { perr(p, "unknown op"); return false; }
    switch (op) {
    case OP_ICONST:
        if (!parse_type(p, &ty)) return false;
        result = emit(f, blk, ins_iconst(ty, parse_int(p)));
        break;
    case OP_FCONST:
        if (!parse_type(p, &ty)) return false;
        result = parse_value(p, f, blk, ty);
        break;
    case OP_ADD: case OP_SUB: case OP_MUL: case OP_UDIV: case OP_SDIV:
    case OP_UREM: case OP_SREM: case OP_AND: case OP_OR: case OP_XOR:
    case OP_SHL: case OP_LSHR: case OP_ASHR:
    case OP_FADD: case OP_FSUB: case OP_FMUL: case OP_FDIV:
    case OP_VADD: case OP_VSUB: case OP_VMUL: case OP_VUDIV:
    case OP_VFADD: case OP_VFSUB: case OP_VFMUL: case OP_VFDIV:
    case OP_VAND: case OP_VOR: case OP_VXOR: case OP_VLSHR: {
        if (!parse_type(p, &ty)) return false;
        int a = parse_value(p, f, blk, ty);
        if (!eat_ch(p, ',')) { perr(p, "expected ,"); return false; }
        int b = parse_value(p, f, blk, ty);
        result = emit(f, blk, ins_bin((uint8_t)op, ty, a, b));
        break;
    }
    case OP_NEG: case OP_NOT: case OP_POPCOUNT: case OP_CLZ: case OP_CTZ: case OP_BSWAP:
    case OP_FNEG: case OP_FABS: case OP_VSPLAT: {
        if (!parse_type(p, &ty)) return false;
        Type at = op == OP_VSPLAT ? ty_elem(ty) : ty;
        int a = parse_value(p, f, blk, at);
        result = emit(f, blk, ins_un((uint8_t)op, ty, a));
        break;
    }
    case OP_ICMP: case OP_FCMP: {
        const char *dot = strrchr(w, '.');
        if (!dot) { perr(p, "cmp needs .pred"); return false; }
        int pred = -1;
        if (op == OP_ICMP) {
            static const char *PN[10] = { "eq","ne","ult","ule","ugt","uge","slt","sle","sgt","sge" };
            for (int i = 0; i < 10; i++) if (strcmp(dot + 1, PN[i]) == 0) pred = i;
        } else {
            static const char *PN[14] = { "oeq","one","olt","ole","ogt","oge","ueq","une","ult","ule","ugt","uge","ord","uno" };
            for (int i = 0; i < 14; i++) if (strcmp(dot + 1, PN[i]) == 0) pred = i;
        }
        if (pred < 0) { perr(p, "bad predicate"); return false; }
        if (!parse_type(p, &ty)) return false;
        int a = parse_value(p, f, blk, ty);
        if (!eat_ch(p, ',')) { perr(p, "expected ,"); return false; }
        int b = parse_value(p, f, blk, ty);
        Instr in = ins_make((uint8_t)op, ty_i1()); in.a = a; in.b = b; in.pred = (uint8_t)pred;
        result = emit(f, blk, in);
        break;
    }
    case OP_FMA: {
        if (!parse_type(p, &ty)) return false;
        int a = parse_value(p, f, blk, ty);
        if (!eat_ch(p, ',')) return false;
        int b = parse_value(p, f, blk, ty);
        if (!eat_ch(p, ',')) return false;
        int cv = parse_value(p, f, blk, ty);
        Instr in = ins_make(OP_FMA, ty); in.a = a; in.b = b; in.c = cv;
        result = emit(f, blk, in);
        break;
    }
    case OP_SELECT: {
        if (!parse_type(p, &ty)) return false;
        int cd = parse_value(p, f, blk, ty_i1());
        if (!eat_ch(p, ',')) return false;
        int a = parse_value(p, f, blk, ty);
        if (!eat_ch(p, ',')) return false;
        int b = parse_value(p, f, blk, ty);
        Instr in = ins_make(OP_SELECT, ty); in.a = cd; in.b = a; in.c = b;
        result = emit(f, blk, in);
        break;
    }
    case OP_TRUNC: case OP_ZEXT: case OP_SEXT: case OP_FTRUNC: case OP_FEXT:
    case OP_FPTOSI: case OP_FPTOUI: case OP_SITOFP: case OP_UITOFP: case OP_BITCAST: case OP_FREEZE: {
        /* syntax: op <result-ty> <value> — source type from the value */
        if (!parse_type(p, &ty)) return false;
        skip_ws(p);
        /* need the value's own type: scan ahead for a name, else the
         * widest guess (i64/f64) from context is impossible — require
         * named values or typed literals for conversions */
        char nm[64];
        const char *sv = p->p;
        if (is_number_start(p)) {
            /* literal: interpret in the "natural" type: ints as the
             * result width won't do; use i64 for ints, f64 for reals */
            bool isfloat = false;
            const char *q = p->p;
            while (*q && (isdigit((uint8_t)*q) || *q == '-' || *q == '+' || *q == '.' || *q == 'e' || *q == 'E')) { if (*q == '.' || *q == 'e' || *q == 'E') isfloat = true; q++; }
            Type st2 = isfloat ? ty_f64() : ty_i64();
            int a = parse_value(p, f, blk, st2);
            Instr in = ins_make((uint8_t)op, ty); in.a = a;
            result = emit(f, blk, in);
            (void)nm; (void)sv;
        } else {
            if (!word(p, nm, sizeof nm)) { perr(p, "conversion operand"); return false; }
            int a = sym_find(p, nm);
            if (a < 0) { perr(p, "unknown value"); return false; }
            Instr in = ins_make((uint8_t)op, ty); in.a = a;
            result = emit(f, blk, in);
        }
        break;
    }
    case OP_LOAD: case OP_VLOAD: case OP_LOADV: {
        if (!parse_type(p, &ty)) return false;
        if (!eat_ch(p, ',')) { perr(p, "load ,"); return false; }
        int a = parse_value(p, f, blk, ty_ptr());
        Instr in = ins_make((uint8_t)op, ty); in.a = a;
        result = emit(f, blk, in);
        break;
    }
    case OP_STORE: case OP_VSTORE: case OP_STOREV: {
        if (!parse_type(p, &ty)) return false;
        int a = parse_value(p, f, blk, ty_ptr());
        if (!eat_ch(p, ',')) { perr(p, "store ,"); return false; }
        int b = parse_value(p, f, blk, ty);
        Instr in = ins_make((uint8_t)op, ty); in.a = a; in.b = b;
        emit(f, blk, in);
        result = -1;
        break;
    }
    case OP_GEP: {
        Type et;
        if (!parse_type(p, &et)) return false;
        int a = parse_value(p, f, blk, ty_ptr());
        if (!eat_ch(p, ',')) { perr(p, "gep ,"); return false; }
        int b = parse_value(p, f, blk, ty_i64());
        Instr in = ins_make(OP_GEP, ty_ptr()); in.a = a; in.b = b; in.ety = et;
        result = emit(f, blk, in);
        break;
    }
    case OP_ALLOCA: {
        int64_t sz = parse_int(p);
        int64_t al = 8;
        if (eat_ch(p, ',')) al = parse_int(p);
        Instr in = ins_make(OP_ALLOCA, ty_ptr()); in.imm = sz; in.c = (int32_t)al;
        result = emit(f, blk, in);
        break;
    }
    case OP_DATAPTR: {
        int64_t idx = parse_int(p);
        Instr in = ins_make(OP_DATAPTR, ty_ptr()); in.imm = idx;
        result = emit(f, blk, in);
        break;
    }
    case OP_CALL: {
        if (!parse_type(p, &ty)) return false;
        char nm[64];
        if (!word(p, nm, sizeof nm)) return false;
        bool ext = false; int ci = mod_find_func(p->m, nm);
        if (ci < 0) { ci = mod_find_extern(p->m, nm); ext = true; }
        if (ci < 0) { perr(p, "unknown callee"); return false; }
        const Type *ps; int np;
        if (ext) { ps = p->m->exts[ci].params; np = p->m->exts[ci].nparams; }
        else { ps = p->fsig_params[ci]; np = p->fsig_nparams[ci]; }
        if (!eat_ch(p, '(')) { perr(p, "call ("); return false; }
        int32_t *args = NULL; int n = 0;
        skip_ws(p);
        if (*p->p != ')') {
            for (;;) {
                int v = parse_value(p, f, blk, ps[n < np ? n : 0]);
                args = realloc(args, sizeof(int32_t) * (size_t)(n + 1));
                args[n++] = (int32_t)v;
                if (!eat_ch(p, ',')) break;
            }
        }
        if (!eat_ch(p, ')')) { perr(p, "call )"); return false; }
        result = emit(f, blk, ins_call(ty, ci, ext, args, n, false));
        break;
    }
    case OP_MEMCPY: case OP_MEMSET: {
        int a = parse_value(p, f, blk, ty_ptr());
        if (!eat_ch(p, ',')) return false;
        int b = parse_value(p, f, blk, op == OP_MEMCPY ? ty_ptr() : ty_i32());
        if (!eat_ch(p, ',')) return false;
        int cv = parse_value(p, f, blk, ty_i64());
        Instr in = ins_make((uint8_t)op, ty_void()); in.a = a; in.b = b; in.c = cv;
        emit(f, blk, in);
        result = -1;
        break;
    }
    case OP_ALOAD: case OP_AADD: case OP_AXCHG: case OP_ASUB: case OP_AAND:
    case OP_AOR: case OP_AXOR: case OP_AMINS: case OP_AMAXS: case OP_AMINU:
    case OP_AMAXU: case OP_ACMPXCHG: {
        if (!parse_type(p, &ty)) return false;
        int a = parse_value(p, f, blk, ty_ptr());
        Instr in = ins_make((uint8_t)op, ty); in.a = a; in.aux = (uint8_t)parse_order(p, w);
        if (op != OP_ALOAD) {
            if (!eat_ch(p, ',')) return false;
            in.b = parse_value(p, f, blk, ty);
        }
        if (op == OP_ACMPXCHG) {
            if (!eat_ch(p, ',')) return false;
            in.c = parse_value(p, f, blk, ty);
        }
        result = emit(f, blk, in);
        break;
    }
    case OP_ASTORE: {
        if (!parse_type(p, &ty)) return false;
        int a = parse_value(p, f, blk, ty_ptr());
        if (!eat_ch(p, ',')) return false;
        int b = parse_value(p, f, blk, ty);
        Instr in = ins_make(OP_ASTORE, ty); in.a = a; in.b = b; in.aux = (uint8_t)parse_order(p, w);
        emit(f, blk, in);
        result = -1;
        break;
    }
    case OP_FENCE: {
        Instr in = ins_make(OP_FENCE, ty_void()); in.aux = (uint8_t)parse_order(p, w);
        emit(f, blk, in);
        result = -1;
        break;
    }
    case OP_VEXTRACT: {
        if (!parse_type(p, &ty)) return false;
        skip_ws(p);
        char nm[64];
        if (!word(p, nm, sizeof nm)) return false;
        int a = sym_find(p, nm);
        if (!eat_ch(p, ',')) return false;
        int64_t lane = parse_int(p);
        Instr in = ins_make(OP_VEXTRACT, ty); in.a = a; in.imm = lane;
        result = emit(f, blk, in);
        break;
    }
    case OP_VINSERT: {
        if (!parse_type(p, &ty)) return false;
        skip_ws(p);
        char nm[64];
        if (!word(p, nm, sizeof nm)) return false;
        int a = sym_find(p, nm);
        if (!eat_ch(p, ',')) return false;
        int b = parse_value(p, f, blk, ty_elem(ty));
        if (!eat_ch(p, ',')) return false;
        int64_t lane = parse_int(p);
        Instr in = ins_make(OP_VINSERT, ty); in.a = a; in.b = b; in.imm = lane;
        result = emit(f, blk, in);
        break;
    }
    default:
        perr(p, "op not supported in surface syntax");
        return false;
    }
    if (resname[0]) {
        if (result < 0) { perr(p, "instruction has no result to bind"); return false; }
        sym_add(p, resname, result);
    }
    return !p->err[0];
}

/* ---- two-phase function parsing ----
 * Phase A creates every block of the function (with signatures) so
 * forward branch/call references resolve; phase B parses instructions.
 * A block header is the only text shape `ident ( ... ) :` — instruction
 * argument lists are never followed by a colon. */
static const char *raw_skip_ws(const char *q) {
    for (;;) {
        while (*q && isspace((uint8_t)*q)) q++;
        if (*q == ';' || *q == '#') { while (*q && *q != '\n') q++; continue; }
        break;
    }
    return q;
}
static const char *match_paren(const char *q) {   /* q at '(' */
    int d = 0;
    while (*q) {
        if (*q == ';' || *q == '#') { while (*q && *q != '\n') q++; continue; }
        if (*q == '(') d++;
        else if (*q == ')') { d--; if (!d) return q; }
        q++;
    }
    return NULL;
}
/* if q starts a block header, return the position just after its ':'
 * and (when lbl != NULL) the label; else NULL */
static const char *header_at(const char *q, char *lbl, size_t cap) {
    if (!(isalpha((uint8_t)*q) || *q == '_')) return NULL;
    const char *s = q;
    while (is_idc(*q)) q++;
    if (q == s) return NULL;
    const char *t = raw_skip_ws(q);
    if (*t != '(') return NULL;
    const char *close = match_paren(t);
    if (!close) return NULL;
    const char *u = raw_skip_ws(close + 1);
    if (*u != ':') return NULL;
    if (lbl) {
        size_t ln = (size_t)(q - s); if (ln >= cap) ln = cap - 1;
        memcpy(lbl, s, ln); lbl[ln] = 0;
    }
    return u + 1;
}
/* parse one block header at p->p (label already known to be there);
 * creates the block, records arg names in the arena */
static bool parse_block_header(P *p, Func *f, const char *lbl) {
    char w[64];
    if (!word(p, w, sizeof w) || strcmp(w, lbl) != 0) { perr(p, "block label"); return false; }
    if (!eat_ch(p, '(')) { perr(p, "block ("); return false; }
    Type atys[64]; char anames[64][64]; int na = 0;
    skip_ws(p);
    if (*p->p != ')') {
        for (;;) {
            if (na >= 64) { perr(p, "too many block args"); return false; }
            if (!word(p, anames[na], sizeof anames[na])) { perr(p, "arg name"); return false; }
            if (!eat_ch(p, ':')) { perr(p, "arg :"); return false; }
            if (!parse_type(p, &atys[na])) return false;
            na++;
            if (!eat_ch(p, ',')) break;
        }
    }
    if (!eat_ch(p, ')')) { perr(p, "block )"); return false; }
    if (!eat_ch(p, ':')) { perr(p, "block :"); return false; }
    int bidx = block_find(p, lbl);
    if (bidx < 0) {
        if (p->nblocks >= 256) { perr(p, "too many blocks"); return false; }
        bidx = p->nblocks;
        snprintf(p->blocks[p->nblocks].name, 64, "%s", lbl);
        p->blocks[p->nblocks].idx = bidx;
        p->nblocks++;
    }
    int blk = func_add_block(f, atys, na);
    if (blk != bidx) { perr(p, "block index mismatch"); return false; }
    p->bnargs[blk] = na;
    p->barg_off[blk] = p->argarena_len;
    for (int i = 0; i < na; i++) {
        snprintf(p->argarena + p->argarena_len, 64, "%.63s", anames[i]);
        p->argarena_len += 64;
    }
    return true;
}

static bool parse_fn_body(P *p, Func *f, const char *start, const char *end) {
    p->nsyms = 0; p->nblocks = 0; p->argarena_len = 0;
    /* phase A: create all blocks */
    const char *q = start;
    while (q < end) {
        q = raw_skip_ws(q);
        if (q >= end) break;
        char lbl[64];
        const char *after = header_at(q, lbl, sizeof lbl);
        if (after) {
            p->p = q;
            if (!parse_block_header(p, f, lbl)) return false;
            q = p->p;
        } else q++;
    }
    /* phase B: instructions */
    q = start;
    int curblk = -1, nexthdr = 0;
    while (q < end) {
        q = raw_skip_ws(q);
        if (q >= end) break;
        char lbl[64];
        const char *after = header_at(q, lbl, sizeof lbl);
        if (after && nexthdr < p->nblocks && strcmp(lbl, p->blocks[nexthdr].name) == 0) {
            curblk = nexthdr++;
            for (int i = 0; i < p->bnargs[curblk]; i++)
                sym_add(p, p->argarena + p->barg_off[curblk] + i * 64, f->blocks[curblk].arg_vals[i]);
            q = after;
            continue;
        }
        if (curblk < 0) { perr(p, "instruction before first block"); return false; }
        p->p = q;
        if (!parse_instr(p, f, curblk)) return false;
        q = p->p;
    }
    return !p->err[0];
}

/* parse "name (types) -> type {" and queue the body; "fn" consumed */
static bool parse_fn_header(P *p) {
    char name[64];
    if (!word(p, name, sizeof name)) { perr(p, "fn name"); return false; }
    if (!eat_ch(p, '(')) { perr(p, "fn ("); return false; }
    Type pts[16]; int npt = 0;
    skip_ws(p);
    if (*p->p != ')') {
        for (;;) {
            Type t;
            if (!parse_type(p, &t)) return false;
            if (npt < 16) pts[npt++] = t;
            if (!eat_ch(p, ',')) break;
        }
    }
    if (!eat_ch(p, ')')) { perr(p, "fn )"); return false; }
    Type rt = ty_void();
    if (eat(p, "->")) { if (!parse_type(p, &rt)) return false; }
    if (!eat_ch(p, '{')) { perr(p, "fn {"); return false; }
    Func *f = mod_add_func(p->m, name, rt, 0);
    int fi = p->m->nfuncs - 1;
    (void)f;
    if (fi < 1024) {
        p->fsig_nparams[fi] = npt;
        for (int i = 0; i < npt; i++) p->fsig_params[fi][i] = pts[i];
    }
    /* body span: to the matching close brace */
    const char *start = p->p;
    const char *q = start;
    int depth = 1;
    while (*q && depth > 0) {
        if (*q == ';' || *q == '#') { while (*q && *q != '\n') q++; continue; }
        if (*q == '{') depth++;
        else if (*q == '}') depth--;
        q++;
    }
    if (depth != 0) { perr(p, "unterminated fn body"); return false; }
    if (p->nbodies >= 1024) { perr(p, "too many functions"); return false; }
    p->bodies[p->nbodies].fi = fi;
    p->bodies[p->nbodies].start = start;
    p->bodies[p->nbodies].end = q - 1;   /* the matching '}' */
    p->nbodies++;
    p->p = q;
    return true;
}

Module *surface_parse(const char *text, char *err, size_t errcap) {
    P *p = calloc(1, sizeof(P));
    if (!p) { if (err && errcap) snprintf(err, errcap, "surface: out of memory"); return NULL; }
    p->p = text;
    p->m = mod_new();
    for (;;) {
        skip_ws(p);
        if (!*p->p) break;
        if (eat(p, "fn")) { if (!parse_fn_header(p)) goto fail; }
        else if (eat(p, "data")) {
            char name[64];
            if (!word(p, name, sizeof name)) { perr(p, "data name"); goto fail; }
            if (!eat_ch(p, ':')) { perr(p, "data :"); goto fail; }
            Type et;
            if (!parse_type(p, &et)) goto fail;
            if (eat_ch(p, '[')) { (void)parse_int(p); if (!eat_ch(p, ']')) { perr(p, "data ]"); goto fail; } }
            if (!eat_ch(p, '=')) { perr(p, "data ="); goto fail; }
            if (!eat_ch(p, '{')) { perr(p, "data {"); goto fail; }
            uint8_t *bytes = NULL; size_t nb = 0;
            int esz = ty_bytes(et);
            skip_ws(p);
            if (*p->p != '}') {
                for (;;) {
                    int64_t v = parse_int(p);
                    bytes = realloc(bytes, nb + (size_t)esz);
                    for (int i = 0; i < esz; i++) bytes[nb + (size_t)i] = (uint8_t)(v >> (8 * i));
                    nb += (size_t)esz;
                    if (!eat_ch(p, ',')) break;
                }
            }
            if (!eat_ch(p, '}')) { perr(p, "data }"); goto fail; }
            mod_add_data(p->m, name, (uint32_t)esz, bytes, (uint32_t)nb);
            free(bytes);
        }
        else if (eat(p, "extern")) {
            char name[64];
            if (!word(p, name, sizeof name)) { perr(p, "extern name"); goto fail; }
            if (!eat_ch(p, '(')) { perr(p, "extern ("); goto fail; }
            Type pt[16]; int np = 0;
            skip_ws(p);
            if (*p->p != ')') {
                for (;;) {
                    if (!parse_type(p, &pt[np])) goto fail;
                    np++;
                    if (!eat_ch(p, ',')) break;
                }
            }
            if (!eat_ch(p, ')')) { perr(p, "extern )"); goto fail; }
            Type rt = ty_void();
            if (eat(p, "->")) { if (!parse_type(p, &rt)) goto fail; }
            mod_add_extern(p->m, name, pt, np, rt);
        }
        else { perr(p, "expected fn/data/extern"); goto fail; }
        if (p->err[0]) goto fail;
    }
    /* pass 2: function bodies (all shells, data, externs exist now) */
    for (int i = 0; i < p->nbodies; i++) {
        Func *f = &p->m->funcs[p->bodies[i].fi];
        if (!parse_fn_body(p, f, p->bodies[i].start, p->bodies[i].end)) goto fail;
    }
    {
        Module *m = p->m;
        free(p);
        return m;
    }
fail:
    if (err && errcap) snprintf(err, errcap, "%s", p->err[0] ? p->err : "surface: parse error");
    mod_free(p->m);
    free(p);
    return NULL;
}
