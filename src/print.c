/* Krell-IR — text dump (debug output only; nothing parses this). */
#include "krell.h"

static const char *ICP[10] = { "eq","ne","ult","ule","ugt","uge","slt","sle","sgt","sge" };
static const char *FCP[14] = { "oeq","one","olt","ole","ogt","oge","ueq","une","ult","ule","ugt","uge","ord","uno" };

void ty_dump(Type t, FILE *out) {
    switch (t.kind) {
    case TY_VOID: fputs("void", out); break;
    case TY_INT: fprintf(out, "i%d", t.bits); break;
    case TY_FLOAT: fprintf(out, "f%d", t.bits); break;
    case TY_PTR: fputs("ptr", out); break;
    case TY_VEC: {
        Type e = ty_elem(t);
        fprintf(out, "vec<vscale x %d x ", t.n);
        ty_dump(e, out);
        fputc('>', out);
        break;
    }
    default: fputs("?", out); break;
    }
}

static void val_list(FILE *out, const int32_t *a, int n) {
    for (int i = 0; i < n; i++) fprintf(out, "%s%%%d", i ? ", " : "", a[i]);
}

static void ins_dump(Func *f, Instr *in, FILE *out) {
    (void)f;
    if (in->result >= 0) {
        fprintf(out, "%%%d: ", in->result);
        ty_dump(in->ty, out);
        fputs(" = ", out);
    }
    int op = in->op;
    fputs(op_name(op), out);
    switch (op) {
    case OP_ICONST: fprintf(out, " %lld", (long long)in->imm); break;
    case OP_FCONST: fprintf(out, " 0x%llx", (unsigned long long)in->imm); break;
    case OP_ICMP: fprintf(out, ".%s %%%d, %%%d", ICP[in->pred], in->a, in->b); break;
    case OP_FCMP: fprintf(out, ".%s %%%d, %%%d", FCP[in->pred], in->a, in->b); break;
    case OP_BR:
        fprintf(out, " b%d(", in->blk); val_list(out, in->args, in->nargs); fputc(')', out);
        break;
    case OP_CONDBR:
        fprintf(out, " %%%d, b%d(", in->a, in->blk); val_list(out, in->args, in->nargs);
        fprintf(out, "), b%d(", in->blk2); val_list(out, in->args2, in->nargs2); fputc(')', out);
        break;
    case OP_RET:
        if (in->a >= 0) fprintf(out, " %%%d", in->a);
        break;
    case OP_CALL: case OP_TAILCALL:
        fprintf(out, " %s%d(", in->callee_extern ? "@" : "fn", in->callee);
        val_list(out, in->args, in->nargs); fputc(')', out);
        break;
    case OP_ALLOCA: fprintf(out, " %lld, align %d", (long long)in->imm, in->c); break;
    case OP_DATAPTR: fprintf(out, " data%d", (int)in->imm); break;
    case OP_GEP:
        fprintf(out, " %%%d, %%%d, ", in->a, in->b); ty_dump(in->ety, out);
        break;
    case OP_VEXTRACT: fprintf(out, " %%%d, %lld", in->a, (long long)in->imm); break;
    case OP_VINSERT: fprintf(out, " %%%d, %%%d, %lld", in->a, in->b, (long long)in->imm); break;
    case OP_ALOAD: case OP_ASTORE: case OP_AADD:
        fprintf(out, ".%d %%%d", in->aux, in->a);
        if (in->b >= 0) fprintf(out, ", %%%d", in->b);
        break;
    case OP_SELECT: fprintf(out, " %%%d, %%%d, %%%d", in->a, in->b, in->c); break;
    default:
        if (in->a >= 0) fprintf(out, " %%%d", in->a);
        if (in->b >= 0) fprintf(out, ", %%%d", in->b);
        if (in->c >= 0) fprintf(out, ", %%%d", in->c);
        break;
    }
    fputc('\n', out);
}

void mod_dump(Module *m, FILE *out) {
    for (int i = 0; i < m->nexts; i++) {
        Extern *e = &m->exts[i];
        fprintf(out, "extern @%s(", e->name);
        for (int j = 0; j < e->nparams; j++) { if (j) fputs(", ", out); ty_dump(e->params[j], out); }
        fputs(") -> ", out); ty_dump(e->ret, out); fputc('\n', out);
    }
    for (int i = 0; i < m->ndata; i++)
        fprintf(out, "data %s align %u len %u\n", m->data[i].name, m->data[i].align, m->data[i].len);
    for (int i = 0; i < m->nfuncs; i++) {
        Func *f = &m->funcs[i];
        fprintf(out, "fn %s(", f->name);
        Block *b0 = &f->blocks[0];
        for (int j = 0; j < b0->nargs; j++) {
            if (j) fputs(", ", out);
            fprintf(out, "%%%d: ", b0->arg_vals[j]); ty_dump(b0->arg_types[j], out);
        }
        fputs(") -> ", out); ty_dump(f->ret, out);
        if (f->flags & FUNC_PURE) fputs(" pure", out);
        fputs(":\n", out);
        for (int j = 0; j < f->nblocks; j++) {
            Block *b = &f->blocks[j];
            fprintf(out, "  b%d(", j);
            for (int k = 0; k < b->nargs; k++) {
                if (k) fputs(", ", out);
                fprintf(out, "%%%d: ", b->arg_vals[k]); ty_dump(b->arg_types[k], out);
            }
            fputs("):\n", out);
            for (int k = 0; k < b->nins; k++) {
                fputs("    ", out);
                ins_dump(f, &b->ins[k], out);
            }
        }
    }
}
