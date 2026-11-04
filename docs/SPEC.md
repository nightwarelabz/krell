# Krell — IR Specification

Companion to `SEMANTICS.md` (which defines what programs mean; this defines
what modules are). Version 1.

## 1. Module structure

A module contains:

- **externs**: named declarations (name, parameter types, return type) for
  functions provided by the host (typically C ABI functions). The backend
  owns all ABI details; an extern is just a signature.
- **functions**: named definitions. Each has parameter types, a return type,
  and a list of blocks. The first block is the entry; its arguments are the
  function's parameters.
- **data**: named constant byte blobs with an alignment; their addresses are
  taken with the `dataptr` op. (Used for lookup tables and test vectors.)

## 2. Functions, blocks, values

- A function is a list of blocks. Each block has: typed arguments, a list of
  instructions, one terminator.
- Every block argument and every instruction result is a **value**, numbered
  densely per function in definition order (block arguments first, block by
  block). Values are SSA: defined once, and every use is dominated by its
  definition (the verifier checks this).
- Instructions are numbered by their result value where they have one.
  Instructions without results (stores, branches) still occupy an index in
  the block's instruction list but produce no value.

## 3. Opcode menu (v1)

Notation: `iN` any integer type, `fv` f32/f64, `v` a vector of the operand's
element type. Unless noted, integer ops are width-polymorphic over iN.

Constants and identity:
`iconst` (i64 immediate, truncated to type), `fconst` (IEEE bit pattern),
`freeze` (identity, see semantics).

Integer: `add sub mul udiv sdiv urem srem neg and or xor not shl lshr ashr`
`icmp.<pred>` (pred in eq ne ult ule ugt uge slt sle sgt sge)
`popcount clz ctz bswap` (bswap: i16/i32/i64)
`fshl fshr` (funnel shifts: three operands — high part, low part, shift
amount; i8/i16/i32/i64)
`trunc zext sext`

Float: `fadd fsub fmul fdiv fneg fabs fma`
`fcmp.<pred>` (pred in oeq one olt ole ogt oge ueq une ult ule ugt uge ord uno)
`ftrunc fext fptosi fptoui sitofp uitofp`
`bitcast` (any equal-sized pair)

Memory: `alloca` (immediate size, align), `load`, `store`, `gep`
(base, index, element type), `memcpy`, `memset`, `dataptr` (data index).

Vectors (lane-wise, element type = the vector's):
`vsplat`, `vadd vsub vmul vudiv vfadd vfsub vfmul vfdiv`,
`vand vor vxor`, `vload`, `vstore`,
`vextract` (immediate lane), `vinsert` (immediate lane).

Atomics: `aload astore aadd` (immediate ordering: 0 relaxed, 1 acqrel,
2 seqcst).

Control: `br` (block + args), `condbr` (cond, block+args, block+args),
`ret` (value or void), `call` (function/extern index + args),
`tailcall` (same, terminator), `select`, `assume` (i1).

Total: ~70 opcodes. Anything not on this menu does not exist; per-target
intrinsics are a future extension behind explicit gates, never silent
additions.

## 4. Types encoding

A type is (kind, a, b): kinds are VOID, INT (a = bits), FLOAT (a = 32|64),
PTR, VEC (a = element type index in the function's local type list encoded
inline as (elem kind/bits), b = n, the vscale multiplier count).

In the binary format, types are encoded per-use (they are tiny); there is no
global type table in v1.

## 5. Binary format

All integers are LEB128 (unsigned unless noted SLEB128). Layout:

```
magic   : 'K' 'R' 'E' 'L'
version : u16 = 1
sections: repeated { u8 id, uleb length, bytes }
  1 STRINGS : uleb count, then count × { uleb len, bytes }   (names)
  2 EXTERNS : uleb count, then per extern:
              uleb name_idx, uleb nparams, params (type each), rettype
  3 DATA    : uleb count, then per blob:
              uleb name_idx, uleb align, uleb len, bytes
  4 FUNCS   : uleb count, then per function:
              uleb name_idx, uleb nparams, param types, rettype,
              uleb nblocks, then per block:
                uleb nargs, then per arg: uleb value id, type,
                uleb ninstrs, then instructions:
                  u8 opcode, uleb result id (0 = none, else id+1),
                  result type, operands as the op's signature requires
                  (value ids uleb; immediates sleb/uleb/f32/f64 bits;
                   branch targets: block index uleb + arg value ids)
              Value ids are explicit in the format: a decoder never
              renumbers, so any producer's numbering survives transport.
              terminators are instructions like any other (they end a block)
flags   : a function may carry flag PURE (no memory writes, no calls to
          impure functions) — a producer promise (see SEMANTICS §5).
```

Properties the format is designed for: single-pass streaming decode
(sections in order, functions self-delimiting), dense IDs everywhere (no
names in code, only indices), and a canonical form — two encodes of the same
module are byte-identical, so a module's SHA-256 is a meaningful identity
(used for caching and for superoptimizer rule keys).

## 6. Cost oracle format

One text file per target (`targets/<target>.cost`), parsed by the toolchain:

```
target x86_64
vl 4            # vector-length unit: lanes of i32 per vscale step (128-bit)
op add.i32   lat 1 thr 1 ports 4
op udiv.i32  lat 26 thr 10 ports 1 cliff 0
op vgather   lat - thr - ports - cliff 1   # (example shape only; not an op)
fn fptosi.sat cost 4    # specified fixup sequences and their price
```

`cliff 1` marks operations whose cost on this target is an order of
magnitude off the portable class. Core ops (§3) must have `cliff 0` on every
shipping target — the verifier's target gate enforces this: a module using
an op that is cliff-flagged (or absent) on the requested target is rejected
for that target. This is the no-silent-emulation rule made mechanical.

## 7. The text dump (debug only)

A generated, non-canonical rendering for humans debugging the toolchain:

```
fn fill32(ptr %dst, i64 %n, i32 %val) -> void:
  b0(%dst: ptr, %n: i64, %val: i32):
    %3:i64 = iconst 0
    br b1(%3)
  b1(%i: i64):
    %5:i1 = icmp.ult %i, %n
    condbr %5, b2(%i), b3()
  ...
```

It is output-only. Nothing parses it. (Phase 6's human surface syntax is a
separate, deliberately different language that compiles to this IR through
the builder API.)

## 8. Variadic consumers (v3)

Krell has no variadic functions and no varargs call operation: the
call rule stays exact, with argument count and types checked against
a fixed signature. A producer that needs printk-style variadic
behavior passes an **explicit variadic descriptor** instead: a
fixed-signature function takes, as an ordinary final argument, a
pointer to a caller-built argument block. Producers build the block
with alloca and stores; consumers read it with loads. The layout is
a data convention, not an IR feature:

```
offset 0:  u64 nslots
offset 8:  u64 reserved (0)
then nslots slots, 16 bytes each:
  +0: u64 tag      (0=i64, 1=i32, 2=i1/other small int (in low bits),
                    3=f64, 4=f32 (bits in low 32), 5=ptr,
                    6=string (ptr to bytes) + length in value's high 32)
  +8: u64 value    (bit pattern of the argument, zero/sign-extended
                    per the tag's usual rules)
```

A variadic consumer is an ordinary function, e.g.
`klog(fmt: ptr, args: ptr) -> i64`. Its signature is fixed, so it
can be called directly, indirectly (the signature-table entry is
just `(ptr, ptr) -> i64`), and tail-called, with the verifier
checking every call.

Extern calls on x86_64 set AL to the number of FP registers used by
the fixed signature, as the System V ABI requires for variadic
callees; non-variadic callees ignore AL, so the value is set
unconditionally. The native backends emit the store directly; the
LLVM lane emits extern and indirect calls with a variadic function
type whose fixed prefix matches the signature, which makes LLVM
set AL identically.
