# Krell — Semantics

The whole semantics of Krell-IR, on purpose short enough to reimplement from.
This document is normative. The reference interpreter (`src/interp.c`) is the
same semantics made executable; where the two ever disagree, this document
wins and the interpreter has a bug.

## 1. Design stance

- **Everything is defined.** There is no undefined behavior and no poison.
  Every operation produces a specified value for every input. Optimizers may
  only rewrite programs in ways that preserve these values exactly.
- **Determinism.** A module executed twice with the same inputs produces the
  same outputs, on every target, bit for bit. The two documented exceptions
  are NaN payloads (§6) and the contents of uninitialized memory (§4) — both
  are specified narrowly enough that conforming test suites can avoid them.
- **SMT-encodability.** Every operation's semantics is a total function
  expressible in the theory of bitvectors + IEEE floats. There are no
  operations whose meaning depends on optimizer state.

## 2. Values and types

Types: `void`, `iN` for N in {1, 8, 16, 32, 64}, `f32`, `f64`, `ptr`, and
`vec<vscale × n × T>` for n in {1, 2, 4, 8, 16} and T any scalar type.

- An `iN` value is an N-bit two's-complement bit pattern. Signedness is a
  property of operations, never of values.
- A `ptr` is a 64-bit address into the single address space (§4).
- A `vec` value is a sequence of lanes. The lane count is `n × VL`, where
  `VL` (the target's vector length in elements for the element type) is a
  property of the execution target, fixed for any one execution. All vector
  operations are lane-wise; lane i of a result depends only on lane i of the
  inputs. Programs that do not inspect the lane count compute the same scalars
  on every target.
- `i1` is a single bit; when stored to memory it occupies one byte, 0 or 1.

## 3. Integer and bit operations

- `add, sub, mul, neg`: arithmetic modulo 2^N. Overflow wraps.
- `udiv, sdiv, urem, srem`: division truncates toward zero; the remainder
  takes the dividend's sign. **Division by zero yields 0** (for both div and
  rem). `sdiv`/`srem` of INT_MIN by -1 yields INT_MIN / 0 respectively
  (the mathematical result wraps). These definitions exist so that division
  needs no traps, no branches, and no special cases on any target; backends
  insert the zero-check or use the target's equivalent sequence.
- `and, or, xor, not`: bitwise.
- `shl, lshr, ashr`: the shift amount is taken modulo N (the bit width).
  `lshr` zero-fills, `ashr` sign-fills.
- `fshl a b s`, `fshr a b s`: funnel shifts over the 2N-bit concatenation
  of `a` (the high part) and `b` (the low part). The shift amount is
  taken modulo N. `fshl` yields the N bits of `(a:b) << s` that end in
  the high half — `(a << s) | (b >> (N - s))`, and exactly `a` when
  `s mod N = 0`. `fshr` yields the low N bits of `(a:b) >> s` —
  `(a << (N - s)) | (b >> s)`, and exactly `b` when `s mod N = 0`.
  `fshl x x s` is a rotate-left of `x` by `s`; `fshr x x s` is a
  rotate-right.
- `icmp p a b`: compares as unsigned (`u*` predicates) or signed (`s*`).
  Result is `i1`.
- `popcount, clz, ctz`: count over the N-bit pattern. `clz`/`ctz` of 0 yield N.
- `bswap`: byte reversal within the N-bit pattern (N in {16, 32, 64}).
- `trunc, zext, sext`: width changes — drop high bits, zero-fill, sign-fill.
- `select c a b`: yields `a` if c = 1 else `b`. Both operands are values;
  there is no poison to propagate, so select is trivially total.
- `freeze x`: yields `x`. It exists so future refinements of the semantics
  (and machine producers that reason about undef-like values) have a defined
  place to stand; in this version it is the identity.

## 4. Memory

- One byte-addressed address space, **little-endian** on all v1 targets.
  Addresses are 64-bit. Address 0 is a valid address as far as the IR is
  concerned; whether it is mapped is the host program's business (the IR has
  no traps).
- `load T, ptr` / `store T, val, ptr`: move the byte representation of T
  (N/8 bytes for iN, 4/8 for floats, 8 for ptr, lane-major for vectors).
  Unaligned accesses are permitted and have their obvious byte meaning;
  targets where they are slow charge them in the cost oracle.
- Reading memory that was never written yields **unspecified bytes** — some
  fixed value per execution, not a trap and not observable nondeterminism
  within a single execution beyond its arbitrariness. Conforming programs
  (and all test kernels) do not depend on unwritten bytes.
- `alloca size, align`: reserves `size` bytes of stack storage for the
  caller's frame, returning a pointer with the requested alignment. Storage
  is released when the function returns and its bytes are unwritten.
- `gep ptr, idx, T`: yields `ptr + idx × sizeof(T)` computed modulo 2^64.
  It is address arithmetic only; it never traps and implies nothing about
  validity.
- `memcpy dst, src, n` / `memset dst, byte, n`: byte operations. Overlapping
  `memcpy` regions behave as if copied through a temporary buffer (memmove
  semantics), so the result is order-independent.
- `assume c`: a producer's claim that c = 1 whenever control reaches it.
  Executing `assume` with c = 0 is a contract breach by the producer, not a
  trap: the interpreter ignores `assume`, and backends may treat a breached
  assume as permission to have emitted anything — the only non-total corner
  of the semantics, deliberately fenced to this one op, and never emitted by
  the toolchain's own producers.
  The optimizer uses `assume` block-locally: within the remainder of the
  block that contains it, a select or branch whose condition the assertion
  decides — the asserted value itself, its negation, or a comparison of
  the same value against the same constant with the same or the
  complementary predicate — resolves statically, as does a later
  comparison the assertion pins. Facts never cross block boundaries.
  This is the sanctioned way for a producer contract (for example "this
  count is nonzero in this loop") to remove the defensive select that a
  total-semantics op would otherwise force on a hot path.

## 5. Control and calls

- A function is a list of blocks. Each block takes typed **arguments**
  (its only inputs besides memory), contains instructions, and ends with
  exactly one terminator: `br`, `condbr`, `ret`, or it falls off via a
  `tailcall` used as terminator.
- `br target(args...)`: transfers control, binding the target block's
  arguments to the given values. `condbr c, t(args...), f(args...)` selects
  by c. Loop structure is expressed, as in assembly, with backward branches.
- `call f(args...)` / extern calls: arguments and results follow §7. A call
  may read and write any memory (unless the callee is declared `pure`, a
  producer promise with the same standing as `assume`).
- `tailcall f(args...)`: like call, but the caller's frame is released
  before the callee begins; it must be the block terminator and its result
  is the function's result. **Guaranteed**: backends must implement it as a
  jump, never a nested call.
- There are no exceptions, no signals, and no unwinding in the IR. Hosts that
  need them keep them outside.

## 6. Floating point

- IEEE 754 binary32/binary64 arithmetic: `fadd, fsub, fmul, fdiv, fneg,
  fabs, fma` (fused, single rounding), comparisons `fcmp` with the usual
  ordered/unordered predicates.
- `fma` is a distinct operation; backends must not contract separate
  `fmul`+`fadd` into it, nor split it — what is written is what rounds.
- NaN: operations produce *a* quiet NaN; the payload is target-defined.
  Programs requiring bit-identical floats across targets must not let NaNs
  reach observable outputs (all test kernels comply). Infinities and
  denormals follow IEEE on all v1 targets (no flush-to-zero anywhere).
- Conversions: `sitofp/uitofp` round to nearest, ties to even.
  `fptosi/fptoui` **saturate**: out-of-range values clamp to the target
  type's min/max; NaN converts to 0. (Backends on targets whose native
  conversion does not saturate emit the fixup sequence; the cost oracle
  records it.)
- `bitcast` reinterprets bit patterns between equal-sized types.

## 7. Calling convention (owned by the backend)

Producers never see a register. The convention is a property of each backend,
stated here in its portable part:

- Scalar arguments are passed in the target's argument registers in order —
  integer/pointer and floating arguments draw from their separate register
  files — with overflow arguments on the stack; one scalar result returns in
  the first register of its file. v1 supports scalar arguments and results
  only; aggregates travel by pointer.
- The *internal* convention and the *extern* (C ABI) convention coincide on
  scalars in v1; they differ only in that `tailcall` is guaranteed for
  internal calls. Frontends reimplement nothing: the ABI lives entirely in
  the backend (the lesson bought expensively by LLVM's frontend ecosystem
  and cheaply by QBE).

## 8. Atomics

- `aload, astore, aadd` on integer types with an ordering in
  {seqcst, acqrel, relaxed}. v1 backends implement all three with the
  target's strongest simple sequence (seqcst fences); the ordering is
  recorded in the IR so later backends may relax. Atomic operations on the
  same address are coherent; the IR's concurrency model is sequential
  consistency for data-race-free programs, and data races are the
  producer's problem, not the IR's.

## 9. What a backend must guarantee

1. Bit-identical results with the interpreter for every program that does
   not observe unwritten memory or NaN payloads.
2. `tailcall` as a jump.
3. No silent emulation: an operation the target cannot lower efficiently is
   a verifier error for that target, not a library call smuggled in. (The
   library-call sequences the semantics themselves prescribe — division by
   zero handling, saturating float conversion — are specified here, priced
   in the cost oracle, and are the only exceptions.)
