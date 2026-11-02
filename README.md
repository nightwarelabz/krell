<p align="center">
  <img src="brand/krell-mark-1280x640-transparent.png" alt="Krell mark" width="640">
</p>

# Krell

**A machine-facing portable assembly.** Krell is a program representation
that sits between assembly and C: the raw power and speed of assembly,
with the portability of C — designed from the start for machines, not
humans, to produce and consume. Producers are compilers, superoptimizers,
and automated agents; the format, semantics, and tooling are all shaped
for them.

```text
one program, written once  ──►  Krell-IR (binary, hashed, verified)
                                   ├── x86_64   native backend
                                   ├── AArch64  native backend
                                   ├── RISC-V   native backend (RV64)
                                   └── LLVM IR  lowering lane (release)
```

https://github.com/user-attachments/assets/fdf0ceef-8e54-44ec-a440-a470060f964a

*Every frame of this film was computed by a single Krell program.*

## Design

- **Typed SSA with block arguments** — infinite virtual registers,
  explicit blocks, no phi nodes; the form four independent IR designs
  converged on, because it is the one that works.
- **Total semantics** — every operation is defined for every input.
  Division by zero is 0, `INT_MIN / -1` wraps, shifts mask their amount,
  float→int conversions saturate and map NaN to 0. There is no undefined
  behavior and no poison, so translation validation stays decidable and
  the specification (`docs/SEMANTICS.md`) is small enough to encode.
- **Backend-owned ABI** — backends own register allocation, instruction
  selection, and the C calling convention for their target; producers
  never reimplement an ABI.
- **Curated op set** — the instruction set is the intersection of
  operations that are efficient on every target, plus predicated
  escape hatches where the intersection is empty.
- **A shipped cost oracle** — every target carries a machine-readable
  cost table (`targets/*.cost`: latency, throughput, and *cliff* flags
  for operations with no reasonable implementation). The verifier
  rejects modules that use cliff operations for a target, and the
  optimizer prices its rewrites from the same tables.
- **Machine-first binary encoding** — canonical, hash-consed, and
  content-addressed: a module's SHA-256 over its canonical encoding is
  its identity. Round-trips are byte-identical by construction.
- **A reference interpreter** — the semantics document made executable;
  every backend is differentially tested against it.

## Layout

```text
src/        the toolchain (C11, no dependencies beyond libc/libm)
  krell.h     public API: IR, builder, binary format, verifier,
              cost oracle, interpreter, optimizer, backends
  ir.c        IR core: builder, hash-consing, constant folding
  binary.c    canonical binary encoding + SHA-256 module identity
  verify.c    structural/type/dominance verifier + target gate
  cost.c      per-target cost oracle
  interp.c    reference interpreter
  opt.c       optimizer (rewrites, magic-number division, DCE)
  surface.c   human surface syntax (debugging/authoring aid)
  be.c        shared backend kit: liveness, linear-scan allocation
  be_x86.c    x86_64 backend (System V)
  be_arm64.c  AArch64 backend (AAPCS64, ARMv8.1 baseline)
  be_rv64.c   RISC-V RV64 backend (lp64d, RV64GC + Zbb, scalarized vectors)
  be_llvm.c   LLVM IR lowering lane
  main.c      the krellc driver
targets/      cost oracle tables (x86_64, aarch64, riscv64)
tests/        kernel suite, differential battery, fuzz harness
tools/        fragment superoptimizer, random-module fuzzer
docs/         SEMANTICS.md (normative), SPEC.md (formats)
brand/        the Krell mark
```

## Build

```sh
make            # libkrell.a + krellc
make tests      # kernel suite + binary round-trip gate
```

## Use

```sh
krellc parse  prog.txt -o prog.krel        # surface syntax -> binary
krellc verify prog.krel --target riscv64   # verify + target gate
krellc run    prog.krel sumsq 100          # interpret: 338350
krellc build  prog.krel --target x86_64 -o prog.s
krellc build  prog.krel --target llvm -O -o prog.ll
krellc opt    prog.krel -o prog.opt.krel   # optimize
krellc hash   prog.krel                    # canonical module identity
```

Differential gates (battery of ~4,500 recorded cases per backend,
plus a random-module fuzzer) run from `tests/`:

```sh
tests/run_backend.sh x86     # also: arm, rv, llvm
tests/run_fuzz.sh x86 12345 opt
```

## Performance shape

Two lane classes, on purpose. The native backends are deliberately
simple — correctness and portability first; on the acceptance kernels
(CASM's `ps15_fill32` and a texture span kernel, expressed once in
Krell-IR) they land within a small multiple of `cc -O0`. The LLVM
lowering lane is the release lane: the same kernels through it match
or beat `cc -O2` (fill32 ≈ 3× faster than the C reference at -O2 on
the test host; span at parity), because LLVM does the register
allocation and vectorization. Write once; pick the lane per target.

## License

Apache-2.0 (see `LICENSE` and `NOTICE`).

**Toolchain output carries no obligations.** Programs encoded in Krell
form, and code produced by compiling them with this toolchain, are
outputs of the toolchain. The Apache-2.0 license of the toolchain
itself imposes no license obligations on those outputs: you may use,
modify, and distribute Krell-encoded programs and their compiled forms
under any terms you choose.
