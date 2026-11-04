# SYNCHRONY

A film only possible with Krell.

Four Lorenz systems start from the same point, offset in x by 0,
1e-9, 2e-9 and 3e-9 — less than one part in a billion. Chaos
amplifies the offsets until four separate butterflies fill the
frame. One Krell program computes every frame; a second program
integrates the same equations to synthesize the score.

The finished film interleaves four compiled backends of the same
program — frame 0 from x86_64, frame 1 from AArch64, frame 2 from
RISC-V 64, frame 3 from the LLVM lane, repeating. A chaotic
system is the most sensitive divergence detector there is: any
single-bit difference between backends grows exponentially, and
the sampled frames of the shipped film reproduce byte-identically
on all four backends (sha256 of the raw frames).

## The programs

- `synchrony.krell` — video. One PPM (P6) frame on stdout.
  Args: `[frame] [total] [size]`, defaults `0 1728 960`.
- `synchrony-audio.krell` — score. Raw PCM on stdout:
  44100 Hz, mono, signed 16-bit little endian, 72 s.

## The mathematics

The Lorenz equations at σ = 10, ρ = 28, β = 8/3, four copies
from (1, 1, 20) with the x-offsets above. With Lyapunov exponent
λ ≈ 0.9 per time unit a separation grows as δ₀e^(λt): one pixel
at ≈ 20 time units, full separation at ≈ 23. The film runs
10,000 settle steps (8.0 time units), then spans 22.1184 time
units — one white butterfly separating into four coloured ones.

Integration is classical RK4 at h = 0.0008 (audio: h = 6.966e-6,
one step per sample). Every frame is recomputed from the
initial condition; no state crosses frames. Each frame draws
the trailing 3,400 steps as additive light in f64 RGB buffers,
three sub-stamps per step, tone-mapped by g = 0.22v/(1 + 0.22v).

The bits agree on four machines because every floating-point
operation is IEEE-754 binary64 +, −, × or ÷ — correctly rounded,
so each result is a function of its operands alone. There is no
fused multiply-add, no host libm (sine and cosine are Taylor
polynomials evaluated inside the programs), and one fixed order
of operations.

In the score, each system's height z sets a drone pitch
(55 + 1.1z Hz, 82.5 + 1.65z Hz), and a bell with an inharmonic
partial at 2.756× is struck whenever the first system changes
wing (x crosses zero).

## Build and run

```
krellc parse synchrony.krell -o synchrony.krel
krellc build synchrony.krel --target x86_64  -o synchrony.s
krellc build synchrony.krel --target aarch64 -o synchrony-arm.s
krellc build synchrony.krel --target riscv64 -o synchrony-rv.s
krellc build synchrony.krel --target llvm    -o synchrony.ll

cc synchrony.s -o synchrony-x86 -lm
aarch64-linux-gnu-gcc -march=armv8.1-a -static synchrony-arm.s -o synchrony-arm -lm
riscv64-linux-gnu-gcc -march=rv64gc_zbb -static synchrony-rv.s -o synchrony-rv -lm
clang synchrony.ll -o synchrony-llvm -lm

./synchrony-x86 0 1728 960 > frame0.ppm

krellc parse synchrony-audio.krell -o synchrony-audio.krel
krellc build synchrony-audio.krel --target x86_64 -o synchrony-audio.s
cc synchrony-audio.s -o synchrony-audio -lm
./synchrony-audio > synchrony.pcm
```

To assemble the film, render frame f with backend f mod 4 in
the order above (AArch64 and RISC-V under qemu), convert each
PPM frame to an image sequence, and encode at 24 fps with the
PCM converted to a 44100 Hz WAV as the audio track. The
reference film is 960×960, 1,728 frames, 72.000 s.
