# NIGHTWARE LABZ: Demoscene Cyber Hologram Engine

An infinitely animated, fullscreen demoscene terminal program written in **pure Krell surface IR** (`nightware_labz.krell`), compiled natively via the Krell compiler toolchain (`krellc`).

Zero runtime overhead, zero external dependencies, total SSA semantics.

---

## Visual & Mathematical Architecture

1. **3D Volumetric Undulating Typography ("NIGHTWARE LABZ")**:
   - High-definition 5x5 demoscene glyphs for `NIGHTWARE` and wide-tracked `L A B Z`.
   - Per-letter harmonic wave physics: each character floats with its own phase on a dynamic 3D undulating ribbon.
   - Multi-layer 3D extrusion with depth testing: specular front face, beveled metallic lighting (`#`), and deep drop shadow (`:`).
   - Real-time laser chrome sweep passing horizontally across the text, triggering blinding white-hot specular laser shine (`@`) and electric cyan/magenta corona reflections.

2. **Retro-Futuristic Synthwave Perspective Ground Grid**:
   - Full 3D perspective projection below the horizon (`z_depth = 1.0 / (dy + 0.08)`).
   - Dynamic high-speed travel lines scrolling into infinity with atmospheric fog falloff.
   - Grid line intersections rendered with glowing neon purple/magenta truecolor (`\033[38;2;...m\033[48;2;...m`).

3. **Cosmic Multi-Harmonic Plasma Nebula & Starfield**:
   - Continuous 3-harmonic sine fluid plasma above the horizon with deep cosmic midnight-indigo and aurora borealis shifts.
   - Real-time procedural twinkling starfield using deterministic integer hashing.

4. **Dual 3D Intersecting Quantum Gyroscope Rings**:
   - Twin rotating 3D tori orbiting around the central logo in counter-rotating 3D space (`A`, `B` rotation matrices).
   - Full 3D depth-buffer (Z-buffer) testing so the quantum sparks pass both in front of and behind the 3D typography.

5. **32-Band Procedural Synthesizer Audio Spectrum Visualizer**:
   - Equalizer VU meters bouncing to a procedural synthwave beat rhythm along the bottom canvas.
   - Dynamic three-tier color gradient: neon emerald green $\to$ laser gold/yellow $\to$ crimson peak.

6. **Cyberpunk Demoscene Telemetry HUD**:
   - High-tech double-bordered frame adapting dynamically to any terminal dimensions via non-variadic `kc_winsize` / `TIOCGWINSZ`.
   - Real-time 6-digit frame counter, 40 FPS silky smooth refresh rate, and system status readouts.

---

## Quick Start

### Run the Demo
```bash
./examples/nightware_labz/run_demo.sh
```

### Build with Make
```bash
cd examples/nightware_labz
make
./nightware_labz
```

### Manual Compilation from Krell IR Source
```bash
# 1. Compile Krell IR to LLVM IR and x86_64 assembly
./krellc build examples/nightware_labz/nightware_labz.krell --target llvm -o examples/nightware_labz/nightware_labz.ll
./krellc build examples/nightware_labz/nightware_labz.krell --target x86_64 -o examples/nightware_labz/nightware_labz.s

# 2. Encode to canonical binary IR
./krellc parse examples/nightware_labz/nightware_labz.krell -o examples/nightware_labz/nightware_labz.krel

# 3. Link native executable with clang / gcc
cc -O3 examples/nightware_labz/nightware_labz.ll examples/nightware_labz/kc_shim.c -lm -o examples/nightware_labz/nightware_labz

# 4. Launch!
./examples/nightware_labz/nightware_labz
```
*Press `Ctrl+C` to exit at any time.*
