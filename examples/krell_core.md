# krell_core

A fullscreen terminal animation written in pure Krell surface
syntax: a 3D dual-ring gyroscope with z-buffering over a flowing
plasma background, rendered as 24-bit truecolor ANSI with a
demoscene HUD and telemetry readout. It sizes itself to the
terminal it runs in and runs continuously until Ctrl+C.

Files:

- `krell_core.krell` — the program. All computation is in Krell;
  its only externs are libc/libm (`write`, `usleep`, `malloc`,
  `free`, `sin`, `cos`, `sqrt`) plus the shim below.
- `krell_core_shim.c` — a one-function C wrapper for the
  terminal-size query. The program calls `kc_winsize(fd, buf)`
  instead of `ioctl` directly: the `TIOCGWINSZ` request value
  belongs to the platform header, and `ioctl` is variadic — on
  Darwin ARM64, variadic arguments travel on the stack rather
  than in registers, so a direct call from generated code reads
  the wrong pointer and fails. The compiled wrapper makes the
  same module work on every platform.
- `krell_core_macos.sed` — the ELF-to-Mach-O conversion for
  Krell's AArch64 output, used by the macOS build below (Mach-O
  relocation syntax, no `.type`/`.size` directives, leading
  underscores on external symbols).

## Run on Linux

From the repository root, with `krellc` built (`make`):

```
KRELL_TARGETS=$PWD/targets ./krellc parse examples/krell_core.krell -o /tmp/krell_core.krel
KRELL_TARGETS=$PWD/targets ./krellc build /tmp/krell_core.krel --target x86_64 -o /tmp/krell_core.s
cc -c examples/krell_core_shim.c -o /tmp/krell_core_shim.o
cc /tmp/krell_core.s /tmp/krell_core_shim.o -o krell_core -lm
./krell_core
```

(For a Linux AArch64 host, build with `--target aarch64` and
assemble/link with the AArch64 toolchain instead.)

## Run on macOS (Apple Silicon)

```
KRELL_TARGETS=$PWD/targets ./krellc parse examples/krell_core.krell -o /tmp/krell_core.krel
KRELL_TARGETS=$PWD/targets ./krellc build /tmp/krell_core.krel --target aarch64 -o /tmp/krell_core.s
sed -E -f examples/krell_core_macos.sed /tmp/krell_core.s > /tmp/krell_core_macos.s
cc -c examples/krell_core_shim.c -o /tmp/krell_core_shim.o
cc /tmp/krell_core_macos.s /tmp/krell_core_shim.o -o krell_core -lm
./krell_core
```

## Notes

- Run it in a real terminal; it queries the terminal size at
  startup and fills whatever window it finds (fullscreen
  terminal, fullscreen display). If the size query fails it
  falls back to 80x24.
- Frame pacing is ~30 fps. Ctrl+C exits.
