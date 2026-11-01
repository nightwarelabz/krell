#!/bin/bash
# usage: tests/run_backend.sh <x86|arm|rv|llvm>
# Builds the generator for one backend, emits code for the battery +
# kernels modules, records interpreter-expected results, then replays
# them against the native (or qemu-emulated) code. Exit 0 = gate passed.
set -u
BE=${1:?backend}
cd "$(dirname "$0")/.."
B=build/$BE
mkdir -p "$B"
CFLAGS="-std=c11 -O1 -Wall -Wextra -Werror -Isrc -g"
SRCS="src/ir.c src/binary.c src/print.c src/verify.c src/cost.c src/interp.c src/be.c src/opt.c"
case $BE in
  x86)  SRCS="$SRCS src/be_x86.c"; BEDEF=-DKRELL_BE_X86 ;;
  arm)  SRCS="$SRCS src/be_arm64.c"; BEDEF=-DKRELL_BE_ARM ;;
  rv)   SRCS="$SRCS src/be_rv64.c"; BEDEF=-DKRELL_BE_RV ;;
  llvm) SRCS="$SRCS src/be_llvm.c"; BEDEF=-DKRELL_BE_LLVM ;;
  *) echo "unknown backend $BE" >&2; exit 2 ;;
esac
set -e
cc $CFLAGS $BEDEF -o "$B/gen" tests/gen.c tests/battery.c tests/kernels.c -DKERNELS_NO_MAIN $SRCS -lm
if [ "$BE" = llvm ]; then EXT=ll; else EXT=s; fi
"$B/gen" "$BE" "$B/out" "$B/expected.bin"
# the battery function named "alloca" shadows libc's; rename its symbol
# (carefully: the LLVM lane's text also contains the `alloca` opcode)
if [ "$EXT" = ll ]; then
  sed -i 's/@alloca(/@krell_alloca(/g' "$B/out.bat.$EXT"
else
  sed -i 's/\balloca\b/krell_alloca/g' "$B/out.bat.$EXT"
fi
case $BE in
  x86)
    cc -c "$B/out.bat.$EXT" -o "$B/bat.o"
    cc -c "$B/out.ker.$EXT" -o "$B/ker.o"
    cc $CFLAGS -o "$B/driver" tests/driver.c tests/kernels.c src/ir.c -DKERNELS_NO_MAIN "$B/bat.o" "$B/ker.o" -lm
    "$B/driver" "$B/expected.bin"
    ;;
  arm)
    aarch64-linux-gnu-gcc -march=armv8.1-a -c "$B/out.bat.$EXT" -o "$B/bat.o"
    aarch64-linux-gnu-gcc -march=armv8.1-a -c "$B/out.ker.$EXT" -o "$B/ker.o"
    aarch64-linux-gnu-gcc -static -std=c11 -O1 -Wall -Wextra -Werror -Isrc -g \
      -o "$B/driver" tests/driver.c tests/kernels.c src/ir.c -DKERNELS_NO_MAIN "$B/bat.o" "$B/ker.o" -lm
    qemu-aarch64 "$B/driver" "$B/expected.bin"
    ;;
  rv)
    riscv64-linux-gnu-gcc -march=rv64gc_zbb -c "$B/out.bat.$EXT" -o "$B/bat.o"
    riscv64-linux-gnu-gcc -march=rv64gc_zbb -c "$B/out.ker.$EXT" -o "$B/ker.o"
    riscv64-linux-gnu-gcc -static -std=c11 -O1 -Wall -Wextra -Werror -Isrc -g \
      -o "$B/driver" tests/driver.c tests/kernels.c src/ir.c -DKERNELS_NO_MAIN "$B/bat.o" "$B/ker.o" -lm
    qemu-riscv64 "$B/driver" "$B/expected.bin"
    ;;
  llvm)
    clang -c "$B/out.bat.$EXT" -o "$B/bat.o"
    clang -c "$B/out.ker.$EXT" -o "$B/ker.o"
    cc $CFLAGS -o "$B/driver" tests/driver.c tests/kernels.c src/ir.c -DKERNELS_NO_MAIN "$B/bat.o" "$B/ker.o" -lm
    "$B/driver" "$B/expected.bin"
    ;;
esac
