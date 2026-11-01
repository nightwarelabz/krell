#!/bin/bash
# usage: tests/run_fuzz.sh <x86|arm|rv|llvm> <seed> <opt|noopt> [nfuncs]
set -u
BE=${1:?backend}; SEED=${2:?seed}; OPT=${3:?opt|noopt}; NF=${4:-120}
cd "$(dirname "$0")/.."
B=build/fuzz-$BE-$SEED-$OPT
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
cc $CFLAGS $BEDEF -o "$B/fuzz_gen" tools/fuzz_gen.c $SRCS -lm
"$B/fuzz_gen" "$BE" "$SEED" "$NF" "$OPT" "$B/out"
if [ "$BE" = llvm ]; then EXT=ll; else EXT=s; fi
case $BE in
  x86)
    cc -c "$B/out.fz.$EXT" -o "$B/fz.o"
    cc $CFLAGS -DFTAB_H="\"$(pwd)/$B/out.ftab.h\"" -o "$B/fuzz_driver" tools/fuzz_driver.c "$B/fz.o" -lm
    "$B/fuzz_driver" "$B/out.fcases"
    ;;
  arm)
    aarch64-linux-gnu-gcc -march=armv8.1-a -c "$B/out.fz.$EXT" -o "$B/fz.o"
    aarch64-linux-gnu-gcc -static -std=c11 -O1 -Wall -Wextra -Werror -Isrc -g \
      -DFTAB_H="\"$(pwd)/$B/out.ftab.h\"" -o "$B/fuzz_driver" tools/fuzz_driver.c "$B/fz.o" -lm
    qemu-aarch64 "$B/fuzz_driver" "$B/out.fcases"
    ;;
  rv)
    riscv64-linux-gnu-gcc -march=rv64gc_zbb -c "$B/out.fz.$EXT" -o "$B/fz.o"
    riscv64-linux-gnu-gcc -static -std=c11 -O1 -Wall -Wextra -Werror -Isrc -g \
      -DFTAB_H="\"$(pwd)/$B/out.ftab.h\"" -o "$B/fuzz_driver" tools/fuzz_driver.c "$B/fz.o" -lm
    qemu-riscv64 "$B/fuzz_driver" "$B/out.fcases"
    ;;
  llvm)
    clang -c "$B/out.fz.$EXT" -o "$B/fz.o"
    cc $CFLAGS -DFTAB_H="\"$(pwd)/$B/out.ftab.h\"" -o "$B/fuzz_driver" tools/fuzz_driver.c "$B/fz.o" -lm
    "$B/fuzz_driver" "$B/out.fcases"
    ;;
esac
