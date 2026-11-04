#!/usr/bin/env bash
set -e

DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
cd "$DIR"

ROOT_DIR="$(cd "$DIR/../.." && pwd)"

# Ensure krellc compiler is built
KRELLC="$ROOT_DIR/krellc"
if [ ! -x "$KRELLC" ]; then
    echo "[*] Compiling Krell toolchain (krellc)..."
    make -C "$ROOT_DIR" krellc
fi

# Build nightware_labz if not present or source is newer
if [ ! -f ./nightware_labz ] || [ ./nightware_labz.krell -nt ./nightware_labz ]; then
    echo "[*] Compiling NIGHTWARE LABZ demoscene engine from pure Krell IR..."
    "$KRELLC" build nightware_labz.krell --target llvm -o nightware_labz.ll
    "$KRELLC" build nightware_labz.krell --target x86_64 -o nightware_labz.s
    "$KRELLC" parse nightware_labz.krell -o nightware_labz.krel
    
    # Compile native binary with clang / cc
    CC=${CC:-cc}
    $CC -O3 nightware_labz.ll kc_shim.c -lm -o nightware_labz
    echo "[*] Build successful: ./nightware_labz"
fi

echo "[*] Launching NIGHTWARE LABZ Cyber Hologram Engine (Press Ctrl+C to exit)..."
sleep 0.5
exec ./nightware_labz
