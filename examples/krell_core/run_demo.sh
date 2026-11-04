#!/usr/bin/env bash
set -e

DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
cd "$DIR"

# Build krell_core if not present
if [ ! -f ./krell_core ]; then
    echo "[*] Building krell_core executable from pure Krell source..."
    if [ ! -f ./krellc ]; then
        make krellc
    fi
    ./krellc build krell_core.krell --target x86_64 -o krell_core.s
    cc krell_core.s -lm -o krell_core
fi

echo "[*] Launching KRELL CORE Terminal Demo (Press Ctrl+C to exit)..."
sleep 0.5
exec ./krell_core
