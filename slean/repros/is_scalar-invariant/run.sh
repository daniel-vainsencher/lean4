#!/usr/bin/env bash
# Build and run the reproducer test harness using the installed Lean
# toolchain (via elan). No runtime rebuild needed.
set -euo pipefail

cd "$(dirname "$0")"

LEANPFX=$(lean --print-prefix)
LEANC="$LEANPFX/bin/leanc"

OUT=$(mktemp -d)
trap 'rm -rf "$OUT"' EXIT

# Compile Lean -> C
lean -c "$OUT/Test.c" Test.lean

# Compile the FFI helper. LEAN_USE_GMP exposes lean_alloc_mpz in
# <lean/lean_gmp.h>.
"$LEANC" -DLEAN_USE_GMP -I/usr/include -c mkboxed.c -o "$OUT/mkboxed.o"
"$LEANC"                               -c "$OUT/Test.c"  -o "$OUT/Test.o"

# Link against libgmp
"$LEANC" "$OUT/Test.o" "$OUT/mkboxed.o" -lgmp -o "$OUT/test"

# Run
"$OUT/test"
