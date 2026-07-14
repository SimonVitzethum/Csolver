#!/usr/bin/env bash
# Regenerate x86_length_corpus.txt — the differential ground truth for the x86
# decoder length test (tests/x86_length_diff.rs). Reproducible: needs only clang
# and llvm-mc/llvm-objdump (LLVM). Each line is `HEXBYTES|LENGTH|MNEMONIC`, the
# authoritative per-instruction byte length from llvm-objdump — the property the
# recursive-descent decoder must match exactly (a wrong length desyncs the stream).
#
# Usage:  cd crates/asm/tests/data && ./regen.sh
set -euo pipefail
cd "$(dirname "$0")"
OUT=x86_length_corpus.txt

genobj() { # $1 = object file -> append HEXBYTES|LEN|MNEMONIC lines
  llvm-objdump -d "$1" 2>/dev/null \
    | grep -E "^\s+[0-9a-f]+:\s" \
    | sed -E 's/^\s+[0-9a-f]+:\s+//' \
    | awk -F'\t' '{
        n = split($1, b, " ");
        mn = $2; gsub(/^[ \t]+|[ \t]+$/, "", mn); split(mn, m, " ");
        if (n < 1 || n > 15) next;               # skip malformed / bad-length lines
        hex = ""; for (i = 1; i <= n; i++) hex = hex b[i];
        print hex "|" n "|" m[1]
      }'
}

tmp=$(mktemp) ; trap 'rm -f "$tmp" t.o extra.o' EXIT
: > "$tmp"
# Real compiler output across opt levels and ISA extensions (broad, reproducible).
for opt in O0 O1 O2 O3 Os; do
  for arch in "" "-mavx2" "-msse4.2"; do
    for src in big.c corpus.c c2.c; do
      clang -"$opt" $arch -c "$src" -o t.o 2>/dev/null && genobj t.o >> "$tmp"
    done
  done
done
# Hand-written families clang rarely emits (SSE-int, AVX, bit-manip, atomics, cmov).
llvm-mc --assemble --arch=x86-64 --filetype=obj extra.s -o extra.o 2>/dev/null && genobj extra.o >> "$tmp"

sort -u "$tmp" -o "$OUT"
echo "wrote $(wc -l < "$OUT") unique instructions to $OUT"
