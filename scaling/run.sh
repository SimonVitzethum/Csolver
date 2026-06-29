#!/usr/bin/env bash
# Scaling test: run CSolver over WHOLE real crates and measure the UNKNOWN
# distribution at scale.
#
# The curated differential corpus answers "is a verdict sound?" — one pattern per
# function. It cannot answer "what does real code actually contain, and how often?"
# This harness does: it takes real, dependency-free crates straight from the local
# cargo cache, emits their MIR (`rustc --emit=mir`), runs `solver verify` over the
# whole thing, and aggregates *why* functions come back UNKNOWN. The point is not a
# PASS rate — it is a data-driven priority list for what to build next, one level
# up from the curated corpus.
#
# It needs no network: the crates must already be unpacked under the cargo cache
# (`~/.cargo/registry/src/*/`). Crates that are not present, or fail to compile to
# MIR (missing features/deps), are skipped with a note.
set -uo pipefail
DIR="$(cd "$(dirname "$0")" && pwd)"
ROOT="$(cd "$DIR/.." && pwd)"
OUT="$DIR/out"
mkdir -p "$OUT"

# Real crates to sweep — chosen to span the kinds of code that matter for memory
# safety: arithmetic (PRNG/checksum), buffer formatting, and — most relevant —
# data structures full of slices, indexing and `unsafe` (arrayvec/tinyvec).
CRATES=(oorandom adler2 itoa hexf-parse base64 smallvec tinyvec arrayvec)

echo "== building the solver CLI =="
(cd "$ROOT" && cargo build -q -p csolver-cli) || { echo "build failed"; exit 2; }
SOLVER="$ROOT/target/debug/solver"

CACHE_GLOB=("$HOME"/.cargo/registry/src/*/)
ALL="$OUT/all.txt"
: > "$ALL"

printf "%-12s %5s %5s %5s %6s\n" "crate" "PASS" "FAIL" "UNK" "total"
printf -- "-------------------------------------------\n"
tP=0; tF=0; tU=0
for name in "${CRATES[@]}"; do
    # newest matching version in the cache
    dir=""
    for g in "${CACHE_GLOB[@]}"; do
        d=$(ls -d "$g$name"-*/ 2>/dev/null | sort -V | tail -1)
        [ -n "$d" ] && dir="$d" && break
    done
    if [ -z "$dir" ] || [ ! -f "${dir}src/lib.rs" ]; then
        printf "%-12s %s\n" "$name" "(not in cargo cache — skipped)"
        continue
    fi
    ed=$(grep -m1 -oE 'edition *= *"[0-9]+"' "${dir}Cargo.toml" | grep -oE '[0-9]+')
    mir="$OUT/$name.mir"
    if ! rustc --edition "${ed:-2021}" --emit=mir --crate-type=lib \
            "${dir}src/lib.rs" -o "$mir" 2>"$OUT/$name.rustc.err" || [ ! -s "$mir" ]; then
        printf "%-12s %s\n" "$name" "(rustc --emit=mir failed — skipped)"
        continue
    fi
    verdicts=$(timeout 300 "$SOLVER" verify "$mir" 2>>"$ALL")
    echo "$verdicts" >> "$ALL"
    p=$(echo "$verdicts" | grep -cE "^  fn .* : PASS")
    f=$(echo "$verdicts" | grep -cE "^  fn .* : FAIL")
    u=$(echo "$verdicts" | grep -cE "^  fn .* : UNKNOWN")
    tP=$((tP+p)); tF=$((tF+f)); tU=$((tU+u))
    printf "%-12s %5d %5d %5d %6d\n" "$name" "$p" "$f" "$u" "$((p+f+u))"
done
printf -- "-------------------------------------------\n"
printf "%-12s %5d %5d %5d %6d\n" "TOTAL" "$tP" "$tF" "$tU" "$((tP+tF+tU))"

echo
echo "== why UNKNOWN: frontend gaps (a parse/lowering error loses the whole fn) =="
# Normalise reasons: drop concrete identifiers/integers so they bucket.
grep -oE "not analyzed by the frontend: [^)]*" "$ALL" \
    | sed -E "s/found Punct\('(.)'\)/found '\1'/; s/found \`[^\`]*\`/found <ident>/; \
              s/found Word\(\"[^\"]*\"\)/found <word>/; s/[0-9]+/N/g" \
    | sort | uniq -c | sort -rn | head -15

echo
echo "== why UNKNOWN: per-obligation residuals (fn analyzed, a check unproven) =="
grep -A1 -E "^    UNKNOWN PO" "$ALL" | grep -E "residual:" \
    | grep -v "not analyzed by the frontend" \
    | sed -E "s/_[0-9]+/_N/g; s/[0-9]+/N/g" \
    | sort | uniq -c | sort -rn | head -12

echo
echo "(full output: $ALL)"
