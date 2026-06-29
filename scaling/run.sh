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

# Dep-free utility crates — emitted directly with `rustc --emit=mir`. Span the
# code that matters for memory safety: arithmetic (PRNG/checksum), buffer
# formatting, and data structures full of slices, indexing and `unsafe`.
CRATES=(oorandom adler2 itoa hexf-parse base64 smallvec tinyvec arrayvec)
# Complex application-grade crates, one notch harder, for the constructs the
# utility crates lack: called closures (nom's parser combinators), complex
# generics + unsafe (hashbrown), trait-object / fn-pointer dispatch (bytes), SIMD
# (memchr). They carry dependencies, so they are emitted via cargo (which builds
# the deps) with `RUSTFLAGS=--emit=mir`, not rustc directly.
COMPLEX=(nom hashbrown bytes memchr)

echo "== building the solver CLI =="
(cd "$ROOT" && cargo build -q -p csolver-cli) || { echo "build failed"; exit 2; }
SOLVER="$ROOT/target/debug/solver"

CACHE_GLOB=("$HOME"/.cargo/registry/src/*/)
ALL="$OUT/all.txt"
: > "$ALL"

# Emit the complex crates' MIR into $OUT via a throwaway cargo project.
emit_complex() {
    local proj="$OUT/_cx" c f
    mkdir -p "$proj/src"
    : > "$proj/src/lib.rs"
    {
        printf '[package]\nname="cx"\nversion="0.0.0"\nedition="2021"\n'
        printf '[dependencies]\nnom="7"\nhashbrown="0.16"\nbytes="1"\n[workspace]\n'
    } > "$proj/Cargo.toml"
    (cd "$proj" && RUSTFLAGS="--emit=mir" cargo build --offline -q 2>/dev/null) || return 1
    for c in "${COMPLEX[@]}"; do
        f=$(ls -S "$proj"/target/debug/deps/"$c"-*.mir 2>/dev/null | head -1)
        [ -n "$f" ] && cp "$f" "$OUT/$c.mir"
    done
}
emit_complex || echo "(complex-crate MIR emission failed — skipping that tier)"

printf "%-12s %5s %5s %5s %6s\n" "crate" "PASS" "FAIL" "UNK" "total"
printf -- "-------------------------------------------\n"
tP=0; tF=0; tU=0
for name in "${CRATES[@]}" "${COMPLEX[@]}"; do
    mir="$OUT/$name.mir"
    # Dep-free crates are emitted here from the cache; complex ones were emitted
    # above by `emit_complex`.
    if [[ " ${CRATES[*]} " == *" $name "* ]]; then
        dir=""
        for g in "${CACHE_GLOB[@]}"; do
            d=$(ls -d "$g$name"-*/ 2>/dev/null | sort -V | tail -1)
            [ -n "$d" ] && dir="$d" && break
        done
        if [ -z "$dir" ] || [ ! -f "${dir}src/lib.rs" ]; then
            printf "%-12s %s\n" "$name" "(not in cargo cache — skipped)"; continue
        fi
        ed=$(grep -m1 -oE 'edition *= *"[0-9]+"' "${dir}Cargo.toml" | grep -oE '[0-9]+')
        if ! rustc --edition "${ed:-2021}" --emit=mir --crate-type=lib \
                "${dir}src/lib.rs" -o "$mir" 2>"$OUT/$name.rustc.err" || [ ! -s "$mir" ]; then
            printf "%-12s %s\n" "$name" "(rustc --emit=mir failed — skipped)"; continue
        fi
    elif [ ! -s "$mir" ]; then
        printf "%-12s %s\n" "$name" "(complex MIR not emitted — skipped)"; continue
    fi
    verdicts=$(timeout 200 "$SOLVER" verify "$mir" 2>>"$ALL"); rc=$?
    if [ "$rc" -eq 124 ]; then
        # A new category at this complexity tier: the front end digests the crate
        # but the engine is too slow to finish — a scaling limit, not a gap.
        printf "%-12s %s\n" "$name" "(TIMEOUT — engine too slow on this crate)"; continue
    fi
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
# Bucket by each residual's ROOT CAUSE — the parenthetical, which names the
# *missing capability* (provenance, loop/symbolic depth, nullness), not the
# obligation kind, which only says which check tripped. NOTE: match the
# `residual:` line directly. An earlier version anchored on `UNKNOWN PO` with
# `grep -A1`, which lands on the `predicate:` line — the residual is one line
# further down — so it counted zero and made this whole bucket look empty. It
# was never empty; it is in fact the dominant driver of UNKNOWN at scale.
grep -E "residual:" "$ALL" \
    | grep -v "not analyzed by the frontend" \
    | sed -E "s/.*residual: [^(]*\((.*)\)$/\1/" \
    | sed -E "s/_[0-9]+/_N/g; s/[0-9]+/N/g" \
    | sort | uniq -c | sort -rn | head -12

echo
echo "(full output: $ALL)"
