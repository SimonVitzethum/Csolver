#!/usr/bin/env bash
# Kernel bug-finding sweep: run CSolver (--bugs) over a directory of LLVM-IR files
# emitted from a Linux kernel build, and aggregate the FAIL reports — each a
# potential memory-safety bug with a concrete witness.
#
# This is meant for a VPS: emitting and sweeping real kernel IR is resource-heavy.
# It does NOT build the kernel — it consumes .ll files you produce first (see
# README.md; the short version is `make LLVM=1 path/to/file.ll` per translation unit).
#
# Usage:
#   scaling/kernel/run.sh <dir-of-ll>          # sweep every *.ll under <dir>
#   TIMEOUT=120 JOBS=8 scaling/kernel/run.sh ll # tune per-file timeout / parallelism
#
# Output: a per-file tally, then a ranked list of the functions that FAIL (the bug
# candidates) with their residual, and a summary. FAIL under --bugs means CSolver
# found a reachable input that drives an OOB/UAF/double-free, with a witness — a
# high-signal lead to triage, not a proof of exploitability.
set -uo pipefail
DIR="$(cd "$(dirname "$0")" && pwd)"
ROOT="$(cd "$DIR/../.." && pwd)"
LLDIR="${1:-$DIR/ll}"
: "${TIMEOUT:=90}"      # per-file wall-clock cap (seconds); kernel TUs can be large
: "${JOBS:=$(nproc 2>/dev/null || echo 4)}"

if [ ! -d "$LLDIR" ]; then
    echo "no such directory: $LLDIR"
    echo "produce kernel IR first (see scaling/kernel/README.md), then point me at it."
    exit 2
fi

echo "== building the solver CLI =="
(cd "$ROOT" && cargo build -q --release -p csolver-cli) || { echo "build failed"; exit 2; }
SOLVER="$ROOT/target/release/solver"

OUT="$DIR/out"
mkdir -p "$OUT"
: > "$OUT/fails.txt"; : > "$OUT/errors.txt"; : > "$OUT/timeouts.txt"

mapfile -t FILES < <(find "$LLDIR" -name '*.ll' | sort)
echo "== sweeping ${#FILES[@]} .ll files (--bugs, timeout ${TIMEOUT}s, $JOBS parallel) =="

# One file → a line of counts, plus any FAIL lines appended to fails.txt.
sweep_one() {
    local f="$1" rel; rel="${f#"$LLDIR"/}"
    local out; out="$(timeout "$TIMEOUT" "$SOLVER" verify "$f" --bugs 2>&1)"; local code=$?
    if [ "$code" -eq 124 ]; then echo "$rel" >> "$OUT/timeouts.txt"; printf 'TIMEOUT %s\n' "$rel"; return; fi
    if echo "$out" | grep -qiE "^error|tool error"; then echo "$rel" >> "$OUT/errors.txt"; fi
    # Record each FAIL function with its file and first residual line.
    echo "$out" | awk -v file="$rel" '
        /fn .* : FAIL/ { fn=$2; print "FAIL\t" file "\t" fn; getline r; sub(/^[ \t]*/,"",r); if (r ~ /residual/) print "    " r > "/dev/stderr" }
    ' >> "$OUT/fails.txt" 2>>"$OUT/fails.residuals.txt"
    local nf; nf=$(echo "$out" | grep -c "fn .* : FAIL")
    printf '%-50s FAIL=%s\n' "$rel" "$nf"
}
export -f sweep_one; export SOLVER OUT LLDIR TIMEOUT

printf '%s\0' "${FILES[@]}" | xargs -0 -P "$JOBS" -I{} bash -c 'sweep_one "$@"' _ {}

echo
echo "== bug candidates (FAIL under --bugs) =="
if [ -s "$OUT/fails.txt" ]; then
    sort "$OUT/fails.txt" | awk -F'\t' '{printf "  %-40s %s\n", $3, $2}'
else
    echo "  (none)"
fi

echo
echo "== summary =="
echo "files swept     : ${#FILES[@]}"
echo "bug candidates  : $(wc -l < "$OUT/fails.txt")   (FAIL functions — triage against the source)"
echo "parse/tool errs : $(sort -u "$OUT/errors.txt" | wc -l)   (unsupported IR — function(s) skipped, not analyzed)"
echo "timeouts        : $(wc -l < "$OUT/timeouts.txt")   (raise TIMEOUT to reach them)"
echo
echo "details in $OUT/  (fails.txt, errors.txt, timeouts.txt)"
