#!/usr/bin/env bash
# Complete kernel scan with a LIVE bug feed.
#
# This runs CSolver's whole-program `scan` over a tree of LLVM-IR (`.ll`) files
# emitted from a Linux kernel build and streams every memory-safety violation to the
# console the moment it is found — `[FOUND #n] file::function [property] witness: …`.
#
# The `scan` command is already the COMPLETE-scan configuration by default (see
# `solver --help`): --bugs, --assume-valid-params, --closed-world, --cross-file,
# --whole-program, --auto-entries and --aliasing-model are all ON unless you pass the
# matching anti-flag (`--no-<name>`). So a bare scan is the maximal-recall sweep; this
# wrapper just builds the release binary, points it at the corpus, and tees a log.
#
# Usage:
#   scaling/kernel/full-scan.sh [<dir-of-ll>] [extra solver flags…]
#
#   # default corpus (the checked-in kernel build), full complete scan, live feed:
#   scaling/kernel/full-scan.sh
#
#   # a different tree:
#   scaling/kernel/full-scan.sh /path/to/kernel-ll
#
#   # narrow the scan with anti-flags (drop the unsound framework-valid-param assumption):
#   scaling/kernel/full-scan.sh Kerneltests/linux --no-assume-valid-params
#
# Environment:
#   CSOLVER_JOBS=N            concurrent units (memory vs parallelism; default = cores)
#   CSOLVER_THREADS_PER_UNIT=N  threads handed to each unit (default keeps total ≈ cores)
#
# Exit code: 1 if any bug was found, 0 if the tree is clean, 2 on a setup error.
set -uo pipefail
DIR="$(cd "$(dirname "$0")" && pwd)"
ROOT="$(cd "$DIR/../.." && pwd)"

# First non-flag argument is the corpus directory; everything else is passed through to
# the scanner (e.g. `--no-assume-valid-params`, `--entries <file>`, `--reachable`).
LLDIR=""
PASS_THROUGH=()
for a in "$@"; do
    if [ -z "$LLDIR" ] && [[ "$a" != --* ]]; then LLDIR="$a"; else PASS_THROUGH+=("$a"); fi
done
# Default corpus: the checked-in kernel IR tree, if present.
if [ -z "$LLDIR" ]; then
    for cand in "$ROOT/Kerneltests/linux" "$DIR/ll"; do
        if [ -d "$cand" ]; then LLDIR="$cand"; break; fi
    done
fi
if [ -z "$LLDIR" ] || [ ! -d "$LLDIR" ]; then
    echo "no corpus directory found."
    echo "usage: scaling/kernel/full-scan.sh [<dir-of-ll>] [extra solver flags…]"
    echo "produce kernel IR first (see scaling/kernel/README.md) or pass a directory."
    exit 2
fi

echo "== building the solver CLI (release) =="
(cd "$ROOT" && cargo build -q --release -p csolver-cli) || { echo "build failed"; exit 2; }
SOLVER="$ROOT/target/release/solver"

N_LL=$(find "$LLDIR" -name '*.ll' 2>/dev/null | wc -l)
OUT="$DIR/out"
mkdir -p "$OUT"
STAMP="$(date +%Y%m%d-%H%M%S)"
LOG="$OUT/full-scan-$STAMP.log"

echo
echo "== complete kernel scan (whole-program, live bug feed) =="
echo "  corpus         : $LLDIR  ($N_LL .ll files)"
echo "  configuration  : COMPLETE scan defaults (--bugs --assume-valid-params --closed-world"
echo "                   --cross-file --whole-program --auto-entries --aliasing-model)"
if [ "${#PASS_THROUGH[@]}" -gt 0 ]; then
    echo "  overrides      : ${PASS_THROUGH[*]}"
fi
echo "  live feed      : each bug prints as [FOUND #n] the moment it is found"
echo "  log            : $LOG"
echo

# `scan` streams findings live to stderr (unbuffered); `stdbuf` keeps stdout line-buffered
# so the interleaved progress + final coverage report also appear promptly under `tee`.
# `2>&1 | tee` mirrors the live feed to the console AND the log without hiding either stream.
stdbuf -oL -eL "$SOLVER" scan "$LLDIR" "${PASS_THROUGH[@]}" 2>&1 | tee "$LOG"
code="${PIPESTATUS[0]}"

echo
echo "== scan complete =="
echo "  full log saved to: $LOG"
FOUND=$(grep -c '\[FOUND #' "$LOG" 2>/dev/null || echo 0)
echo "  bugs streamed    : $FOUND   (see the '== memory-safety violations found ==' section above)"
exit "$code"
