#!/usr/bin/env bash
# Positive control for the sweep's aggregation (aggregate.sh).
#
# A "0" or an "empty bucket" is the easiest observation in the world to fake: a
# broken filter and a genuine zero produce identical output. This project learned
# that the hard way — the per-obligation bucket read empty for four sweeps because
# the aggregation anchored on `UNKNOWN PO …` with `grep -A1` (which lands on the
# `predicate:` line, one short of the `residual:`), and an unverified zero almost
# got carved into the roadmap as "the engine is overdimensioned".
#
# So: feed a fixture with a KNOWN number of KNOWN residual lines — laid out in the
# real three-line `UNKNOWN PO` / `predicate:` / `residual:` shape, so the off-by-one
# that caused the phantom would resurface as a wrong count here — and assert each
# bucket reports exactly what went in. This runs the SAME functions the real sweep
# uses (sourced from aggregate.sh), so it cannot drift from what it guards.
set -uo pipefail
DIR="$(cd "$(dirname "$0")" && pwd)"
# shellcheck source=aggregate.sh
. "$DIR/aggregate.sh"

FIX="$(mktemp)"
trap 'rm -f "$FIX"' EXIT
cat > "$FIX" <<'EOF'
  fn prov_a : UNKNOWN
    UNKNOWN PO1 [in_bounds] @ mir:prov_a#1
        predicate: requires known provenance
        residual: requires known provenance (pointer provenance is not tracked)
    UNKNOWN PO2 [no_use_after_free] @ mir:prov_a#1
        predicate: requires known provenance
        residual: requires known provenance (pointer provenance is not tracked)
  fn null_b : UNKNOWN
    UNKNOWN PO1 [no_null_deref] @ mir:null_b#1
        predicate: pointer is non-null
        residual: pointer is non-null (pointer may be null or have opaque provenance)
  fn loop_c : UNKNOWN
    UNKNOWN PO5 [in_bounds] @ mir:loop_c#2
        predicate: access is within allocation bounds
        residual: access is within allocation bounds (memory operation not analyzed (loops, symbolic disabled, or truncated))
  fn frontend_d : UNKNOWN
    UNKNOWN PO1 [whole_body] @ mir:frontend_d#1
        predicate: whole function body
        residual: whole function body (not analyzed by the frontend: parse error: expected a local `_7`, found `core`)
  fn ok_e : PASS
EOF

fails=0
# Extract the count for a bucket whose text contains $2 from aggregator output $1.
# Empty match -> 0 (this is itself the thing under test: a real absence must read 0
# and a present bucket must read its true count — they must be distinguishable).
bucket() {
    local out="$1" needle="$2" n
    n=$(printf '%s\n' "$out" | grep -F "$needle" | awk '{print $1}' | head -1)
    echo "${n:-0}"
}
expect() { # label  actual  wanted
    if [ "$2" = "$3" ]; then
        printf "  ok    %-52s = %s\n" "$1" "$2"
    else
        printf "  FAIL  %-52s = %s (wanted %s)\n" "$1" "$2" "$3"
        fails=$((fails + 1))
    fi
}

RES="$(agg_residual "$FIX")"
FRONT="$(agg_frontend "$FIX")"

echo "== per-obligation residual buckets =="
# The core positive control: two provenance residuals, both two lines below their
# `UNKNOWN PO` anchor. An off-by-one regression reads this as 0.
expect "provenance bucket"          "$(bucket "$RES" 'pointer provenance is not tracked')" 2
expect "nullness bucket"            "$(bucket "$RES" 'pointer may be null or have opaque provenance')" 1
# Nested parenthetical must survive intact (root-cause keeps its own inner parens).
expect "loop/symbolic bucket"       "$(bucket "$RES" 'memory operation not analyzed (loops, symbolic disabled, or truncated)')" 1
# Total residual lines counted — the single number the phantom drove to 0.
expect "total residual lines"       "$(printf '%s\n' "$RES" | awk '{s+=$1} END{print s+0}')" 4
# Negative control: a bucket that genuinely is not present must read 0, so a real
# zero stays trustworthy (the absence is distinguishable from a present bucket).
expect "absent bucket reads 0"      "$(bucket "$RES" 'this root cause never occurs')" 0
# Frontend gaps must be excluded from the residual aggregation (counted separately).
expect "frontend gap not in residuals" "$(bucket "$RES" 'not analyzed by the frontend')" 0

echo "== frontend-gap buckets =="
expect "frontend gap counted once"  "$(printf '%s\n' "$FRONT" | awk '{s+=$1} END{print s+0}')" 1
expect "frontend ident normalised"  "$(bucket "$FRONT" 'found <ident>')" 1

echo
if [ "$fails" -eq 0 ]; then
    echo "aggregation self-test: PASS (the metric reports known inputs correctly)"
    exit 0
else
    echo "aggregation self-test: $fails FAILED — the sweep's numbers are NOT trustworthy"
    exit 1
fi
