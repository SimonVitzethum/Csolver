#!/usr/bin/env bash
# Differential validation: CSolver (static, all inputs) vs Miri (dynamic, the
# driven inputs) over the corpus in src/lib.rs.
#
#   Miri UB + CSolver PASS  -> SOUNDNESS VIOLATION (a false PASS; must be zero)
#   Miri UB + CSolver !PASS -> sound (caught as FAIL, or honestly UNKNOWN)
#   Miri clean + CSolver PASS  -> precise
#   Miri clean + CSolver !PASS -> precision miss (UNKNOWN on safe code)
#
# Only Miri's *Undefined Behavior* is the soundness oracle. A normal Rust panic
# (e.g. a bounds-check abort) is *safe* behaviour — CSolver proves memory safety,
# not panic-freedom — so a panic counts as "no UB".
#
# Exits non-zero iff any soundness violation is found.
set -uo pipefail
DIR="$(cd "$(dirname "$0")" && pwd)"
ROOT="$(cd "$DIR/.." && pwd)"

echo "== building the solver CLI =="
(cd "$ROOT" && cargo build -q -p csolver-cli) || { echo "build failed"; exit 2; }
SOLVER="$ROOT/target/debug/solver"

echo "== CSolver: verifying the corpus MIR =="
rustc --emit=mir --crate-type=lib "$DIR/src/lib.rs" -o "$DIR/corpus.mir" 2>/dev/null \
    || { echo "rustc --emit=mir failed"; exit 2; }
CS_OUT="$("$SOLVER" verify "$DIR/corpus.mir" 2>&1)"

# Each corpus function = the `pub fn`s in src/lib.rs.
FNS=$(grep -oE '^pub fn [a-z_]+' "$DIR/src/lib.rs" | sed 's/pub fn //')

verdict() { # CSolver verdict for a function name
    echo "$CS_OUT" | grep -E "fn $1 :" | grep -oE 'PASS|FAIL|UNKNOWN' | head -1
}

echo "== Miri: driving each function (first run is cached) =="
violations=0
precise=0
miss=0
sound_caught=0
printf "%-18s %-9s %-7s  %s\n" "function" "CSolver" "Miri" "result"
printf -- "------------------------------------------------------------\n"
for fn in $FNS; do
    cs="$(verdict "$fn")"
    [ -z "$cs" ] && cs="(none)"
    mout="$(cd "$DIR" && cargo +nightly miri test -q -- --exact "drive_$fn" 2>&1)"
    if echo "$mout" | grep -q "Undefined Behavior"; then
        miri="UB"
    elif echo "$mout" | grep -q "panicked"; then
        miri="PANIC"   # safe (a checked abort) — not a soundness concern
    else
        miri="CLEAN"
    fi

    if [ "$miri" = "UB" ] && [ "$cs" = "PASS" ]; then
        res="!! SOUNDNESS VIOLATION (false PASS)"; violations=$((violations+1))
    elif [ "$miri" = "UB" ]; then
        res="ok (UB caught / unknown)"; sound_caught=$((sound_caught+1))
    elif [ "$cs" = "PASS" ]; then
        res="ok (precise)"; precise=$((precise+1))
    else
        res="~ precision miss (unknown on safe)"; miss=$((miss+1))
    fi
    printf "%-18s %-9s %-7s  %s\n" "$fn" "$cs" "$miri" "$res"
done

echo
echo "== summary =="
echo "soundness violations : $violations   (must be 0)"
echo "UB caught/unknown    : $sound_caught"
echo "safe & precise (PASS): $precise"
echo "safe & unknown       : $miss"
[ "$violations" -eq 0 ] && echo "RESULT: SOUND (no false PASS on this corpus)" \
                        || echo "RESULT: UNSOUND — investigate the violations above"
exit "$violations"
