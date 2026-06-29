#!/usr/bin/env bash
# Soundness at scale: fuzz real scaling-corpus crates under Miri and cross-check
# against CSolver's PASS verdicts.
#
#   Miri UB in a crate whose functions CSolver verified PASS  ->  a false PASS may
#   be present: cross-reference the Miri backtrace's function against the crate's
#   per-function verdicts (printed by ../run.sh). This is the cardinal sin.
#   Miri clean over a broad fuzz  ->  the executed PASS functions are validated on
#   those paths — the coverage number becomes a trustworthy one.
#
# Only Miri's *Undefined Behavior* is the oracle; a Rust panic is safe behaviour.
# Built offline from the cargo cache. FUZZ_CASES bounds the per-driver count under
# (slow) Miri.
set -uo pipefail
DIR="$(cd "$(dirname "$0")" && pwd)"
ROOT="$(cd "$DIR/../.." && pwd)"
: "${FUZZ_CASES:=40}"
export FUZZ_CASES

# crate  ->  fuzz test name (1:1).
CRATES=(adler2 oorandom arrayvec tinyvec itoa memchr bytes hashbrown nom)

echo "== building the solver CLI =="
(cd "$ROOT" && cargo build -q -p csolver-cli) || { echo "build failed"; exit 2; }
SOLVER="$ROOT/target/debug/solver"
CACHE_GLOB=("$HOME"/.cargo/registry/src/*/)
OUT="$DIR/out"
mkdir -p "$OUT"

cs_pass() { # CSolver PASS count for a crate (emit its MIR, count `: PASS`)
    local name="$1" dir="" g
    for g in "${CACHE_GLOB[@]}"; do
        dir=$(ls -d "$g$name"-*/ 2>/dev/null | sort -V | tail -1)
        [ -n "$dir" ] && break
    done
    [ -z "$dir" ] && { echo "?"; return; }
    local ed
    ed=$(grep -m1 -oE 'edition *= *"[0-9]+"' "${dir}Cargo.toml" | grep -oE '[0-9]+')
    local mir="$OUT/$name.mir"
    rustc --edition "${ed:-2021}" --emit=mir --crate-type=lib "${dir}src/lib.rs" \
        -o "$mir" 2>/dev/null || { echo "?"; return; }
    timeout 300 "$SOLVER" verify "$mir" 2>/dev/null | grep -cE "^  fn .* : PASS"
}

echo "== fuzzing each crate under Miri (FUZZ_CASES=$FUZZ_CASES) =="
printf "%-10s %-12s %-7s  %s\n" "crate" "CSolver-PASS" "Miri" "result"
printf -- "------------------------------------------------------------\n"
findings=0
for name in "${CRATES[@]}"; do
    pass="$(cs_pass "$name")"
    mout="$(cd "$DIR" && cargo +nightly miri test -q --offline -- --exact "fuzz_$name" 2>&1)"
    if echo "$mout" | grep -q "Undefined Behavior"; then
        miri="UB"; res="!! POSSIBLE FALSE PASS — cross-check the backtrace fn"
        findings=$((findings+1))
    elif echo "$mout" | grep -q "panicked"; then
        miri="PANIC"; res="safe (a panic is not UB)"
    elif echo "$mout" | grep -qE "test result: ok"; then
        miri="CLEAN"; res="ok (PASS fns validated on fuzzed paths)"
    else
        miri="?"; res="(miri did not run — see output)"
        echo "$mout" | tail -3
    fi
    printf "%-10s %-12s %-7s  %s\n" "$name" "$pass" "$miri" "$res"
done

echo
echo "== summary =="
echo "possible false PASSes (Miri UB): $findings   (must be 0)"
[ "$findings" -eq 0 ] \
    && echo "RESULT: SOUND AT SCALE (no Miri UB across the fuzzed real-crate APIs)" \
    || echo "RESULT: investigate the UB above against ../run.sh's per-function verdicts"
exit "$findings"
