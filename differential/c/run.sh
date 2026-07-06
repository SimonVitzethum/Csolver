#!/usr/bin/env bash
# Differential validation for C: CSolver (static) vs AddressSanitizer+UBSan
# (dynamic) over the corpus in corpus.c.
#
#   sanitizer UB + CSolver PASS   -> SOUNDNESS VIOLATION (a false PASS; must be zero)
#   sanitizer UB + CSolver !PASS  -> sound (caught as FAIL, or honestly UNKNOWN)
#   sanitizer clean + CSolver PASS  -> precise
#   sanitizer clean + CSolver !PASS -> precision miss (UNKNOWN on safe)
#
# The C soundness oracle is AddressSanitizer (heap/stack overflow, use-after-free,
# double-free) + UndefinedBehaviorSanitizer (array-index bounds, overflow, alignment)
# — the C analogue of Miri. Each driver FUZZES its input across a range that spans
# the in-bounds/OOB boundary (see drive.c), so a function that is UB on a reachable
# input actually reaches it. FUZZ_CASES bounds the sweep per function.
#
# On hardened kernels ASan's shadow mapping collides with a PIE load address; `-no-pie`
# places the binary low and avoids it (see the ELF_ET_DYN_BASE issue). The build below
# uses it unconditionally — it does not affect the oracle's verdicts.
#
# Exits non-zero iff any soundness violation is found.
set -uo pipefail
DIR="$(cd "$(dirname "$0")" && pwd)"
ROOT="$(cd "$DIR/../.." && pwd)"
: "${FUZZ_CASES:=256}"
# The oracle is scoped to **memory-safety** UB: ASan (spatial + temporal) plus the
# memory subset of UBSan (out-of-bounds indexing, misalignment, null deref, pointer
# arithmetic). Arithmetic UB (signed overflow, shifts, divide-by-zero) is deliberately
# EXCLUDED — CSolver proves memory safety, not overflow-freedom, so counting it would
# manufacture false violations (see f_signed_ovf, a control that stays clean here).
SAN_FLAGS="-fsanitize=address,bounds,alignment,null,pointer-overflow,object-size -fno-sanitize-recover=all -no-pie"

# --selftest: positive-control the violation detector, so a reported "0 violations"
# cannot be a broken metric. Feed the classifier a synthetic (CSolver=PASS,
# oracle=UB) row and assert it is flagged; a clean row must not be.
if [ "${1:-}" = "--selftest" ]; then
    classify() { # $1=cs $2=san -> "VIOLATION" | "ok"
        if [ "$2" = "UB" ] && [ "$1" = "PASS" ]; then echo VIOLATION; else echo ok; fi
    }
    fail=0
    [ "$(classify PASS UB)" = "VIOLATION" ] || { echo "selftest: UB+PASS not flagged"; fail=1; }
    [ "$(classify UNKNOWN UB)" = "ok" ]     || { echo "selftest: UB+UNKNOWN misflagged"; fail=1; }
    [ "$(classify PASS CLEAN)" = "ok" ]     || { echo "selftest: CLEAN+PASS misflagged"; fail=1; }
    [ "$fail" -eq 0 ] && echo "selftest: OK (violation detector fires exactly on UB+PASS)"
    exit "$fail"
fi

echo "== building the solver CLI =="
(cd "$ROOT" && cargo build -q -p csolver-cli) || { echo "build failed"; exit 2; }
SOLVER="$ROOT/target/debug/solver"

echo "== CSolver: verifying the corpus (clang -O0 -g -emit-llvm) =="
clang -O0 -g -emit-llvm -S "$DIR/corpus.c" -o "$DIR/corpus.ll" 2>/dev/null \
    || { echo "clang emit-llvm failed"; exit 2; }
CS_OUT="$("$SOLVER" verify "$DIR/corpus.ll" 2>&1)"

# Corpus entries = the `f_*` definitions in corpus.c.
FNS=$(grep -oE '^int64_t f_[a-z_]+' "$DIR/corpus.c" | sed 's/int64_t //')

verdict() { echo "$CS_OUT" | grep -E "fn $1 :" | grep -oE 'PASS|FAIL|UNKNOWN' | head -1; }

echo "== building the sanitizer driver (ASan+UBSan, -no-pie) =="
clang -O0 -g $SAN_FLAGS "$DIR/corpus.c" "$DIR/drive.c" -o "$DIR/drive" 2>/dev/null \
    || { echo "sanitizer build failed"; exit 2; }

echo "== ASan+UBSan: fuzzing each function ($FUZZ_CASES cases) =="
violations=0; precise=0; miss=0; sound_caught=0
printf "%-20s %-9s %-7s  %s\n" "function" "CSolver" "Sanitizer" "result"
printf -- "------------------------------------------------------------\n"
for fn in $FNS; do
    cs="$(verdict "$fn")"; [ -z "$cs" ] && cs="(none)"
    sout="$("$DIR/drive" "$fn" "$FUZZ_CASES" 2>&1)"; code=$?
    if echo "$sout" | grep -qiE "runtime error|ERROR: AddressSanitizer"; then
        san="UB"
    elif [ "$code" -ne 0 ]; then
        san="CRASH"   # a non-sanitizer abort — treat as unsafe, not a false-PASS oracle
    else
        san="CLEAN"
    fi

    if [ "$san" = "UB" ] && [ "$cs" = "PASS" ]; then
        res="!! SOUNDNESS VIOLATION (false PASS)"; violations=$((violations+1))
    elif [ "$san" = "UB" ] || [ "$san" = "CRASH" ]; then
        res="ok (UB caught / unknown)"; sound_caught=$((sound_caught+1))
    elif [ "$cs" = "PASS" ]; then
        res="ok (precise)"; precise=$((precise+1))
    else
        res="~ precision miss (unknown on safe)"; miss=$((miss+1))
    fi
    printf "%-20s %-9s %-7s  %s\n" "$fn" "$cs" "$san" "$res"
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
