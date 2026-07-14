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
    classify() { # $1=cs $2=san -> "VIOLATION" | "FALSEPOS" | "ok"
        if [ "$2" = "UB" ] && [ "$1" = "PASS" ]; then echo VIOLATION
        elif [ "$2" = "CLEAN" ] && [ "$1" = "FAIL" ]; then echo FALSEPOS
        else echo ok; fi
    }
    fail=0
    [ "$(classify PASS UB)" = "VIOLATION" ]  || { echo "selftest: UB+PASS not flagged"; fail=1; }
    [ "$(classify FAIL CLEAN)" = "FALSEPOS" ] || { echo "selftest: CLEAN+FAIL not flagged as false positive"; fail=1; }
    [ "$(classify UNKNOWN UB)" = "ok" ]      || { echo "selftest: UB+UNKNOWN misflagged"; fail=1; }
    [ "$(classify PASS CLEAN)" = "ok" ]      || { echo "selftest: CLEAN+PASS misflagged"; fail=1; }
    [ "$(classify FAIL UB)" = "ok" ]         || { echo "selftest: UB+FAIL misflagged"; fail=1; }
    [ "$fail" -eq 0 ] && echo "selftest: OK (violation on UB+PASS, false-positive on CLEAN+FAIL)"
    exit "$fail"
fi

# `--bugs` runs CSolver in bug-finding mode (higher recall, so more FAILs; the
# CLEAN+FAIL = false-positive column is the thing to watch there).
SOLVER_FLAGS=""
MODE="verify (strict)"
if [ "${1:-}" = "--bugs" ]; then SOLVER_FLAGS="--bugs"; MODE="bug-finding (--bugs)"; fi

echo "== building the solver CLI =="
(cd "$ROOT" && cargo build -q -p csolver-cli) || { echo "build failed"; exit 2; }
SOLVER="$ROOT/target/debug/solver"

echo "== CSolver: verifying the corpus (clang -O0 -g -emit-llvm) =="
clang -O0 -g -emit-llvm -S "$DIR/corpus.c" -o "$DIR/corpus.ll" 2>/dev/null \
    || { echo "clang emit-llvm failed"; exit 2; }
CS_OUT="$("$SOLVER" verify "$DIR/corpus.ll" $SOLVER_FLAGS 2>&1)"

# Corpus entries = the `f_*` definitions in corpus.c.
FNS=$(grep -oE '^int64_t f_[a-z_]+' "$DIR/corpus.c" | sed 's/int64_t //')

verdict() { echo "$CS_OUT" | grep -E "fn $1 :" | grep -oE 'PASS|FAIL|UNKNOWN' | head -1; }

echo "== building the sanitizer driver (ASan+UBSan, -no-pie) =="
clang -O0 -g $SAN_FLAGS "$DIR/corpus.c" "$DIR/drive.c" -o "$DIR/drive" 2>/dev/null \
    || { echo "sanitizer build failed"; exit 2; }

echo "== ASan+UBSan: fuzzing each function ($FUZZ_CASES cases) — CSolver mode: $MODE =="
# The property names CSolver reports for the arithmetic UB this oracle deliberately
# EXCLUDES (signed overflow, shifts, divide-by-zero — see SAN_FLAGS). A CSolver FAIL whose
# failing obligations are *only* these is an arithmetic-overflow finding out of this
# memory-safety benchmark's scope, not a memory-safety false positive. `--bugs` enables the
# exact-path refutation for `no_arith_overflow`, so f_signed_ovf (a genuine `x+2` past
# INT64_MAX) legitimately FAILs there while the memory-scoped sanitizer stays CLEAN.
ARITH_PROPS="no_arith_overflow no_shift_overflow no_div_by_zero"
# True iff every failing obligation of function $1 is an excluded-arithmetic property.
fail_is_arith_only() {
    local props; props="$(echo "$CS_OUT" | awk -v fn="$1" '
        $0 ~ "fn "fn" :" {inb=1; next}
        inb && /^  fn / {inb=0}
        inb && /FAIL PO/ { if (match($0, /\[[a-z_]+\]/)) print substr($0, RSTART+1, RLENGTH-2) }
    ')"
    [ -z "$props" ] && return 1
    local p
    for p in $props; do
        case " $ARITH_PROPS " in *" $p "*) ;; *) return 1;; esac
    done
    return 0
}

violations=0; false_pos=0; precise=0; miss=0; bug_found=0; sound_miss=0; arith=0
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
    elif [ "$san" = "CLEAN" ] && [ "$cs" = "FAIL" ] && fail_is_arith_only "$fn"; then
        res="ok (arithmetic-overflow FAIL — out of memory-safety scope)"; arith=$((arith+1))
    elif [ "$san" = "CLEAN" ] && [ "$cs" = "FAIL" ]; then
        res="!! FALSE POSITIVE (false FAIL on safe code)"; false_pos=$((false_pos+1))
    elif [ "$san" = "UB" ] || [ "$san" = "CRASH" ]; then
        if [ "$cs" = "FAIL" ]; then
            res="ok (BUG FOUND — FAIL + witness)"; bug_found=$((bug_found+1))
        else
            res="ok (UB unknown — sound but missed)"; sound_miss=$((sound_miss+1))
        fi
    elif [ "$cs" = "PASS" ]; then
        res="ok (precise)"; precise=$((precise+1))
    else
        res="~ precision miss (unknown on safe)"; miss=$((miss+1))
    fi
    printf "%-20s %-9s %-7s  %s\n" "$fn" "$cs" "$san" "$res"
done

echo
echo "== summary ($MODE) =="
echo "soundness violations (false PASS): $violations   (must be 0)"
echo "false positives      (false FAIL): $false_pos   (must be 0)"
echo "bugs FOUND (FAIL + witness)      : $bug_found"
echo "UB sound-but-missed  (UNKNOWN)   : $sound_miss"
echo "safe & precise (PASS)            : $precise"
echo "safe & unknown                   : $miss"
echo "arith-overflow FAIL (out of scope): $arith   (real UB the oracle excludes, not a false FAIL)"
bad=$((violations + false_pos))
[ "$bad" -eq 0 ] && echo "RESULT: SOUND (no false PASS, no false FAIL on this corpus)" \
                 || echo "RESULT: UNSOUND — $violations false PASS, $false_pos false FAIL"
exit "$bad"
