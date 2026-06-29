# Aggregation logic for the scaling sweep, factored out so the positive-control
# self-test (`selftest.sh`) exercises the *same* code the real run uses.
#
# Why this file exists at all: a grep/sed pipeline is part of the measurement, and
# an untested one already cost this project four rounds of a phantom "empty bucket"
# — the per-obligation aggregation anchored on the `UNKNOWN PO …` line with
# `grep -A1`, which lands on the `predicate:` line (the `residual:` is one line
# *further* down), so it counted zero residuals every sweep and made the whole
# bucket look empty. A broken filter and a real zero are indistinguishable from the
# output alone; the only defence is a positive control that feeds a *known* line in
# and asserts it lands in the right bucket. See `selftest.sh`.

# Frontend gaps: a parse/lowering error that loses a whole function before the
# analysis runs. One line per loss; normalise concrete identifiers/integers so they
# bucket.
agg_frontend() {
    grep -oE "not analyzed by the frontend: [^)]*" "$1" \
        | sed -E "s/found Punct\('(.)'\)/found '\1'/; s/found \`[^\`]*\`/found <ident>/; \
                  s/found Word\(\"[^\"]*\"\)/found <word>/; s/[0-9]+/N/g" \
        | sort | uniq -c | sort -rn
}

# Per-obligation residuals: the function was analysed but a check is unproven.
# Bucket by the residual's parenthetical *root cause* — the missing capability
# (provenance, loop/symbolic depth, nullness) — not the obligation kind, which only
# says which check tripped. Match the `residual:` line DIRECTLY: it sits two lines
# below the `UNKNOWN PO` anchor, so any context-line trick keyed off that anchor
# silently miscounts. The frontend-gap residuals (whole-function losses) are counted
# by `agg_frontend`, so they are excluded here.
agg_residual() {
    grep -E "residual:" "$1" \
        | grep -v "not analyzed by the frontend" \
        | sed -E "s/.*residual: [^(]*\((.*)\)$/\1/" \
        | sed -E "s/_[0-9]+/_N/g; s/[0-9]+/N/g" \
        | sort | uniq -c | sort -rn
}
