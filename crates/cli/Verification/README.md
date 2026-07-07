# Verification — csolver-cli

## Design
The `solver` binary: input detection, frontend dispatch, verification, and
text/JSON reporting. Exit codes encode the verdict (0/1/2) or tool error (3).

## Specification
- `verify <path>` selects the frontend by extension/ELF magic; a frontend that
  cannot lower is a **tool error** (exit 3), not a verdict. Flags: `--closed-world`,
  `--bugs`, `--assume-valid-params`, `--pre <file>`, `--json`.
- `scan <dir>` verifies **every** `.ll` under a tree without stopping at any
  UNKNOWN/FAIL, then prints every memory-safety violation (file::function,
  property, genuine-input witness) and a **coverage** breakdown (PASS/FAIL/UNKNOWN
  %, decided = PASS+FAIL, dropped). Exits `1` iff any bug was found (an inventory,
  not one verdict). Respects `--bugs` / `--assume-valid-params` / `--closed-world`.
- `demo` verifies a built-in MSIR module to exercise the whole pipeline offline.
- Exit codes: `PASS=0`, `FAIL=1`, `UNKNOWN=2`, tool error `=3`.

## Assumptions
- The caller treats exit codes as authoritative for CI gating.

## Limits
- M0: `verify` reaches only stub frontends; `report` (re-render saved JSON) is
  not implemented. `demo` is the working end-to-end path.

## Proofs (arguments)
- The CLI performs no analysis itself; it cannot affect soundness, only routing
  and presentation. Verdict→exit-code mapping is total and tested via `demo`.

## Test strategy
Manual/CI smoke: `solver demo` must print a PASS proof, a FAIL counterexample,
an UNKNOWN residual, and exit non-zero. Integration tests for argument handling
planned (M1).
