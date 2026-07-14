# Verification — csolver-cli

## Design
The `solver` binary: input detection, frontend dispatch, verification, and
text/JSON reporting. Exit codes encode the verdict (0/1/2) or tool error (3).

## Specification
- `verify <path>` selects the frontend by extension/magic: `.rs` (turnkey rustc→MIR),
  `.mir`, `.ll`, `.s`, an **object file** (ELF / PE-COFF / Mach-O, via `load_object`),
  or a **container** (`.iso` ISO 9660, `.wim` WIM) which is unpacked and each object file
  inside verified (worst-verdict aggregated). A frontend that cannot lower is a **tool
  error** (exit 3), not a verdict. Flags: `--closed-world`, `--bugs`,
  `--assume-valid-params`, `--aliasing-model` (opt-in Rust borrow-stack), `--pre <file>`,
  `--json`.
- `scan <dir>` verifies **every** `.ll` under a tree without stopping at any
  UNKNOWN/FAIL, then prints every memory-safety violation (file::function,
  property, genuine-input witness) and a **coverage** breakdown (PASS/FAIL/UNKNOWN
  %, decided = PASS+FAIL, dropped). Exits `1` iff any bug was found (an inventory,
  not one verdict). Respects `--bugs` / `--assume-valid-params` / `--closed-world`.
  Runs one worker per core with reservation-based **memory backpressure**
  (`CSOLVER_JOBS=N` overrides); `--cross-file` links a directory's TUs before
  verifying; `--auto-entries` discovers syscall + ops-struct handlers as entries;
  `--entries <file>` supplies an explicit attacker-reachable entry policy. A unit
  whose exploration hits its per-function budget is **deferred** and re-scanned in
  a serial second phase with the wall-clock disabled and all threads — a resource
  limit becomes a full-effort decision, not a premature UNKNOWN (deterministic,
  results re-sorted by unit index).
- `demo` verifies a built-in MSIR module to exercise the whole pipeline offline.
- Exit codes: `PASS=0`, `FAIL=1`, `UNKNOWN=2`, tool error `=3`.

## Assumptions
- The caller treats exit codes as authoritative for CI gating.

## Limits
- The `.s` textual-assembly frontend is AT&T-x86-64 only; other syntaxes/arches
  degrade to `Unsupported`. WIM LZX/LZMS resources are skipped (reported), not decoded.

## Proofs (arguments)
- The CLI performs no analysis itself; it cannot affect soundness, only routing
  and presentation. Verdict→exit-code mapping is total and tested via `demo`.

## Test strategy
Manual/CI smoke: `solver demo` must print a PASS proof, a FAIL counterexample,
an UNKNOWN residual, and exit non-zero. Integration tests for argument handling
planned (M1).
