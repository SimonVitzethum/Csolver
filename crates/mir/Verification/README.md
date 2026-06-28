# Verification — csolver-mir

## Design
Rust MIR → MSIR frontend (M5). Richest input: borrow facts, panic edges, and
precise types sharpen the obligations and let CSolver attach extra checks.

## Specification (target)
- Refinement: every concrete MIR execution is a concrete MSIR execution.
- Borrow/aliasing facts become `NoForbiddenOverlap`/`ValidReference` checks;
  panic terminators become explicit edges (not silently dropped).

## Assumptions
- MIR is consumed from a fixed `rustc` version (stable-MIR or a driver callback);
  the MIR→MSIR table is versioned with it.

## Limits
- M0 is interface-only (`lower` → `Unsupported`).
- `unsafe` blocks lower like any other code; their obligations are *not* assumed
  away — that is the whole point.

## Proofs (arguments)
- Refinement argued per MIR statement/terminator; borrow-derived checks are
  additive (they can only tighten, never loosen, the verdict).

## Test strategy
Planned: lower real `unsafe` crates and compare obligations against MIRI-observed
UB on a corpus (M5).
