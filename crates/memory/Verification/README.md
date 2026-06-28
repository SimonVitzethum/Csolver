# Verification — csolver-memory

## Design
A symbolic memory model: `Region`s (kind, size, align, permissions, lifetime)
owned by a `MemoryModel`, and `Pointer`s (`Provenance` + `SymOffset` + align).
`check_access` reduces an access to per-property `CheckOutcome`s.

## Specification
For an access through pointer `p` of `size`/`align`/permissions:
- **NoNullDeref**: `Violated` iff `p.provenance = Null`.
- **NoUseAfterFree**: `Proven` iff region `Live`; `Violated` iff `Freed`/`Uninit`.
- **InBounds**: with concrete offset `o` and size `s`, `Proven` iff
  `0 ≤ o ∧ o+size ≤ s`, else `Violated`; symbolic ⇒ `Residual`.
- **Alignment**: `Proven` iff `p.align % access.align = 0`; concrete-but-short ⇒
  `Violated`; symbolic offset ⇒ `Residual`.
- **ValidRead/Write**: `Violated` iff the region lacks the permission.
- `deallocate`: `Live→Freed` `Proven`; `Freed`/`Uninit` ⇒ `Violated` (double free).

## Assumptions
- Region base addresses are aligned to `region.align`.
- Offsets are byte offsets from the region base (provenance-respecting).

## Aliasing
[`AliasResult`] (`Must`/`May`/`No`) is the shared vocabulary for whether two
accesses overlap. The enum lives here (the memory-model home); the *decision*
(which needs the path condition and the solver) is made in `csolver-symbolic`'s
`alias_check`. Distinct allocations never alias; within one allocation it is
decided by proving offset equality (Must) or range-disjointness (No), else May.

## Limits
- Inter-region aliasing/overlap (`NoForbiddenOverlap`) at the access-checking
  level is not decided here yet; it needs the address-assignment model.
- `Provenance::Unknown` (from int→ptr) always yields `Residual` — never `Proven`.

## Proofs (arguments)
- **No false `Proven`.** `Proven` is emitted only on concrete, decided
  quantities; every unknown path yields `Residual` or a `Violated`. Hence a
  `Proven` outcome is a genuine over-approximation-safe fact. Covered by the
  symbolic-offset and unknown-provenance tests.
- **Alignment via gcd.** `Pointer::offset_bytes` reduces the guaranteed
  alignment to `gcd(base_align, |delta|)`, never overstating it.

## Test strategy
Unit tests for in-bounds pass/fail, null deref, use-after-free + double free,
misalignment, read-only write, and symbolic⇒residual. Property tests over random
allocations/offsets are planned (M2).
