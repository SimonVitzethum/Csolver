# Verification — csolver-mir

## Design
A pure-Rust frontend that lowers a practical subset of **textual Rust MIR**
(`rustc --emit=mir` / `-Zunpretty=mir`) into MSIR — no `rustc` linkage, mirroring
how `csolver-llvm` consumes `.ll` text. A lexer tokenises MIR (locals `_N`,
blocks `bbN`, `->`/`=>` arrows, ints with `_` separators and type suffixes,
strings); a parser builds a small AST (params, blocks, statements, terminators,
rvalues, places, types); a lowerer emits `csolver_ir` instructions and per-
parameter region contracts.

## Why MIR (the value over LLVM-IR)
MIR makes the **bounds/overflow checks rustc inserts explicit**: a slice/array
index `s[i]` is preceded by `assert(Lt(i, len), "index out of bounds…") ->
[success: bbN, …]`. The lowering turns that `assert` into a `CondBr` whose
**success edge carries the guard** and whose failure edge diverges to an
`unreachable` panic landing pad. So the indexed load in the success block is
*proved* in bounds precisely because the check is present — and the same index
**without** the assert is correctly **not** proved (`mir_unchecked_index_is_not_pass`).

## Supported subset
- **Types**: `iN`/`uN`/`isize`/`usize` (128-bit modelled at 64), `bool`, `()`,
  `&T`/`&mut T`, `*const T`/`*mut T`, `[T; N]`, `[T]` (element only).
- **Parameters**: a sized reference (`&[T; N]`, `&T`, `&mut T`) becomes a region
  contract (`Bytes(size)`, alignment, `writable` only for `&mut`/`*mut` — so a
  write through `&T` is soundly not provable); a scalar parameter is a register.
- **Places**: `_N`, `(*_N)`, `(*_N)[_M]` (→ `PtrOffset` + `Load`/`Store`); a
  `Field` projection is opaque.
- **Rvalues**: `Use`/`copy`/`move`/`const`, the integer binops and comparisons
  (`Lt`/`Le`/… as **unsigned** — index/length checks are over `usize`),
  `Len(&[T; N])` → the constant `N`, `&place` (element address / inner pointer),
  `as` casts (value-preserving).
- **Terminators**: `goto`, `return`, `switchInt` (→ `CondBr`/`Switch`),
  `assert` (→ guarded `CondBr` + panic pad), `unreachable`.

## Soundness (refinement obligation)
Every concrete MIR execution must be a concrete MSIR execution. The mapping is
local and conservative; in particular:
- the `assert` **only adds** a guard on the success path (the panic path
  diverges), so it never weakens an obligation — it strengthens the success path
  exactly as rustc's runtime check does;
- an unmodelled terminator (`call`, `drop`, `yield`), rvalue, or unsized-slice
  length is **surfaced**: the affected function is recorded in `Module.unanalyzed`
  and reported `UNKNOWN` (per-function recovery), never mis-lowered into a
  sound-looking shape;
- comparisons are lowered unsigned, matching the `usize` index/length domain;
- a reference parameter is `writable` only when `&mut`/`*mut`.

## Limits (this increment)
- **Slices `&[T]`** (symbolic length) are not yet given a region: `Len((*_1))`
  on a slice is opaque, so slice-indexing functions stay `UNKNOWN`. Fixed arrays
  `&[T; N]` (concrete length) are fully modelled. (A later increment threads the
  slice length the way `Len` exposes it.)
- **Calls/drops** reject the function (no interprocedural lowering yet).
- **Aggregates/fields**, checked-arithmetic tuples, and constant-index
  projections are opaque.
- Integer constants are lowered at 64-bit width.

## Test strategy
Unit test: the `get(&[i32; 8], usize)` body parses and lowers to a `PtrOffset` +
`Load` under a contracted parameter. End-to-end (`csolver-testsuite/tests/
mir_frontend.rs`): the checked index verifies **PASS** (with the `param-contracts`
assumption), the unchecked index is **not** proved, and a call-using function is
recovered as `UNKNOWN` while a sound sibling still verifies. Next: a real
multi-block `rustc --emit=mir` corpus and slice-length modelling.
