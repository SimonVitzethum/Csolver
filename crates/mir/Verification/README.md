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
  write through `&T` is soundly not provable); a **slice** `&[T]` becomes a
  pointer plus a synthetic `usize` length parameter and a `ParamElements`
  contract (region size `len · elem`), with `Len((*_1))` resolving to that length
  — the same slice ABI the analysis already models; a scalar parameter is a
  register.
- **Places**: `_N`, `(*_N)`, `(*_N)[_M]` (→ `PtrOffset` + `Load`/`Store`); a
  `Field` projection is opaque.
- **Rvalues**: `Use`/`copy`/`move`/`const`, the integer binops and comparisons
  (`Lt`/`Le`/… as **unsigned** — index/length checks are over `usize`), `Len(&[T;
  N])` → the constant `N` and `PtrMetadata(slice_ref)` → the synthetic slice
  length (modern rustc emits `PtrMetadata`, not `Len`), `&place` (element
  address / inner pointer), `as` casts (value-preserving); checked-arithmetic
  (`AddWithOverflow`, …) and other aggregate rvalues are opaque.
- **Checked arithmetic** (`AddWithOverflow`/`SubWithOverflow`/…) is modelled by
  its result: field `.0` of the `(result, overflow)` tuple becomes the actual
  `a ± b`, so a checked value used downstream keeps its meaning; the `.1`
  overflow flag stays opaque (it only feeds the overflow `assert`).
- **Places** also tolerate a variant downcast (`(_5 as Some)`), a type ascription
  (`(_11.1: bool)`, `(*_1: &[i32])`), and a borrow-kind annotation (`&raw const
  (fake) (*_1)`).
- **Terminators**: `goto`, `return`, `switchInt` (→ `CondBr`/`Switch`),
  `assert` (→ guarded `CondBr` + panic pad), the assignment-form **call**
  `_d = f(args) -> [return: bb, …]` (→ an MSIR `Call` + a `Br` to the return
  block; the callee resolves to `Direct` for an in-module function, else
  `Symbol`/`Indirect`), and `unreachable`.

## Soundness (refinement obligation)
Every concrete MIR execution must be a concrete MSIR execution. The mapping is
local and conservative; in particular:
- the `assert` **only adds** a guard on the success path (the panic path
  diverges), so it never weakens an obligation — it strengthens the success path
  exactly as rustc's runtime check does;
- a **call** lowers to an MSIR `Call`, on whose return edge the verifier applies
  the callee's summary (`Direct`) or havocs an unknown/external one (`Symbol`/
  `Indirect`) — both sound; the call's **unwind** edge (cleanup) is not analysed,
  which is incomplete but never unsound for the return path;
- **no memory access is ever silently dropped** (which would be an unsound
  vacuous `PASS`): a deref/index whose element type is unknown still emits the
  access through its real pointer with a one-byte fallback (so an opaque pointer
  — e.g. a `get_unchecked` result — yields `UNKNOWN`, not `PASS`); a memory
  access whose pointer cannot be recovered at all (a field through a pointer
  without struct layout, a double-deref) **rejects the whole function**
  (`UNKNOWN`);
- an unmodelled terminator (`drop`, `yield`), rvalue, or place is **surfaced**:
  the affected function is recorded in `Module.unanalyzed` and reported `UNKNOWN`
  — at **both** the parse and the lower stage (a body that fails to parse does
  not abort the module: parsing resumes at the next `fn`), never mis-lowered;
- a slice's synthetic length flows through pointer copies/borrows (`_4 = &raw
  const (*_1); PtrMetadata(_4)`), so a checked write `s[i] = v` is proved too;
- comparisons are lowered unsigned, matching the `usize` index/length domain;
- a reference parameter is `writable` only when `&mut`/`*mut`.

## Limits (this increment)
- **Drops** reject the function; a call's **unwind/cleanup** path is not analysed
  (the return path is); call **return types** default to a 64-bit scalar (local
  decls are not yet parsed for the dst type).
- **Struct field accesses through a pointer** (`(*_1).f`) and the
  **iterator/enum-downcast** shape (`for x in s`) are `UNKNOWN` (the former needs
  struct layout, absent from the MIR text; the latter needs enum-variant
  modelling).
- A **nested** index (`m[i][j]`) is `UNKNOWN` (the inner index needs the
  element-stride relation the model does not yet carry).
- The aggregate field accessed must be `.0` of a checked-arithmetic tuple;
  general struct/tuple fields and constant-index projections are opaque.
- Integer constants are lowered at 64-bit width.

## Test strategy
Unit tests: the `get(&[i32; 8], usize)` body parses and lowers to a `PtrOffset` +
`Load` under a contracted parameter; a checked `AddWithOverflow` result is
modelled as a real `Add` and forwarded by `move (_3.0)`. End-to-end
(`csolver-testsuite/tests/
mir_frontend.rs`): the checked array index verifies **PASS** (`param-contracts`);
a checked **slice** index `get(&[i32], usize)`, an index-based slice **loop**
`for i in 0..s.len() { s[i] }`, a mutable-slice **fill** loop, and the last-element
idiom `s[len - 1]` all verify **PASS** (`slice-abi`); the unchecked index
is **not** proved; an **interprocedural** module (`caller` calling a checked
`helper`) lowers the call to a `Direct` MSIR `Call` and verifies **PASS** via the
helper's summary, while a dereference of an **external** call's unknown result is
not proved; and a `drop`-using function is recovered as `UNKNOWN` while a sound
sibling still verifies. **Real-output validation**: two functions captured
verbatim from `rustc 1.94.1 --emit=mir`: a slice `get`/`write_slice`, a
debug-build `sum` loop (with `AddWithOverflow` tuples, type-ascribed field
places, `switchInt`, nested `scope`s), and — for soundness — an
`unsafe get_unchecked` deref that is correctly **not** proved. Validating against
genuine compiler output surfaced and fixed the `copy (place)` prefix, the `(_n:
T)` / `(x as Variant)` place forms, the `&raw const (fake)` borrow, `assume`, and
crucially the **silently-dropped-memory-access** soundness hole. Next: struct
layout for field accesses, the iterator/enum-downcast shape, and a larger corpus.
