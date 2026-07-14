# Verification — csolver-llvm

## Design
A pure-Rust frontend that parses a practical subset of textual LLVM IR (`.ll`)
and lowers it to MSIR, so the audited analysis core verifies compiled Rust
unchanged. Three stages: `lexer` (tokens), `parser` (→ AST), `lower` (AST →
MSIR). The one structural transformation is **PHI elimination**: each block's
leading `phi` nodes become MSIR block parameters and every in-edge supplies the
matching incoming values as branch arguments.

Recognized library/kernel calls (allocators, deallocators, `copy_from_user`,
`copy_to_user`, provenance-labelling primitives) are lowered from **external,
file-driven contracts** (`csolver-contracts`, `data/*.contract`) rather than
hardcoded name tables: `emit_contract` turns a contract's effects into the
modelling MSIR (`Alloc`/`Dealloc`/`MemIntrinsic`/`ProvLabel`/`CapRequire`). A
`read … sink=user` effect (`copy_to_user`) lowers to `MemKind::UserDrain`. A new
API is a contract block, not a match arm.

**Constant-initializer devirtualization tables.** For a `constant` global, the
parser walks its initializer and records every `ptr @func` field with its exact
byte offset (padded struct/array layout, LP64 — matching the executor's gep). The
lowering keeps the fields whose target is a function defined in the module in
`Module::global_fn_ptrs`, so an indirect call loaded from an ops-struct/vtable
global can be devirtualized. The whole table is dropped on any layout-tracking
uncertainty (an imprecise offset would be unsound; a missed field only lowers
recall).

## Supported subset
`define`d functions; `void`/`iN`/`ptr`/`[N x T]` types (and legacy `T*`);
`alloca`, `load`, `store`, `getelementptr` (pointer-arith and `[N x T]` array
forms), the integer binary ops, `icmp`, the integer/pointer casts, `call`,
`phi`; and `ret`/`br`/`switch`/`unreachable`.

## `switch` (multi-way dispatch)
A `switch iN %v, label %def [ iN c₀, label %d₀ … ]` (Rust `match` / enum
discriminant) lowers to MSIR's native `Terminator::Switch` — the scrutinee, the
`(cⱼ, dⱼ)` case pairs, and the default. The analysis core treats each case as an
**exact** edge guard (`%v == cⱼ`) and the default as a **sound
over-approximation** (it is explored without the `%v ∉ {cⱼ}` condition, i.e. a
weaker path condition — never unsound). MSIR `Switch` carries no per-target
arguments, so a case/default block that has `phi`s referencing the switch block
receives **fresh** (havoc'd) parameters — again a sound over-approximation, and
precise for the common discriminant dispatch whose arms have no such `phi`s.

## Specification (refinement obligation)
The lowering must over-approximate LLVM semantics: every concrete `.ll`
execution is a concrete MSIR execution. The mapping is opcode-local —
`alloca`→`Alloc(Stack)`, `getelementptr`→`PtrOffset`, `load`/`store`→the
explicit memory ops (which the verifier turns into the canonical obligations),
`icmp`/binops/casts→`Assign`, `call`→`Call`, PHIs→block parameters/arguments.

## Real `rustc` output
The parser tolerates the surrounding shape of `rustc --emit=llvm-ir`: line
comments, `source_filename`/`target …` directives, mangled names, function and
parameter attributes (`unnamed_addr`, `#0`, `noundef`, `dereferenceable(32)`,
`captures(none)`, …), return attributes (`define noundef i32 …`), `getelementptr
inbounds nuw`, per-instruction metadata (`, !dbg !N`), `; preds = …` label
comments, the `attributes #N = { … }` block, and the trailing `!…` metadata
section — all skipped or stripped. Pointer-parameter attributes are *imported*
as `PtrContract`s: `dereferenceable(N)`/`align`/`readonly`/`writeonly` make a
parameter a known live region of N bytes (under the `param-contracts`
assumption). A real `rustc -O` function taking `&mut [i32; 8]`
(`ptr … dereferenceable(32) %buf`) and writing `buf[i]` under `i <u 8` now
verifies fully **PASS**; writing through a `readonly` parameter is correctly
*not* proved.

**`nonnull` (non-null-only) and cross-language coverage.** A `nonnull` pointer
parameter *without* a `dereferenceable` size (Zig `*T`, and any frontend that
asserts non-null but not a size) becomes a `SizeSpec::NonNull` contract — a
non-null **opaque** pointer, not a region: only `NoNullDeref` is discharged through
it (and gep/copy-derived pointers), while bounds/liveness stay `UNKNOWN` (a
`nonnull` pointer may still dangle). The `dereferenceable`/`nonnull` attribute paths
are **language-independent** and LLVM-semantics-sound, so they cover any LLVM
frontend: verified against real **Zig** 0.16 (`*T` ⇒ `ptr nonnull`, `?*T` ⇒ not) and
**Julia** 1.12 (`swiftcc` + `nonnull dereferenceable(N)` GC arrays); the same path
covers **Swift**'s ABI. The DWARF path (`crates/elf` / `debuginfo.rs`) recovers
per-language *reference* pointees (`&T` for Rust, `T&` for C++/D) as a secondary
source; see `tests/dwarf-corpus`.

**Slices.** An aligned pointer parameter immediately followed by an integer is
recognized as the Rust slice ABI `&[T]` `(ptr, usize len)`; its region size is
the symbolic `len * size_of::<T>()` (element size taken from a `getelementptr`
on it), under the `slice-abi` assumption. So a real `rustc`
`get(s: &[i32], i) -> if i < s.len() { s[i] }` verifies **PASS**; an *unguarded*
slice index is correctly *not* proved. **Index-based loops** over a slice
(`while i < s.len() { … s[i] … }`) also verify **PASS**: the loop invariant
`i >= 0`, the guard `i < len`, and the slice contract combine to prove every
iteration's access (a real `rustc -C opt-level=0` `sum_indexed` with its
`panic_bounds_check` machinery verifies, 51/51).

The fully-*optimized* iterator form `for x in s` instead lowers to a vectorized
**pointer-walking** loop terminated by an end-pointer comparison (`iter != end`).
That needs a relational pointer-offset domain *plus* congruence/modular
reasoning (the `!=` guard) — genuinely advanced — so it stays `UNKNOWN` (never a
false PASS).

## Vectors and intrinsics (for `-O` output)
`-O` vectorizes small array initializers into `<4 x i32>` stores and brackets
stack slots with `llvm.lifetime` markers. Vector types/constants are parsed and
modelled by their byte footprint (an `i32x4` store is a 16-byte access);
`llvm.lifetime`/`llvm.dbg`/`llvm.assume`/`llvm.invariant` calls are no-ops (they
do not touch caller-visible memory, so unlike an opaque call they must *not*
invalidate the heap/region state). A real `rustc -O` function that builds a
local `[i32; 8]` via vector stores and reads `buf[i]` under a guard verifies
fully **PASS**.

**Bulk memory.** `llvm.memcpy`/`llvm.memmove`/`llvm.memset` lower to an
`Inst::MemIntrinsic`: the destination must be writable and in bounds for `len`
bytes and (for copy/move) the source readable and in bounds for `len` bytes. A
real `rustc -O` `*dst = *src` over `&mut [u8; 16]` / `&[u8; 16]` (a 16-byte
`memcpy`) verifies **PASS**; copying past a region's size is correctly not
proved.

## Assumptions / limits
- **Sound by construction on unsupported input:** anything still outside the
  subset (exceptions/`invoke`, `select`, `indirectbr`, `extractvalue`/aggregates,
  multi-index/struct GEPs, named struct types) is reported as `Unsupported`, so
  the caller degrades to `UNKNOWN` — never silently mis-modelled into a `PASS`.
- **Per-function recovery:** a function with an unsupported construct does not
  fail the whole module — it is skipped during parsing/lowering and recorded in
  `Module.unanalyzed`, which the verifier reports as a dedicated `UNKNOWN`
  function (never a silent omission). So a whole `rustc -O` `.ll` verifies the
  functions it can and honestly marks the rest `UNKNOWN`.
- Pointer element/alignment come from the instruction, matching LLVM's typed
  memory operations; the data layout is LP64.

## Proofs (arguments)
Per-opcode lowering is small and inspectable; PHI elimination is the only
non-local step and is validated end-to-end: a guarded `[8 x i32]` store, a
`phi`-based `for i in 0..16` loop, and an out-of-bounds store all verify to the
expected verdict (`csolver-testsuite/tests/llvm_frontend.rs`). The
fully-optimized iterator loop — `rustc -O`'s rotated **pointer walk** (`phi ptr`
header, `getelementptr` step, pointer `icmp eq … %end`) over a `&[i32]` slice —
also lowers and verifies **PASS** unchanged, with the analysis recognising it as
a pointer-induction loop; its unguarded variant is correctly not proved. So the
lowering carries a real compiled iterator all the way to a sound verdict.
Per-opcode differential testing against `lli`-observed behaviour is the next
hardening.

## Test strategy
Unit tests for the lexer and parser; end-to-end `.ll` → verify tests in
`csolver-testsuite`. Next: broaden the subset toward raw `rustc` output (auto
-numbering, metadata stripping) and add a `.ll` corpus.
