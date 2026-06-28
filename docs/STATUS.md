# Status

Milestone **M1 — symbolic execution + SMT (increment 1 done)**, on top of the
completed **M0 — architecture + foundations**.

## Bit-precise decision procedure (pure-Rust SAT)

`csolver-solver` now carries a self-contained **bit-precise** decision procedure
alongside the linear one — no external C/C++ solver. A bit-blaster (`bitblast`)
lowers the symbolic expression IR to CNF with exact fixed-width/wrapping
bit-vector circuits, an internal DPLL solver (`sat`) refutes it, and
`bitprecise::prove_implies` proves `assumptions ⟹ goal` exactly. The combined
`prove_implies_method` tries the fast linear procedure first, then a tight-budget
bit-precise **refinement** (a goal decided exactly is reported `BitPrecise` and
**carries no `linear-no-overflow` assumption**) and a bit-precise **fallback**
that proves goals the linear fragment cannot model — exact wrap-around and
bitwise masks. A real consequence: `buf[x & 7]` over a `[i8; 8]` verifies
**PASS** (the mask bounds the index to `[0, 7]`), which the linear procedure
alone leaves UNKNOWN. The fallback is bounded by a SAT decision budget and a CNF
size cap, so it never dominates analysis time (the whole suite still runs in
~2 s). `cargo test` = 133 green, 0 clippy/build warnings.

## Counterexamples (symbolic FAIL with a witness)

The symbolic engine can now **refute** a scalar safety check and attach a
concrete counterexample, not just prove or leave it `UNKNOWN`. On an **exact**
path (one with no loop-header havoc, opaque call, or non-determined load — so its
path condition describes genuinely reachable states), a check that is *definitely*
violated — `assumptions ⟹ ¬goal`, proved **bit-precisely** — becomes a `FAIL`
whose `Model` names the violating inputs (`bitprecise::find_counterexample`). This
mirrors the interval `False` verdict but with bit-precision: e.g. `(x | 8) < 8`,
which interval analysis cannot see through, is reported `FAIL` with a witness
(e.g. `arg0 = 0`), whereas a merely under-constrained check like an unconstrained
`i < 8` stays `UNKNOWN` (only *definite* violations are refuted, so
under-specified helpers are not turned into spurious failures). Memory-access OOB
refutation (which needs overflow/provenance-aware spatial reasoning) is a
documented follow-up; memory checks remain proof-only for now.

## First real front-end: LLVM-IR

`csolver-llvm` now **parses and lowers textual LLVM IR** (a practical subset) to
MSIR — the first input that is not hand-built. The audited analysis core is used
unchanged. `solver verify file.ll` works end-to-end: a guarded `[8 x i32]`
store, a `phi`-based `for i in 0..16` loop, and an out-of-bounds store verify to
PASS / PASS / not-PASS respectively (`tests/llvm_frontend.rs`). PHIs are lowered
to MSIR block parameters; unsupported constructs degrade to `UNKNOWN` (never a
silent PASS). The parser tolerates real `rustc --emit=llvm-ir` shape (mangled
names, attributes, metadata, `!dbg`, `; preds` comments) and **imports pointer-
parameter contracts** (`dereferenceable(N)`/`align`/`readonly`/`writeonly`): a
real `rustc -O` function taking `&mut [i32; 8]` and writing `buf[i]` under a
`i < 8` guard verifies fully **PASS** (under the `param-contracts` assumption);
a write through a `readonly` parameter is correctly not proved. **Vectors and
`llvm.lifetime`/`dbg` intrinsics** (from `-O`) are handled too: a real `rustc -O`
function that builds a local `[i32; 8]` via `<4 x i32>` vector stores and reads
`buf[i]` under a guard verifies fully **PASS**. **Per-function recovery** lets a
whole `rustc -O` `.ll` be processed: a function with an unsupported construct is
recorded and reported `UNKNOWN` rather than failing the module. On a real
4-function compiled crate, three functions verify **PASS**. **Slice parameters**
(`&[T]` = `(ptr, usize len)`) are now imported too: a real `rustc -O`
`get(s: &[i32], i) -> if i < s.len() { s[i] }` verifies **PASS** (region size =
`len * size_of::<T>()`, under the `slice-abi` assumption), while an unguarded
slice index is correctly not proved. **Index-based slice loops**
(`while i < s.len() { … s[i] … }`) verify too — a real `rustc -C opt-level=0`
`sum_indexed` (with its `panic_bounds_check` machinery) verifies fully PASS
(51/51). The fully-optimized iterator form (`for x in s`) lowers to a vectorized
**pointer-walking** loop (`iter != end`) needing a relational pointer-offset
domain + congruence reasoning — genuinely advanced — so it stays `UNKNOWN`
(never a false PASS). **Bulk memory** (`llvm.memcpy`/`memmove`/`memset`) is
checked too: a real `rustc -O` `*dst = *src` over `&mut [u8; 16]` (a 16-byte
`memcpy`) verifies **PASS** (destination writable + in bounds for `len`, source
readable + in bounds), while copying past a region's size is not proved. This is
the shortest path to verifying compiled Rust; see [ROADMAP.md](ROADMAP.md).

## Soundness audit

The discharge pipeline was audited for **false-PASS** bugs (the only fatal
defect for a verifier). Five were found and fixed, each with a regression test;
see [AUDIT.md](AUDIT.md). The honest path from here to full Rust/assembly/binary
coverage is in [ROADMAP.md](ROADMAP.md).

## M1 increments 1–5 (current)

- **Increment 5 — interprocedural summaries.** Each function gets a summary:
  its memory **effects** (writes/frees, propagated to a call-graph fixpoint — so
  recursion is sound) and its **return value** as a parameter-relative template
  (a parameter pointer plus an affine offset, the wrapper/accessor shape). At a
  call, a pure callee no longer invalidates the caller's heap, and a returned
  pointer is rebuilt against the actual arguments **keeping its provenance**.
  The `interproc_caller` demo (`p = first(buf); *p = 0`) is **PASS** — even
  though the wrapper `first` cannot prove its own parameter-pointer arithmetic
  in isolation (it is only safe under preconditions, so it stays UNKNOWN
  standalone). `solver demo` now reports **34 PASS / 1 FAIL / 2 UNKNOWN**.

- **Increment 4 — symbolic heap + alias analysis.** Each path carries a symbolic
  store; a `Load` resolves via `AliasResult` (Must/May/No) against prior stores,
  so a pointer's provenance survives a store→load round-trip. Distinct
  allocations never alias; within one, offsets are compared by the solver. The
  raw-pointer-through-memory pattern (`indirect_store`: store `buf`→slot, load,
  deref) is fully **PASS**. Loop-modified memory is conservatively forgotten at
  headers. `solver demo` now reports **29 PASS / 1 FAIL / 1 UNKNOWN**.

- **Increment 3 — loops.** The symbolic engine no longer skips loops. Back-edges
  are cut and each loop header's parameters are havoc'd to fresh symbols
  constrained by the sound interval invariant (from `csolver-absint`); one pass
  over the body under that invariant plus the loop guard covers every iteration.
  The canonical `for i in 0..n { buf[i] = 0 }` (`loop_array_store`) is now fully
  **PASS** — `i >= 0` from the invariant, `i < n` from the guard, combined by
  the linear solver. `solver demo` reports **14 PASS / 1 FAIL / 1 UNKNOWN**.



### Increments 1–2 (symbolic foundation + memory)

A sound symbolic-execution engine that **turns whole classes of UNKNOWN into
PASS** without weakening soundness:

- **Increment 1.** `csolver-solver` gained a hash-consed symbolic expression IR
  (`expr`) and a sound incomplete **linear decision procedure**
  (`linear::prove_implies`, Fourier–Motzkin). `csolver-symbolic` discharges
  scalar `SafetyCheck`s path-sensitively. `guarded_get` (`i<len` under a guard)
  is now PASS.
- **Increment 2 — symbolic memory.** `csolver-symbolic` now models pointers
  (provenance + symbolic offset + alignment, never bare integers) and a
  per-path region table (size, lifetime, permissions). It decides the canonical
  obligations of `Load`/`Store`/`PtrOffset`/`Dealloc` — non-null, no-UAF,
  in-bounds, alignment, read/write permission, valid pointer arithmetic,
  no-double-free. The verifier enumerates these from the IR
  (`Inst::implied_checks`), so a memory op is **never silently passed**.
  `solver demo`'s `safe_buffer_store` (a guarded `buf[i]` write into a freshly
  allocated `[i32; n]`) is fully **PASS**; a use-after-free stays **UNKNOWN**
  (never a false PASS). Proofs surface their `alloc-succeeds` /
  `linear-no-overflow` assumptions.

This increment is `Proven`/`Unknown` only — it never *refutes* (a sound FAIL
needs a satisfiable model on a provably-reachable path; the UNSAT-only solver
cannot supply one). Constant violations are still caught as FAIL by intervals.

Remaining M1 increments (planned, see ARCHITECTURE §8): loop summaries +
dominator-based path **merging**; heap-content/`memcpy` modelling + **alias
analysis** (Must/May/No); **function summaries** + direct/mutual **recursion**
via iterative fixpoints; counterexample **model extraction** for FAIL; external
SMT backends (Bitwuzla → Z3 → CVC5) behind the existing `SmtSolver` trait; the
large unit/integration/property/fuzz corpus.

---

## M0 — architecture + foundations (done)

## Implemented and tested

| Crate | What works now |
|---|---|
| `csolver-core` | Verdict lattice, proof obligations/results, proof trees, counterexamples, bit-vectors. |
| `csolver-ir` | MSIR types: typed block-argument SSA, explicit memory ops, `SafetyCheck`, C-style layout. |
| `csolver-cfg` | CFG, dominators, post-dominators, natural loops (Cooper–Harvey–Kennedy). |
| `csolver-memory` | Region/pointer model; concrete decision of in-bounds / UAF / double-free / alignment / null / permissions; symbolic ⇒ residual. |
| `csolver-absint` | Interval lattice + widening/narrowing, generic worklist fixpoint, MSIR transfer, sound trivalent condition evaluation. |
| `csolver-solver` | Bit-vector constraint IR + meaning-preserving simplifier. |
| `csolver-smt` | `SmtSolver` trait + sound `NullSolver` fallback. |
| `csolver-parser` | Cursor + diagnostics plumbing. |
| `csolver-verifier` | Obligation generation + interval discharge + verdict roll-up → `ModuleReport`. |
| `csolver-report` | Text + JSON rendering. |
| `csolver-cli` | `solver demo` runs the full pipeline; `verify` dispatches to frontends. |

Run `cargo test` (61 tests) and `cargo run -p csolver-cli -- demo`.

## Interface-only stubs (return `Unsupported`)

`csolver-mir`, `csolver-asm`, `csolver-elf` — public APIs fixed, lowering to
come. (`csolver-symbolic` is fully implemented since M1; `csolver-llvm` parses
and lowers a real subset since the LLVM-IR front-end landed.)

## Working end-to-end slice

`solver demo` proves an in-bounds check (PASS, with an interval proof tree),
refutes an out-of-bounds check (FAIL, with a counterexample), and reports a
symbolic check as UNKNOWN (with the residual obligation and a suggested minimal
assumption). This exercises every implemented crate.

## Next (see ARCHITECTURE.md §8)

M1 LLVM-IR frontend + branch-condition refinement → first real in-bounds proofs
of compiled Rust; M2 symbolic execution + internal BV solver + counterexample
models; M3 Z3 + heap arrays (UAF/double-free); M4 ELF+x86-64; M5 MIR + borrow
facts + interprocedural summaries.
