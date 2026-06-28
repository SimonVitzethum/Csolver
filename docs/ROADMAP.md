# Roadmap to full Rust / assembly / binary memory-safety proofs

The goal is to *prove* memory safety for real Rust — at MIR, LLVM-IR, assembly
and ELF level — accepting arbitrarily high compute cost. This document is the
honest map from where CSolver is to that goal: what already holds, what is
engineering, and what is bounded by theory.

## The theoretical ceiling (and how we live under it)

Full memory safety of an arbitrary program is **undecidable**, so no tool can
return a correct verdict for *every* program. CSolver's contract makes this
livable: a `PASS` is *proven safe under the reported assumptions*; otherwise it
returns `UNKNOWN` (with the residual + the minimal assumption that would close
it) or `FAIL` (with a counterexample). "Extreme compute" buys *more* `PASS` (more
unrolling, larger constraint systems, more precise domains) but never converts an
honest `UNKNOWN` into an unsound `PASS`. See [PROVABILITY.md](PROVABILITY.md).

## What is proven today (M1, on MSIR)

The analysis core is real and audited (see [AUDIT.md](AUDIT.md)). On the
common-IR (MSIR) level it already proves, soundly:

- spatial safety (in-bounds, valid pointer arithmetic) for constant, guarded,
  and **loop** accesses (`for i in 0..n { buf[i] }`) via interval invariants +
  symbolic execution + a linear decision procedure;
- temporal safety (no-use-after-free, no-double-free) and null/alignment/
  permission checks over a symbolic pointer/region model;
- pointer **provenance through memory** (store→load round-trip) via an
  alias-aware symbolic heap (Must/May/No alias);
- **interprocedural** calls via function summaries (effects + provenance-
  preserving returns).

Everything above runs on hand-built or frontend-produced MSIR. The pieces still
missing fall into three buckets.

## Bucket A — front-ends (the largest remaining engineering)

To consume real Rust/asm/binaries, the stub front-ends must lower to MSIR:

1. **LLVM-IR** (`csolver-llvm`): **started** — a pure-Rust parser + lowerer for a
   practical subset (functions, `iN`/`ptr`/`[N x T]` types, `alloca`/`load`/
   `store`/`getelementptr`/`icmp`/binops/casts/`call`/`phi`/`ret`/`br`) already
   verifies real `.ll` end-to-end, including `phi`-based loops. Remaining:
   broaden toward raw `rustc` output (auto-numbering, metadata stripping,
   `switch`, intrinsics like `memcpy`/`llvm.lifetime`). This is the shortest path
   to "verify compiled Rust" because `rustc` emits LLVM-IR.
2. **Rust MIR** (`csolver-mir`): consume `rustc`'s MIR (stable-MIR or a driver),
   carrying borrow facts and panic edges that *sharpen* obligations.
3. **Assembly** (`csolver-asm`) + **ELF/DWARF** (`csolver-elf`): decode x86-64 /
   AArch64, recover the stack frame and types from DWARF, and lower to MSIR with
   the flat-memory model. Needed for "prove a binary with no source".

Each front-end owes a **refinement proof** (every concrete behaviour of the
input is a concrete behaviour of the emitted MSIR) — the soundness hinge for the
whole tool, argued in each crate's `Verification/`.

## Bucket B — analysis depth (raises the `PASS` rate, uses the compute budget)

- **Bit-precise reasoning** — **started, pure-Rust.** `csolver-solver` now has a
  self-contained bit-precise decision procedure: a bit-blaster (`bitblast`, exact
  fixed-width/wrapping bit-vector circuits) feeding an internal DPLL SAT solver
  (`sat`), exposed as `bitprecise::prove_implies`. The combined
  `prove_implies_method` runs the fast linear procedure first, then a bit-precise
  *refinement* (so goals decidable exactly are reported `BitPrecise` and **drop
  the `linear-no-overflow` assumption**) and a bit-precise *fallback* (proving
  wrap-sensitive / bitwise goals the linear fragment abstracts away — e.g.
  `buf[x & 7]` is now PASS). This is pure Rust by design (no C/C++), keeping with
  the project's principle. Remaining here: bit-blast division/remainder and
  symbolic shifts, array/heap theories, and — only if ever wanted — an *opt-in*
  external backend (Bitwuzla → Z3 → CVC5) behind the `SmtSolver` trait for very
  large queries.
- **Counterexample model extraction** — **done** (for the current analysis). The
  internal SAT layer returns a satisfying model (`bitprecise::find_counterexample`),
  and the symbolic engine emits a `FAIL` with a concrete witness (named `arg{i}`)
  for a *definitely-violated* scalar check, a memory access out of bounds for some
  reaching input — **including dynamically-sized** buffers and slices, via the
  `count * stride <= isize::MAX` no-wrap premise added only to the refutation
  query — and **temporal** violations (use-after-free / double-free, from the
  region lifetime with a feasibility witness), all on an **exact** path. Remaining:
  richer step traces, and refutation through over-approximated (loop / call) paths
  (needs path-precise reachability, not just the `exact` gate).
- **Pointer-induction loops** — the fully-optimized `for x in s` lowers to a
  vectorized **pointer-walking** loop (`iter != end`, `end = base + len*sizeof`).
  Verifying it soundly needs a relational pointer-offset abstract domain *plus*
  congruence/modular reasoning (the `!=` end-pointer guard). Index-based slice
  loops already verify; this is the remaining (research-level) loop shape.
- **Relational loop invariants** (octagon / polyhedra domains, invariant
  inference) beyond `i ≥ 0`, for loops whose safety needs `a[i] == …` relations.
- **Precondition propagation / context-sensitive interprocedural** proving, so a
  helper that accesses `buf[i]` is verified once-per-context. (A first form of
  this is already in: pointer-parameter `dereferenceable`/`align`/`readonly`
  contracts — what the Rust reference type guarantees — are imported and
  assumed, so functions taking `&[T]`/`&mut [T; N]` verify directly. The general
  case where a precondition is a *relation between* parameters is next.)
- **`memcpy`/bulk-copy** safety is in (destination/source valid for `len`
  bytes); the remaining piece is modelling the *content* transfer (so a value
  copied by `memcpy` is then known on a subsequent load) and full Must/May/No
  alias for aggregate operations.
- **Path merging** (dominator-based) and **incremental + parallel** analysis to
  spend the compute budget without path explosion.

## Bucket C — `unsafe` / FFI / machine reality (explicit assumptions)

These are where "full safety" becomes "safety relative to a named contract":

- **FFI / external calls**: a summarized pre/post-contract, else `UNKNOWN` +
  suggested contract.
- **`int → ptr` casts / inline asm**: provable only with an assumption that
  re-establishes provenance / supplies a semantics.
- **Indirect calls/branches**: provable when the target set is recoverable
  (vtables, jump tables), else a `ValidIndirectTarget` assumption.
- **Concurrency / weak memory**: out of the current model; a data-race-aware
  extension would be required for concurrent safety.

## Sequencing

The fastest route to "verify real compiled Rust" is **Bucket A.1 (LLVM-IR
front-end) + Bucket B bit-precise SMT**, reusing the entire audited MSIR
analysis unchanged. Assembly/ELF (A.3) then extends the same pipeline to
source-less binaries. Each step is additive: the MSIR analysis core does not
change, so soundness is argued once and inherited.
