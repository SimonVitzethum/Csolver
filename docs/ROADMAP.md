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
   `store`/`getelementptr`/`icmp`/binops/casts/`call`/`phi`/`ret`/`br`/`switch`,
   the `memcpy`/`memset`/`llvm.lifetime` intrinsics, and `rustc`-style metadata)
   already verifies real `.ll` end-to-end, including `phi`-based loops and
   `match`/enum-dispatch `switch`es (each case is an exact edge guard, the
   default a sound over-approximation). Remaining: broaden toward raw `rustc`
   output (`select`, `extractvalue`/aggregates, more intrinsics). This is the
   shortest path to "verify compiled Rust" because `rustc` emits LLVM-IR.
2. **Rust MIR** (`csolver-mir`): **started** — a pure-Rust lexer + parser +
   lowerer for a practical subset of **textual** MIR (`rustc --emit=mir`), no
   `rustc` linkage (mirroring the `.ll` approach). Its point is that the
   bounds/overflow checks rustc inserts are *explicit*: `assert(Lt(i, len)) ->
   [success: bb, …]` lowers to a `CondBr` whose success edge carries the guard
   (failure → an `unreachable` panic pad), so a checked `s[i]` over `&[i32; N]`
   verifies **PASS** precisely because the check is present, while the unchecked
   index is not proved. Sized references become region contracts; index/deref
   places become `PtrOffset` + `Load`/`Store`. **Slices `&[T]`** are modelled too:
   the fat-pointer length (exposed via `Len((*_1))`) becomes a synthetic `usize`
   length parameter with a `ParamElements` contract (region size `len·elem`), so
   a checked slice index *and* an index-based slice loop `for i in 0..s.len()`
   verify **PASS** from MIR. **Calls** lower too: the assignment-form `_d =
   f(args) -> [return: bb, …]` becomes an MSIR `Call` (resolved to `Direct` for an
   in-module callee, else `Symbol`/`Indirect`) + a branch to the return block, so
   an interprocedural module verifies via the callee's summary. Unmodelled
   constructs (`drop`, aggregates) degrade per-function to `UNKNOWN`. Remaining:
   aggregates/fields, call return-type tracking, and a real multi-block corpus.
3. **Assembly** (`csolver-asm`) + **ELF/DWARF** (`csolver-elf`): **started.** A
   pure-Rust ELF64 reader (`csolver-elf`) parses sections/symbols and recovers a
   function's machine bytes; a minimal x86-64 decoder (`csolver-asm`
   `x86::decode_function`) lowers a straight-line function to MSIR, including a
   **stack-frame model** (`sub rsp, N` → an `N`-byte `Stack` allocation, so
   `[rsp+disp]` accesses are bounds-checked against the frame). The whole binary
   pipeline runs end-to-end and now *proves real memory safety*: a stack store
   inside the frame is PASS, an out-of-frame store FAIL, and a `xor eax,eax; ret`
   PASS; unprovable/undecoded functions are UNKNOWN (never a false PASS). The
   decoder **reconstructs control flow** too (`jmp`/`jcc`/`cmp` → MSIR blocks with
   `Br`/`CondBr`, backward branches → back-edges), so a *guarded* stack store and
   a *loop* in a binary verify end-to-end via the state-merging engine. A second
   decoder handles **AArch64** (fixed 32-bit instructions: `ret`, `add`/`sub`
   immediate incl. the stack frame, `ldr`/`str`), so the same stack-safety proofs
   hold on ARM binaries. Remaining: the broad ISA (and ARM control flow), DWARF
   types, relocations/PLT, and PE/Mach-O.

> **Scope decision — the binary/ASM track is FROZEN as a research demonstrator.**
> The x86-64 and AArch64 decoders carry **hand-written, unvalidated instruction
> semantics**, which is the single highest residual false-`PASS` risk in the whole
> project. Graceful degradation (`unrecognised opcode → UNKNOWN`) only protects
> against *missing* instructions; it does **not** catch a *handled* opcode whose
> modelled semantics is subtly wrong — e.g. a 32-bit `mov eax, …` must zero the
> upper 32 bits of `rax` (partial-register write), and flag / sign-extension /
> one-past-the-end-pointer rules are easy to mis-encode. Such a bug yields a silent
> false `PASS` on a real binary. Because the project's truth source for "proving
> real Rust" is **MIR**, not the binary, engineering effort goes to the Rust
> pipeline (Bucket A points 1–2) and the binary track is held at its current
> demonstrator scope. **It must not be relied on for safety-critical claims until
> its decoders are translation-validated** against a reference emulator (random
> byte sequences → MSIR semantics vs. a real CPU/emulator), the same measured
> discipline the bit-blaster now has (exhaustive oracle test) and the verdict
> pipeline now has (Miri differential corpus). This is recorded so the freeze is a
> conscious choice, not a silent gap.

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
  the project's principle. A **wall-clock valve** (`SOLVE_TIME_BUDGET` in
  `crates/solver/src/sat`) caps each SAT query on *time*, not just decision count,
  so a single hard query cannot hang the whole analysis (it bails to `Unknown`,
  which only weakens a verdict). Remaining here: bit-blast division/remainder and
  symbolic shifts, array/heap theories.

  **External SMT backend — deliberately deferred (data-driven).** The `SmtSolver`
  trait + `NullSolver` are the prepared opt-in extension point (Bitwuzla → Z3 →
  CVC5), but it is *not* built, on purpose. Scaling the corpus to memchr surfaced
  the only timeout so far (its `packedpair` SIMD search), and diagnosis showed it
  was a **liveness** problem — the bit-precise SAT grinding toward its budget — not
  a **precision** one: the obligations prove fine on the linear path, so the
  wall-clock valve turns the timeout into a fast PASS. No corpus function has yet
  needed bit-precise reasoning the internal solver cannot deliver. Until the
  per-obligation residual bucket shows a case that stays `UNKNOWN` where a generous
  bit-precise proof would `PASS`, an external backend would add C/C++ TCB surface
  (and break the offline pure-Rust build) for a need the data has not demonstrated.
  That residual bucket is the precise trigger to revisit this.
- **Counterexample model extraction** — **done** (for the current analysis). The
  internal SAT layer returns a satisfying model (`bitprecise::find_counterexample`),
  and the symbolic engine emits a `FAIL` with a concrete witness (named `arg{i}`)
  for a *definitely-violated* scalar check, a memory access out of bounds for some
  reaching input — **including dynamically-sized** buffers and slices, via the
  `count * stride <= isize::MAX` no-wrap premise added only to the refutation
  query — **temporal** violations (use-after-free / double-free, from the
  region lifetime with a feasibility witness), and **definedness** violations (a
  read of *uninitialized* memory: an `Unwritten` load from a freshly-allocated
  region with no caller contract), all on an **exact** path. Remaining:
  richer step traces, and refutation through over-approximated (loop / call) paths
  (needs path-precise reachability, not just the `exact` gate).
- **Definedness / shape (ownership) analysis** — **started.** The first shape
  fact is the *validity state* of allocated bytes: fresh allocations are
  uninitialized until written, so a provably-unwritten read is refuted
  (annotation-free, sound, additive). Next toward annotation-free heap reasoning:
  a separation/ownership domain (disjointness of sub-regions, exclusive `&mut`
  ownership) and inferred per-region initialization ranges for symbolic offsets.
- **Pointer-induction loops** — the fully-optimized `for x in s` lowers to a
  vectorized **pointer-walking** loop (`iter != end`, `end = base + len*sizeof`).
  **Stage 1 is in:** an *equality-exit induction* analysis (`csolver-absint`
  `induction`) recognizes a counter `v` that steps by a constant stride and exits
  on `v == bound`, and the symbolic engine asserts the sound invariant `start ≤ v
  ≤ bound` — but only after **proving** the side-conditions (`0 ≤ start ≤ bound ≤
  isize::MAX` and `stride | (bound − start)`, the divisibility that stops the
  counter overshooting a `!=` bound). With the loop guard `v != bound` this gives
  the strict `v < bound` the interval domain cannot derive from a `!=` exit, so an
  **integer** `while i != n { buf[i] … }` loop verifies. **Stage 2 is in:** the
  same reasoning is carried to the **pointer** offset — a same-allocation pointer
  comparison is evaluated as an offset relation, and a recognized `iter != end`
  walk keeps `iter`'s region provenance with a fresh offset bounded by `0 ≤ o ≤
  end_off ≤ size` plus the **congruence** `o ≡ 0 (mod stride)` (so a `stride`-byte
  load at `o < end_off` is in bounds, which `o ≤ end_off − 1` alone is not). The
  header-test `for x in s` walk verifies (`ptr_walk_loop` → PASS; a walk past the
  end → not PASS). **Stage 3 is in:** the rotated `-O` (bottom-test) form, where
  the load precedes the `next == end` check, also verifies — the stronger bound
  `iter + stride ≤ end` is sound only on a non-empty range, and rather than
  analyse the `is_empty` preheader guard structurally the engine **proves the base
  case** `b0 + stride ≤ end_off` from that guard in the path condition (so a
  missing guard simply fails the proof: `ptr_walk_bottom_loop` → PASS,
  `ptr_walk_bottom_unguarded` → not PASS). **End-to-end from compiled Rust:** the
  real `rustc -O` `for x in s` over `&[i32]` — the rotated phi-pointer walk in
  `.ll` — lowers through the LLVM front-end (phi → block parameter, `getelementptr`
  → `PtrOffset`, pointer `icmp` → comparison, slice ABI → region) and verifies
  **PASS** unchanged (`llvm_pointer_walk_loop_verifies_pass`), with the unguarded
  variant correctly not proved. The fully-optimized iterator loop is thus verified
  from source-compiled Rust, not just hand-built MSIR.
- **Relational loop invariants** — **in** (zone / difference-bound domain). A
  `Zone` DBM tracks `vⱼ − vᵢ ≤ c` between registers; the symbolic engine adds its
  header invariants as facts, so a loop whose safety is a *relation* (a second
  induction variable, `buf[j]` with `j ≤ i < n`) verifies — which the per-variable
  interval domain and the loop guard alone cannot. Still ahead: full octagon
  (`±x ± y`) / polyhedra and relations between more than two variables.
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
- **Path feasibility pruning** and **state merging** are **in**. Pruning drops a
  conditional branch whose guard is bit-precisely unsatisfiable. Merging processes
  the CFG in reverse postorder, joining each block's incoming edge-states once
  (PHIs → `ITE` on edge path conditions, regions → conservative common prefix,
  path condition/facts → common prefix/intersection), so independent-branch
  explosion becomes *O(blocks)* instead of *O(2^N)* paths. Still ahead:
  **relational loop invariants** (octagon / polyhedra) and **incremental +
  parallel** analysis.

## Bucket C — `unsafe` / FFI / machine reality (explicit assumptions)

These are where "full safety" becomes "safety relative to a named contract":

- **FFI / external calls**: a summarized pre/post-contract, else `UNKNOWN` +
  suggested contract. Recognized APIs are described by **external, file-driven
  contracts** (`csolver-contracts`, `data/*.contract`) — one block per API family,
  covering allocators, deallocators, user-copies, and provenance/capability rules;
  a new API is a contract, not a code change.
- **`int → ptr` casts / inline asm**: provable only with an assumption that
  re-establishes provenance / supplies a semantics.
- **Indirect calls/branches**: provable when the target set is recoverable
  (vtables, jump tables), else a `ValidIndirectTarget` assumption.
- **Concurrency / weak memory**: out of the current model; a data-race-aware
  extension would be required for concurrent safety.

## Bucket D — provenance across syscalls (the Copy-Fail class)

CVE-2026-31431 "Copy Fail" is not a spatial OOB: a page-cache page, inserted into
a socket's scatterlist by `splice()` in one syscall, is later written through an
in-place AEAD op set up in another — a **provenance + write-capability + aliasing**
bug assembled across syscall boundaries. Covering this class needs, in order:

1. **Provenance labels + a capability lattice — DONE**, file-driven
   (`prov`/`label`/`require`, `SafetyProperty::WriteCapability`,
   `Inst::ProvLabel`/`CapRequire`, `Module::prov_grants`). Sound-by-default: an
   unlabelled region grants everything, so it never false-FAILs.
2. **Scatterlist as a structured region** (a list of `(page, offset, len)` segments
   + `sg_chain`) and **src=dst segment aliasing**, so a `require write` on a crypto
   request reaches the labelled destination segment.
3. **Crypto-API effect contracts** (`crypto_aead_encrypt` writes `req->dst`) — a
   handful of interface axioms at the trust boundary, or derived by a general
   effect-summary inference (mod/ref + provenance-transfer fixpoint) that also
   auto-derives most ordinary contracts.
4. **Multi-entry typestate** over the socket object (reachable operation sequences)
   — the precise-but-research-scale finale that yields a syscall-sequence witness.

## Sequencing

The fastest route to "verify real compiled Rust" is **Bucket A.1 (LLVM-IR
front-end) + Bucket B bit-precise SMT**, reusing the entire audited MSIR
analysis unchanged. Assembly/ELF (A.3) then extends the same pipeline to
source-less binaries. Each step is additive: the MSIR analysis core does not
change, so soundness is argued once and inherited.
