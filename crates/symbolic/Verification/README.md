# Verification — csolver-symbolic

## Design
Path-sensitive symbolic discharge over MSIR (M1, increments 1–3). The executor
enumerates paths from the entry, accumulating a path condition, a symbolic
register environment (scalars **and pointers**, over `csolver-solver`
expressions) and a **per-path region table** (so allocate/free is
path-sensitive). For each `SafetyCheck` it asks the linear procedure whether the
path condition implies the condition; for each **memory operation**
(`Load`/`Store`/`PtrOffset`/`Dealloc`) it decides the canonical obligations
(non-null, no-use-after-free, in-bounds, alignment, read/write permission,
valid pointer arithmetic, no-double-free) from the region table + path
condition + solver.

## Loops (increment 3)
Loops are handled without unbounded unrolling: back-edges are **cut**, and each
loop header's parameters are replaced by fresh symbols **constrained by the
sound interval invariant** at that header (from `csolver-absint`). One symbolic
pass over the body — under the invariant *and* the loop guard (a path
condition) — therefore over-approximates every iteration. This is what lets the
canonical `for i in 0..n { buf[i] }` be proved in bounds: `i >= 0` comes from
the interval invariant, `i < n` from the guard, and the relational combination
is discharged by the linear solver. Soundness rests on the interval invariant
being a true over-approximation of the header state on every iteration (proved
in `csolver-absint`).

## Symbolic memory model
A pointer is `provenance + symbolic offset + alignment` — **never a bare
integer**. A region carries a symbolic byte size, a lifetime state
(Live/Freed), and permissions. In-bounds is `0 ≤ off ∧ off+size ≤ region_size`
(each conjunct proved separately); alignment is decided from the pointer's
`gcd`-tracked alignment; temporal/permission/null checks are decided from the
region state. Allocation is assumed to succeed (`alloc-succeeds` assumption).

## Interprocedural summaries (increment 5)
Each function gets a [`Summary`] (`summary.rs`): its **effects** (`writes` /
`frees`, propagated to a fixpoint over the call graph so recursion and
transitive impurity are sound) and its **return value** as a parameter-relative
template (`PtrFromArg { arg, affine-offset }` for the wrapper/accessor shape,
`Scalar(affine)` for affine scalar returns). At a `Call`, instead of havocking:
a *pure* callee leaves the caller's heap intact; the return is instantiated
against the actual arguments so a returned pointer **keeps its provenance**.
Direct calls to unsummarized/recursive functions and indirect/external calls
fall back to havoc + heap clear (sound). This makes pointer-returning helpers
transparent — `caller` proving its dereference of `first(buf)` even though
`first` alone cannot (its parameter pointer has no provenance in isolation).

## Symbolic heap + alias analysis (increment 4)
Each path carries a list of store records. A `Load` resolves by scanning them
most-recent-first via [`csolver_memory::AliasResult`]: a **must-aliasing** store
supplies the value, a **may-aliasing** store makes it ambiguous (fresh unknown),
a **no-aliasing** store is skipped. `alias_check(a, b)` decides:
**No** when the pointers are in different allocations, or provably disjoint
ranges in the same allocation; **Must** when their offsets are provably equal
and the store covers the load; **May** otherwise (or on opaque/null provenance).
This is what preserves a pointer's provenance across a store→load round-trip, so
raw-pointer-in-memory patterns (slots, linked structures, `Box<*T>`) verify. At
loop headers the heap is cleared (sound over-approximation of loop-modified
memory).

## Refutation + counterexamples (FAIL with a witness)
A scalar `SafetyCheck` can also be **refuted**: on an **exact** path the engine
shows the check is *definitely* violated and returns a concrete counterexample.

- **Exact path.** Each `PathState` carries an `exact` flag, set false by any
  over-approximation — a loop-header havoc, an opaque call, or a non-determined
  load (a fresh unknown). Refutation is attempted only while `exact`, so the
  path condition characterizes genuinely reachable states (a violating model is
  a real execution).
- **Definite violation.** The check is refuted only when `assumptions ⟹ ¬goal`
  is proved **bit-precisely** (`csolver-solver/bitprecise`) — i.e. *no* reaching
  input satisfies it. This mirrors the interval `False` verdict but with
  bit-precision, so e.g. `(x | 8) < 8` (which intervals cannot see through) is
  caught as a definite OOB. A merely *satisfiable-but-not-valid* check (e.g. an
  unconstrained `i < 8`) is **not** refuted — it stays `Unknown` (this avoids
  turning under-constrained helpers into spurious FAILs).
- **Witness.** `bitprecise::find_counterexample` returns a model of
  `assumptions ∧ ¬goal`; its existence also confirms the path is feasible. Scalar
  inputs are named `arg{i}`, so the counterexample reads directly.
- **No assumption.** Because the violation proof is bit-precise, a refutation
  carries no `linear-no-overflow` caveat, and the model is a genuine machine
  witness.

Memory-access (in-bounds / pointer-arithmetic) refutation is intentionally *not*
attempted yet: a sound, clean OOB witness needs overflow/provenance-aware spatial
reasoning (the byte offset `index * stride` can wrap, so a wrapped index would
spuriously land back in range under pure modular arithmetic). Memory checks are
still proved (`Proven`/`Unknown`) only; refuting them is a dedicated follow-up.

## Specification
- A check is `Proven` iff it is proved on **every** path that reaches it.
- A scalar check is `Refuted` (with a counterexample) iff it is *definitely*
  violated on some **exact** path; otherwise an undecided check is `Unknown`.
  Soundness is one-sided in both directions: never an unsound PASS, never an
  unsound FAIL.
- If exploration exceeds its visit budget it is *truncated* and reports **no**
  decisions — so a truncated run can never hide a violating path.

## Assumptions
- Inherits the linear procedure's "no wraparound on the linear relations"
  assumption (surfaced by the verifier as `linear-no-overflow`).
- Loads/calls/casts that are not value-preserving become fresh unknowns
  (sound over-approximation).
- **Refutation assumes well-formed SSA** (no use-before-def): a definite
  violation quantifies over every free symbol's value, so the only soundness
  hinge is the program point's *reachability*, which the `exact` flag tracks via
  the over-approximation sites (havoc / call / non-determined load). A register
  used before definition would yield an unconstrained fresh value that, if
  branched on, could make an unreachable point look reachable — but valid MSIR
  (what every frontend emits) never does this.

## Limits (this increment)
- Loop precision is bounded by the interval invariant: relational loop
  invariants beyond `header_param ≥ 0` (e.g. `a[i] == a[i-1]+1`) are not
  inferred. Pointer-induction loops havoc the pointer to opaque provenance
  (→ `Unknown`); scalar-index loops are precise.
- No path merging yet (acyclic paths between cut points are still enumerated,
  bounded). Dominator-based merging and interprocedural summaries are next.
- Heap contents are tracked per straight-line segment (read-your-writes) and
  across must/no-aliasing stores; loop-modified memory is conservatively
  forgotten at headers. `memcpy`/bulk-copy modelling is still pending.
- `Ne` and disjunctive goals are not linearized → `Unknown` (sound).

## Proofs (arguments)
- **No unsound PASS.** `Proven` requires the combined prover to succeed on every
  reaching path; it only succeeds bit-precisely or on rational-infeasibility of
  the negated goal (see `csolver-solver/Verification`). Truncation suppresses all
  decisions.
- **No unsound FAIL.** `Refuted` requires (a) the path is `exact` — so the path
  condition is an under-approximation-free characterization of reachable states —
  and (b) a bit-precise proof that the goal is *always* violated on it, plus a
  concrete model that re-establishes feasibility. Over-approximated paths are
  never refuted. So a counterexample always corresponds to a real execution.

## Test strategy
Unit tests for the guarded/unguarded/loop cases and the refutation path; end-to-end
coverage in `csolver-testsuite` (guarded access UNKNOWN→PASS with the assumption
recorded; `definite_violation_is_refuted_with_a_counterexample` shows a bitwise
`(x|8) < 8` that intervals leave UNKNOWN becoming a FAIL with a concrete witness).
Planned: path-merge equivalence tests, symbolic-memory tests (Vec/Box/raw
pointers), property/fuzz tests, the 300+/150+ corpus.
