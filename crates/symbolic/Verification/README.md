# Verification — csolver-symbolic

## Design
Path-sensitive symbolic discharge over MSIR. The executor walks the
(back-edge-cut) CFG in **reverse postorder**, processing **each block once**: a
block's incoming edges are all available when it is reached and are **merged**
into one entry state (see *State merging* below). It carries a symbolic register
environment (scalars **and pointers**, over `csolver-solver` expressions), a path
condition, and a **region table** (so allocate/free is path-sensitive). For each
`SafetyCheck` it asks the solver whether the path condition implies the condition;
for each **memory operation** (`Load`/`Store`/`PtrOffset`/`Dealloc`) it decides
the canonical obligations (non-null, no-use-after-free, in-bounds, alignment,
read/write permission, valid pointer arithmetic, no-double-free) from the region
table + path condition + solver.

Each region also carries a **set of provenance labels** (`SymRegion.prov_labels`):
`ProvLabel` inserts one, `ProvPropagate` unions a source region's labels into a
destination (a container inherits its elements' provenance), and `CapRequire` /
`CapRequireIfAlias` refute exactly when *some* label *provably* lacks the demanded
capability (per `Module::prov_grants`) — a `WriteCapability` FAIL only on an exact /
bug-finding path (via `record_temporal`), else UNKNOWN. `CapRequireIfAlias` fires only
when its two pointers are the same region (an in-place `src==dst` op). An unlabelled
region grants everything, so this never fabricates a false FAIL.

**General inference.** A per-function `ProvTransfer` summary (which arg's labels flow to
which, which arg is labelled) is derived from the body and composed through direct callees
to a fixpoint (`summarize_module`); `apply_prov_transfer` applies a callee's transfer at the
call site — so an internal wrapper around a provenance primitive propagates provenance with
no hand-written contract. Only definite parameter aliasing is recorded (never spurious).

**Indirect-call devirtualization.** A pointer load from a constant ops-struct/vtable
global at a concrete offset with a known function-pointer field (`Module::global_fn_ptrs`,
tracked into `PathState.fn_ptrs`, meet-joined at merges) resolves the loaded value to its
`FuncId`; an indirect call through that register then uses the callee summary (precise
writes/frees/return/provenance effects) instead of the opaque havoc an unknown call forces
(assumption `devirtualized-indirect-call`). Sound — resolution only narrows an
over-approximation; an unknown base falls back to the havoc.

**Additional obligations.** `NoInfoLeak` — a `copy_to_user` (`MemKind::UserDrain`) whose
source is a fresh allocation with an *unwritten* copied range on an exact path is refuted
(reuses the uninit-read machinery). `NoSizeOverflow` (bug-finding only) — an `Alloc` whose
byte size is `var * C` for a constant `C > 1` records the constant-bound goal
`var ≤ UINT_MAX/C` (no wide multiply — the bit-blaster has no divider). `DataRace`
(bug-finding only) — a per-path lockset by lock-pointer base identity
(`LOCK_ACQUIRE`/`LOCK_RELEASE` symbol names, meet-joined) refutes re-acquiring a held lock
(AA self-deadlock). The last two are gated to bug-finding and are never enumerated by the
verifier in sound mode.

**Performance (output-identical).** The interval analysis is reused from the verifier
(`Option<&IntervalAnalysis>` into `discharge_*`) instead of a second fixpoint; a
per-function prove cache memoizes `(assumptions, goal) → ProofMethod` (sound — the
`ExprCtx` is append-only), re-applying the `linear-no-overflow` side effect on a hit.

## State merging (scaling — process each block once)
The old executor enumerated paths recursively, so a CFG with *N* independent
branches forked into *2^N* paths and could trip the visit budget into a
truncated, all-`UNKNOWN` run. Now blocks are processed in reverse postorder and a
join's incoming edge-states are **merged** into one:

- **Single predecessor** → applied precisely (its guard pushed, its block-param
  args bound). Branch blocks keep their exact path condition, so in-branch
  accesses lose no precision.
- **Multiple predecessors (a join)** → over-approximated soundly:
  - **Block parameters (PHIs)** become an `ITE` keyed on each edge's
    discriminator (its path condition), i.e. exactly the φ-value — so an access
    on a merged value is still precise (e.g. `p = if c {3} else {5}; p < 8` is
    proved). Same-provenance pointers merge by `ITE` on the offset; differing
    provenance degrades to opaque (sound).
  - **Regions** keep the common prefix (identical byte size) with a conservative
    lifetime (`Live` only if live on every edge); a pointer into a dropped region
    is made opaque.
  - The **path condition** is the longest common prefix and the **facts** their
    intersection (both weaker, hence sound); the **heap** is forgotten and the
    merged path is no longer `exact` (so it is never refuted).

Each block is thus visited once: a 256-path CFG verifies under a 40-visit budget
(`wide_cfg_is_processed_once_per_block_not_per_path`). The merge relies on SSA
(values live past a join are either block parameters, merged here, or defined
before the split, hence equal on every edge).

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

### Equality-exit induction bounds (`while i != n`)
A loop that exits on an **equality** (`i == n`, continuing while `i != n`)
defeats the interval domain — a `!=` guard refines no bound, so `i` widens to
`[0, +∞]`. For such loops `csolver-absint::induction` recognizes the counter
(start, stride, bound), and `assert_eq_exit_bound` adds the invariant `start ≤ i
≤ bound` at the header **only after proving** the side-conditions that make it a
true invariant: `0 ≤ start ≤ bound ≤ isize::MAX` and `stride | (bound − start)`
(for power-of-two strides, the exact bit-precise `(bound − start) & (stride−1) ==
0`). The divisibility is essential: if `bound` were off the counter's grid, `i`
would step over it, never hit the `== bound` exit, and exceed `bound` — so the
bound would be unsound. With these proved, the body (entered under `i != bound`)
has `i ≤ bound ∧ i != bound`, i.e. the strict `i < bound` that proves `buf[i]` in
bounds. If any side-condition is unproved, no fact is asserted (sound fallback),
so an out-of-bounds exit bound never fakes safety.

### Pointer-walk loops (`iter != end`)
The same reasoning carries to a **pointer** induction. First, comparisons are
**pointer-aware**: `iter == end` between two pointers into the *same* allocation
is the offset relation `o == end_off` (differing/opaque provenance falls back to
fresh — sound). Then for a recognized pointer walk (`PtrIndVar`), the generic
havoc makes `iter` opaque; `assert_ptr_walk_bound` restores its region
provenance with a fresh offset `o` and the facts `b0 ≤ o ≤ end_off ≤ size` and
`o ≡ b0 (mod stride)` — but **only after proving** `0 ≤ b0 ≤ end_off ≤ size ≤
isize::MAX` and `stride | (end_off − b0)` (with the region's no-wrap premise
added for a symbolic slice length). The congruence is essential here in a way it
was not for the integer index loop: a load reads `stride` bytes, so `o ≤ end_off
− 1` does not suffice; `o ≡ b0 mod stride` together with `o < end_off` gives `o ≤
end_off − stride`, hence `o + stride ≤ end_off ≤ size`. With the guard `iter !=
end` (`o != end_off`) the moving load is in bounds. If a side-condition is
unproved (e.g. the end pointer lies past the region), the offset is never
installed and `iter` stays opaque — the access is not proved (no false PASS).

The **rotated `-O` (bottom-test)** form — where the load precedes the `next ==
end` check — uses the stronger invariant `o + stride ≤ end_off` (the load is
unconditional, so there is no guard to combine with). That bound is sound only
when the loop is entered non-empty, and rather than verify the `is_empty`
preheader guard structurally, the engine **proves the base case** `b0 + stride ≤
end_off` — which is provable exactly when the preheader guard `base != end` sits
in this header's path condition. So the soundness-critical "non-empty entry"
condition is *gate-checked*, not trusted: a rotated walk without the guard fails
the base-case proof and is not verified (`ptr_walk_bottom_unguarded` → not PASS,
where on an empty range the unconditional load would be out of bounds).

## Symbolic memory model
A pointer is `provenance + symbolic offset + alignment` — **never a bare
integer**. A region carries a symbolic byte size, a lifetime state
(Live/Freed), and permissions. In-bounds is `0 ≤ off ∧ off+size ≤ region_size`
(each conjunct proved separately); alignment is decided from the pointer's
`gcd`-tracked alignment; temporal/permission/null checks are decided from the
region state. Allocation is assumed to succeed (`alloc-succeeds` assumption). A
**non-null opaque pointer** (a `SizeSpec::NonNull` / LLVM `nonnull` parameter, e.g.
Zig `*T`) is not a region: its provenance id is held in `PathState.nonnull_provs`
(seeded at entry, meet-joined at merges) and the null check treats it — and
gep/copy-derived pointers carrying the id — as non-null, so only `NoNullDeref`
proves while bounds/liveness stay unknown (a `nonnull` pointer may still dangle).

**Rust aliasing model (opt-in `--aliasing-model`).** Two `NoAliasingViolation` classes,
both refuted only on a feasible path (no false FAIL), off by default:
(1) **write through a shared `&T`** — a static pre-pass (`shared_borrow_regs`) marks every
pointer register derived (copy/cast/`PtrOffset`/`FieldPtr`) from a `RefWitness{writable:false}`;
a `Store` through one is flagged.
(2) **use-after-invalidation of a `&mut`** (and read through an invalidated `&T`) — the MIR
frontend emits a `csolver.retag.{mut,shared}` marker for a `&mut *_p` / `&(*_p)` reborrow, and
prepends a protector marker for each `&mut` reference **parameter**. Each borrow carries a **tag**
on its pointer value (`SymPointer::borrow`, excluded from `PartialEq` so no verdict changes), which
flows through copies, `gep`, **memory** (store→load) and **phi** (merge keeps it iff both sides agree).
`PathState.region_borrows` holds each region's live borrow-tag stack: a `&mut` reborrow pushes its
tag popping the parent's other descendants (siblings invalidated), a root reborrow invalidates all
prior borrows, a shared reborrow coexists (added without popping), a write pops the tags above it;
an access through a tag no longer on the stack is the violation. A merge keeps a region's stack only
if all incoming paths agree, else poisons it (checks skipped — sound). Both classes are **record-only**:
`discharge` queries the decision per Load/Store under the flag and raises a FAIL only on a found
violation. Remaining (precision, not soundness): exact two-phase/`UnsafeCell`, interprocedural
protectors — see `Todo.md`.

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

A freeing (or unsummarized) call invalidates region **liveness** so a later use
of freed memory is never a false `PASS` — but only for **owned** regions (a local
`alloc`, no contract). A **contracted reference region** (`&[T]`/`&T`/`&mut T`) is
*borrowed*: the caller holds the borrow for the whole call, so the callee cannot
deallocate it (a borrow confers no ownership), and its liveness **survives the
call**. Without this, any method call (`s.is_empty()`, `s.len()`, a helper) would
mark every borrowed region freed and defeat every subsequent access — fatal for
real, call-heavy code (caught by the Miri differential harness).

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

## Definedness — no read of uninitialized memory
A freshly-allocated region (a `Heap`/`Stack` allocation, i.e. one with **no
caller contract**) holds **uninitialized** bytes until written; reading them is
undefined behaviour in Rust. The store scan classifies each `Load`'s origin:
**`Stored`** (a `Must`-aliasing store determines the value), **`Uncertain`** (a
`May`-aliasing store might), or **`Unwritten`** (every record is `No`-alias — no
store reaches the location). On an **exact** path an `Unwritten` load from a
fresh allocation is a *definite* read of never-written memory: it is refuted as a
`ValidRead` violation with a feasibility witness. The check is **sound and
additive** — it only fires when (a) the path is `exact` (so the store log is
complete; any call/loop havoc drops `exact` and suppresses it), (b) the scan saw
**no** `May`-aliasing store (so the bytes are provably unwritten, not merely
unknown), and (c) the region is a fresh allocation (a contracted pointer
parameter is caller-initialized, so it is never flagged). It therefore adds new
`FAIL`s for uninitialized reads without turning any initialized read into an
`UNKNOWN`. (Tested by `uninitialized_read_is_refuted` / `initialized_read_is_not_flagged`.)

## Path feasibility pruning (scaling)
At each conditional branch, a successor whose guard is **bit-precisely**
unsatisfiable under the current path condition (`pathcond ∧ facts ⟹ ¬guard`) is
**pruned** — it has no concrete execution, so skipping it preserves every real
behaviour. This spends the exploration budget only on reachable paths, so
correlated branches (whose contradictory combinations are dead) do not explode
the path count or trip the visit budget into a `truncated` run. The check is
deliberately **bit-precise**, not linear: pruning on a
`linear-no-overflow`-dependent implication could discard a branch that is in fact
reachable only through wraparound and so hide a real violation (a false PASS); a
bit-precise `⟹ ¬guard` holds for *every* machine value, so the branch is
genuinely dead. Missing a linear-only infeasibility merely keeps a redundant
path — never unsound. (Tested by `infeasible_branch_is_pruned` /
`feasible_branch_is_explored`.)

## Refutation + counterexamples (FAIL with a witness)
A check can be **refuted**: on an **exact** path the engine exhibits a concrete
input that violates it. The proving step always runs first, so a provable check
is never refuted.

- **Exact path.** Each `PathState` carries an `exact` flag, set false by any
  over-approximation — a loop-header havoc, an opaque call, or a non-determined
  load (a fresh unknown). Refutation is attempted only while `exact`, so the
  path condition characterizes genuinely reachable states and a violating model
  is a real execution. The witness (`bitprecise::find_counterexample`, a model of
  `assumptions ∧ ¬goal`) also confirms the path is feasible; scalar inputs are
  named `arg{i}` so it reads directly. Being bit-precise, a refutation carries no
  `linear-no-overflow` caveat.

Two refutation strengths are used (`RefuteMode`):

- **Definite** (scalar `SafetyCheck`s). Refuted only when `assumptions ⟹ ¬goal`
  is proved **bit-precisely** — i.e. *no* reaching input satisfies it. This
  mirrors the interval `False` verdict but with bit-precision, so e.g.
  `(x | 8) < 8` (opaque to intervals) is caught as a definite violation. A merely
  *satisfiable-but-not-valid* check (e.g. an unconstrained `i < 8`) stays
  `Unknown` — under-constrained obligations are not turned into FAILs.
- **Possible** (memory-access **in-bounds**). Refuted when *some* reaching input
  makes the access out of bounds. This is right for a memory operation because
  the access **executes**: any reachable OOB input is a real runtime violation,
  so `buf[i]` with an unconstrained `i` is `FAIL` with a witness (e.g. `i = 8`).
  Soundness rests on (a) the exact path — the model is a real input — and (b) the
  region's byte size not wrapping. For a **concrete** size that is automatic; for
  a **symbolic** size `count * stride` (a dynamic `alloc T * n`, or a `&[T]`
  slice) it holds because a successful allocation / valid slice has
  `count * stride <= isize::MAX`, recorded as a `count <= isize::MAX/stride`
  premise. That premise is kept off the proving assumptions (it would slow every
  proof) and added **only** to the refutation query, so the witness's size cannot
  be a wrapped too-small value. The signed in-bounds formula is then faithful: a
  wrapped huge index that aliases back into range correctly is *not* a violation,
  while a genuine past-the-end offset is. So `buf[i]` into a dynamically-sized
  `[i32; n]`, or `s.get_unchecked(i)` on a slice, is refuted with a witness for
  the length *and* the index. Pointer-arithmetic checks are prove-only; the
  access's in-bounds check carries the OOB counterexample.

**Temporal** safety (use-after-free / double-free) is refuted too, but decided
structurally from the region's lifetime rather than by the solver. On an **exact**
path a region only becomes `Freed` through an explicit `Dealloc` (a freeing call
or loop sets `exact = false`), so a `Freed` region at an access — or a second
free — is a *definite* violation for every reaching input. It is `Refuted` with a
**feasibility witness** (a model of the path condition, confirming the point is
reached; input-free for a straight-line `alloc; free; use`). Off an exact path,
where a region was only *maybe* freed, it degrades to `Unknown`.

## Specification
- A check is `Proven` iff it is proved on **every** path that reaches it.
- A check is `Refuted` (with a counterexample) iff, on some **exact** path, a
  scalar check is *definitely* violated or a concrete-size memory access is
  violated by *some* reaching input; otherwise an undecided check is `Unknown`.
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
