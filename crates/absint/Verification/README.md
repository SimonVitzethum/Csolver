# Verification — csolver-absint

## Design
A monotone-framework abstract interpreter: the `AbstractDomain` lattice trait,
the `Interval` domain (with widening/narrowing), the `IntervalState` register
environment, the worklist `solve`r, and the MSIR interval transfer functions
plus a sound trivalent condition evaluator. Alongside the (per-variable)
interval domain there is a **relational** `Zone` domain and its analysis.

## Zone (relational) domain
Where intervals track each variable independently, a `Zone` is a Difference-Bound
Matrix tracking *differences* `vⱼ − vᵢ ≤ c` (with a zero node for absolute
bounds) — the relational invariants intervals cannot express, e.g. a second
induction variable `j` that tracks `i`, so `j ≤ i`. `relational::analyze_zones`
runs it over MSIR: only *affine* register updates (`x = c`, `x = y`, `x = y ± c`,
the self-increment `x = x ± c` via an exact translation) refine the zone; anything
else **forgets** the register (sound). A conditional branch refines the zone with
the guard (and its negation on the other edge), via a static boolean-register →
comparison map. The symbolic engine queries `entry_diffs(header)` and adds the
difference invariants as facts on the havoc'd loop variables, so a `buf[j]` with
`j ≤ i < n` proves in bounds (see the `relational_loop` end-to-end test).

### Soundness and termination of the zone
`add_constraint`/`meet` only ever tighten (sound narrowing); `join` is the looser
bound; closure is Floyd–Warshall (a negative diagonal ⇒ the infeasible bottom).
The widening is the aggressive **keep-if-equal** operator (a bound survives only
if unchanged, else → `+∞`): the finite-entry count is monotonically
non-increasing across widenings, so every chain stabilizes in ≤ `(n+1)²` steps —
termination is immediate, while the *stable* difference bounds that loop induction
relations need are kept. The variable count is capped (`MAX_VARS`); past it the
analysis yields no relations (sound).

## Specification
- `Interval` is `⊥ ∪ [lo,hi]` over `ℤ ∪ {±∞}`; arithmetic saturates at ±∞.
- `widen`: bounds that grew jump to ±∞ (finite ascending chains collapse in ≤2
  steps per bound).
- `solve` computes a post-fixpoint: `out[b] = transfer(in[b])`,
  `in[b] = ⊔_p edge(p→b, out[p])`, widening at loop headers.
- `Trivalent`: `True`/`False` only when the relation holds for the **whole**
  over-approximation; `Unknown` otherwise.

## Assumptions
- Loop headers reported by `csolver-cfg` are complete (so widening is applied
  wherever needed — the termination precondition).
- The interval comparator treats values as signed; sound for the non-negative
  indices/sizes that dominate bounds checks (unsigned-sensitive cases go to SMT).

## Limits
- No branch-condition refinement yet ⇒ induction variables widen to `[0,+∞]`
  (sound, imprecise). Refinement and narrowing passes arrive with M1.
- Division/shift/bitwise ops transfer to `⊤`.

## Proofs (arguments)
- **Termination.** Every loop header widens; interval widening admits no
  infinite ascending chain, so the worklist stabilizes. Demonstrated by the
  counting-loop test (which would otherwise diverge).
- **Soundness of discharge.** Since `[lo,hi]` over-approximates the concrete
  value set, "relation holds on all of `[lo,hi]`" ⇒ holds concretely (`PASS`),
  and "holds on none" ⇒ fails concretely (`FAIL`). Tested by the
  `True`/`False`/`Unknown` condition cases.

## Test strategy
Unit tests: lattice laws (join/meet/leq), widening/narrowing, saturating
arithmetic, environment join, straight-line constant folding, loop termination,
and trivalent soundness. Lattice-law property tests planned (M1).
