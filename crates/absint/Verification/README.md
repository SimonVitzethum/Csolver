# Verification — csolver-absint

## Design
A monotone-framework abstract interpreter: the `AbstractDomain` lattice trait,
the `Interval` domain (with widening/narrowing), the `IntervalState` register
environment, the worklist `solve`r, and the MSIR interval transfer functions
plus a sound trivalent condition evaluator.

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
