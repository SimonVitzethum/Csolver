# Verification — csolver-cfg

## Design
Structural control-flow analysis: `Cfg` (dense node space, succ/pred,
reverse-postorder), `Dominators`/`PostDominators` (Cooper–Harvey–Kennedy), and
natural-loop detection.

## Specification
- `Dominators::dominates(a,b)` ⇔ every entry→b path passes through `a`.
- `PostDominators` are dominators of the reverse graph rooted at a synthetic
  exit that all returns/`unreachable` flow into.
- A back edge is `n→h` with `h dom n`; a natural loop is `h` plus all nodes that
  reach `n` without passing `h`; loops sharing a header are merged.

## Assumptions
- Edges come solely from `Terminator::successors`; the IR is well-formed
  (targets exist — malformed edges are dropped, never panicked on).

## Limits
- Irreducible CFGs: natural-loop detection still terminates and is sound for
  widening placement, but may be less precise (extra headers only cost
  precision, never soundness).

## Proofs (arguments)
- **Exactness.** The CHK fixpoint computes the least solution of the dominance
  equations; it is exact, not an over-approximation. Validated against
  hand-computed diamonds and loops in tests.
- **Header completeness.** Every back edge produces a header, so the fixpoint
  engine widens at every loop — the precondition for its termination proof.

## Test strategy
Unit tests: diamond dominators/post-dominators, self-loop idoms, while-loop
natural-loop body, acyclic ⇒ no loops. Randomized CFG cross-checks vs a naive
reachability oracle are planned (M1).
