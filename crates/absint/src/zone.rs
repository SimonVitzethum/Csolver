//! A **zone** (difference-bound) relational abstract domain.
//!
//! Where the interval domain tracks each variable independently (`x ∈ [a, b]`),
//! a zone also tracks *differences* between variables — constraints of the form
//! `vⱼ − vᵢ ≤ c` — which is what proves loops whose safety is a *relation*
//! between variables (e.g. a second induction variable `j` that tracks `i`, so
//! `j ≤ i < n`). It is represented as a Difference-Bound Matrix (DBM): a special
//! "zero" node (index 0, the constant 0) plus one node per tracked variable, with
//! `m[i][j]` an upper bound on `vⱼ − vᵢ` (so `m[0][k]` bounds `vₖ` above and
//! `m[k][0]` bounds it below).
//!
//! ## Soundness and termination
//!
//! `meet`/`add_constraint` only ever *tighten* (a sound narrowing of the
//! concrete set). `join` takes the looser bound (covers both). The **widening**
//! is deliberately the aggressive *keep-if-equal* operator: a difference bound is
//! kept only if it is **identical** in the previous and new states, otherwise it
//! is dropped to `+∞`. The number of finite entries is therefore monotonically
//! non-increasing across widenings, so any ascending chain stabilizes in at most
//! `(n+1)²` widenings — termination is immediate. It still keeps the *stable*
//! difference bounds that loop induction relations need (e.g. `j − i = 0`), which
//! is exactly the relational information the symbolic engine cannot get from the
//! per-variable interval domain or a single loop guard.

use crate::domain::AbstractDomain;

/// A difference bound: `Some(c)` means `≤ c`; `None` means `+∞` (no bound).
type Bnd = Option<i128>;

/// `a + b` over difference bounds (`+∞` absorbs).
fn add(a: Bnd, b: Bnd) -> Bnd {
    match (a, b) {
        (Some(x), Some(y)) => Some(x.saturating_add(y)),
        _ => None,
    }
}

/// `min(a, b)` (tighter); `+∞` is the maximum.
fn min(a: Bnd, b: Bnd) -> Bnd {
    match (a, b) {
        (Some(x), Some(y)) => Some(x.min(y)),
        (Some(x), None) | (None, Some(x)) => Some(x),
        (None, None) => None,
    }
}

/// `max(a, b)` (looser); `+∞` is the maximum.
fn max(a: Bnd, b: Bnd) -> Bnd {
    match (a, b) {
        (Some(x), Some(y)) => Some(x.max(y)),
        _ => None,
    }
}

/// `a ≤ b` in the bound order (`+∞` is the top).
fn le(a: Bnd, b: Bnd) -> bool {
    match (a, b) {
        (_, None) => true,
        (None, Some(_)) => false,
        (Some(x), Some(y)) => x <= y,
    }
}

/// Combine two equal-shape matrices element-wise.
fn combine(a: &[Vec<Bnd>], b: &[Vec<Bnd>], f: impl Fn(Bnd, Bnd) -> Bnd) -> Vec<Vec<Bnd>> {
    a.iter()
        .zip(b)
        .map(|(ra, rb)| ra.iter().zip(rb).map(|(&x, &y)| f(x, y)).collect())
        .collect()
}

/// A zone over a fixed number of variables (node 0 is the constant zero).
#[derive(Debug, Clone, PartialEq)]
pub struct Zone {
    /// `m[i][j]` = upper bound on `vⱼ − vᵢ`. Side length `n + 1` (the +1 is the
    /// zero node). Empty for the sizeless [`AbstractDomain::bottom`].
    m: Vec<Vec<Bnd>>,
    /// Whether this is the (sizeless) infeasible bottom element.
    bottom: bool,
}

impl Zone {
    /// The unconstrained zone over `nvars` variables (all differences `+∞`,
    /// diagonal `0`).
    pub fn top(nvars: usize) -> Zone {
        let side = nvars + 1;
        let mut m = vec![vec![None; side]; side];
        for (i, row) in m.iter_mut().enumerate() {
            row[i] = Some(0);
        }
        Zone { m, bottom: false }
    }

    /// Whether the zone is the infeasible (empty) element.
    pub fn is_bottom(&self) -> bool {
        self.bottom
    }

    fn nvars(&self) -> usize {
        self.m.len().saturating_sub(1)
    }

    /// Tighten with `vₐ − v_b ≤ c` (indices into the variable space, `0` = zero
    /// node), then re-close. A no-op when out of range.
    pub fn add_constraint(&mut self, a: usize, b: usize, c: i128) {
        if self.bottom || a >= self.m.len() || b >= self.m.len() {
            return;
        }
        self.m[b][a] = min(self.m[b][a], Some(c)); // v_a - v_b ≤ c  ⇒  m[b][a]
        self.close();
    }

    /// The bound on `vⱼ − vᵢ`, or `+∞`.
    fn get(&self, i: usize, j: usize) -> Bnd {
        if self.bottom {
            Some(i128::MIN) // vacuously tight
        } else {
            self.m[i][j]
        }
    }

    /// `vₖ ≤ c` (upper bound on a variable, `k` ≥ 1).
    pub fn upper(&self, k: usize) -> Bnd {
        self.get(0, k)
    }

    /// `vₖ ≥ −m[k][0]` ⇒ lower bound; returns `Some(lo)` or `None` (`−∞`).
    pub fn lower(&self, k: usize) -> Option<i128> {
        self.get(k, 0).map(|c| -c)
    }

    /// The difference bound `vₐ − v_b ≤ c` if finite.
    pub fn diff_upper(&self, a: usize, b: usize) -> Option<i128> {
        self.get(b, a)
    }

    /// Forget everything known about variable `k` (set all its differences to
    /// `+∞`), e.g. before an opaque assignment to it.
    pub fn forget(&mut self, k: usize) {
        if self.bottom || k == 0 || k >= self.m.len() {
            return;
        }
        for i in 0..self.m.len() {
            if i != k {
                self.m[k][i] = None;
                self.m[i][k] = None;
            }
        }
        self.m[k][k] = Some(0);
    }

    /// The self-update `vₖ ← vₖ + c` (an exact translation of variable `k`):
    /// every bound on `vₖ` and every difference involving it shifts by `c`. This
    /// preserves closure, so no re-closing is needed — and it is what models a
    /// loop induction step `i = i + 1` without losing `i`'s relations.
    pub fn translate(&mut self, k: usize, c: i128) {
        if self.bottom || k == 0 || k >= self.m.len() {
            return;
        }
        for j in 0..self.m.len() {
            if j == k {
                continue;
            }
            self.m[j][k] = self.m[j][k].map(|b| b.saturating_add(c)); // v_k - v_j up by c
            self.m[k][j] = self.m[k][j].map(|b| b.saturating_sub(c)); // v_j - v_k down by c
        }
    }

    /// Floyd–Warshall transitive tightening; marks `bottom` on a negative cycle.
    fn close(&mut self) {
        let side = self.m.len();
        for k in 0..side {
            for i in 0..side {
                for j in 0..side {
                    let through = add(self.m[i][k], self.m[k][j]);
                    self.m[i][j] = min(self.m[i][j], through);
                }
            }
        }
        for i in 0..side {
            if matches!(self.m[i][i], Some(c) if c < 0) {
                self.bottom = true;
                return;
            }
        }
    }
}

impl AbstractDomain for Zone {
    fn bottom() -> Self {
        Zone { m: Vec::new(), bottom: true }
    }

    fn join(&self, other: &Self) -> Self {
        if self.bottom {
            return other.clone();
        }
        if other.bottom || self.nvars() != other.nvars() {
            return self.clone();
        }
        Zone { m: combine(&self.m, &other.m, max), bottom: false }
    }

    fn meet(&self, other: &Self) -> Self {
        if self.bottom || other.bottom {
            return Zone::bottom();
        }
        if self.nvars() != other.nvars() {
            return self.clone();
        }
        let mut z = Zone { m: combine(&self.m, &other.m, min), bottom: false };
        z.close();
        z
    }

    fn widen(&self, other: &Self) -> Self {
        if self.bottom {
            return other.clone();
        }
        if other.bottom || self.nvars() != other.nvars() {
            return self.clone();
        }
        // Keep-if-equal: a bound survives only if unchanged, else → +∞. The
        // finite-entry count strictly decreases until a fixpoint, so this
        // terminates in at most (n+1)² widenings.
        let m = combine(&self.m, &other.m, |x, y| if x == y { x } else { None });
        Zone { m, bottom: false }
    }

    fn leq(&self, other: &Self) -> bool {
        if self.bottom {
            return true;
        }
        if other.bottom || self.nvars() != other.nvars() {
            return false;
        }
        let side = self.m.len();
        (0..side).all(|i| (0..side).all(|j| le(self.m[i][j], other.m[i][j])))
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn constraints_close_transitively() {
        // x ≤ y and y ≤ z  ⇒  x ≤ z. Vars: 1=x, 2=y, 3=z.
        let mut z = Zone::top(3);
        z.add_constraint(1, 2, 0); // x - y ≤ 0
        z.add_constraint(2, 3, 0); // y - z ≤ 0
        assert_eq!(z.diff_upper(1, 3), Some(0), "x - z ≤ 0 by transitivity");
    }

    #[test]
    fn contradiction_is_bottom() {
        // x ≤ y and y < x (y - x ≤ -1) is infeasible.
        let mut z = Zone::top(2);
        z.add_constraint(1, 2, 0); // x - y ≤ 0
        z.add_constraint(2, 1, -1); // y - x ≤ -1
        assert!(z.is_bottom());
    }

    #[test]
    fn bounds_and_differences() {
        let mut z = Zone::top(2);
        z.add_constraint(1, 0, 10); // x - zero ≤ 10  ⇒  x ≤ 10
        z.add_constraint(0, 1, 0); // zero - x ≤ 0   ⇒  x ≥ 0
        assert_eq!(z.upper(1), Some(10));
        assert_eq!(z.lower(1), Some(0));
    }

    #[test]
    fn join_is_the_looser_bound() {
        let mut a = Zone::top(1);
        a.add_constraint(1, 0, 5); // x ≤ 5
        let mut b = Zone::top(1);
        b.add_constraint(1, 0, 10); // x ≤ 10
        let j = a.join(&b);
        assert_eq!(j.upper(1), Some(10), "join keeps the looser bound");
    }

    #[test]
    fn widen_keeps_stable_drops_unstable() {
        // Stable difference (x - y ≤ 0 in both) kept; unstable bound dropped.
        let mut a = Zone::top(2);
        a.add_constraint(1, 2, 0); // x - y ≤ 0
        a.add_constraint(1, 0, 5); // x ≤ 5
        let mut b = Zone::top(2);
        b.add_constraint(1, 2, 0); // x - y ≤ 0  (stable)
        b.add_constraint(1, 0, 6); // x ≤ 6      (grew)
        let w = a.widen(&b);
        assert_eq!(w.diff_upper(1, 2), Some(0), "stable difference kept");
        assert_eq!(w.upper(1), None, "unstable bound widened to +inf");
    }

    #[test]
    fn widen_terminates_by_decreasing_finite_entries() {
        // Repeated widening against a growing bound reaches a fixpoint fast.
        let mut acc = Zone::top(1);
        acc.add_constraint(1, 0, 0);
        for k in 1..100 {
            let mut next = Zone::top(1);
            next.add_constraint(1, 0, k);
            let w = acc.widen(&next);
            if w == acc {
                // Reached a fixpoint; the growing bound was dropped to +inf.
                assert_eq!(w.upper(1), None);
                return;
            }
            acc = w;
        }
        panic!("widening did not converge");
    }

    #[test]
    fn bottom_is_identity_for_join() {
        let mut a = Zone::top(1);
        a.add_constraint(1, 0, 3);
        assert_eq!(Zone::bottom().join(&a), a);
        assert_eq!(a.join(&Zone::bottom()), a);
        assert!(Zone::bottom().leq(&a));
    }
}
