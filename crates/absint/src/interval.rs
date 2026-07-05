//! The integer-interval lattice.
//!
//! Values are intervals `[lo, hi]` over the integers extended with ±∞, plus a
//! distinguished `Bottom` (the empty interval, i.e. unreachable). Bounds are
//! stored as `i128`; arithmetic saturates to ±∞ rather than overflowing, which
//! keeps the abstraction sound (an over-approximation) at the extremes.

use crate::domain::AbstractDomain;
use std::fmt;

/// An interval endpoint.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Bound {
    /// −∞.
    NegInf,
    /// A finite endpoint.
    Fin(i128),
    /// +∞.
    PosInf,
}

impl Bound {
    fn min(a: Bound, b: Bound) -> Bound {
        use Bound::*;
        match (a, b) {
            (NegInf, _) | (_, NegInf) => NegInf,
            (PosInf, x) | (x, PosInf) => x,
            (Fin(x), Fin(y)) => Fin(x.min(y)),
        }
    }

    fn max(a: Bound, b: Bound) -> Bound {
        use Bound::*;
        match (a, b) {
            (PosInf, _) | (_, PosInf) => PosInf,
            (NegInf, x) | (x, NegInf) => x,
            (Fin(x), Fin(y)) => Fin(x.max(y)),
        }
    }

    /// `a <= b` in the extended order.
    fn le(a: Bound, b: Bound) -> bool {
        use Bound::*;
        match (a, b) {
            (NegInf, _) => true,
            (_, PosInf) => true,
            (_, NegInf) => false,
            (PosInf, _) => false,
            (Fin(x), Fin(y)) => x <= y,
        }
    }

    fn add(a: Bound, b: Bound) -> Bound {
        use Bound::*;
        match (a, b) {
            // +∞ + −∞ cannot arise for valid intervals (lo+lo, hi+hi).
            (NegInf, PosInf) | (PosInf, NegInf) => Fin(0),
            (NegInf, _) | (_, NegInf) => NegInf,
            (PosInf, _) | (_, PosInf) => PosInf,
            (Fin(x), Fin(y)) => match x.checked_add(y) {
                Some(v) => Fin(v),
                None if x > 0 => PosInf,
                None => NegInf,
            },
        }
    }

    fn neg(a: Bound) -> Bound {
        match a {
            Bound::NegInf => Bound::PosInf,
            Bound::PosInf => Bound::NegInf,
            Bound::Fin(x) => Bound::Fin(x.saturating_neg()),
        }
    }

    fn mul(a: Bound, b: Bound) -> Bound {
        use Bound::*;
        match (a, b) {
            (Fin(0), _) | (_, Fin(0)) => Fin(0),
            (Fin(x), Fin(y)) => match x.checked_mul(y) {
                Some(v) => Fin(v),
                None if (x > 0) == (y > 0) => PosInf,
                None => NegInf,
            },
            (inf, Fin(k)) | (Fin(k), inf) => {
                let pos = matches!(inf, PosInf);
                if k > 0 {
                    if pos {
                        PosInf
                    } else {
                        NegInf
                    }
                } else if pos {
                    NegInf
                } else {
                    PosInf
                }
            }
            (PosInf, PosInf) | (NegInf, NegInf) => PosInf,
            (PosInf, NegInf) | (NegInf, PosInf) => NegInf,
        }
    }
}

/// An interval lattice element.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Interval {
    /// The empty interval (unreachable / no value).
    Bottom,
    /// A non-empty range `[lo, hi]` with `lo <= hi`.
    Range(Bound, Bound),
}

impl Interval {
    /// The top element `[−∞, +∞]`.
    pub fn top() -> Interval {
        Interval::Range(Bound::NegInf, Bound::PosInf)
    }

    /// The singleton `[n, n]`.
    pub fn singleton(n: i128) -> Interval {
        Interval::Range(Bound::Fin(n), Bound::Fin(n))
    }

    /// The range `[lo, hi]`, normalizing an empty range to `Bottom`.
    pub fn range(lo: i128, hi: i128) -> Interval {
        if lo <= hi {
            Interval::Range(Bound::Fin(lo), Bound::Fin(hi))
        } else {
            Interval::Bottom
        }
    }

    /// Intersection: the tightest interval contained in both (`Bottom` if they
    /// are disjoint). Used to apply a branch guard to an incoming edge.
    pub fn meet(&self, other: &Interval) -> Interval {
        match (self, other) {
            (Interval::Bottom, _) | (_, Interval::Bottom) => Interval::Bottom,
            (Interval::Range(l1, h1), Interval::Range(l2, h2)) => {
                let lo = Bound::max(*l1, *l2);
                let hi = Bound::min(*h1, *h2);
                if Bound::le(lo, hi) {
                    Interval::Range(lo, hi)
                } else {
                    Interval::Bottom
                }
            }
        }
    }

    /// The half-line `(-∞, upper]` (`< self`'s max when `strict`). Used to bound a
    /// value that a guard proves is `≤`/`<` this interval.
    pub fn as_upper_constraint(&self, strict: bool) -> Interval {
        match self.upper() {
            Some(hi) => {
                let hi = if strict { Bound::add(hi, Bound::Fin(-1)) } else { hi };
                Interval::Range(Bound::NegInf, hi)
            }
            None => Interval::Bottom,
        }
    }

    /// The half-line `[lower, +∞)` (`> self`'s min when `strict`).
    pub fn as_lower_constraint(&self, strict: bool) -> Interval {
        match self.lower() {
            Some(lo) => {
                let lo = if strict { Bound::add(lo, Bound::Fin(1)) } else { lo };
                Interval::Range(lo, Bound::PosInf)
            }
            None => Interval::Bottom,
        }
    }

    /// The lower bound, if not bottom.
    pub fn lower(&self) -> Option<Bound> {
        match self {
            Interval::Range(lo, _) => Some(*lo),
            Interval::Bottom => None,
        }
    }

    /// The upper bound, if not bottom.
    pub fn upper(&self) -> Option<Bound> {
        match self {
            Interval::Range(_, hi) => Some(*hi),
            Interval::Bottom => None,
        }
    }

    /// Whether the interval is bottom.
    pub fn is_bottom(&self) -> bool {
        matches!(self, Interval::Bottom)
    }

    /// Whether every member of `self` is `< n` (a useful in-bounds query).
    pub fn is_strictly_below(&self, n: i128) -> bool {
        match self {
            Interval::Bottom => true,
            // `hi <= n - 1`, written with a saturating decrement so `n` at
            // `i128::MIN` cannot underflow.
            Interval::Range(_, hi) => Bound::le(*hi, Bound::Fin(n.saturating_sub(1))),
        }
    }

    /// Whether every member of `self` is `>= n`.
    pub fn is_at_least(&self, n: i128) -> bool {
        match self {
            Interval::Bottom => true,
            Interval::Range(lo, _) => Bound::le(Bound::Fin(n), *lo),
        }
    }

    /// Interval addition.
    pub fn add(&self, other: &Interval) -> Interval {
        match (self, other) {
            (Interval::Bottom, _) | (_, Interval::Bottom) => Interval::Bottom,
            (Interval::Range(a, b), Interval::Range(c, d)) => {
                Interval::Range(Bound::add(*a, *c), Bound::add(*b, *d))
            }
        }
    }

    /// Interval negation.
    pub fn neg(&self) -> Interval {
        match self {
            Interval::Bottom => Interval::Bottom,
            Interval::Range(a, b) => Interval::Range(Bound::neg(*b), Bound::neg(*a)),
        }
    }

    /// Interval subtraction.
    pub fn sub(&self, other: &Interval) -> Interval {
        self.add(&other.neg())
    }

    /// Interval multiplication (via the four corner products).
    pub fn mul(&self, other: &Interval) -> Interval {
        match (self, other) {
            (Interval::Bottom, _) | (_, Interval::Bottom) => Interval::Bottom,
            (Interval::Range(a, b), Interval::Range(c, d)) => {
                let products = [
                    Bound::mul(*a, *c),
                    Bound::mul(*a, *d),
                    Bound::mul(*b, *c),
                    Bound::mul(*b, *d),
                ];
                let lo = products.iter().copied().reduce(Bound::min).unwrap_or(Bound::NegInf);
                let hi = products.iter().copied().reduce(Bound::max).unwrap_or(Bound::PosInf);
                Interval::Range(lo, hi)
            }
        }
    }
}

impl AbstractDomain for Interval {
    fn bottom() -> Self {
        Interval::Bottom
    }

    fn join(&self, other: &Self) -> Self {
        match (self, other) {
            (Interval::Bottom, x) | (x, Interval::Bottom) => *x,
            (Interval::Range(a, b), Interval::Range(c, d)) => {
                Interval::Range(Bound::min(*a, *c), Bound::max(*b, *d))
            }
        }
    }

    fn meet(&self, other: &Self) -> Self {
        match (self, other) {
            (Interval::Bottom, _) | (_, Interval::Bottom) => Interval::Bottom,
            (Interval::Range(a, b), Interval::Range(c, d)) => {
                let lo = Bound::max(*a, *c);
                let hi = Bound::min(*b, *d);
                if Bound::le(lo, hi) {
                    Interval::Range(lo, hi)
                } else {
                    Interval::Bottom
                }
            }
        }
    }

    fn widen(&self, other: &Self) -> Self {
        match (self, other) {
            (Interval::Bottom, x) => *x,
            (x, Interval::Bottom) => *x,
            (Interval::Range(a, b), Interval::Range(c, d)) => {
                // Unstable lower bound -> −∞; unstable upper bound -> +∞.
                let lo = if Bound::le(*a, *c) { *a } else { Bound::NegInf };
                let hi = if Bound::le(*d, *b) { *b } else { Bound::PosInf };
                Interval::Range(lo, hi)
            }
        }
    }

    fn narrow(&self, other: &Self) -> Self {
        // Standard interval narrowing: only refine bounds that were at infinity.
        match (self, other) {
            (Interval::Bottom, _) | (_, Interval::Bottom) => Interval::Bottom,
            (Interval::Range(a, b), Interval::Range(c, d)) => {
                let lo = if *a == Bound::NegInf { *c } else { *a };
                let hi = if *b == Bound::PosInf { *d } else { *b };
                Interval::Range(lo, hi)
            }
        }
    }

    fn leq(&self, other: &Self) -> bool {
        match (self, other) {
            (Interval::Bottom, _) => true,
            (_, Interval::Bottom) => false,
            (Interval::Range(a, b), Interval::Range(c, d)) => {
                Bound::le(*c, *a) && Bound::le(*b, *d)
            }
        }
    }
}

impl fmt::Display for Bound {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Bound::NegInf => f.write_str("-inf"),
            Bound::PosInf => f.write_str("+inf"),
            Bound::Fin(n) => write!(f, "{n}"),
        }
    }
}

impl fmt::Display for Interval {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Interval::Bottom => f.write_str("⊥"),
            Interval::Range(lo, hi) => write!(f, "[{lo}, {hi}]"),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn join_is_convex_hull() {
        let a = Interval::range(0, 5);
        let b = Interval::range(10, 20);
        assert_eq!(a.join(&b), Interval::range(0, 20));
        assert_eq!(Interval::Bottom.join(&a), a);
    }

    #[test]
    fn meet_is_intersection() {
        let a = Interval::range(0, 10);
        let b = Interval::range(5, 20);
        assert_eq!(a.meet(&b), Interval::range(5, 10));
        assert_eq!(a.meet(&Interval::range(20, 30)), Interval::Bottom);
    }

    #[test]
    fn leq_is_inclusion() {
        assert!(Interval::range(2, 4).leq(&Interval::range(0, 10)));
        assert!(!Interval::range(0, 10).leq(&Interval::range(2, 4)));
        assert!(Interval::Bottom.leq(&Interval::range(0, 0)));
        assert!(Interval::range(0, 5).leq(&Interval::top()));
    }

    #[test]
    fn widening_jumps_unstable_bounds_to_infinity() {
        // Growing upper bound -> +inf, stable lower bound stays.
        let prev = Interval::range(0, 5);
        let next = Interval::range(0, 6);
        assert_eq!(prev.widen(&next), Interval::Range(Bound::Fin(0), Bound::PosInf));
        // Both stable -> unchanged.
        assert_eq!(prev.widen(&Interval::range(0, 5)), prev);
        // widen is extensive.
        assert!(prev.leq(&prev.widen(&next)));
        assert!(next.leq(&prev.widen(&next)));
    }

    #[test]
    fn narrowing_recovers_infinite_bounds() {
        let widened = Interval::Range(Bound::Fin(0), Bound::PosInf);
        let refined = Interval::range(0, 9);
        assert_eq!(widened.narrow(&refined), Interval::range(0, 9));
    }

    #[test]
    fn arithmetic() {
        assert_eq!(Interval::range(1, 2).add(&Interval::range(3, 4)), Interval::range(4, 6));
        assert_eq!(Interval::range(1, 5).sub(&Interval::range(0, 2)), Interval::range(-1, 5));
        assert_eq!(Interval::range(2, 3).mul(&Interval::range(-1, 4)), Interval::range(-3, 12));
    }

    #[test]
    fn bound_queries() {
        let i = Interval::range(0, 9);
        assert!(i.is_strictly_below(10));
        assert!(!i.is_strictly_below(9));
        assert!(i.is_at_least(0));
        assert!(!i.is_at_least(1));
    }

    #[test]
    fn saturating_add_stays_sound() {
        let big = Interval::Range(Bound::Fin(i128::MAX - 1), Bound::Fin(i128::MAX));
        let r = big.add(&Interval::singleton(10));
        // Upper bound saturates to +inf instead of overflowing.
        assert_eq!(r.upper(), Some(Bound::PosInf));
    }
}
