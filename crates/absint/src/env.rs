//! A per-register interval environment — the abstract state the interval
//! analysis propagates through the CFG.

use crate::domain::AbstractDomain;
use crate::interval::Interval;
use csolver_ir::RegId;
use std::collections::{BTreeMap, BTreeSet};

/// An abstract environment mapping SSA registers to intervals.
///
/// An absent register is implicitly `Interval::top()` (no information). To keep
/// `PartialEq` meaningful, `top` entries are never stored explicitly.
/// [`IntervalState::Unreachable`] is the lattice bottom (the point is not
/// reached on any path so far).
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum IntervalState {
    /// No execution reaches here (lattice bottom).
    Unreachable,
    /// Reachable, with the given non-top register intervals.
    Reachable(BTreeMap<RegId, Interval>),
}

impl IntervalState {
    /// The top environment (reachable, every register unconstrained).
    pub fn top() -> Self {
        IntervalState::Reachable(BTreeMap::new())
    }

    /// Whether this state is reachable.
    pub fn is_reachable(&self) -> bool {
        matches!(self, IntervalState::Reachable(_))
    }

    /// The interval currently known for `r` (top if unconstrained, bottom if
    /// the state is unreachable).
    pub fn get(&self, r: RegId) -> Interval {
        match self {
            IntervalState::Unreachable => Interval::Bottom,
            IntervalState::Reachable(m) => m.get(&r).copied().unwrap_or_else(Interval::top),
        }
    }

    /// Set `r` to `v` (no-op if the state is unreachable). Storing `top`
    /// removes the entry to preserve the canonical form.
    pub fn set(&mut self, r: RegId, v: Interval) {
        if let IntervalState::Reachable(m) = self {
            if v == Interval::top() {
                m.remove(&r);
            } else {
                m.insert(r, v);
            }
        }
    }

    fn keys_union<'a>(a: &'a BTreeMap<RegId, Interval>, b: &'a BTreeMap<RegId, Interval>) -> BTreeSet<RegId> {
        a.keys().chain(b.keys()).copied().collect()
    }

    /// Combine two reachable maps pointwise with `op`, treating absent keys as
    /// top and dropping any result that is top.
    fn pointwise(
        a: &BTreeMap<RegId, Interval>,
        b: &BTreeMap<RegId, Interval>,
        op: impl Fn(&Interval, &Interval) -> Interval,
    ) -> BTreeMap<RegId, Interval> {
        let mut out = BTreeMap::new();
        for r in Self::keys_union(a, b) {
            let av = a.get(&r).copied().unwrap_or_else(Interval::top);
            let bv = b.get(&r).copied().unwrap_or_else(Interval::top);
            let v = op(&av, &bv);
            if v != Interval::top() {
                out.insert(r, v);
            }
        }
        out
    }
}

impl AbstractDomain for IntervalState {
    fn bottom() -> Self {
        IntervalState::Unreachable
    }

    fn join(&self, other: &Self) -> Self {
        match (self, other) {
            (IntervalState::Unreachable, x) | (x, IntervalState::Unreachable) => x.clone(),
            (IntervalState::Reachable(a), IntervalState::Reachable(b)) => {
                IntervalState::Reachable(Self::pointwise(a, b, Interval::join))
            }
        }
    }

    fn meet(&self, other: &Self) -> Self {
        match (self, other) {
            (IntervalState::Unreachable, _) | (_, IntervalState::Unreachable) => {
                IntervalState::Unreachable
            }
            (IntervalState::Reachable(a), IntervalState::Reachable(b)) => {
                IntervalState::Reachable(Self::pointwise(a, b, Interval::meet))
            }
        }
    }

    fn widen(&self, other: &Self) -> Self {
        match (self, other) {
            (IntervalState::Unreachable, x) | (x, IntervalState::Unreachable) => x.clone(),
            (IntervalState::Reachable(a), IntervalState::Reachable(b)) => {
                IntervalState::Reachable(Self::pointwise(a, b, |x, y| x.widen(y)))
            }
        }
    }

    fn narrow(&self, other: &Self) -> Self {
        match (self, other) {
            (IntervalState::Unreachable, _) | (_, IntervalState::Unreachable) => {
                IntervalState::Unreachable
            }
            (IntervalState::Reachable(a), IntervalState::Reachable(b)) => {
                IntervalState::Reachable(Self::pointwise(a, b, |x, y| x.narrow(y)))
            }
        }
    }

    fn leq(&self, other: &Self) -> bool {
        match (self, other) {
            (IntervalState::Unreachable, _) => true,
            (_, IntervalState::Unreachable) => false,
            (IntervalState::Reachable(a), IntervalState::Reachable(b)) => {
                Self::keys_union(a, b).into_iter().all(|r| {
                    let av = a.get(&r).copied().unwrap_or_else(Interval::top);
                    let bv = b.get(&r).copied().unwrap_or_else(Interval::top);
                    av.leq(&bv)
                })
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn unreachable_is_bottom() {
        let bot = IntervalState::Unreachable;
        let top = IntervalState::top();
        assert!(bot.leq(&top));
        assert!(!top.leq(&bot));
        assert_eq!(bot.join(&top), top);
    }

    #[test]
    fn set_and_get_roundtrip() {
        let mut s = IntervalState::top();
        s.set(RegId(0), Interval::range(0, 9));
        assert_eq!(s.get(RegId(0)), Interval::range(0, 9));
        // Unconstrained register reads as top.
        assert_eq!(s.get(RegId(1)), Interval::top());
    }

    #[test]
    fn join_keeps_only_intersecting_constraints() {
        let mut a = IntervalState::top();
        a.set(RegId(0), Interval::range(0, 5));
        a.set(RegId(1), Interval::range(0, 0));
        let mut b = IntervalState::top();
        b.set(RegId(0), Interval::range(10, 20));
        // RegId(1) absent in b => top => joined away.
        let j = a.join(&b);
        assert_eq!(j.get(RegId(0)), Interval::range(0, 20));
        assert_eq!(j.get(RegId(1)), Interval::top());
    }

    #[test]
    fn top_entries_are_not_stored() {
        let mut s = IntervalState::top();
        s.set(RegId(0), Interval::top());
        assert_eq!(s, IntervalState::top());
    }
}
