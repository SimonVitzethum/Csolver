//! The abstract-domain (lattice) contract.

/// A lattice with the operations the fixpoint solver needs.
///
/// Laws (checked for the interval domain in its tests):
/// * `join` is associative, commutative, idempotent; `bottom()` is its
///   identity.
/// * `leq` is a partial order and `a.leq(&a.join(b))` for all `a, b`.
/// * `widen` is *extensive* (`a.leq(&a.widen(b))` and `b.leq(&a.widen(b))`) and
///   any ascending chain accelerated by `widen` stabilizes in finitely many
///   steps — this is what makes the solver terminate.
pub trait AbstractDomain: Clone + PartialEq {
    /// The least element (no information / unreachable).
    fn bottom() -> Self;

    /// Least upper bound.
    fn join(&self, other: &Self) -> Self;

    /// Greatest lower bound. A default is not provided because not every domain
    /// has an exact meet; domains that need it implement it.
    fn meet(&self, other: &Self) -> Self;

    /// Widening operator used at loop headers to enforce termination.
    fn widen(&self, other: &Self) -> Self;

    /// Narrowing operator used to recover precision after widening. The default
    /// is the identity (`self`), which is always sound (it never lowers below
    /// the post-fixpoint).
    fn narrow(&self, _other: &Self) -> Self {
        self.clone()
    }

    /// The lattice order: `self ⊑ other`.
    fn leq(&self, other: &Self) -> bool;
}
