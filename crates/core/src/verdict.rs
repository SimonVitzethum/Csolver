//! The three-valued verdict and its combination lattice.

use std::fmt;

/// The outcome of a verification, at any granularity (obligation, function,
/// module).
///
/// The ordering of "informativeness" is `Pass`/`Fail` (definite) above
/// `Unknown` (indefinite). Combination is *not* a simple lattice meet; it
/// encodes the soundness policy described on [`Verdict::combine`].
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum Verdict {
    /// Proven safe under the reported assumptions.
    Pass,
    /// Proven unsafe: a concrete counterexample exists.
    Fail,
    /// Neither proven nor refuted (residual obligations remain).
    Unknown,
}

impl Verdict {
    /// Combine two verdicts under CSolver's soundness policy:
    ///
    /// * any `Fail` dominates — a single proven violation fails the whole;
    /// * otherwise any `Unknown` dominates — we never round up to `Pass`;
    /// * only `Pass` ⊕ `Pass` is `Pass`.
    ///
    /// This makes `combine` associative and commutative with identity `Pass`,
    /// so folding a collection of obligation verdicts is well-defined.
    pub fn combine(self, other: Verdict) -> Verdict {
        match (self, other) {
            (Verdict::Fail, _) | (_, Verdict::Fail) => Verdict::Fail,
            (Verdict::Unknown, _) | (_, Verdict::Unknown) => Verdict::Unknown,
            (Verdict::Pass, Verdict::Pass) => Verdict::Pass,
        }
    }

    /// Fold a sequence of verdicts. An empty sequence is vacuously `Pass`
    /// (there is nothing that could be unsafe).
    pub fn combine_all<I: IntoIterator<Item = Verdict>>(iter: I) -> Verdict {
        iter.into_iter().fold(Verdict::Pass, Verdict::combine)
    }

    /// Whether this verdict is a definite `Pass`.
    pub fn is_pass(self) -> bool {
        matches!(self, Verdict::Pass)
    }

    /// A stable machine-friendly identifier.
    pub fn id(self) -> &'static str {
        match self {
            Verdict::Pass => "PASS",
            Verdict::Fail => "FAIL",
            Verdict::Unknown => "UNKNOWN",
        }
    }
}

impl fmt::Display for Verdict {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str(self.id())
    }
}

#[cfg(test)]
mod tests {
    use super::Verdict::*;
    use super::*;

    #[test]
    fn fail_dominates_everything() {
        assert_eq!(Fail.combine(Pass), Fail);
        assert_eq!(Pass.combine(Fail), Fail);
        assert_eq!(Fail.combine(Unknown), Fail);
        assert_eq!(Unknown.combine(Fail), Fail);
        assert_eq!(Fail.combine(Fail), Fail);
    }

    #[test]
    fn unknown_dominates_pass_but_not_fail() {
        assert_eq!(Pass.combine(Unknown), Unknown);
        assert_eq!(Unknown.combine(Pass), Unknown);
        assert_eq!(Unknown.combine(Unknown), Unknown);
    }

    #[test]
    fn pass_is_the_identity() {
        for v in [Pass, Fail, Unknown] {
            assert_eq!(Pass.combine(v), v);
            assert_eq!(v.combine(Pass), v);
        }
    }

    #[test]
    fn combine_is_commutative_and_associative() {
        let all = [Pass, Fail, Unknown];
        for a in all {
            for b in all {
                assert_eq!(a.combine(b), b.combine(a), "commutativity {a}/{b}");
                for c in all {
                    assert_eq!(
                        a.combine(b).combine(c),
                        a.combine(b.combine(c)),
                        "associativity {a}/{b}/{c}"
                    );
                }
            }
        }
    }

    #[test]
    fn empty_fold_is_pass() {
        assert_eq!(Verdict::combine_all(std::iter::empty()), Pass);
        assert_eq!(Verdict::combine_all([Pass, Pass]), Pass);
        assert_eq!(Verdict::combine_all([Pass, Unknown, Pass]), Unknown);
        assert_eq!(Verdict::combine_all([Pass, Unknown, Fail]), Fail);
    }
}
