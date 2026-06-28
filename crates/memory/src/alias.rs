//! Alias relationships between two memory accesses.
//!
//! Aliasing is the question "can these two pointers refer to overlapping
//! bytes?". The answer drives load resolution (read-your-writes), redundant-
//! store elimination, and `noalias`/`restrict` reasoning. CSolver classifies it
//! three ways; the *decision* (which needs the path condition and the solver)
//! lives in `csolver-symbolic`, while this enum is the shared vocabulary.

/// The alias relationship between two accesses.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum AliasResult {
    /// They always refer to the same bytes (provably equal location, and the
    /// first access fully covers the second).
    Must,
    /// They might or might not overlap (the safe, conservative default).
    May,
    /// They provably never overlap (different allocations, or disjoint ranges
    /// within one allocation).
    No,
}

impl AliasResult {
    /// A stable machine-friendly identifier.
    pub fn id(self) -> &'static str {
        match self {
            AliasResult::Must => "must",
            AliasResult::May => "may",
            AliasResult::No => "no",
        }
    }

    /// Whether the two accesses are guaranteed not to interfere.
    pub fn is_disjoint(self) -> bool {
        matches!(self, AliasResult::No)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn ids_and_disjointness() {
        assert_eq!(AliasResult::Must.id(), "must");
        assert_eq!(AliasResult::May.id(), "may");
        assert_eq!(AliasResult::No.id(), "no");
        assert!(AliasResult::No.is_disjoint());
        assert!(!AliasResult::May.is_disjoint());
        assert!(!AliasResult::Must.is_disjoint());
    }
}
