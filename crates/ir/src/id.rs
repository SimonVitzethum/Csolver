//! Typed, dense indices into an MSIR [`crate::Module`].
//!
//! Each id is a thin `u32` newtype. Using distinct types for functions,
//! blocks and registers makes it impossible to index the wrong table by
//! accident — a frequent source of bugs in IR tooling.

use std::fmt;

macro_rules! index_id {
    ($(#[$m:meta])* $name:ident, $prefix:literal) => {
        $(#[$m])*
        #[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord)]
        pub struct $name(pub u32);

        impl $name {
            /// The underlying index.
            pub fn index(self) -> usize {
                self.0 as usize
            }
        }

        impl fmt::Display for $name {
            fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
                write!(f, concat!($prefix, "{}"), self.0)
            }
        }
    };
}

index_id!(
    /// Identifies a [`crate::Function`] within a [`crate::Module`].
    FuncId, "fn"
);
index_id!(
    /// Identifies a [`crate::BasicBlock`] within a [`crate::Function`].
    BlockId, "bb"
);
index_id!(
    /// Identifies an SSA register (value) within a [`crate::Function`].
    RegId, "%"
);
