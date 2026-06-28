//! # csolver-cfg
//!
//! Control-flow analysis over MSIR functions: the [`Cfg`] (with predecessor and
//! successor adjacency and reverse-postorder), [`Dominators`] and
//! [`PostDominators`] (Cooper–Harvey–Kennedy), and natural-loop detection
//! ([`loops::Loops`]).
//!
//! Everything here is *structural* and exact — there is no approximation, so
//! these results are trusted inputs to the analyses that follow (the fixpoint
//! iterator widens at loop headers identified here; the verifier uses
//! post-dominance to attribute obligations to paths).

pub mod dominators;
pub mod graph;
pub mod loops;

pub use dominators::{Dominators, PostDominators};
pub use graph::Cfg;
pub use loops::{Loop, Loops};
