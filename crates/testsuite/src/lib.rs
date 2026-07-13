//! # csolver-testsuite
//!
//! Shared MSIR fixtures that model real (often `unsafe`) Rust patterns at the
//! IR level, plus the integration tests in `tests/`. Keeping the fixtures in a
//! library lets multiple integration tests reuse them.
//!
//! As real frontends land (LLVM-IR, MIR), these hand-built fixtures are
//! progressively replaced by lowering actual Rust/`unsafe` programs.

use csolver_core::{RegionKind, SafetyProperty};
use csolver_ir::{
    BasicBlock, BinOp, BlockId, CmpOp, Condition, FuncId, Function, Inst, Module, Operand, RegId,
    RValue, Terminator, Type,
};


// --- module split (mechanical refactor) ---
mod loop_fixtures;
mod memory_fixtures;
mod ptr_fixtures;
mod scalar_fixtures;
pub use loop_fixtures::*;
pub use memory_fixtures::*;
pub use ptr_fixtures::*;
pub use scalar_fixtures::*;
