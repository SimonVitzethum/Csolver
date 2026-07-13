//! # csolver-llvm — LLVM-IR frontend
//!
//! Lowers a practical subset of textual LLVM IR (`.ll`) into MSIR, so the
//! audited MSIR analysis core can verify code compiled from Rust without any
//! change. The structural work is PHI elimination (PHIs become MSIR block
//! parameters; see [`lower`]).
//!
//! ## Supported subset
//!
//! `define`d functions; `void`/`iN`/`ptr`/`[N x T]` types (and legacy `T*`);
//! `alloca`, `load`, `store`, `getelementptr` (pointer-arith and array forms),
//! the integer binary ops, `icmp`, the integer/pointer casts, `call`, `phi`;
//! and the `ret`/`br`/`unreachable` terminators. Constructs outside the subset
//! (vectors, exceptions, `switch`, metadata, complex GEPs, …) are reported as
//! [`csolver_core::Error::Unsupported`] so the caller degrades to `UNKNOWN`
//! rather than silently mis-modelling them — the sound default.
//!
//! ## Soundness obligation
//!
//! The lowering must refine the LLVM semantics (every concrete `.ll` execution
//! is a concrete MSIR execution). The mapping is opcode-local and documented in
//! [`lower`]; see `Verification/`.

mod debuginfo;
mod lexer;
mod lower;
mod parser;

pub use lower::lower_module;
pub use parser::{parse_module, LModule};

use csolver_core::Result;
use csolver_ir::{Frontend, Module};

/// LLVM-IR source input.
#[derive(Debug, Clone)]
pub struct LlvmInput {
    /// The textual `.ll` module.
    pub source: String,
    /// A name for diagnostics (e.g. the file name).
    pub name: String,
}

/// The LLVM-IR frontend.
#[derive(Debug, Default, Clone, Copy)]
pub struct LlvmFrontend;

impl Frontend for LlvmFrontend {
    type Input = LlvmInput;

    fn name(&self) -> &'static str {
        "llvm"
    }

    fn lower(&self, input: LlvmInput) -> Result<Module> {
        let parsed = parse_module(&input.source)?;
        lower_module(&parsed, &input.name)
    }
}

#[cfg(test)]
#[path = "llvm_tests.rs"]
mod tests;
#[cfg(test)]
#[path = "llvm_tests2.rs"]
mod tests2;
