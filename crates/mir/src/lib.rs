//! # csolver-mir — Rust MIR frontend (M0 stub)
//!
//! Lowers Rust MIR into MSIR. MIR is the richest input: it still carries
//! borrow-checker facts, panic edges, and precise types, all of which sharpen
//! the obligations CSolver generates.
//!
//! ## Status
//!
//! Interface only. [`MirFrontend::lower`] currently reports
//! [`csolver_core::Error::Unsupported`]; the real lowering (planned milestone
//! M5) will consume `rustc`'s MIR (via a `rustc_driver` callback or the
//! `-Zunpretty=mir`/stable-MIR surface) and translate statements/terminators
//! into [`csolver_ir::Inst`]s, attaching the canonical safety checks plus extra
//! ones derived from borrow facts.

use csolver_core::{Error, Result};
use csolver_ir::{Frontend, Module};

/// Placeholder input: a path to a crate or a MIR dump. The real type will be a
/// structured handle to rustc's MIR.
#[derive(Debug, Clone)]
pub struct MirInput {
    /// Path to the crate root or MIR dump.
    pub path: String,
}

/// The Rust MIR frontend.
#[derive(Debug, Default, Clone, Copy)]
pub struct MirFrontend;

impl Frontend for MirFrontend {
    type Input = MirInput;

    fn name(&self) -> &'static str {
        "mir"
    }

    fn lower(&self, _input: MirInput) -> Result<Module> {
        Err(Error::unsupported(
            "MIR lowering is not implemented yet (planned milestone M5)",
        ))
    }
}
