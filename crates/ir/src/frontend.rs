//! The contract every frontend implements: lower some input artifact into an
//! MSIR [`Module`].
//!
//! The soundness obligation on an implementation is the refinement property
//! stated in the crate docs: every concrete behaviour of the input must be a
//! concrete behaviour of the returned module.

use crate::Module;
use csolver_core::Result;

/// A lowering from a source artifact (MIR, LLVM-IR, assembly, …) into MSIR.
pub trait Frontend {
    /// The kind of input this frontend consumes.
    type Input;

    /// A short identifier for diagnostics (e.g. `"llvm"`).
    fn name(&self) -> &'static str;

    /// Lower `input` into an MSIR module, or report why it cannot.
    ///
    /// Returning [`csolver_core::Error::Unsupported`] is the honest outcome for
    /// constructs not yet modelled; callers must degrade the verdict to
    /// `Unknown`, never silently to `Pass`.
    fn lower(&self, input: Self::Input) -> Result<Module>;
}
