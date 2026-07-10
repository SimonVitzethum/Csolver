//! Streaming whole-program fact extraction.
//!
//! Bundles the four whole-program precondition builders — summaries, scalar
//! preconditions, pointer contracts, member-provenance — behind one incremental
//! API: fold each module in with [`WholeProgramFacts::push_module`] (after which it
//! may be dropped), then [`WholeProgramFacts::finalize`] to the four results. Peak
//! memory is bounded by the compact facts, not the resident IR, so a whole-kernel
//! pass runs in a few GB regardless of the codebase size. The results are
//! bit-identical to running each pass on the fully linked module (each builder is
//! proven equivalent in `contracts` / `csolver_symbolic`).

use crate::contracts::{ContractFacts, FieldFacts, ScalarFacts};
use csolver_ir::{FieldContract, FuncId, Module, PtrContract};
use csolver_symbolic::{Summary, SummaryFacts};
use std::collections::HashMap;

/// Incremental builder of the whole-program facts.
#[derive(Default)]
pub struct WholeProgramFacts {
    summaries: SummaryFacts,
    scalars: ScalarFacts,
    contracts: ContractFacts,
    fields: FieldFacts,
    n_functions: usize,
}

impl WholeProgramFacts {
    /// A fresh, empty builder.
    pub fn new() -> WholeProgramFacts {
        WholeProgramFacts::default()
    }

    /// Fold one module into every builder. The module is only read here; the caller
    /// may drop it immediately after.
    pub fn push_module(&mut self, m: &Module) {
        self.n_functions += m.functions.len();
        self.summaries.push_module(m);
        self.scalars.push_module(m);
        self.contracts.push_module(m);
        self.fields.push_module(m);
    }

    /// Finalize all four passes. Pointer contracts feed member-provenance, exactly
    /// as in the linked pipeline (`verify_module`).
    pub fn finalize(self, closed_world: bool) -> ProgramFacts {
        let summaries = self.summaries.finalize();
        let scalars = self.scalars.finalize(closed_world);
        let ptr_contracts = self.contracts.finalize(closed_world);
        let field_contracts = self.fields.finalize(&ptr_contracts, closed_world);
        ProgramFacts {
            n_functions: self.n_functions,
            summaries,
            scalars,
            ptr_contracts,
            field_contracts,
        }
    }
}

/// The finalized whole-program facts, keyed by the streaming-assigned global
/// `FuncId`s (identical to what `merge_modules` would assign).
pub struct ProgramFacts {
    /// Total functions folded in.
    pub n_functions: usize,
    /// Per-function effect summary.
    pub summaries: HashMap<FuncId, Summary>,
    /// Per integer parameter, its synthesized `[lo, hi]` value-range precondition.
    pub scalars: HashMap<(FuncId, u32), (i128, i128)>,
    /// Per pointer parameter, its synthesized region contract.
    pub ptr_contracts: HashMap<(FuncId, u32), PtrContract>,
    /// Per pointer parameter, the valid-pointer fields of its aggregate.
    pub field_contracts: HashMap<(FuncId, u32), Vec<FieldContract>>,
}
