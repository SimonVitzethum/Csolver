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

    /// Absorb a fact set built in parallel over a *later* range of files, so shards
    /// extracted concurrently can be merged in file order into ids identical to a
    /// single sequential push — the finalized results are then bit-identical.
    pub fn merge(&mut self, other: WholeProgramFacts) {
        self.n_functions += other.n_functions;
        self.summaries.merge(other.summaries);
        self.scalars.merge(other.scalars);
        self.contracts.merge(other.contracts);
        self.fields.merge(other.fields);
    }

    /// Finalize all four passes. Pointer contracts feed member-provenance, exactly
    /// as in the linked pipeline (`verify_module`).
    pub fn finalize(self, closed_world: bool) -> ProgramFacts {
        // Grab the external name → global-id map before `finalize` consumes the
        // builder, so each finalized summary can be paired back to its callee name
        // for on-demand cross-file call resolution (2b).
        let name_to_id: HashMap<String, FuncId> = self.summaries.name_to_id().clone();
        let summaries = self.summaries.finalize();
        let name_summaries: HashMap<String, Summary> = name_to_id
            .into_iter()
            .filter_map(|(name, id)| summaries.get(&id).map(|s| (name, s.clone())))
            .collect();
        let scalars = self.scalars.finalize(closed_world);
        let ptr_contracts = self.contracts.finalize(closed_world);
        let field_contracts = self.fields.finalize(&ptr_contracts, closed_world);
        ProgramFacts {
            n_functions: self.n_functions,
            summaries,
            name_summaries,
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
    /// Effect summary keyed by external callee **name** (first definition winning) —
    /// the map [`verify_module_whole_program`](crate::verify_module_whole_program)
    /// consumes to resolve cross-file `Symbol` calls to their real callee effect.
    pub name_summaries: HashMap<String, Summary>,
    /// Per integer parameter, its synthesized `[lo, hi]` value-range precondition.
    pub scalars: HashMap<(FuncId, u32), (i128, i128)>,
    /// Per pointer parameter, its synthesized region contract.
    pub ptr_contracts: HashMap<(FuncId, u32), PtrContract>,
    /// Per pointer parameter, the valid-pointer fields of its aggregate.
    pub field_contracts: HashMap<(FuncId, u32), Vec<FieldContract>>,
}
