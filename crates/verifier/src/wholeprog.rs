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
    /// MMIO dispatch handlers by name, unioned across every file. A handler may be defined in
    /// one file and registered (its ops named) in another (`register_read_memory`), so its
    /// dispatch bound must be recovered whole-program: `finalize` emits a `size ∈ [1, 8]` scalar
    /// precondition for each, keyed by name, so the per-file overlay applies it wherever the
    /// handler is actually defined.
    mmio_handlers: HashMap<String, csolver_ir::MmioHandler>,
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
        for (name, h) in &m.mmio_handlers {
            self.mmio_handlers.entry(name.clone()).or_insert(*h);
        }
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
        for (name, h) in other.mmio_handlers {
            self.mmio_handlers.entry(name).or_insert(h);
        }
    }

    /// Finalize all four passes. Pointer contracts feed member-provenance, exactly
    /// as in the linked pipeline (`verify_module`).
    pub fn finalize(self, closed_world: bool) -> ProgramFacts {
        // Grab the external name → global-id map before `finalize` consumes the
        // builder, so each finalized fact can be paired back to its function's name
        // for on-demand cross-file resolution (2b). All four builders assign ids in the
        // same module-push order, so this one id space keys every fact map below.
        let name_to_id: HashMap<String, FuncId> = self.summaries.name_to_id().clone();
        // External global-id → name (bijective on externals), for re-keying the
        // whole-program preconditions by the function's name.
        let id_to_name: HashMap<FuncId, String> =
            name_to_id.iter().map(|(n, &id)| (id, n.clone())).collect();
        let summaries = self.summaries.finalize();
        let name_summaries: HashMap<String, Summary> = name_to_id
            .iter()
            .filter_map(|(name, id)| summaries.get(id).map(|s| (name.clone(), s.clone())))
            .collect();
        let scalars = self.scalars.finalize(closed_world);
        let ptr_contracts = self.contracts.finalize(closed_world);
        let field_contracts = self.fields.finalize(&ptr_contracts, closed_world);
        // Re-key each whole-program precondition by the **external name** of its
        // function, so pass 2 can overlay it onto the matching function in a per-file
        // module (the on-demand cross-file precondition path). Restricted to external
        // names: an internal/static's contract is already file-complete and must never
        // be matched across files (two files may define same-named statics). Only sound
        // to apply under closed-world — the extraction mode of these very facts.
        let by_name = |g: &FuncId| id_to_name.get(g).cloned();
        let mut name_scalars: HashMap<(String, u32), (i128, i128)> = scalars
            .iter()
            .filter_map(|(&(g, p), v)| by_name(&g).map(|n| ((n, p), *v)))
            .collect();
        // Emit the MMIO dispatch bound `size ∈ [1, 8]` as a name-keyed scalar precondition for
        // every handler (whole-program union), so a handler defined in one file but registered
        // in another (`register_read_memory`) is bounded wherever it is verified. Sound: it is
        // a real invariant of how the memory core dispatches. A genuine synthesized range (from
        // direct callers) is narrower or equal, so it wins where present.
        for (name, h) in &self.mmio_handlers {
            name_scalars.entry((name.clone(), h.size_param)).or_insert((1, 8));
        }
        let name_ptr_contracts = ptr_contracts
            .iter()
            .filter_map(|(&(g, p), v)| by_name(&g).map(|n| ((n, p), *v)))
            .collect();
        let name_field_contracts = field_contracts
            .iter()
            .filter_map(|(&(g, p), v)| by_name(&g).map(|n| ((n, p), v.clone())))
            .collect();
        ProgramFacts {
            n_functions: self.n_functions,
            summaries,
            name_summaries,
            scalars,
            ptr_contracts,
            field_contracts,
            name_scalars,
            name_ptr_contracts,
            name_field_contracts,
            name_mmio: self.mmio_handlers,
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
    /// [`scalars`](Self::scalars) re-keyed by external function name (pass-2 overlay).
    pub name_scalars: HashMap<(String, u32), (i128, i128)>,
    /// [`ptr_contracts`](Self::ptr_contracts) re-keyed by external function name.
    pub name_ptr_contracts: HashMap<(String, u32), PtrContract>,
    /// [`field_contracts`](Self::field_contracts) re-keyed by external function name.
    pub name_field_contracts: HashMap<(String, u32), Vec<FieldContract>>,
    /// MMIO dispatch handlers by name (whole-program union). Applied to the handler wherever it
    /// is defined — **even when it is an `--auto-entries` entry** (exported): the memory-core
    /// dispatch bound (`size ∈ {1,2,4,8}`, `addr + size ≤ region_size`) is a real invariant of
    /// how the handler is invoked, not a caller convention, so unlike `name_scalars` it is not
    /// gated on non-exported linkage.
    pub name_mmio: HashMap<String, csolver_ir::MmioHandler>,
}

impl ProgramFacts {
    /// A borrowing bundle of the four name-keyed whole-program fact maps, as consumed
    /// by [`verify_module_whole_program`](crate::verify_module_whole_program) to resolve
    /// a per-file module's cross-file calls and overlay its callees' whole-program
    /// preconditions.
    pub fn context(&self) -> WholeProgramContext<'_> {
        WholeProgramContext {
            name_summaries: &self.name_summaries,
            name_scalars: &self.name_scalars,
            name_ptr_contracts: &self.name_ptr_contracts,
            name_field_contracts: &self.name_field_contracts,
            name_mmio: &self.name_mmio,
        }
    }
}

/// A borrowing view of the whole-program facts keyed by function name — everything
/// pass 2 needs to analyse one file with whole-program precision without linking:
/// cross-file `Symbol` calls resolve to `name_summaries`, and an external callee's
/// whole-program preconditions (`name_*`) overlay its per-file (open-world) contracts.
///
/// The precondition overlays are only sound when the facts were extracted
/// **closed-world** (the union of call sites is then provably complete); the effect
/// summaries are sound unconditionally (an intrinsic property of each callee).
#[derive(Clone, Copy)]
pub struct WholeProgramContext<'a> {
    /// Cross-file effect summaries, keyed by callee name.
    pub name_summaries: &'a HashMap<String, Summary>,
    /// Whole-program scalar preconditions, keyed by function name.
    pub name_scalars: &'a HashMap<(String, u32), (i128, i128)>,
    /// Whole-program pointer contracts, keyed by function name.
    pub name_ptr_contracts: &'a HashMap<(String, u32), PtrContract>,
    /// Whole-program member-provenance field contracts, keyed by function name.
    pub name_field_contracts: &'a HashMap<(String, u32), Vec<FieldContract>>,
    /// Whole-program MMIO dispatch handlers, keyed by function name (applied even when exported).
    pub name_mmio: &'a HashMap<String, csolver_ir::MmioHandler>,
}
