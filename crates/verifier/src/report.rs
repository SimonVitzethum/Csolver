//! The verifier's result types.

use csolver_core::{Assumption, ObligationResult, ProofObligation, Verdict};

/// One obligation paired with the result of trying to discharge it.
#[derive(Debug, Clone)]
pub struct ObligationOutcome {
    /// The obligation.
    pub obligation: ProofObligation,
    /// Its discharge result.
    pub result: ObligationResult,
}

impl ObligationOutcome {
    /// The verdict this single obligation contributes.
    pub fn verdict(&self) -> Verdict {
        self.result.verdict()
    }
}

/// The verification result for one function.
#[derive(Debug, Clone)]
pub struct FunctionReport {
    /// The function name.
    pub function: String,
    /// The rolled-up verdict over all its obligations.
    pub verdict: Verdict,
    /// Per-obligation outcomes.
    pub outcomes: Vec<ObligationOutcome>,
    /// Whether symbolic exploration was **truncated at its budget** (visit or
    /// wall-clock) for this function — so its `Unknown` obligations are a
    /// resource limit, not genuine undecidability. Lets a scan *defer* a
    /// budget-limited unit for a full-effort re-run instead of accepting Unknown.
    pub truncated: bool,
}

impl FunctionReport {
    /// Count outcomes with the given verdict.
    pub fn count(&self, verdict: Verdict) -> usize {
        self.outcomes
            .iter()
            .filter(|o| o.verdict() == verdict)
            .count()
    }
}

/// The verification result for a whole module.
#[derive(Debug, Clone)]
pub struct ModuleReport {
    /// The module name.
    pub module: String,
    /// The rolled-up verdict over all functions.
    pub verdict: Verdict,
    /// Per-function reports.
    pub functions: Vec<FunctionReport>,
    /// Assumptions the proofs in this module depend on.
    pub assumptions: Vec<Assumption>,
}

impl ModuleReport {
    /// Total obligations with the given verdict across the module.
    pub fn count(&self, verdict: Verdict) -> usize {
        self.functions.iter().map(|f| f.count(verdict)).sum()
    }

    /// Whether any function's symbolic exploration was truncated at its budget.
    pub fn any_truncated(&self) -> bool {
        self.functions.iter().any(|f| f.truncated)
    }
}
