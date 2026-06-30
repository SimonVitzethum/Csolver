//! # csolver-verifier — orchestration
//!
//! Turns an MSIR [`Module`] into a [`ModuleReport`] of `PASS`/`FAIL`/`UNKNOWN`
//! verdicts with proofs, counterexamples, and residual obligations.
//!
//! ## Discharge strategy (escalating, cheapest first)
//!
//! 1. **Abstract interpretation.** Run the interval analysis and evaluate each
//!    [`csolver_ir::Inst::SafetyCheck`] condition. Because intervals
//!    over-approximate, "condition holds on the whole over-approximation" is a
//!    sound `PASS`, and "holds on none of it" is a sound `FAIL`.
//! 2. **Symbolic execution + SMT.** (Milestones M2+.) For conditions the
//!    intervals leave [`csolver_absint::Trivalent::Unknown`], hand the residual
//!    to symbolic execution and the SMT solver.
//! 3. **Residual.** Anything still open becomes `UNKNOWN` with the precise
//!    remaining condition and a suggested minimal assumption.
//!
//! ## Soundness
//!
//! The roll-up uses [`Verdict::combine`]: any `FAIL` fails the function/module,
//! and anything not provably `PASS` degrades to `UNKNOWN`. A function with no
//! emitted obligations is vacuously `PASS` *over the obligations present* — the
//! report is always relative to the checks the frontend emitted.

mod report;

pub use report::{FunctionReport, ModuleReport, ObligationOutcome};

use csolver_absint::{analyze_intervals, Trivalent};
use csolver_core::{
    proof::{Justification, ProofStep, ProofTree},
    Assumption, CounterExample, Location, Model, ObligationId, ObligationResult, ProofObligation,
    ResidualObligation, SafetyProperty, SourceLevel, SuggestedAssumption, Verdict,
};
use csolver_ir::{Condition, Const, FuncId, Function, Inst, Module, Operand, PtrContract};
use csolver_symbolic::{
    discharge_full, discharge_function, summarize_module, Summary, SymOutcome, SymbolicReport,
};
use std::collections::HashMap;

/// The id of the assumption that symbolic linear proofs depend on.
const LINEAR_ASSUMPTION: &str = "linear-no-overflow";

/// Verifier configuration.
#[derive(Debug, Clone)]
pub struct Config {
    /// The source level to tag obligation locations with (for reporting).
    pub level: SourceLevel,
    /// Whether to run the interval abstract interpretation pass.
    pub use_intervals: bool,
    /// Whether to escalate undecided checks to symbolic execution + the solver.
    pub use_symbolic: bool,
}

impl Default for Config {
    fn default() -> Self {
        Config {
            level: SourceLevel::Llvm,
            use_intervals: true,
            use_symbolic: true,
        }
    }
}

/// Verify every function in `module`.
///
/// Interprocedural: function summaries are computed once and used so that calls
/// preserve pointer provenance and respect the callee's memory effects.
pub fn verify_module(module: &Module, config: &Config) -> ModuleReport {
    let summaries = config.use_symbolic.then(|| summarize_module(module));
    let mut next_id: u32 = 0;
    let mut functions = Vec::with_capacity(module.functions.len());
    for f in &module.functions {
        let contracts = module.contracts_for(f);
        functions.push(verify_function_with(
            f,
            summaries.as_ref(),
            &contracts,
            config,
            &mut next_id,
        ));
    }

    // Functions a frontend could not lower are reported as UNKNOWN (never a
    // silent omission), so the module verdict reflects that they were not
    // verified.
    for (uname, reason) in &module.unanalyzed {
        let id = ObligationId(next_id);
        next_id += 1;
        let location = Location::level_only(config.level).in_function(uname.as_str());
        let obligation = ProofObligation::new(
            id,
            SafetyProperty::ValidReference,
            location,
            "the function body is analyzable",
        );
        let result = ObligationResult::Open {
            residual: vec![ResidualObligation {
                predicate: "whole function body".into(),
                reason: format!("not analyzed by the frontend: {reason}"),
            }],
            suggested: vec![],
        };
        functions.push(FunctionReport {
            function: uname.clone(),
            verdict: Verdict::Unknown,
            outcomes: vec![ObligationOutcome { obligation, result }],
        });
    }

    let verdict = Verdict::combine_all(functions.iter().map(|f| f.verdict));

    // Surface — once each — every assumption any proof in the module depends on.
    let mut ids: std::collections::BTreeSet<String> = std::collections::BTreeSet::new();
    for func in &functions {
        for o in &func.outcomes {
            if let ObligationResult::Proven(tree) = &o.result {
                ids.extend(tree.assumptions.iter().cloned());
            }
        }
    }
    let assumptions = ids.into_iter().map(assumption_record).collect();

    ModuleReport {
        module: module.name.clone(),
        verdict,
        functions,
        assumptions,
    }
}

/// Expand a known assumption id into its full record for the report.
fn assumption_record(id: String) -> Assumption {
    match id.as_str() {
        LINEAR_ASSUMPTION => Assumption {
            id,
            statement: "the integer/offset/size quantities reasoned about are \
                        non-negative and fit in isize::MAX, so they do not wrap and \
                        their signed and unsigned comparisons coincide"
                .into(),
            justification: "the internal linear decision procedure models bit-vectors \
                            as mathematical integers; Rust caps any allocation at \
                            isize::MAX bytes, so offsets, sizes and valid indices lie \
                            in [0, isize::MAX] where this holds. Programs using the \
                            full unsigned range with the sign bit set need the \
                            bit-precise SMT backend (later milestone)"
                .into(),
        },
        "alloc-succeeds" => Assumption {
            id,
            statement: "allocation requests succeed: they return a valid, non-null, \
                        suitably-sized and -aligned block (out-of-memory is not modelled)"
                .into(),
            justification: "the symbolic memory model treats an allocation as producing \
                            a live region; programs that must handle allocation failure \
                            need that null-check modelled separately"
                .into(),
        },
        "param-contracts" => Assumption {
            id,
            statement: "pointer parameters satisfy their declared contracts: a \
                        `dereferenceable(N)`/`align`/`readonly`/`writeonly` pointer \
                        points to N valid bytes with that alignment and access mode"
                .into(),
            justification: "these come from the parameters' Rust reference types \
                            (`&[T]`, `&mut [T; N]`, …), which the compiler guarantees and \
                            emits as LLVM parameter attributes; the proof is relative to \
                            the caller upholding the reference's validity"
                .into(),
        },
        "slice-abi" => Assumption {
            id,
            statement: "a `(ptr, usize len)` parameter pair is a Rust slice `&[T]`: \
                        the pointer is valid for `len * size_of::<T>()` bytes"
                .into(),
            justification: "the front-end paired an aligned pointer parameter with the \
                            following length parameter per the Rust slice ABI and took the \
                            element size from a use; this is a heuristic, made explicit so \
                            the proof's trust boundary is visible"
                .into(),
        },
        _ => Assumption {
            statement: id.clone(),
            id,
            justification: String::new(),
        },
    }
}

/// Verify a single function in isolation (no interprocedural summaries or
/// parameter contracts), drawing obligation ids from `next_id`.
pub fn verify_function(f: &Function, config: &Config, next_id: &mut u32) -> FunctionReport {
    verify_function_with(f, None, &[], config, next_id)
}

/// Verify a single function, optionally using module-wide summaries for calls
/// and per-parameter pointer contracts.
fn verify_function_with(
    f: &Function,
    summaries: Option<&HashMap<FuncId, Summary>>,
    contracts: &[Option<PtrContract>],
    config: &Config,
    next_id: &mut u32,
) -> FunctionReport {
    let analysis = config.use_intervals.then(|| analyze_intervals(f));
    let symbolic = config.use_symbolic.then(|| match summaries {
        Some(s) => discharge_full(f, s, contracts),
        None => discharge_function(f),
    });

    let sym_assumptions = symbolic
        .as_ref()
        .map(|r| r.assumptions.clone())
        .unwrap_or_default();

    let mut outcomes = Vec::new();
    for block in &f.blocks {
        for (index, inst) in block.insts.iter().enumerate() {
            if let Inst::SafetyCheck {
                property,
                condition,
                note,
            } = inst
            {
                // Explicit check: intervals first, then symbolic scalar.
                let id = ObligationId(*next_id);
                *next_id += 1;
                let location = Location::level_only(config.level)
                    .in_function(f.name.as_str())
                    .at_instruction(index as u32)
                    .with_raw(block.inst_spans.get(index).cloned().flatten());
                let predicate = render_condition(condition);
                let obligation = ProofObligation::new(id, *property, location, predicate.clone());

                let interval = analysis
                    .as_ref()
                    .map(|a| a.eval_condition(f, block.id, index, condition))
                    .unwrap_or(Trivalent::Unknown);
                let sym = symbolic.as_ref().and_then(|r| r.outcome(block.id, index));

                let result = discharge(interval, sym, *property, &predicate, note);
                outcomes.push(ObligationOutcome { obligation, result });
                continue;
            }

            // Implied memory-op obligations: discharged by the symbolic memory
            // model. Enumerated from the IR so a memory op is never silently
            // treated as safe (when symbolic did not run, it is `Open`).
            for &property in inst.implied_checks() {
                let id = ObligationId(*next_id);
                *next_id += 1;
                let location = Location::level_only(config.level)
                    .in_function(f.name.as_str())
                    .at_instruction(index as u32)
                    .with_raw(block.inst_spans.get(index).cloned().flatten());
                let decision = symbolic
                    .as_ref()
                    .and_then(|r| r.mem_decision(block.id, index, property));
                let predicate = decision
                    .map(|d| d.predicate.clone())
                    .unwrap_or_else(|| property.describe().to_string());
                let obligation =
                    ProofObligation::new(id, property, location, predicate.clone());

                let result = match decision {
                    Some(d) if d.proven => proven_by_symbolic_memory(&predicate, &sym_assumptions),
                    Some(d) => match &d.refutation {
                        Some(model) => refuted_by_symbolic(property, &predicate, model.clone()),
                        None => open_memory(property, &predicate, &d.residual),
                    },
                    None => open_memory(property, &predicate, not_analyzed_reason(&symbolic)),
                };
                outcomes.push(ObligationOutcome { obligation, result });
            }
        }
    }

    let verdict = Verdict::combine_all(outcomes.iter().map(ObligationOutcome::verdict));
    FunctionReport {
        function: f.name.clone(),
        verdict,
        outcomes,
    }
}

/// Combine the interval result and the symbolic result into one obligation
/// outcome. Intervals are tried first (cheapest); an interval `Unknown`
/// escalates to the symbolic linear proof.
fn discharge(
    interval: Trivalent,
    symbolic: Option<SymOutcome>,
    property: SafetyProperty,
    predicate: &str,
    note: &str,
) -> ObligationResult {
    match interval {
        Trivalent::True => proven_by_intervals(predicate, note),
        Trivalent::False => refuted(property, predicate, note),
        Trivalent::Unknown => match symbolic {
            Some(SymOutcome::Proven) => proven_by_symbolic(predicate, note),
            Some(SymOutcome::Refuted(model)) => refuted_by_symbolic(property, predicate, model),
            _ => open(property, predicate, note),
        },
    }
}

fn proven_by_intervals(predicate: &str, note: &str) -> ObligationResult {
    ObligationResult::Proven(ProofTree::new(ProofStep::leaf(
        predicate.to_string(),
        Justification::AbstractInterpretation {
            domain: "interval".into(),
            invariant: format!("{predicate} holds for the inferred interval ({note})"),
        },
    )))
}

fn proven_by_symbolic(predicate: &str, note: &str) -> ObligationResult {
    let tree = ProofTree::new(ProofStep::leaf(
        predicate.to_string(),
        Justification::SmtUnsat {
            solver: "internal-linear".into(),
            unsat_core: vec![format!("path condition implies `{predicate}` ({note})")],
        },
    ))
    .with_assumptions(vec![LINEAR_ASSUMPTION.into()]);
    ObligationResult::Proven(tree)
}

fn proven_by_symbolic_memory(predicate: &str, assumptions: &[String]) -> ObligationResult {
    let tree = ProofTree::new(ProofStep::leaf(
        predicate.to_string(),
        Justification::SmtUnsat {
            solver: "symbolic-memory".into(),
            unsat_core: vec![predicate.to_string()],
        },
    ))
    .with_assumptions(assumptions.to_vec());
    ObligationResult::Proven(tree)
}

/// Why a memory op produced no symbolic decision, kept distinct so the scaling
/// sweep can separate three very different situations that all read as `Open`:
///
/// - **disabled** — symbolic analysis was switched off (a config, not a limit);
/// - **truncated** — exploration hit its visit budget, after which *no* decisions
///   are reported for the whole function (a deliberate soundness rule: truncation
///   must never hide a violating path, so every op falls back to `Open`);
/// - **undecided** — exploration ran to completion and *reached* this op but the
///   symbolic memory model could not decide it (a loop body it does not summarise,
///   or an unsupported construct) — the genuine per-op engine limit.
///
/// All three are sound: the op is still enumerated as an obligation and stays
/// `Open`, so the function can never `PASS` on an unanalysed access. The split only
/// makes the *reason* honest, so a coverage cap is not mistaken for an engine gap
/// (nor either for a hidden front-end truncation, which cannot reach here — a
/// dropped body yields fewer obligations or a whole-function parse error, not an
/// `Open` memory op). See `Verification/`.
fn not_analyzed_reason(symbolic: &Option<SymbolicReport>) -> &'static str {
    match symbolic {
        None => "memory operation not analyzed (symbolic analysis disabled)",
        Some(r) if r.truncated => {
            "memory operation not analyzed (symbolic exploration truncated at the visit budget)"
        }
        Some(_) => "memory operation not analyzed (reached but not decided by the \
                    symbolic memory model: loop body or unsupported op)",
    }
}

fn open_memory(property: SafetyProperty, predicate: &str, reason: &str) -> ObligationResult {
    ObligationResult::Open {
        residual: vec![ResidualObligation {
            predicate: predicate.to_string(),
            reason: reason.to_string(),
        }],
        suggested: vec![SuggestedAssumption {
            assumption: format!("an invariant establishing `{predicate}`"),
            rationale: format!("{} would then follow", property.describe()),
        }],
    }
}

fn refuted(property: SafetyProperty, predicate: &str, note: &str) -> ObligationResult {
    ObligationResult::Refuted(CounterExample {
        summary: format!(
            "{}: {predicate} is false for every value in the inferred interval ({note})",
            property.describe()
        ),
        // The interval proof establishes the violation for the whole
        // over-approximation; for symbolic definite violations the bit-precise
        // layer supplies a concrete model (see `refuted_by_symbolic`).
        model: Model::default(),
        trace: vec![format!("at check: {note}")],
    })
}

/// A refutation discharged by the symbolic engine: on a genuinely reachable
/// (exact) path the property is *always* violated, witnessed by a concrete
/// bit-precise model.
fn refuted_by_symbolic(
    property: SafetyProperty,
    predicate: &str,
    model: Model,
) -> ObligationResult {
    ObligationResult::Refuted(CounterExample {
        summary: format!(
            "{}: `{predicate}` is violated for the witnessed inputs on a reachable path",
            property.describe()
        ),
        model,
        trace: vec!["symbolic execution reached this point with the model below".into()],
    })
}

fn open(property: SafetyProperty, predicate: &str, note: &str) -> ObligationResult {
    ObligationResult::Open {
        residual: vec![ResidualObligation {
            predicate: predicate.to_string(),
            reason: "neither interval analysis nor the linear symbolic layer could \
                     decide it; needs a stronger domain or full SMT (later increment)"
                .into(),
        }],
        suggested: vec![SuggestedAssumption {
            assumption: format!("a bound establishing `{predicate}` at this point"),
            rationale: format!("{} would then follow directly ({note})", property.describe()),
        }],
    }
}

/// Render a condition to a readable predicate string.
fn render_condition(c: &Condition) -> String {
    match c {
        Condition::True => "true".to_string(),
        Condition::Cmp { op, lhs, rhs } => {
            format!("{} {} {}", render_operand(lhs), render_cmp(*op), render_operand(rhs))
        }
        Condition::And(cs) => join(cs, " && "),
        Condition::Or(cs) => join(cs, " || "),
        Condition::Not(c) => format!("!({})", render_condition(c)),
    }
}

fn join(cs: &[Condition], sep: &str) -> String {
    if cs.is_empty() {
        return "true".to_string();
    }
    cs.iter()
        .map(render_condition)
        .collect::<Vec<_>>()
        .join(sep)
}

fn render_cmp(op: csolver_ir::CmpOp) -> &'static str {
    use csolver_ir::CmpOp::*;
    match op {
        Eq => "==",
        Ne => "!=",
        Ult | Slt => "<",
        Ule | Sle => "<=",
        Ugt | Sgt => ">",
        Uge | Sge => ">=",
    }
}

fn render_operand(op: &Operand) -> String {
    match op {
        Operand::Reg(r) => format!("{r}"),
        Operand::Const(Const::Int(bv)) => format!("{}", bv.unsigned()),
        Operand::Const(Const::Null) => "null".into(),
        Operand::Const(Const::Undef) => "undef".into(),
        Operand::Const(Const::Symbol(s)) => format!("@{s}"),
    }
}
