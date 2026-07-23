use super::*;

/// Verify a single function in isolation (no interprocedural summaries or
/// parameter contracts), drawing obligation ids from `next_id`.
pub fn verify_function(f: &Function, config: &Config, next_id: &mut u32) -> FunctionReport {
    verify_function_with(
        f, None, &HashMap::new(), &[], &[], &[], &HashMap::new(), &HashMap::new(),
        &HashMap::new(), &HashMap::new(), &HashMap::new(), None, &HashMap::new(), config, true, next_id,
    )
}

/// Verify a single function, optionally using module-wide summaries for calls
/// and per-parameter pointer contracts.
#[allow(clippy::too_many_arguments)]
pub(crate) fn verify_function_with(
    f: &Function,
    summaries: Option<&HashMap<FuncId, Summary>>,
    name_summaries: &HashMap<String, Summary>,
    contracts: &[Option<PtrContract>],
    field_contracts: &[Vec<FieldContract>],
    scalar_pre: &[Option<(i128, i128)>],
    globals: &HashMap<String, csolver_ir::GlobalDef>,
    prov_grants: &HashMap<u32, std::collections::HashSet<u32>>,
    global_fn_ptrs: &HashMap<String, Vec<(u64, FuncId)>>,
    global_ptr_fields: &HashMap<String, Vec<(u64, String)>>,
    reg_ptr_hints: &HashMap<csolver_ir::RegId, csolver_ir::PtrHint>,
    mmio_region: Option<csolver_ir::MmioHandler>,
    devirt: &HashMap<csolver_ir::RegId, String>,
    config: &Config,
    exported: bool,
    next_id: &mut u32,
) -> FunctionReport {
    let analysis = config.use_intervals.then(|| analyze_intervals(f));
    let symbolic = config.use_symbolic.then(|| match summaries {
        // Hand the interval analysis (already computed for interval discharge) to
        // the executor so it is not recomputed — a clone instead of a 2nd fixpoint.
        Some(s) => discharge_with_scalars(
            f, s, name_summaries, contracts, field_contracts, scalar_pre, globals, prov_grants,
            global_fn_ptrs, global_ptr_fields, analysis.as_ref(), config.time_budget, config.bug_finding, exported,
            config.assume_valid_params, config.aliasing_model,
            // Flat machine-code memory (a binary / assembly front-end): heap regions modelled
            // from a call contract are prove-only for bounds (guards on a heap index are not
            // reliably reconstructable from spilled registers), keeping temporal refutation.
            matches!(config.level, csolver_core::SourceLevel::Elf | csolver_core::SourceLevel::Asm),
            config.assume_valid_returns,
            config.assume_valid_loop_ptrs,
            config.assume_param_buffer_len,
            config.assume_struct_tail,
            config.assume_valid_mmio,
            config.assume_field_invariants,
            reg_ptr_hints,
            mmio_region,
            devirt,
        ),
        None => discharge_function(f),
    });

    let truncated = symbolic.as_ref().is_some_and(|r| r.truncated);
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
                // Size-overflow is a bug-finding-only obligation: in sound `verify` mode
                // it is not enumerated, so it never affects PASS/FAIL there (an allocation
                // size is treated as non-wrapping under `alloc-succeeds`, as before). Only
                // the kernel bug-finding mode checks it.
                if matches!(
                    property,
                    SafetyProperty::NoSizeOverflow
                        | SafetyProperty::DataRace
                        | SafetyProperty::DoubleFetch
                        | SafetyProperty::SleepInAtomic
                        | SafetyProperty::TaintedSink
                        | SafetyProperty::TypestateViolation
                        | SafetyProperty::SecretDependent
                        | SafetyProperty::NoDivByZero
                        | SafetyProperty::NoShiftOverflow
                        | SafetyProperty::NoArithOverflow
                        | SafetyProperty::ValidIndirectTarget
                ) && !config.bug_finding
                {
                    continue;
                }
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
                    // No decision recorded. If the executor proved this block **unreachable**
                    // (every live edge into it was bit-precisely infeasible), the obligation is
                    // *vacuously satisfied*: no concrete execution runs the instruction, so it
                    // cannot be violated. Otherwise the op was genuinely not decided.
                    None if symbolic.as_ref().is_some_and(|r| r.dead_blocks.contains(&block.id)) => {
                        proven_by_symbolic_memory(&predicate, &sym_assumptions)
                    }
                    None => open_memory(property, &predicate, not_analyzed_reason(&symbolic)),
                };
                outcomes.push(ObligationOutcome { obligation, result });
            }

            // Rust aliasing (borrow-stack) violation (`--aliasing-model`): a **record-only**
            // obligation — the executor records a decision at a Load/Store ONLY when it finds a
            // violation (a write through a shared `&T`, or a use of a `&mut` after an aliasing
            // reborrow invalidated it). So query it explicitly and add a FAIL obligation only
            // when a violation was found; a safe access records nothing (no obligation), so this
            // never turns a safe access UNKNOWN. Off unless the aliasing model is enabled.
            if config.aliasing_model
                && matches!(inst, Inst::Load { .. } | Inst::Store { .. } | Inst::Call { .. })
            {
                let property = SafetyProperty::NoAliasingViolation;
                if let Some(d) = symbolic.as_ref().and_then(|r| r.mem_decision(block.id, index, property)) {
                    if !d.proven {
                        let id = ObligationId(*next_id);
                        *next_id += 1;
                        let location = Location::level_only(config.level)
                            .in_function(f.name.as_str())
                            .at_instruction(index as u32)
                            .with_raw(block.inst_spans.get(index).cloned().flatten());
                        let obligation = ProofObligation::new(id, property, location, d.predicate.clone());
                        let result = match &d.refutation {
                            Some(model) => refuted_by_symbolic(property, &d.predicate, model.clone()),
                            None => open_memory(property, &d.predicate, &d.residual),
                        };
                        outcomes.push(ObligationOutcome { obligation, result });
                    }
                }
            }
        }
        // Terminator-level obligation: a `return` of a pointer into this frame's
        // own stack is a dangling return (use-after-return in the making). The
        // executor records it at the terminator slot (`insts.len()`); enumerate it
        // here so the recorded decision is actually read. Bug-finding-only, like
        // the other report-only classes — strict `verify` never raises it.
        if config.bug_finding && matches!(block.term, Terminator::Return(Some(_))) {
            let property = SafetyProperty::NoDanglingDeref;
            let index = block.insts.len();
            let id = ObligationId(*next_id);
            *next_id += 1;
            let location = Location::level_only(config.level)
                .in_function(f.name.as_str())
                .at_instruction(index as u32);
            let decision = symbolic
                .as_ref()
                .and_then(|r| r.mem_decision(block.id, index, property));
            let predicate = decision
                .map(|d| d.predicate.clone())
                .unwrap_or_else(|| property.describe().to_string());
            let obligation = ProofObligation::new(id, property, location, predicate.clone());
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

    let verdict = Verdict::combine_all(outcomes.iter().map(ObligationOutcome::verdict));
    let lock_edges = symbolic
        .as_ref()
        .map(|r| r.lock_edges.clone())
        .unwrap_or_default();
    let race_accesses = symbolic
        .as_ref()
        .map(|r| r.race_accesses.clone())
        .unwrap_or_default();
    let race_trace = symbolic
        .as_ref()
        .map(|r| r.race_trace.clone())
        .unwrap_or_default();
    FunctionReport {
        function: f.name.clone(),
        verdict,
        outcomes,
        truncated,
        lock_edges,
        race_accesses,
        race_trace,
    }
}

/// Combine the interval result and the symbolic result into one obligation
/// outcome. Intervals are tried first (cheapest); an interval `Unknown`
/// escalates to the symbolic linear proof.
pub(crate) fn discharge(
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

pub(crate) fn proven_by_intervals(predicate: &str, note: &str) -> ObligationResult {
    ObligationResult::Proven(ProofTree::new(ProofStep::leaf(
        predicate.to_string(),
        Justification::AbstractInterpretation {
            domain: "interval".into(),
            invariant: format!("{predicate} holds for the inferred interval ({note})"),
        },
    )))
}

pub(crate) fn proven_by_symbolic(predicate: &str, note: &str) -> ObligationResult {
    let tree = ProofTree::new(ProofStep::leaf(
        predicate.to_string(),
        Justification::Unsat {
            solver: "internal-linear".into(),
            unsat_core: vec![format!("path condition implies `{predicate}` ({note})")],
        },
    ))
    .with_assumptions(vec![LINEAR_ASSUMPTION.into()]);
    ObligationResult::Proven(tree)
}

pub(crate) fn proven_by_symbolic_memory(predicate: &str, assumptions: &[String]) -> ObligationResult {
    let tree = ProofTree::new(ProofStep::leaf(
        predicate.to_string(),
        Justification::Unsat {
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
pub(crate) fn not_analyzed_reason(symbolic: &Option<SymbolicReport>) -> &'static str {
    match symbolic {
        None => "memory operation not analyzed (symbolic analysis disabled)",
        Some(r) if r.truncated => {
            "memory operation not analyzed (symbolic exploration truncated at the visit budget)"
        }
        Some(_) => "memory operation not analyzed (reached but not decided by the \
                    symbolic memory model: loop body or unsupported op)",
    }
}

pub(crate) fn open_memory(property: SafetyProperty, predicate: &str, reason: &str) -> ObligationResult {
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

pub(crate) fn refuted(property: SafetyProperty, predicate: &str, note: &str) -> ObligationResult {
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
pub(crate) fn refuted_by_symbolic(
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

pub(crate) fn open(property: SafetyProperty, predicate: &str, note: &str) -> ObligationResult {
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
pub(crate) fn render_condition(c: &Condition) -> String {
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

pub(crate) fn join(cs: &[Condition], sep: &str) -> String {
    if cs.is_empty() {
        return "true".to_string();
    }
    cs.iter()
        .map(render_condition)
        .collect::<Vec<_>>()
        .join(sep)
}

pub(crate) fn render_cmp(op: csolver_ir::CmpOp) -> &'static str {
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

pub(crate) fn render_operand(op: &Operand) -> String {
    match op {
        Operand::Reg(r) => format!("{r}"),
        Operand::Const(Const::Int(bv)) => format!("{}", bv.unsigned()),
        Operand::Const(Const::Null) => "null".into(),
        Operand::Const(Const::Undef) => "undef".into(),
        Operand::Const(Const::Symbol(s)) => format!("@{s}"),
        Operand::Const(Const::SymbolOffset(s, off)) => format!("@{s}+{off}"),
    }
}
