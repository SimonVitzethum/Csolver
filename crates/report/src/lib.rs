//! # csolver-report
//!
//! Renders a [`ModuleReport`] for humans ([`render_text`]) and machines
//! ([`render_json`], a dependency-free hand-rolled encoder). The renderers are
//! pure functions of the report, so they are easy to test and stable to diff.

use csolver_core::{ObligationResult, Verdict};
use csolver_verifier::{FunctionReport, ModuleReport, ObligationOutcome};
use std::fmt::Write as _;

/// Render a report as plain text suitable for a terminal.
pub fn render_text(report: &ModuleReport) -> String {
    let mut s = String::new();
    let _ = writeln!(
        s,
        "module {}: {}  (pass {}, fail {}, unknown {})",
        report.module,
        report.verdict,
        report.count(Verdict::Pass),
        report.count(Verdict::Fail),
        report.count(Verdict::Unknown),
    );
    for f in &report.functions {
        render_function_text(&mut s, f);
    }
    if !report.assumptions.is_empty() {
        let _ = writeln!(s, "\nassumptions:");
        for a in &report.assumptions {
            let _ = writeln!(s, "  - [{}] {}", a.id, a.statement);
        }
    }
    s
}

fn render_function_text(s: &mut String, f: &FunctionReport) {
    let _ = writeln!(s, "\n  fn {} : {}", f.function, f.verdict);
    if f.outcomes.is_empty() {
        let _ = writeln!(s, "    (no obligations emitted — vacuously PASS)");
    }
    for o in &f.outcomes {
        render_outcome_text(s, o);
    }
}

fn render_outcome_text(s: &mut String, o: &ObligationOutcome) {
    let ob = &o.obligation;
    let _ = writeln!(
        s,
        "    {} {} [{}] @ {}",
        o.verdict(),
        ob.id,
        ob.property,
        ob.location
    );
    let _ = writeln!(s, "        predicate: {}", ob.predicate);
    match &o.result {
        ObligationResult::Proven(tree) => {
            let _ = writeln!(s, "        proof: {}", justification_line(tree));
        }
        ObligationResult::Refuted(cx) => {
            let _ = writeln!(s, "        counterexample: {}", cx.summary);
            // The witnessing inputs — the concrete values that drive the violation,
            // so a FAIL is reproducible, not just asserted.
            for a in &cx.model.assignments {
                let _ = writeln!(s, "          input {} = {}", a.name, a.value);
            }
        }
        ObligationResult::Open { residual, suggested } => {
            for r in residual {
                let _ = writeln!(s, "        residual: {} ({})", r.predicate, r.reason);
            }
            for a in suggested {
                let _ = writeln!(s, "        suggest: assume {} — {}", a.assumption, a.rationale);
            }
        }
    }
}

fn justification_line(tree: &csolver_core::ProofTree) -> String {
    use csolver_core::proof::Justification::*;
    match &tree.root.justification {
        Axiom { name } => format!("axiom {name}"),
        AbstractInterpretation { domain, invariant } => {
            format!("by {domain} abstract interpretation: {invariant}")
        }
        Unsat { solver, .. } => format!("{solver} found the negation unsatisfiable"),
        CaseSplit { cases } => format!("case split over {} cases", cases.len()),
        ByAssumption { assumption_id } => format!("by assumption {assumption_id}"),
        _ => "by a justification not yet rendered".to_string(),
    }
}

/// Render a report as a compact JSON object (hand-rolled; no serde dependency).
pub fn render_json(report: &ModuleReport) -> String {
    let mut s = String::new();
    s.push('{');
    field_str(&mut s, "module", &report.module);
    s.push(',');
    field_str(&mut s, "verdict", report.verdict.id());
    s.push(',');
    let _ = write!(s, "\"functions\":[");
    for (i, f) in report.functions.iter().enumerate() {
        if i > 0 {
            s.push(',');
        }
        render_function_json(&mut s, f);
    }
    s.push_str("]}");
    s
}

fn render_function_json(s: &mut String, f: &FunctionReport) {
    s.push('{');
    field_str(s, "function", &f.function);
    s.push(',');
    field_str(s, "verdict", f.verdict.id());
    s.push(',');
    let _ = write!(s, "\"obligations\":[");
    for (i, o) in f.outcomes.iter().enumerate() {
        if i > 0 {
            s.push(',');
        }
        s.push('{');
        field_str(s, "id", &o.obligation.id.to_string());
        s.push(',');
        field_str(s, "property", o.obligation.property.id());
        s.push(',');
        field_str(s, "verdict", o.verdict().id());
        s.push(',');
        field_str(s, "predicate", &o.obligation.predicate);
        s.push('}');
    }
    s.push_str("]}");
}

fn field_str(s: &mut String, key: &str, value: &str) {
    let _ = write!(s, "\"{}\":\"{}\"", escape(key), escape(value));
}

fn escape(s: &str) -> String {
    let mut out = String::with_capacity(s.len());
    for c in s.chars() {
        match c {
            '"' => out.push_str("\\\""),
            '\\' => out.push_str("\\\\"),
            '\n' => out.push_str("\\n"),
            '\t' => out.push_str("\\t"),
            '\r' => out.push_str("\\r"),
            c if (c as u32) < 0x20 => {
                let _ = write!(out, "\\u{:04x}", c as u32);
            }
            c => out.push(c),
        }
    }
    out
}

#[cfg(test)]
mod tests {
    use super::*;
    use csolver_core::{Location, ObligationId, ProofObligation, SafetyProperty, SourceLevel};
    use csolver_verifier::{FunctionReport, ModuleReport, ObligationOutcome};

    fn sample_report() -> ModuleReport {
        let ob = ProofObligation::new(
            ObligationId(0),
            SafetyProperty::InBounds,
            Location::level_only(SourceLevel::Llvm).in_function("f"),
            "0 < 4",
        );
        let proven = ObligationOutcome {
            obligation: ob,
            result: csolver_core::ObligationResult::Proven(csolver_core::ProofTree::new(
                csolver_core::proof::ProofStep::leaf(
                    "0 < 4",
                    csolver_core::proof::Justification::AbstractInterpretation {
                        domain: "interval".into(),
                        invariant: "[0,0] < 4".into(),
                    },
                ),
            )),
        };
        let func = FunctionReport {
            function: "f".into(),
            verdict: Verdict::Pass,
            outcomes: vec![proven],
            truncated: false,
            lock_edges: vec![],
            race_accesses: vec![],
            race_trace: vec![],
        };
        ModuleReport {
            module: "m".into(),
            verdict: Verdict::Pass,
            functions: vec![func],
            assumptions: vec![],
        }
    }

    #[test]
    fn text_mentions_verdict_and_proof() {
        let t = render_text(&sample_report());
        assert!(t.contains("module m: PASS"));
        assert!(t.contains("interval abstract interpretation"));
    }

    #[test]
    fn text_renders_the_counterexample_witness() {
        use csolver_core::proof::{Assignment, CounterExample, Model};
        use csolver_core::BitVector;
        let ob = ProofObligation::new(
            ObligationId(1),
            SafetyProperty::InBounds,
            Location::level_only(SourceLevel::Mir).in_function("f"),
            "index < len",
        );
        let cx = CounterExample {
            summary: "access is within allocation bounds: violated".into(),
            model: Model {
                assignments: vec![Assignment { name: "arg0".into(), value: BitVector::new(64, 10) }],
            },
            trace: vec![],
        };
        let func = FunctionReport {
            function: "f".into(),
            verdict: Verdict::Fail,
            outcomes: vec![ObligationOutcome {
                obligation: ob,
                result: csolver_core::ObligationResult::Refuted(cx),
            }],
            truncated: false,
            lock_edges: vec![],
            race_accesses: vec![],
            race_trace: vec![],
        };
        let report = ModuleReport {
            module: "m".into(),
            verdict: Verdict::Fail,
            functions: vec![func],
            assumptions: vec![],
        };
        let t = render_text(&report);
        assert!(t.contains("counterexample:"), "{t}");
        // The witnessing input value is rendered, so the FAIL is reproducible.
        assert!(t.contains("input arg0 = 10"), "witness value renders: {t}");
    }

    #[test]
    fn json_is_well_formed_ish() {
        let j = render_json(&sample_report());
        assert!(j.starts_with('{') && j.ends_with('}'));
        assert!(j.contains("\"verdict\":\"PASS\""));
        assert!(j.contains("\"property\":\"in_bounds\""));
    }
}
