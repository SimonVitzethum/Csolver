//! End-to-end tests: build MSIR fixtures, run the verifier, check verdicts and
//! the rendered report. This exercises ir → cfg → absint → verifier → report.

use csolver_core::{SafetyProperty, Verdict};
use csolver_report::{render_json, render_text};
use csolver_testsuite::{
    dangling_store, guarded_get, indirect_store, interproc_module, loop_array_store,
    masked_index_store, mixed_module, needs_solver, oob_index_store, oob_mask_check, provably_buggy,
    provably_safe, safe_buffer_store,
};
use csolver_verifier::{verify_function, verify_module, Config};

#[test]
fn provably_safe_function_passes() {
    let f = provably_safe();
    let mut id = 0;
    let report = verify_function(&f, &Config::default(), &mut id);
    assert_eq!(report.verdict, Verdict::Pass, "report: {report:?}");
    assert_eq!(report.count(Verdict::Pass), 1);
}

#[test]
fn provably_buggy_function_fails_with_counterexample() {
    let f = provably_buggy();
    let mut id = 0;
    let report = verify_function(&f, &Config::default(), &mut id);
    assert_eq!(report.verdict, Verdict::Fail);
    // The single obligation must be a concrete refutation.
    let result = &report.outcomes[0].result;
    assert!(
        matches!(result, csolver_core::ObligationResult::Refuted(_)),
        "expected a counterexample, got {result:?}"
    );
}

#[test]
fn symbolic_index_is_unknown_not_pass() {
    // Soundness: an undecided check must never be reported as PASS.
    let f = needs_solver();
    let mut id = 0;
    let report = verify_function(&f, &Config::default(), &mut id);
    assert_eq!(report.verdict, Verdict::Unknown);
    let result = &report.outcomes[0].result;
    match result {
        csolver_core::ObligationResult::Open { residual, suggested } => {
            assert!(!residual.is_empty());
            assert!(!suggested.is_empty(), "should suggest a closing assumption");
        }
        other => panic!("expected Open, got {other:?}"),
    }
}

#[test]
fn symbolic_proves_guarded_access_that_intervals_cannot() {
    let f = guarded_get();

    // With only intervals, the guarded `i < len` cannot be decided.
    let intervals_only = Config {
        use_symbolic: false,
        ..Config::default()
    };
    let mut id = 0;
    let r0 = verify_function(&f, &intervals_only, &mut id);
    assert_eq!(r0.verdict, Verdict::Unknown, "intervals alone cannot prove it");

    // With symbolic execution enabled, the path condition `i < len` discharges
    // the check: UNKNOWN becomes PASS.
    let mut id2 = 0;
    let r1 = verify_function(&f, &Config::default(), &mut id2);
    assert_eq!(r1.verdict, Verdict::Pass, "symbolic execution proves it: {r1:?}");
    assert!(matches!(
        r1.outcomes[0].result,
        csolver_core::ObligationResult::Proven(_)
    ));
}

#[test]
fn symbolic_proof_records_its_assumption() {
    let mut m = csolver_ir::Module::new("guarded");
    m.functions.push(guarded_get());
    let report = verify_module(&m, &Config::default());
    assert_eq!(report.verdict, Verdict::Pass);
    // The linear proof's trust boundary must be surfaced as an assumption.
    assert!(
        report.assumptions.iter().any(|a| a.id == "linear-no-overflow"),
        "symbolic linear PASS must record its no-overflow assumption"
    );
}

#[test]
fn symbolic_memory_proves_a_guarded_buffer_store() {
    let mut m = csolver_ir::Module::new("mem");
    m.functions.push(safe_buffer_store());
    let report = verify_module(&m, &Config::default());

    assert_eq!(report.verdict, Verdict::Pass, "report: {report:?}");
    // The store implies five obligations + one for the pointer arithmetic;
    // all must be PASS.
    let func = &report.functions[0];
    assert!(func.outcomes.len() >= 6, "expected memory obligations");
    assert!(func.outcomes.iter().all(|o| o.verdict() == Verdict::Pass));
    // Trust boundary recorded.
    assert!(report.assumptions.iter().any(|a| a.id == "alloc-succeeds"));
    assert!(report.assumptions.iter().any(|a| a.id == "linear-no-overflow"));
}

#[test]
fn loop_array_store_is_proven() {
    // `for i in 0..n { buf[i] = 0 }` — the in-loop access is proved in bounds
    // by combining the interval invariant (i >= 0) with the loop guard (i < n).
    let mut m = csolver_ir::Module::new("loop");
    m.functions.push(loop_array_store());
    let report = verify_module(&m, &Config::default());
    assert_eq!(report.verdict, Verdict::Pass, "report: {report:?}");
    assert!(report.functions[0].outcomes.iter().all(|o| o.verdict() == Verdict::Pass));
}

#[test]
fn masked_index_is_proven_bit_precisely() {
    // `buf[x & 7]` into a `[i8; 8]`. The mask bounds the index to [0, 7], so the
    // access is in bounds — but the *linear* procedure abstracts `&` as opaque
    // and cannot prove it. The pure-Rust bit-precise SAT backend decides the
    // mask exactly. This obligation is therefore a PASS that linear arithmetic
    // alone could not reach.
    let mut m = csolver_ir::Module::new("masked");
    m.functions.push(masked_index_store());
    let report = verify_module(&m, &Config::default());
    assert_eq!(report.verdict, Verdict::Pass, "report: {report:?}");
    assert!(
        report.functions[0]
            .outcomes
            .iter()
            .all(|o| o.verdict() == Verdict::Pass),
        "every obligation of the masked store must pass: {report:?}"
    );
    // The in-bounds reasoning was bit-precise, so it carries no overflow
    // assumption — only the allocation-succeeds precondition remains.
    assert!(
        !report.assumptions.iter().any(|a| a.id == "linear-no-overflow"),
        "bit-precise mask proof must not need linear-no-overflow: {:?}",
        report.assumptions
    );
}

#[test]
fn definite_violation_is_refuted_with_a_counterexample() {
    // `(x | 8) < 8` is false for every input. Intervals can't see through `|`,
    // so this is the bit-precise symbolic engine refuting a definite violation
    // on an exact path and producing a concrete witness — a FAIL that interval
    // analysis alone leaves UNKNOWN.
    let f = oob_mask_check();

    // Intervals alone cannot decide it (the bitwise `|` is opaque): UNKNOWN.
    let intervals_only = Config { use_symbolic: false, ..Config::default() };
    let mut id0 = 0;
    let r0 = verify_function(&f, &intervals_only, &mut id0);
    assert_eq!(r0.verdict, Verdict::Unknown, "intervals alone cannot decide it");

    // With symbolic execution, the violation is refuted with a counterexample.
    let mut m = csolver_ir::Module::new("oob");
    m.functions.push(f);
    let report = verify_module(&m, &Config::default());
    assert_eq!(report.verdict, Verdict::Fail, "report: {report:?}");

    let refuted = report.functions[0]
        .outcomes
        .iter()
        .find_map(|o| match &o.result {
            csolver_core::ObligationResult::Refuted(cx) => Some(cx),
            _ => None,
        })
        .expect("the check is refuted with a counterexample");
    // The counterexample carries a concrete witness for the input.
    assert!(
        refuted.model.get("arg0").is_some(),
        "the input arg0 is witnessed: {:?}",
        refuted.model
    );
}

#[test]
fn out_of_bounds_memory_access_is_refuted_with_a_counterexample() {
    // The unguarded write `buf[i] = 0` into a `[i32; 8]`: out of bounds for any
    // `i >= 8`. The access executes, so a reachable OOB input is a real bug; the
    // symbolic engine refutes the in-bounds obligation with a concrete witness.
    let mut m = csolver_ir::Module::new("oobmem");
    m.functions.push(oob_index_store());
    let report = verify_module(&m, &Config::default());
    assert_eq!(report.verdict, Verdict::Fail, "report: {report:?}");

    let refuted = report.functions[0]
        .outcomes
        .iter()
        .find_map(|o| match &o.result {
            csolver_core::ObligationResult::Refuted(cx)
                if o.obligation.property == csolver_core::SafetyProperty::InBounds =>
            {
                Some(cx)
            }
            _ => None,
        })
        .expect("the in-bounds obligation is refuted with a counterexample");
    // The witnessed index genuinely makes the access out of bounds: its byte
    // offset `i * 4` lands at or past the 32-byte allocation (valid offsets are
    // 0..=28 for a 4-byte write).
    let i = refuted.model.get("arg0").expect("the input is witnessed").unsigned() as u64;
    let off = i.wrapping_mul(4);
    assert!(off > 28, "witness offset {off} must be out of bounds (i = {i})");
}

#[test]
fn pointer_roundtrip_through_memory_is_proven() {
    // store buf -> slot; p = load slot; *p = 0  — the alias-aware heap keeps
    // buf's provenance, so the final dereference is fully verified.
    let mut m = csolver_ir::Module::new("indirect");
    m.functions.push(indirect_store());
    let report = verify_module(&m, &Config::default());
    assert_eq!(report.verdict, Verdict::Pass, "report: {report:?}");
    assert!(report.functions[0].outcomes.iter().all(|o| o.verdict() == Verdict::Pass));
}

#[test]
fn interprocedural_call_preserves_provenance() {
    // `entry` dereferences a pointer returned by the wrapper `first`. The
    // summary for `first` carries the pointer back with its provenance, so the
    // dereference in `entry` is proved.
    let m = interproc_module();
    let report = verify_module(&m, &Config::default());

    let entry = report
        .functions
        .iter()
        .find(|f| f.function == "entry")
        .expect("entry verified");
    assert_eq!(entry.verdict, Verdict::Pass, "entry should be PASS: {entry:?}");
    assert!(entry.outcomes.iter().all(|o| o.verdict() == Verdict::Pass));
}

#[test]
fn use_after_free_is_unknown_never_pass() {
    let mut m = csolver_ir::Module::new("uaf");
    m.functions.push(dangling_store());
    let report = verify_module(&m, &Config::default());

    // Soundness: a use-after-free must never be reported PASS.
    assert_eq!(report.verdict, Verdict::Unknown);
    // The temporal-safety obligation on the post-free store is open.
    let func = &report.functions[0];
    let uaf_open = func.outcomes.iter().any(|o| {
        o.obligation.property == SafetyProperty::NoUseAfterFree
            && matches!(o.result, csolver_core::ObligationResult::Open { .. })
    });
    assert!(uaf_open, "use-after-free must be reported as open/unknown");
}

#[test]
fn module_verdict_is_the_worst_case() {
    // mixed = {pass, fail, unknown} => module is FAIL.
    let m = mixed_module();
    let report = verify_module(&m, &Config::default());
    assert_eq!(report.verdict, Verdict::Fail);
    assert_eq!(report.count(Verdict::Pass), 1);
    assert_eq!(report.count(Verdict::Fail), 1);
    assert_eq!(report.count(Verdict::Unknown), 1);
}

#[test]
fn reports_render() {
    let m = mixed_module();
    let report = verify_module(&m, &Config::default());

    let text = render_text(&report);
    assert!(text.contains("module mixed: FAIL"));
    assert!(text.contains("provably_safe"));
    assert!(text.contains("PASS"));

    let json = render_json(&report);
    assert!(json.contains("\"module\":\"mixed\""));
    assert!(json.contains("\"verdict\":\"FAIL\""));
}
