//! End-to-end: real Rust MIR text → MSIR (via the MIR frontend) → verified.
//!
//! The point of MIR over LLVM-IR is that the bounds/overflow checks rustc
//! inserts are *explicit* `assert` terminators, so a checked index `s[i]` is
//! proved in bounds precisely because the check is present — and an access
//! without the check is correctly not proved.

use csolver_core::{SafetyProperty, Verdict};
use csolver_ir::Frontend;
use csolver_mir::{MirFrontend, MirInput};
use csolver_verifier::{verify_module, Config};

#[allow(clippy::expect_used)]
fn lower(src: &str, name: &str) -> csolver_ir::Module {
    MirFrontend
        .lower(MirInput { source: src.into(), name: name.into() })
        .expect("the MIR frontend lowers the body")
}

/// `fn get(s: &[i32; 8], i: usize) -> i32 { s[i] }` as rustc MIR: the
/// bounds-check `assert(Lt(i, 8))` guards the indexed load, so it verifies PASS.
const CHECKED: &str = r#"
fn get(_1: &[i32; 8], _2: usize) -> i32 {
    debug s => _1;
    debug i => _2;
    let mut _0: i32;
    let mut _3: bool;
    bb0: {
        _3 = Lt(_2, const 8_usize);
        assert(move _3, "index out of bounds: the length is {} but the index is {}", const 8_usize, _2) -> [success: bb1, unwind continue];
    }
    bb1: {
        _0 = (*_1)[_2];
        return;
    }
}
"#;

#[test]
fn mir_checked_index_verifies_pass() {
    let module = lower(CHECKED, "checked");
    assert!(module.unanalyzed.is_empty(), "the body lowers, not dropped");
    let report = verify_module(&module, &Config::default());
    assert_eq!(report.verdict, Verdict::Pass, "report: {report:?}");
    // The access was proved in bounds, and the param-contract assumption recorded.
    assert!(report.functions[0].outcomes.iter().all(|o| o.verdict() == Verdict::Pass));
    assert!(report.assumptions.iter().any(|a| a.id == "param-contracts"));
}

/// The same indexed load WITHOUT the bounds-check assert (a hypothetical
/// `get_unchecked`): nothing constrains `i < 8`, so the access must not be
/// proved PASS. This is what makes the MIR assert meaningful.
const UNCHECKED: &str = r#"
fn get_unchecked(_1: &[i32; 8], _2: usize) -> i32 {
    let mut _0: i32;
    bb0: {
        _0 = (*_1)[_2];
        return;
    }
}
"#;

#[test]
fn mir_unchecked_index_is_not_pass() {
    let module = lower(UNCHECKED, "unchecked");
    let report = verify_module(&module, &Config::default());
    let in_bounds_proved = report.functions[0].outcomes.iter().any(|o| {
        o.obligation.property == SafetyProperty::InBounds
            && matches!(o.result, csolver_core::ObligationResult::Proven(_))
    });
    assert!(!in_bounds_proved, "an unchecked index must not prove in-bounds");
}

/// A function using a construct outside the modelled subset (a `call`) is
/// recorded as unanalyzed rather than mis-lowered — and a sound function in the
/// same dump still verifies.
const MIXED: &str = r#"
fn good(_1: &[i32; 8], _2: usize) -> i32 {
    let mut _0: i32;
    let mut _3: bool;
    bb0: {
        _3 = Lt(_2, const 8_usize);
        assert(move _3, "oob", const 8_usize, _2) -> [success: bb1, unwind continue];
    }
    bb1: {
        _0 = (*_1)[_2];
        return;
    }
}

fn uses_call(_1: i32) -> i32 {
    let mut _0: i32;
    bb0: {
        _0 = foo(move _1) -> [return: bb1, unwind continue];
    }
    bb1: {
        return;
    }
}
"#;

#[test]
fn mir_per_function_recovery() {
    let module = lower(MIXED, "mixed");
    // The good function lowered; the call-using one is recorded unanalyzed.
    assert_eq!(module.functions.len(), 1);
    assert_eq!(module.functions[0].name, "good");
    assert!(module.unanalyzed.iter().any(|(n, _)| n == "uses_call"));

    let report = verify_module(&module, &Config::default());
    assert_eq!(report.verdict, Verdict::Unknown);
    let good = report.functions.iter().find(|f| f.function == "good").unwrap();
    assert_eq!(good.verdict, Verdict::Pass);
}
