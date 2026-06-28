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

/// `fn get(s: &[i32], i: usize) -> i32 { s[i] }` over a **slice** (symbolic
/// length): the length comes from `Len((*_1))`, which the frontend resolves to a
/// synthetic length parameter, and the `assert(Lt(i, len))` proves the access in
/// bounds. Verifies PASS under the `slice-abi` assumption.
const SLICE: &str = r#"
fn get(_1: &[i32], _2: usize) -> i32 {
    debug s => _1;
    debug i => _2;
    let mut _0: i32;
    let mut _3: usize;
    let mut _4: bool;
    bb0: {
        _3 = Len((*_1));
        _4 = Lt(_2, move _3);
        assert(move _4, "index out of bounds: the length is {} but the index is {}", move _3, _2) -> [success: bb1, unwind continue];
    }
    bb1: {
        _0 = (*_1)[_2];
        return;
    }
}
"#;

#[test]
fn mir_checked_slice_index_verifies_pass() {
    let module = lower(SLICE, "slice");
    assert!(module.unanalyzed.is_empty());
    let report = verify_module(&module, &Config::default());
    assert_eq!(report.verdict, Verdict::Pass, "report: {report:?}");
    assert!(report.assumptions.iter().any(|a| a.id == "slice-abi"));
}

/// A real index-based slice loop `for i in 0..s.len() { … s[i] … }`: the loop
/// invariant `i >= 0`, the guard `i < len` (from the `switchInt` edge), and the
/// slice contract (region size `len * 4`) combine to prove every access. The
/// length is read from `Len((*_1))` at the header.
const SLICE_LOOP: &str = r#"
fn sum(_1: &[i32]) -> () {
    let mut _0: ();
    let mut _2: usize;
    let mut _3: usize;
    let mut _4: bool;
    let mut _5: i32;
    let mut _6: usize;
    bb0: {
        _2 = const 0_usize;
        goto -> bb1;
    }
    bb1: {
        _3 = Len((*_1));
        _4 = Lt(_2, move _3);
        switchInt(move _4) -> [0: bb4, otherwise: bb2];
    }
    bb2: {
        _5 = (*_1)[_2];
        _2 = Add(_2, const 1_usize);
        goto -> bb1;
    }
    bb4: {
        return;
    }
}
"#;

#[test]
fn mir_slice_index_loop_verifies_pass() {
    let module = lower(SLICE_LOOP, "sumloop");
    assert!(module.unanalyzed.is_empty(), "report: {:?}", module.unanalyzed);
    let report = verify_module(&module, &Config::default());
    assert_eq!(report.verdict, Verdict::Pass, "report: {report:?}");
}

/// A function using a construct outside the modelled subset (a `drop`
/// terminator) is recorded as unanalyzed rather than mis-lowered — and a sound
/// function in the same dump still verifies.
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

fn uses_drop(_1: i32) -> () {
    let mut _0: ();
    bb0: {
        drop(_1) -> [return: bb1, unwind continue];
    }
    bb1: {
        return;
    }
}
"#;

#[test]
fn mir_per_function_recovery() {
    let module = lower(MIXED, "mixed");
    // The good function lowered; the drop-using one is recorded unanalyzed.
    assert_eq!(module.functions.len(), 1);
    assert_eq!(module.functions[0].name, "good");
    assert!(module.unanalyzed.iter().any(|(n, _)| n == "uses_drop"));

    let report = verify_module(&module, &Config::default());
    assert_eq!(report.verdict, Verdict::Unknown);
    let good = report.functions.iter().find(|f| f.function == "good").unwrap();
    assert_eq!(good.verdict, Verdict::Pass);
}

/// An interprocedural module: `caller` calls a verified `helper` (a checked
/// array index). The call's assignment-form terminator lowers to an MSIR `Call`
/// resolved to the in-module `helper` (`Callee::Direct`), and the whole module
/// verifies via the helper's summary.
const INTERPROC: &str = r#"
fn helper(_1: &[i32; 8], _2: usize) -> i32 {
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

fn caller(_1: &[i32; 8]) -> i32 {
    let mut _0: i32;
    let mut _2: i32;
    bb0: {
        _2 = helper(move _1, const 0_usize) -> [return: bb1, unwind continue];
    }
    bb1: {
        _0 = move _2;
        return;
    }
}
"#;

#[test]
fn mir_interprocedural_call_lowers_and_verifies() {
    let module = lower(INTERPROC, "interproc");
    assert!(module.unanalyzed.is_empty(), "both functions lower: {:?}", module.unanalyzed);
    assert_eq!(module.functions.len(), 2);

    // The call resolved to the in-module helper (a direct call).
    let caller = module.functions.iter().find(|f| f.name == "caller").unwrap();
    let helper_id = module.functions.iter().position(|f| f.name == "helper").unwrap();
    let has_direct_call = caller.blocks.iter().flat_map(|b| &b.insts).any(|i| {
        matches!(i, csolver_ir::Inst::Call { callee: csolver_ir::Callee::Direct(id), .. }
                 if *id == csolver_ir::FuncId(helper_id as u32))
    });
    assert!(has_direct_call, "the call resolves to the in-module helper");

    let report = verify_module(&module, &Config::default());
    assert_eq!(report.verdict, Verdict::Pass, "report: {report:?}");
}

/// Soundness: a call to an *external* function (an unresolved symbol) lowers but
/// its result is an unknown — so dereferencing the returned pointer is not
/// proved safe. The function still lowers (it is not dropped).
const EXTERN_CALL: &str = r#"
fn uses_extern(_1: usize) -> i32 {
    let mut _0: i32;
    let mut _2: *mut i32;
    let mut _3: i32;
    bb0: {
        _2 = make_ptr(move _1) -> [return: bb1, unwind continue];
    }
    bb1: {
        _3 = (*_2);
        _0 = move _3;
        return;
    }
}
"#;

#[test]
fn mir_external_call_result_is_unknown() {
    let module = lower(EXTERN_CALL, "ext");
    assert!(module.unanalyzed.is_empty(), "the function lowers despite the extern call");
    let report = verify_module(&module, &Config::default());
    // Dereferencing the unknown returned pointer must not be proved in bounds.
    let deref_proved = report.functions[0].outcomes.iter().any(|o| {
        o.obligation.property == SafetyProperty::InBounds
            && matches!(o.result, csolver_core::ObligationResult::Proven(_))
    });
    assert!(!deref_proved, "deref of an external call's result must not be proved");
}
