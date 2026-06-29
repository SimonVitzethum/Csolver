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

/// **Real** `rustc 1.94.1 --emit=mir` output for `fn get(s: &[i32], i: usize)
/// -> i32 { s[i] }` (frozen verbatim). It exercises the actual shape: the slice
/// length via `PtrMetadata(copy _1)`, `copy`-prefixed operands and index places,
/// the `assert(Lt(i, len))` bounds check, and a `debug`/`let` preamble. Verifies
/// PASS — validating the frontend against genuine compiler output, not just
/// hand-written fixtures.
const REAL_GET: &str = r#"
fn get(_1: &[i32], _2: usize) -> i32 {
    debug s => _1;
    debug i => _2;
    let mut _0: i32;
    let mut _3: usize;
    let mut _4: bool;

    bb0: {
        _3 = PtrMetadata(copy _1);
        _4 = Lt(copy _2, copy _3);
        assert(move _4, "index out of bounds: the length is {} but the index is {}", move _3, copy _2) -> [success: bb1, unwind continue];
    }

    bb1: {
        _0 = copy (*_1)[_2];
        return;
    }
}
"#;

#[test]
fn mir_real_rustc_slice_get_verifies_pass() {
    let module = lower(REAL_GET, "real_get");
    assert!(module.unanalyzed.is_empty());
    let report = verify_module(&module, &Config::default());
    assert_eq!(report.verdict, Verdict::Pass, "report: {report:?}");
    assert!(report.assumptions.iter().any(|a| a.id == "slice-abi"));
}

/// **Real** `rustc 1.94.1 --emit=mir` output (debug build) for
/// `fn sum(s: &[i32]) -> i32 { let mut acc=0; let mut i=0; while i < s.len() {
/// acc += s[i]; i += 1 } acc }` (frozen verbatim). Beyond the slice loop it has
/// `AddWithOverflow` checked-arithmetic tuples, type-ascribed field places
/// (`(_11.1: bool)`), `switchInt`, and nested `scope`s. The indexed load is
/// proved in bounds via the bounds-check `assert`; the overflow checks are
/// modelled opaquely (arithmetic, not memory). Verifies PASS.
const REAL_SUM_LOOP: &str = r#"
fn sum(_1: &[i32]) -> i32 {
    debug s => _1;
    let mut _0: i32;
    let mut _2: i32;
    let mut _4: bool;
    let mut _5: usize;
    let mut _6: usize;
    let mut _7: i32;
    let _8: usize;
    let mut _9: usize;
    let mut _10: bool;
    let mut _11: (i32, bool);
    let mut _12: (usize, bool);
    scope 1 {
        debug acc => _2;
        let mut _3: usize;
        scope 2 {
            debug i => _3;
        }
    }

    bb0: {
        _2 = const 0_i32;
        _3 = const 0_usize;
        goto -> bb1;
    }

    bb1: {
        _5 = copy _3;
        _6 = PtrMetadata(copy _1);
        _4 = Lt(move _5, move _6);
        switchInt(move _4) -> [0: bb6, otherwise: bb2];
    }

    bb2: {
        _8 = copy _3;
        _9 = PtrMetadata(copy _1);
        _10 = Lt(copy _8, copy _9);
        assert(move _10, "index out of bounds: the length is {} but the index is {}", move _9, copy _8) -> [success: bb3, unwind continue];
    }

    bb3: {
        _7 = copy (*_1)[_8];
        _11 = AddWithOverflow(copy _2, copy _7);
        assert(!move (_11.1: bool), "attempt to compute `{} + {}`, which would overflow", copy _2, move _7) -> [success: bb4, unwind continue];
    }

    bb4: {
        _2 = move (_11.0: i32);
        _12 = AddWithOverflow(copy _3, const 1_usize);
        assert(!move (_12.1: bool), "attempt to compute `{} + {}`, which would overflow", copy _3, const 1_usize) -> [success: bb5, unwind continue];
    }

    bb5: {
        _3 = move (_12.0: usize);
        goto -> bb1;
    }

    bb6: {
        _0 = copy _2;
        return;
    }
}
"#;

#[test]
fn mir_real_rustc_debug_loop_verifies_pass() {
    let module = lower(REAL_SUM_LOOP, "real_sum");
    assert!(module.unanalyzed.is_empty(), "lowers despite overflow checks: {:?}", module.unanalyzed);
    let report = verify_module(&module, &Config::default());
    assert_eq!(report.verdict, Verdict::Pass, "report: {report:?}");
}

/// **Real** `rustc --emit=mir` for `fn write_slice(s: &mut [i32], i, v) { s[i] =
/// v }` (frozen). The slice **write** takes the length via a fake raw borrow
/// (`_4 = &raw const (fake) (*_1); _5 = PtrMetadata(move _4)`), so the synthetic
/// length must flow through the pointer copy. The bounds-checked store verifies
/// PASS.
const REAL_WRITE_SLICE: &str = r#"
fn write_slice(_1: &mut [i32], _2: usize, _3: i32) -> () {
    debug s => _1;
    debug i => _2;
    debug v => _3;
    let mut _0: ();
    let mut _4: *const [i32];
    let mut _5: usize;
    let mut _6: bool;

    bb0: {
        _4 = &raw const (fake) (*_1);
        _5 = PtrMetadata(move _4);
        _6 = Lt(copy _2, copy _5);
        assert(move _6, "index out of bounds: the length is {} but the index is {}", move _5, copy _2) -> [success: bb1, unwind continue];
    }

    bb1: {
        (*_1)[_2] = copy _3;
        return;
    }
}
"#;

#[test]
fn mir_real_slice_write_verifies_pass() {
    let module = lower(REAL_WRITE_SLICE, "real_write");
    assert!(module.unanalyzed.is_empty());
    let report = verify_module(&module, &Config::default());
    assert_eq!(report.verdict, Verdict::Pass, "report: {report:?}");
}

/// **Real** `rustc --emit=mir` for `fn fill(s: &mut [u8], v: u8) { let mut i=0;
/// while i < s.len() { s[i] = v; i += 1 } }` (frozen). A mutable-slice write loop
/// over a **unit-stride** `&[u8]` — the access offset is the bare index, whose
/// bit-precise refinement of `i + 1 ≤ len` once made it slow; with the tight
/// refine budget it stays on the fast linear path and verifies PASS quickly.
const REAL_FILL: &str = r#"
fn fill(_1: &mut [u8], _2: u8) -> () {
    debug s => _1;
    debug v => _2;
    let mut _0: ();
    let mut _3: usize;
    let mut _4: bool;
    let mut _5: usize;
    let mut _6: usize;
    let mut _7: &[u8];
    let _8: usize;
    let mut _9: *const [u8];
    let mut _10: usize;
    let mut _11: bool;
    let mut _12: (usize, bool);
    scope 1 {
        debug i => _3;
    }

    bb0: {
        _3 = const 0_usize;
        goto -> bb1;
    }

    bb1: {
        _5 = copy _3;
        _7 = &(*_1);
        _6 = PtrMetadata(move _7);
        _4 = Lt(move _5, move _6);
        switchInt(move _4) -> [0: bb5, otherwise: bb2];
    }

    bb2: {
        _8 = copy _3;
        _9 = &raw const (fake) (*_1);
        _10 = PtrMetadata(move _9);
        _11 = Lt(copy _8, copy _10);
        assert(move _11, "index out of bounds: the length is {} but the index is {}", move _10, copy _8) -> [success: bb3, unwind continue];
    }

    bb3: {
        (*_1)[_8] = copy _2;
        _12 = AddWithOverflow(copy _3, const 1_usize);
        assert(!move (_12.1: bool), "attempt to compute `{} + {}`, which would overflow", copy _3, const 1_usize) -> [success: bb4, unwind continue];
    }

    bb4: {
        _3 = move (_12.0: usize);
        goto -> bb1;
    }

    bb5: {
        return;
    }
}
"#;

#[test]
fn mir_real_mut_slice_fill_loop_verifies_pass() {
    let module = lower(REAL_FILL, "real_fill");
    assert!(module.unanalyzed.is_empty(), "lowers: {:?}", module.unanalyzed);
    let report = verify_module(&module, &Config::default());
    assert_eq!(report.verdict, Verdict::Pass, "report: {report:?}");
}

/// **Soundness** against real output: `fn unchecked(s: &[i32], i) -> i32 {
/// unsafe { *s.get_unchecked(i) } }` (frozen). There is **no** bounds check — the
/// deref goes through the (opaque) result of a `get_unchecked` call. It must NOT
/// be proved PASS: dropping the unmodelled deref would be an unsound vacuous
/// PASS, so the access is emitted through the opaque pointer and stays UNKNOWN.
const REAL_UNCHECKED: &str = r#"
fn unchecked(_1: &[i32], _2: usize) -> i32 {
    debug s => _1;
    debug i => _2;
    let mut _0: i32;
    let mut _3: &i32;

    bb0: {
        _3 = core::slice::<impl [i32]>::get_unchecked::<usize>(copy _1, copy _2) -> [return: bb1, unwind continue];
    }

    bb1: {
        _0 = copy (*_3);
        return;
    }
}
"#;

#[test]
fn mir_real_unchecked_deref_is_not_pass() {
    let module = lower(REAL_UNCHECKED, "real_unchecked");
    let report = verify_module(&module, &Config::default());
    // Must not be a (vacuous) PASS — the unchecked deref is not proved safe.
    assert_ne!(report.verdict, Verdict::Pass, "an unchecked deref must not vacuously pass");
    // And it genuinely emitted an obligation (the deref was not silently dropped).
    assert!(
        !report.functions[0].outcomes.is_empty(),
        "the unmodelled deref must emit an (unprovable) obligation, not vanish"
    );
}

/// **Real** `rustc --emit=mir` for `fn last(s: &[i32]) -> i32 { let n = s.len();
/// if n == 0 { 0 } else { s[n - 1] } }` (frozen). The index `n - 1` is *derived*
/// (a checked subtraction), and the guarding `if n == 0` lowers to a `≠`
/// disequality the linear fragment cannot read. It verifies PASS only because the
/// prover **skips** the unusable `≠` assumption and proves the access from its
/// own `n-1 <u len` bounds guard.
const REAL_LAST: &str = r#"
fn last(_1: &[i32]) -> i32 {
    debug s => _1;
    let mut _0: i32;
    let _2: usize;
    let mut _3: bool;
    let _4: usize;
    let mut _5: (usize, bool);
    let mut _6: usize;
    let mut _7: bool;
    scope 1 {
        debug n => _2;
    }

    bb0: {
        _2 = PtrMetadata(copy _1);
        _3 = Eq(copy _2, const 0_usize);
        switchInt(move _3) -> [0: bb2, otherwise: bb1];
    }

    bb1: {
        _0 = const 0_i32;
        goto -> bb5;
    }

    bb2: {
        _5 = SubWithOverflow(copy _2, const 1_usize);
        assert(!move (_5.1: bool), "attempt to compute `{} - {}`, which would overflow", copy _2, const 1_usize) -> [success: bb3, unwind continue];
    }

    bb3: {
        _4 = move (_5.0: usize);
        _6 = PtrMetadata(copy _1);
        _7 = Lt(copy _4, copy _6);
        assert(move _7, "index out of bounds: the length is {} but the index is {}", move _6, copy _4) -> [success: bb4, unwind continue];
    }

    bb4: {
        _0 = copy (*_1)[_4];
        goto -> bb5;
    }

    bb5: {
        return;
    }
}
"#;

#[test]
fn mir_real_last_element_verifies_pass() {
    let module = lower(REAL_LAST, "real_last");
    assert!(module.unanalyzed.is_empty());
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

fn double_deref(_1: &mut &mut i32) -> i32 {
    let mut _0: i32;
    bb0: {
        _0 = copy (*(*_1));
        return;
    }
}
"#;

#[test]
fn mir_per_function_recovery() {
    let module = lower(MIXED, "mixed");
    // The good function lowered; the one with an access that cannot be lowered to
    // a known pointer (a double deref) is recorded unanalyzed.
    assert_eq!(module.functions.len(), 1);
    assert_eq!(module.functions[0].name, "good");
    assert!(module.unanalyzed.iter().any(|(n, _)| n == "double_deref"));

    let report = verify_module(&module, &Config::default());
    assert_eq!(report.verdict, Verdict::Unknown);
    let good = report.functions.iter().find(|f| f.function == "good").unwrap();
    assert_eq!(good.verdict, Verdict::Pass);
}

/// A `drop` terminator no longer rejects the function: its destructor is modelled
/// as a freeing call, so a guarded access *before* the drop still verifies PASS.
/// (The free's soundness — a use of a *dropped* owned region is not a PASS — is
/// covered by the differential corpus's `cond_use_after_free`.)
const DROP_OK: &str = r#"
fn drop_then_get(_1: &[i32; 8], _2: usize) -> i32 {
    let mut _0: i32;
    let mut _3: bool;
    let _4: i32;
    bb0: {
        _3 = Lt(_2, const 8_usize);
        assert(move _3, "oob", const 8_usize, _2) -> [success: bb1, unwind continue];
    }
    bb1: {
        _0 = (*_1)[_2];
        drop(_4) -> [return: bb2, unwind continue];
    }
    bb2: {
        return;
    }
}
"#;

#[test]
fn mir_drop_terminator_is_modelled_and_analyses() {
    let module = lower(DROP_OK, "drop_ok");
    assert!(module.unanalyzed.is_empty(), "a drop terminator no longer rejects the function");
    let report = verify_module(&module, &Config::default());
    assert_eq!(report.verdict, Verdict::Pass, "report: {report:?}");
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

/// Real `rustc --emit=mir` for
/// `fn nested(m: &[[i32; 4]], i: usize, j: usize) -> i32 {
///      if i < m.len() && j < 4 { m[i][j] } else { 0 } }`.
/// The nested index `(*_1)[_2][_3]` lowers to a *chain* of `PtrOffset`s (outer
/// stride 16 = `size_of::<[i32;4]>()`, inner stride 4 = `size_of::<i32>()`); the
/// two asserts give `i < len` and `j < 4`, which together prove
/// `i*16 + j*4 + 4 <= len*16`. Array strides are unambiguous, so no struct
/// layout is needed. Frozen text, captured from rustc.
const REAL_NESTED: &str = r#"
fn nested(_1: &[[i32; 4]], _2: usize, _3: usize) -> i32 {
    debug m => _1;
    debug i => _2;
    debug j => _3;
    let mut _0: i32;
    let mut _4: bool;
    let mut _5: usize;
    let mut _6: bool;
    let mut _7: usize;
    let mut _8: bool;
    let mut _9: bool;

    bb0: {
        _5 = PtrMetadata(copy _1);
        _4 = Lt(copy _2, move _5);
        switchInt(move _4) -> [0: bb5, otherwise: bb1];
    }

    bb1: {
        _6 = Lt(copy _3, const 4_usize);
        switchInt(move _6) -> [0: bb5, otherwise: bb2];
    }

    bb2: {
        _7 = PtrMetadata(copy _1);
        _8 = Lt(copy _2, copy _7);
        assert(move _8, "index out of bounds: the length is {} but the index is {}", move _7, copy _2) -> [success: bb3, unwind continue];
    }

    bb3: {
        _9 = Lt(copy _3, const 4_usize);
        assert(move _9, "index out of bounds: the length is {} but the index is {}", const 4_usize, copy _3) -> [success: bb4, unwind continue];
    }

    bb4: {
        _0 = copy (*_1)[_2][_3];
        goto -> bb6;
    }

    bb5: {
        _0 = const 0_i32;
        goto -> bb6;
    }

    bb6: {
        return;
    }
}
"#;

#[test]
fn mir_real_nested_index_verifies_pass() {
    let module = lower(REAL_NESTED, "real_nested");
    assert!(module.unanalyzed.is_empty(), "the nested-index body lowers, not dropped");
    let report = verify_module(&module, &Config::default());
    assert_eq!(report.verdict, Verdict::Pass, "report: {report:?}");
}

/// Soundness for the inner stride: a nested index where only the **outer** index
/// is bounded (`i < len`) and the inner `j` is unconstrained. The offset
/// `i*16 + j*4` can exceed `len*16` for a large `j`, so the access must not be
/// proved in bounds — which it can only be if the inner index is actually
/// modelled (dropping it would fabricate a false PASS).
const NESTED_INNER_UNCHECKED: &str = r#"
fn nested_inner(_1: &[[i32; 4]], _2: usize, _3: usize) -> i32 {
    let mut _0: i32;
    let mut _7: usize;
    let mut _8: bool;
    bb0: {
        _7 = PtrMetadata(copy _1);
        _8 = Lt(_2, move _7);
        assert(move _8, "oob", move _7, _2) -> [success: bb1, unwind continue];
    }
    bb1: {
        _0 = (*_1)[_2][_3];
        return;
    }
}
"#;

#[test]
fn mir_nested_index_inner_unchecked_is_not_pass() {
    let module = lower(NESTED_INNER_UNCHECKED, "nested_inner");
    assert!(module.unanalyzed.is_empty(), "it lowers (the access is emitted, not dropped)");
    let report = verify_module(&module, &Config::default());
    let in_bounds_proved = report.functions[0].outcomes.iter().any(|o| {
        o.obligation.property == SafetyProperty::InBounds
            && matches!(o.result, csolver_core::ObligationResult::Proven(_))
    });
    assert!(!in_bounds_proved, "an unbounded inner index must not prove in-bounds");
}

/// Real `rustc --emit=mir` for struct field access through a reference:
/// `fn get_x(p: &Point) -> i32 { p.x }` reads field 0 (`((*_1).0: i32)`) and
/// `fn set_x(p: &mut Point, v: i32) { p.x = v; }` writes it. A struct's layout is
/// absent from MIR (and unspecified for `repr(Rust)`), so the field is *not*
/// placed at a byte offset; instead the `&Point` parameter is an opaque-size
/// region and the field access is proved in bounds and aligned by construction
/// (a typed field of a valid reference lies within it), under `struct-abi`.
const REAL_STRUCT_FIELDS: &str = r#"
fn get_x(_1: &Point) -> i32 {
    debug p => _1;
    let mut _0: i32;
    bb0: {
        _0 = copy ((*_1).0: i32);
        return;
    }
}

fn set_x(_1: &mut Point, _2: i32) -> () {
    debug p => _1;
    debug v => _2;
    let mut _0: ();
    bb0: {
        ((*_1).0: i32) = copy _2;
        return;
    }
}
"#;

#[test]
fn mir_real_struct_field_access_verifies_pass() {
    let module = lower(REAL_STRUCT_FIELDS, "real_fields");
    assert!(module.unanalyzed.is_empty(), "field-through-pointer lowers, not dropped");
    let report = verify_module(&module, &Config::default());
    assert_eq!(report.verdict, Verdict::Pass, "report: {report:?}");
    assert!(report.assumptions.iter().any(|a| a.id == "struct-abi"));
}

/// Soundness of the write permission: the *same* field store through a shared
/// `&Point` (not `&mut`) must not prove `valid_write` — a readonly reference may
/// be read but not written. (rustc would never emit this, but the verifier's
/// permission gate must hold regardless.)
const FIELD_WRITE_READONLY: &str = r#"
fn ro_write(_1: &Point, _2: i32) -> () {
    let mut _0: ();
    bb0: {
        ((*_1).0: i32) = copy _2;
        return;
    }
}
"#;

#[test]
fn mir_readonly_field_write_is_not_pass() {
    let module = lower(FIELD_WRITE_READONLY, "ro_write");
    let report = verify_module(&module, &Config::default());
    let write_proved = report.functions[0].outcomes.iter().any(|o| {
        o.obligation.property == SafetyProperty::ValidWrite
            && matches!(o.result, csolver_core::ObligationResult::Proven(_))
    });
    assert!(!write_proved, "a field write through a shared reference must not prove valid_write");
}

/// Real `rustc --emit=mir` for a `match` on an enum reference:
/// `fn opt_or(o: &Option<i32>) -> i32 { match o { Some(v) => *v, None => -1 } }`.
/// Exercises three new constructs together — `discriminant((*_1))` (a tag read,
/// checked as a memory access but opaque in value, so the `switchInt` explores
/// both arms), `&(((*_1) as Some).0: i32)` (a *variant field* address — the same
/// field-sensitive model as a struct field, since the payload lies within the
/// enum), and the generic type `Option<i32>` in the signature. Verifies PASS.
const REAL_ENUM_MATCH: &str = r#"
fn opt_or(_1: &Option<i32>) -> i32 {
    debug o => _1;
    let mut _0: i32;
    let mut _2: isize;
    let _3: &i32;
    scope 1 {
        debug v => _3;
    }
    bb0: {
        _2 = discriminant((*_1));
        switchInt(move _2) -> [0: bb2, 1: bb3, otherwise: bb1];
    }
    bb1: {
        unreachable;
    }
    bb2: {
        _0 = const -1_i32;
        goto -> bb4;
    }
    bb3: {
        _3 = &(((*_1) as Some).0: i32);
        _0 = copy (*_3);
        goto -> bb4;
    }
    bb4: {
        return;
    }
}
"#;

#[test]
fn mir_real_enum_match_verifies_pass() {
    let module = lower(REAL_ENUM_MATCH, "real_enum");
    assert!(module.unanalyzed.is_empty(), "the enum match lowers (generics + discriminant)");
    let report = verify_module(&module, &Config::default());
    assert_eq!(report.verdict, Verdict::Pass, "report: {report:?}");
    assert!(report.assumptions.iter().any(|a| a.id == "struct-abi"));
}

/// Field-precise heap: storing `3` to field 0 and loading it back must round-trip
/// the value, so the (otherwise unguarded) index `(*_2)[_4]` with `_4 = 3` is
/// proved in bounds of `[i32; 8]`. Without the store→load round-trip the loaded
/// value would be unknown and the index unprovable. (This only propagates a value
/// the program actually stored, so it can never turn a real bug into a PASS.)
const FIELD_ROUNDTRIP: &str = r#"
fn roundtrip(_1: &mut Pair, _2: &[i32; 8]) -> i32 {
    let mut _0: i32;
    let mut _3: i32;
    let mut _4: usize;
    bb0: {
        ((*_1).0: i32) = const 3_i32;
        _3 = copy ((*_1).0: i32);
        _4 = move _3 as usize (IntToInt);
        _0 = (*_2)[_4];
        return;
    }
}
"#;

#[test]
fn mir_field_store_load_roundtrips() {
    let module = lower(FIELD_ROUNDTRIP, "roundtrip");
    assert!(module.unanalyzed.is_empty());
    let report = verify_module(&module, &Config::default());
    assert_eq!(report.verdict, Verdict::Pass, "report: {report:?}");
}

/// Soundness of the field layout's disjointness: storing to field 0 then loading
/// field **1** must *not* recover the stored value (distinct fields do not alias),
/// so the index built from field 1 stays unknown — the store to field 0 may never
/// pollute a different field, which would be a false PASS.
const FIELD_CROSS: &str = r#"
fn cross_field(_1: &mut Pair, _2: &[i32; 8]) -> i32 {
    let mut _0: i32;
    let mut _3: i32;
    let mut _4: usize;
    bb0: {
        ((*_1).0: i32) = const 3_i32;
        _3 = copy ((*_1).1: i32);
        _4 = move _3 as usize (IntToInt);
        _0 = (*_2)[_4];
        return;
    }
}
"#;

#[test]
fn mir_field_distinct_fields_do_not_alias() {
    let module = lower(FIELD_CROSS, "cross_field");
    let report = verify_module(&module, &Config::default());
    // The field accesses are in bounds by construction; the only open obligation
    // is the array index built from field 1 — which must stay unproven, since
    // field 1 never received field 0's stored value.
    assert_ne!(report.verdict, Verdict::Pass, "distinct fields must not alias: {report:?}");
}
