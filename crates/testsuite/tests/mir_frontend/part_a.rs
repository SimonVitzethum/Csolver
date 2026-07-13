use super::*;


/// `fn get(s: &[i32; 8], i: usize) -> i32 { s[i] }` as rustc MIR: the
/// bounds-check `assert(Lt(i, 8))` guards the indexed load, so it verifies PASS.
pub(crate) const CHECKED: &str = r#"
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
pub(crate) const UNCHECKED: &str = r#"
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
pub(crate) const SLICE: &str = r#"
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
pub(crate) const SLICE_LOOP: &str = r#"
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
pub(crate) const REAL_GET: &str = r#"
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
pub(crate) const REAL_SUM_LOOP: &str = r#"
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
pub(crate) const REAL_WRITE_SLICE: &str = r#"
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
pub(crate) const REAL_FILL: &str = r#"
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
pub(crate) const REAL_UNCHECKED: &str = r#"
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
pub(crate) const REAL_LAST: &str = r#"
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
