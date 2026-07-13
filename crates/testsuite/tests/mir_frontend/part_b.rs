use super::*;

/// A function using a construct outside the modelled subset (a `drop`
/// terminator) is recorded as unanalyzed rather than mis-lowered — and a sound
/// function in the same dump still verifies.
pub(crate) const MIXED: &str = r#"
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
pub(crate) const DROP_OK: &str = r#"
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
pub(crate) const INTERPROC: &str = r#"
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
pub(crate) const EXTERN_CALL: &str = r#"
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
pub(crate) const REAL_NESTED: &str = r#"
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
pub(crate) const NESTED_INNER_UNCHECKED: &str = r#"
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
pub(crate) const REAL_STRUCT_FIELDS: &str = r#"
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
pub(crate) const FIELD_WRITE_READONLY: &str = r#"
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
pub(crate) const REAL_ENUM_MATCH: &str = r#"
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
pub(crate) const FIELD_ROUNDTRIP: &str = r#"
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
pub(crate) const FIELD_CROSS: &str = r#"
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

/// `pick` with nightly span comments (`-Z mir-include-spans`): two indexed
/// accesses on *different* source lines — `a[1]` at line 3 (bb2), `a[2]` at line 5
/// (bb4). The frontend captures each statement's `// … at FILE:L:C` span and
/// threads it onto the lowered instructions, so each obligation points back at the
/// access that produced it.
pub(crate) const PICK_SPANS: &str = r#"
fn pick(_1: &[i32; 4], _2: bool) -> i32 {
    debug a => _1;                       // in scope 0 at src/lib.rs:1:13: 1:14
    let _3: usize;                       // in scope 0 at src/lib.rs:3:11: 3:12
    let mut _4: bool;                    // in scope 0 at src/lib.rs:3:9: 3:13
    let _5: usize;                       // in scope 0 at src/lib.rs:5:11: 5:12
    let mut _6: bool;                    // in scope 0 at src/lib.rs:5:9: 5:13

    bb0: {
        switchInt(copy _2) -> [0: bb3, otherwise: bb1]; // scope 0 at src/lib.rs:2:8: 2:12
    }
    bb1: {
        _3 = const 1_usize;              // scope 0 at src/lib.rs:3:11: 3:12
        _4 = Lt(copy _3, const 4_usize); // scope 0 at src/lib.rs:3:9: 3:13
        assert(move _4, "index out of bounds: the length is {} but the index is {}", const 4_usize, copy _3) -> [success: bb2, unwind continue]; // scope 0 at src/lib.rs:3:9: 3:13
    }
    bb2: {
        _0 = copy (*_1)[_3];             // scope 0 at src/lib.rs:3:9: 3:13
        goto -> bb5;                     // scope 0 at src/lib.rs:2:5: 6:6
    }
    bb3: {
        _5 = const 2_usize;              // scope 0 at src/lib.rs:5:11: 5:12
        _6 = Lt(copy _5, const 4_usize); // scope 0 at src/lib.rs:5:9: 5:13
        assert(move _6, "index out of bounds: the length is {} but the index is {}", const 4_usize, copy _5) -> [success: bb4, unwind continue]; // scope 0 at src/lib.rs:5:9: 5:13
    }
    bb4: {
        _0 = copy (*_1)[_5];             // scope 0 at src/lib.rs:5:9: 5:13
        goto -> bb5;                     // scope 0 at src/lib.rs:2:5: 6:6
    }
    bb5: {
        return;                          // scope 0 at src/lib.rs:7:2: 7:2
    }
}
"#;
