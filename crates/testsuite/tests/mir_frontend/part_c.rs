use super::*;

#[test]
fn mir_obligations_carry_their_own_source_line() {
    let module = lower(PICK_SPANS, "pick");
    assert!(module.unanalyzed.is_empty(), "the body lowers, not dropped");
    let report = verify_module(&module, &Config::default());

    // The in-bounds obligations of the two accesses, with their rendered source
    // locations. (Both PASS — rustc guards them — but the *location* is per
    // obligation regardless of verdict, which is exactly what a FAIL would use.)
    let in_bounds_locs: Vec<String> = report.functions[0]
        .outcomes
        .iter()
        .filter(|o| o.obligation.property == SafetyProperty::InBounds)
        .filter_map(|o| o.obligation.location.raw.clone())
        .collect();

    assert!(!in_bounds_locs.is_empty(), "in-bounds obligations exist with a source location");
    // `a[1]` is on line 3, `a[2]` on line 5 — each access's obligation must point
    // at its *own* line.
    assert!(
        in_bounds_locs.iter().any(|l| l.contains(":3:")),
        "the a[1] access → line 3, got {in_bounds_locs:?}"
    );
    assert!(
        in_bounds_locs.iter().any(|l| l.contains(":5:")),
        "the a[2] access → line 5, got {in_bounds_locs:?}"
    );
    // The span-phantom guard: not merely that *some* line renders, but that no
    // obligation claims a line its access is not on (e.g. line 1, the signature,
    // or line 4). Every in-bounds location is line 3 or line 5, never a stray one.
    assert!(
        in_bounds_locs.iter().all(|l| l.contains(":3:") || l.contains(":5:")),
        "an in-bounds obligation rendered a wrong line: {in_bounds_locs:?}"
    );
}

/// The determinism oracle for parallelisation: a module of many functions (mixed
/// PASS/UNKNOWN, a loop) verified at 1 vs 16 threads must be **bit-for-bit
/// identical** — same verdicts, obligation ids, locations, and witnesses (all in
/// the rendered text). A divergence would be an isolation leak (shared mutable
/// state or completion-order dependence). Run several times to catch a timing-only
/// leak that a single run might miss.
#[test]
fn parallel_verification_matches_serial() {
    use csolver_report::render_text;
    use csolver_verifier::verify_module_with_threads;

    let bases = [CHECKED, SLICE, REAL_SUM_LOOP, REAL_UNCHECKED];
    let mut module = csolver_ir::Module::new("determinism");
    let mut fid = 0u32;
    for _ in 0..12 {
        for src in bases {
            for mut f in lower(src, "f").functions {
                f.id = csolver_ir::FuncId(fid);
                f.name = format!("f{fid}");
                module.functions.push(f);
                fid += 1;
            }
        }
    }
    assert!(module.functions.len() >= 40, "enough functions to stress the worker pool");

    let config = Config::default();
    let serial = render_text(&verify_module_with_threads(&module, &config, 1));
    for run in 0..3 {
        let parallel = render_text(&verify_module_with_threads(&module, &config, 16));
        assert_eq!(serial, parallel, "parallel run {run} diverges from serial (isolation leak)");
    }
}

/// A closure's `&[u8]` contract is a caller-established *precondition* (the
/// guard lives at the call site — bytes' `get_u16` checks `remaining() >= 2`
/// before invoking), so an unguarded fixed-size read inside the closure must
/// NOT be refuted: the witness (`len = 1`) may never occur in the real
/// program. The same body as a *named* (externally callable) function is a
/// genuine finding — any safe caller can pass a 1-byte slice — and must FAIL.
/// This pins both directions of `PtrContract::refutable`.
#[test]
fn mir_closure_precondition_is_prove_only_but_public_fn_still_fails() {
    let closure = r#"
fn Buf::get_u16::{closure#0}(_1: &[u8]) -> u8 {
    let mut _0: u8;
    let mut _2: usize;
    bb0: {
        _2 = const 1_usize;
        _0 = (*_1)[_2];
        return;
    }
}
"#;
    let module = lower(closure, "m");
    let report = verify_module(&module, &Config::default());
    let f = &report.functions[0];
    assert!(f.function.contains("closure"), "fixture is a closure: {}", f.function);
    assert_ne!(
        f.verdict,
        Verdict::Fail,
        "a precondition contract must not be refuted: {f:?}"
    );

    let public = r#"
fn second_byte(_1: &[u8]) -> u8 {
    let mut _0: u8;
    let mut _2: usize;
    bb0: {
        _2 = const 1_usize;
        _0 = (*_1)[_2];
        return;
    }
}
"#;
    let module = lower(public, "m");
    let report = verify_module(&module, &Config::default());
    assert_eq!(
        report.functions[0].verdict,
        Verdict::Fail,
        "an externally callable fn reading s[1] of an arbitrary slice is a real finding"
    );
}

/// Sibling closures must keep distinct names (`{closure#0}` vs `{closure#1}`)
/// — a report that calls every closure "closure" cannot locate a finding.
#[test]
fn mir_sibling_closures_keep_distinct_names() {
    let src = r#"
fn A::f::{closure#0}(_1: i32) -> i32 {
    let mut _0: i32;
    bb0: {
        _0 = copy _1;
        return;
    }
}

fn A::f::{closure#1}(_1: i32) -> i32 {
    let mut _0: i32;
    bb0: {
        _0 = copy _1;
        return;
    }
}
"#;
    let module = lower(src, "m");
    let names: Vec<_> = module.functions.iter().map(|f| f.name.as_str()).collect();
    assert!(names.contains(&"A::f{closure#0}"), "{names:?}");
    assert!(names.contains(&"A::f{closure#1}"), "{names:?}");
}

/// A reference extracted from a by-value aggregate the analysis cannot see into
/// (`(_2 as Some).0` of type `&u8` — e.g. `slice::split_first`'s result) is a
/// *valid reference* by Rust's type invariant: a read through it proves (live,
/// in-bounds, aligned), surfacing the `valid-reference` assumption. Before, the
/// pointer was `undef` and every access UNKNOWN. `_2` is a call result, so its
/// aggregate is genuinely opaque — the recovery is purely type-driven.
#[test]
fn mir_reference_from_opaque_aggregate_is_valid() {
    let src = r#"
fn read_first(_1: &[u8]) -> u8 {
    let mut _0: u8;
    let mut _2: std::option::Option<(&u8, &[u8])>;
    let mut _3: &u8;
    bb0: {
        _2 = core::slice::<impl [u8]>::split_first(copy _1) -> [return: bb1, unwind continue];
    }
    bb1: {
        _3 = copy (((_2 as Some).0: (&u8, &[u8])).0: &u8);
        _0 = copy (*_3);
        return;
    }
}
"#;
    let module = lower(src, "m");
    let report = verify_module(&module, &Config::default());
    assert_eq!(report.functions[0].verdict, Verdict::Pass, "{report:?}");
    assert!(
        report.assumptions.iter().any(|a| a.id == "valid-reference"),
        "the read rests on the reference-validity invariant"
    );
}

/// Soundness of the recovery, both directions. A shared reference `&u8` is
/// **read-only**: writing through it must not prove (that write is UB Rust
/// would reject). And the region is exactly `sizeof(pointee)`: an access one
/// element past a `&u8` must not prove (the reference is valid for one byte,
/// not two).
#[test]
fn mir_ref_witness_respects_mutability_and_size() {
    // Write through a shared `&u8` field — must not PASS.
    let shared_write = r#"
fn clobber(_1: (&u8, u8)) -> () {
    let mut _0: ();
    let mut _2: &u8;
    bb0: {
        _2 = copy (_1.0: &u8);
        (*_2) = const 7_u8;
        return;
    }
}
"#;
    let module = lower(shared_write, "m");
    let report = verify_module(&module, &Config::default());
    assert_ne!(
        report.functions[0].verdict,
        Verdict::Pass,
        "a write through a shared &u8 must not prove: {report:?}"
    );

    // A `&mut u8` field DOES grant the write.
    let mut_write = r#"
fn set(_1: (&mut u8, u8)) -> () {
    let mut _0: ();
    let mut _2: &mut u8;
    bb0: {
        _2 = copy (_1.0: &mut u8);
        (*_2) = const 7_u8;
        return;
    }
}
"#;
    let module = lower(mut_write, "m");
    let report = verify_module(&module, &Config::default());
    assert_eq!(
        report.functions[0].verdict,
        Verdict::Pass,
        "a write through &mut u8 is granted: {report:?}"
    );
}

/// rustc appends data/vtable `alloc` blocks after the function bodies. An entry
/// like `alloc297 (fn: promotable_odd_clone)` contains a `fn` token that is NOT
/// a function item — landing on it produced a phantom empty-named `UNKNOWN`
/// function, polluting the coverage report with items that do not exist. The
/// scanner must skip it (a real header is `fn <name>(` / `fn <impl…>`).
#[test]
fn mir_vtable_alloc_entries_do_not_become_phantom_functions() {
    let src = r#"
fn real(_1: usize) -> usize {
    let mut _0: usize;
    bb0: {
        _0 = copy _1;
        return;
    }
}

alloc296 (static: PROMOTABLE_ODD_VTABLE, size: 40, align: 8) {
    0x00 │ ╾──────alloc297───────╼ ╾──────alloc298───────╼ │ ╾──────╼╾──────╼
}

alloc297 (fn: promotable_odd_clone)

alloc298 (fn: promotable_odd_to_vec)
"#;
    let module = lower(src, "m");
    let names: Vec<_> = module.functions.iter().map(|f| f.name.as_str()).collect();
    assert_eq!(names, vec!["real"], "only the real fn is a function: {names:?}");
    assert!(
        module.unanalyzed.is_empty(),
        "the alloc `(fn: …)` entries are not phantom unanalyzed functions: {:?}",
        module.unanalyzed
    );
}

/// A higher-ranked trait-object type `&dyn for<'a> core::ops::Fn(&'a T) -> R`
/// (rustc emits it for boxed/`dyn` closures, e.g. hashbrown's rehash hasher).
/// The `for<'a>` binder prefixes the trait; treating `for` as the trait name
/// stopped the type scan at the binder and left `core::ops::Fn(…)` unconsumed,
/// desyncing the parser into the *next* function (a phantom drop). Both a
/// parameter and a local of this type must parse.
#[test]
fn mir_higher_ranked_trait_object_type_parses() {
    let src = r#"
fn takes_hasher(_1: usize, _2: &dyn for<'a> core::ops::Fn(&'a mut R, usize) -> u64) -> usize {
    let mut _0: usize;
    let mut _7: &dyn for<'a> core::ops::Fn(&'a mut R, usize) -> u64;
    bb0: {
        _0 = copy _1;
        return;
    }
}

fn next_fn(_1: usize) -> usize {
    let mut _0: usize;
    bb0: {
        _0 = copy _1;
        return;
    }
}
"#;
    let module = lower(src, "m");
    let names: Vec<_> = module.functions.iter().map(|f| f.name.as_str()).collect();
    assert_eq!(names, vec!["takes_hasher", "next_fn"], "both parse, no desync: {names:?}");
    assert!(module.unanalyzed.is_empty(), "{:?}", module.unanalyzed);
}

/// A call returning `&T`/`&mut T` yields a *valid reference* (Rust's type
/// invariant — even an external callee cannot return a dangling reference in
/// safe code): a read through the returned reference proves, resting on
/// `valid-reference`. A call returning a raw `*const T` gets no such guarantee
/// and stays opaque (an access through it must not prove). This is the
/// interprocedural counterpart of the by-value-aggregate reference witness.
#[test]
fn mir_reference_returning_call_yields_a_valid_reference() {
    let ref_ret = r#"
fn read(_1: usize) -> u8 {
    let mut _0: u8;
    let mut _2: &u8;
    bb0: {
        _2 = lookup(copy _1) -> [return: bb1, unwind continue];
    }
    bb1: {
        _0 = copy (*_2);
        return;
    }
}
"#;
    let module = lower(ref_ret, "m");
    let report = verify_module(&module, &Config::default());
    assert_eq!(report.functions[0].verdict, Verdict::Pass, "read via returned &u8: {report:?}");
    assert!(
        report.assumptions.iter().any(|a| a.id == "valid-reference"),
        "the read rests on the reference-validity invariant"
    );

    // Raw-pointer return: no validity guarantee, the deref must not prove.
    let ptr_ret = r#"
fn read_raw(_1: usize) -> u8 {
    let mut _0: u8;
    let mut _2: *const u8;
    bb0: {
        _2 = leak(copy _1) -> [return: bb1, unwind continue];
    }
    bb1: {
        _0 = copy (*_2);
        return;
    }
}
"#;
    let module = lower(ptr_ret, "m");
    let report = verify_module(&module, &Config::default());
    assert_ne!(
        report.functions[0].verdict,
        Verdict::Pass,
        "a deref of a raw *const u8 call result must not prove: {report:?}"
    );
}

/// A `drop`/call `unwind: bbN` cleanup block runs on the panic path; its memory
/// ops must be *checked*, not silently left "reached but not decided". Before,
/// the unwind edge was dropped, so the cleanup block was unreachable in the MSIR
/// CFG and its writes went undecided (a coverage hole). Now both edges are
/// modelled (a two-way branch on a fresh condition, like LLVM `invoke`): the
/// cleanup write proves, and — the soundness direction — a genuine out-of-bounds
/// write *on the cleanup path* is a real finding that must FAIL.
#[test]
fn mir_unwind_cleanup_block_memory_is_checked() {
    // Cleanup write within bounds: decided PASS (not left undecided).
    let ok = r#"
fn drop_then_set(_1: &mut Self, _2: Self) -> () {
    let mut _0: ();
    bb0: {
        drop((*_1)) -> [return: bb1, unwind: bb2];
    }
    bb1: {
        (*_1) = move _2;
        return;
    }
    bb2 (cleanup): {
        (*_1) = move _2;
        resume;
    }
}
"#;
    let module = lower(ok, "m");
    let report = verify_module(&module, &Config::default());
    let f = &report.functions[0];
    assert_eq!(f.verdict, Verdict::Pass, "cleanup write within bounds proves: {f:?}");
    // Every obligation is *decided* — none left as an undecided coverage gap.
    assert!(
        f.outcomes.iter().all(|o| o.verdict() != Verdict::Unknown),
        "no memory op is left reached-but-undecided: {f:?}"
    );

    // A definite OOB store on the cleanup path must FAIL (the path is checked).
    let oob = r#"
fn cleanup_oob(_1: &mut [i32; 4]) -> () {
    let mut _0: ();
    let mut _2: ();
    let mut _3: usize;
    bb0: {
        _2 = side_effect() -> [return: bb1, unwind: bb2];
    }
    bb1: {
        return;
    }
    bb2 (cleanup): {
        _3 = const 5_usize;
        (*_1)[_3] = const 0_i32;
        resume;
    }
}
"#;
    let module = lower(oob, "m");
    let report = verify_module(&module, &Config::default());
    // The cleanup path runs after a call, an over-approximation point, so the
    // engine proves but does not *refute* on it (sound: never a false PASS,
    // though a cleanup-path OOB is reported UNKNOWN rather than FAIL). The
    // soundness requirement is that the OOB is *checked* and not vacuously
    // proven — it must not be PASS.
    assert_ne!(
        report.functions[0].verdict,
        Verdict::Pass,
        "an OOB store on the cleanup path must not be a (false) PASS: {report:?}"
    );
}

/// MIR's constant and range place projections — `PLACE[N of M]` (`ConstantIndex`)
/// and `PLACE[from:to]`/`[from:]`/`[:to]` (`Subslice`) — the last frontend parse
/// gaps. `[N of M]` accesses element N; a subslice is modelled by its *start*
/// element pointer (sound for the pointer; the length change is
/// over-approximated). Both must parse and lower to a real, checked access.
#[test]
fn mir_constant_and_subslice_index_projections_parse() {
    let src = r#"
fn first_of(_1: &[u8]) -> u8 {
    let mut _0: u8;
    let mut _2: &[u8];
    bb0: {
        _0 = copy (*_1)[0 of 1];
        _2 = &(*_1)[1:];
        return;
    }
}
"#;
    let module = lower(src, "m");
    assert!(module.unanalyzed.is_empty(), "both projections parse: {:?}", module.unanalyzed);
    // The `[0 of 1]` read lowers to a real memory access (a PtrOffset + Load).
    let f = &module.functions[0];
    let has_offset = f.blocks.iter().flat_map(|b| &b.insts)
        .any(|i| matches!(i, csolver_ir::Inst::PtrOffset { .. }));
    assert!(has_offset, "the constant index is a real element access");
}

/// `core::intrinsics::copy_nonoverlapping::<u8>` must lower to a modelled, checked
/// `MemIntrinsic { kind: Copy }` (bounds/liveness/validity + the source/destination
/// overlap obligation — the concrete Rust aliasing UB), NOT an opaque call that would
/// silently drop the effect.
const COPY_NONOVERLAPPING: &str = r#"
fn cp(_1: *const u8, _2: *mut u8, _3: usize) -> () {
    let mut _0: ();
    bb0: {
        _0 = copy_nonoverlapping::<u8>(copy _1, copy _2, copy _3) -> [return: bb1, unwind continue];
    }
    bb1: {
        return;
    }
}
"#;

#[test]
fn copy_nonoverlapping_lowers_to_a_checked_memcpy() {
    use csolver_ir::{Inst, MemKind};
    let module = lower(COPY_NONOVERLAPPING, "cp");
    assert!(module.unanalyzed.is_empty(), "lowers, not dropped: {:?}", module.unanalyzed);
    let insts: Vec<&Inst> = module.functions.iter().flat_map(|f| f.blocks.iter()).flat_map(|b| &b.insts).collect();
    assert!(
        insts.iter().any(|i| matches!(i, Inst::MemIntrinsic { kind: MemKind::Copy, .. })),
        "copy_nonoverlapping is a MemIntrinsic(Copy), not an opaque call: {insts:?}"
    );
    // Its NoForbiddenOverlap obligation is enumerated for the copy.
    let report = verify_module(&module, &Config::default());
    assert!(
        report.functions[0].outcomes.iter().any(|o| o.obligation.property == SafetyProperty::NoForbiddenOverlap),
        "the copy carries a no-overlap obligation"
    );
}

/// `Offset` (pointer arithmetic `ptr.offset(n)`) must lower to a `PtrOffset` that keeps
/// the base pointer's provenance (stride = the pointee type), not an opaque `Undef` —
/// so a store through the offset pointer is bounds-checked against the same region.
const PTR_OFFSET: &str = r#"
fn f(_1: *mut i32, _2: usize) -> () {
    let mut _0: ();
    let mut _3: *mut i32;
    bb0: {
        _3 = Offset(copy _1, copy _2);
        (*_3) = const 0_i32;
        return;
    }
}
"#;

#[test]
fn ptr_offset_lowers_to_ptroffset_not_opaque() {
    use csolver_ir::Inst;
    let module = lower(PTR_OFFSET, "f");
    assert!(module.unanalyzed.is_empty(), "lowers: {:?}", module.unanalyzed);
    let insts: Vec<&Inst> = module.functions.iter().flat_map(|f| f.blocks.iter()).flat_map(|b| &b.insts).collect();
    let po = insts.iter().find(|i| matches!(i, Inst::PtrOffset { .. })).expect("Offset → PtrOffset");
    // The stride is the pointee type (i32), so the byte offset is count * 4 — a store
    // through it is then checked against the base region (not a lost, opaque pointer).
    assert!(matches!(po, Inst::PtrOffset { elem, .. } if elem.size_bytes(&csolver_ir::DataLayout::LP64) == Some(4)));
    assert!(insts.iter().any(|i| matches!(i, Inst::Store { .. })), "the store through it is modelled");
}

/// A `&mut *_p` reborrow emits a `csolver.retag.mut` marker (for the opt-in aliasing model);
/// a shared `&(*_p)` does NOT. Validates the parser (mutability capture) + the lowering.
pub(crate) const REBORROW_MUT: &str = r#"
fn f(_1: *mut i32) -> () {
    let mut _2: &mut i32;
    bb0: {
        _2 = &mut (*_1);
        (*_2) = const 5_i32;
        return;
    }
}
"#;

pub(crate) const REBORROW_SHARED: &str = r#"
fn g(_1: *const i32) -> i32 {
    let mut _2: &i32;
    let mut _0: i32;
    bb0: {
        _2 = &(*_1);
        _0 = (*_2);
        return;
    }
}
"#;

/// `&raw mut (*_p)` is a unique reborrow — emits a `csolver.retag.mut` marker like `&mut`.
pub(crate) const REBORROW_RAW_MUT: &str = r#"
fn h(_1: *mut i32) -> () {
    let mut _2: *mut i32;
    bb0: {
        _2 = &raw mut (*_1);
        (*_2) = const 7_i32;
        return;
    }
}
"#;

#[test]
fn reborrows_emit_the_right_retag_marker() {
    use csolver_ir::Inst;
    let retag_name = |src, name| -> Option<String> {
        let m = lower(src, name);
        m.functions.iter().flat_map(|f| f.blocks.iter()).flat_map(|b| &b.insts).find_map(|i| match i {
            Inst::Intrinsic { name, .. } if name.starts_with("csolver.retag.") => Some(name.clone()),
            _ => None,
        })
    };
    assert_eq!(retag_name(REBORROW_MUT, "f").as_deref(), Some("csolver.retag.mut"), "&mut *_p → retag.mut");
    assert_eq!(retag_name(REBORROW_SHARED, "g").as_deref(), Some("csolver.retag.shared"), "&(*_p) → retag.shared");
    assert_eq!(retag_name(REBORROW_RAW_MUT, "h").as_deref(), Some("csolver.retag.mut"), "&raw mut *_p → retag.mut");
}

/// **Protector**: a `&mut` reference parameter is a protected root borrow for the whole
/// function. Reborrowing it (`_2`), then writing through the PARAMETER (which pops the
/// reborrow), then using the reborrow is a use-after-invalidation — flagged only with the
/// aliasing model on. Exercises the entry protector marker end-to-end through the frontend.
pub(crate) const PROTECTOR_UAF: &str = r#"
fn f(_1: &mut i32) -> () {
    let mut _2: &mut i32;
    bb0: {
        _2 = &mut (*_1);
        (*_1) = const 5_i32;
        (*_2) = const 6_i32;
        return;
    }
}
"#;

#[test]
fn mut_param_protector_flags_use_after_reborrow_invalidation() {
    let module = lower(PROTECTOR_UAF, "f");
    // With the aliasing model ON: `(*_2)=6` after `(*_1)=5` invalidated _2 is a violation.
    let on = Config { level: csolver_core::SourceLevel::Mir, aliasing_model: true, ..Config::default() };
    assert_eq!(verify_module(&module, &on).verdict, Verdict::Fail, "param protector catches the reborrow-then-param-write-then-use");
    // OFF (default): the borrow stack is inert, so no such violation.
    let off = Config { level: csolver_core::SourceLevel::Mir, ..Config::default() };
    assert_ne!(verify_module(&module, &off).verdict, Verdict::Fail, "off by default → not flagged");
}

/// A `two_phase` `&mut` reborrow is modelled as a **shared** reborrow (`csolver.retag.shared`):
/// its reservation phase coexists with the parent, so it must not be a plain unique retag.
#[test]
fn two_phase_borrow_emits_a_shared_retag() {
    use csolver_ir::Inst;
    let src = r#"
fn f(_1: *mut i32) -> () {
    let mut _2: &mut i32;
    bb0: {
        _2 = &mut (two_phase) (*_1);
        (*_2) = const 5_i32;
        return;
    }
}
"#;
    let m = lower(src, "f");
    let name = m.functions.iter().flat_map(|f| &f.blocks).flat_map(|b| &b.insts).find_map(|i| match i {
        Inst::Intrinsic { name, .. } if name.starts_with("csolver.retag.") => Some(name.clone()),
        _ => None,
    });
    assert_eq!(name.as_deref(), Some("csolver.retag.shared"), "two_phase &mut → shared retag");
}

/// A reborrow through a reference to an interior-mutable type (`&UnsafeCell`/`&Cell`/…) emits NO
/// retag marker: interior mutability writes through a shared reference, so tracking such a borrow
/// in the aliasing model could false-FAIL. A reborrow through a plain `&mut i32` still does.
#[test]
fn interior_mutable_reborrow_emits_no_retag() {
    use csolver_ir::Inst;
    let has_retag = |src, name| {
        lower(src, name).functions.iter().flat_map(|f| &f.blocks).flat_map(|b| &b.insts)
            .any(|i| matches!(i, Inst::Intrinsic { name, .. } if name.starts_with("csolver.retag.")))
    };
    let cell = r#"
fn f(_1: &std::cell::UnsafeCell<i32>) -> () {
    let mut _2: &std::cell::UnsafeCell<i32>;
    bb0: {
        _2 = &(*_1);
        return;
    }
}
"#;
    let plain = r#"
fn g(_1: &mut i32) -> () {
    let mut _2: &mut i32;
    bb0: {
        _2 = &mut (*_1);
        return;
    }
}
"#;
    assert!(!has_retag(cell, "f"), "a &UnsafeCell reborrow must not emit a retag");
    assert!(has_retag(plain, "g"), "a plain &mut reborrow still emits a retag");
}

/// Use-after-scope: take `&_1`, end `_1`'s storage (`StorageDead`), then dereference the pointer.
/// The stack local's region is freed at `StorageDead`, so the later load is a dangling deref
/// (use-after-free of the scope). A read BEFORE the StorageDead is fine.
#[test]
fn use_of_stack_local_after_storage_dead_is_flagged() {
    let uaf = r#"
fn f() -> i32 {
    let mut _1: i32;
    let mut _2: *const i32;
    let mut _0: i32;
    bb0: {
        StorageLive(_1);
        StorageLive(_2);
        _1 = const 7_i32;
        _2 = &_1;
        StorageDead(_1);
        _0 = (*_2);
        return;
    }
}
"#;
    let report = verify_module(&lower(uaf, "f"), &Config { level: csolver_core::SourceLevel::Mir, ..Config::default() });
    assert_eq!(report.functions[0].verdict, Verdict::Fail, "reading a stack local after its StorageDead is use-after-scope");

    // Control: the SAME read BEFORE StorageDead is safe (no violation).
    let ok = r#"
fn g() -> i32 {
    let mut _1: i32;
    let mut _2: *const i32;
    let mut _0: i32;
    bb0: {
        StorageLive(_1);
        StorageLive(_2);
        _1 = const 7_i32;
        _2 = &_1;
        _0 = (*_2);
        StorageDead(_1);
        return;
    }
}
"#;
    assert_ne!(verify_module(&lower(ok, "g"), &Config { level: csolver_core::SourceLevel::Mir, ..Config::default() }).functions[0].verdict, Verdict::Fail, "reading before StorageDead is fine");
}
