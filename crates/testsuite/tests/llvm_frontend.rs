//! End-to-end: real LLVM-IR text → MSIR (via the frontend) → verified safe.
//!
//! This is the first input that is *not* hand-built MSIR: it is parsed and
//! lowered from `.ll`, then run through the unchanged, audited analysis core.

use csolver_core::Verdict;
use csolver_ir::Frontend;
use csolver_llvm::{LlvmFrontend, LlvmInput};
use csolver_verifier::{verify_module, Config};

/// `make_and_store(i)`: allocate `[8 x i32]`, then under `0 <= i && i < 8`
/// store through `&buf[i]`. Every implied memory obligation is provable.
const GUARDED_STORE: &str = r#"
define void @make_and_store(i64 %i) {
entry:
  %buf = alloca [8 x i32], align 4
  %c0 = icmp sle i64 0, %i
  br i1 %c0, label %check, label %done
check:
  %c1 = icmp slt i64 %i, 8
  br i1 %c1, label %body, label %done
body:
  %p = getelementptr inbounds i32, ptr %buf, i64 %i
  store i32 0, ptr %p, align 4
  br label %done
done:
  ret void
}
"#;

#[test]
fn llvm_guarded_store_verifies_pass() {
    let module = LlvmFrontend
        .lower(LlvmInput {
            source: GUARDED_STORE.into(),
            name: "guarded".into(),
        })
        .expect("frontend lowers the .ll");

    let report = verify_module(&module, &Config::default());
    assert_eq!(report.verdict, Verdict::Pass, "report: {report:?}");
    // Memory obligations for the store were emitted and all proved.
    let f = &report.functions[0];
    assert!(!f.outcomes.is_empty(), "store implies obligations");
    assert!(f.outcomes.iter().all(|o| o.verdict() == Verdict::Pass));
}

/// An out-of-bounds constant store must NOT verify as PASS — the guard allows
/// `i < 16` but the buffer only holds 8 `i32`s, so `buf[i]` can be out of
/// bounds. The store stays UNKNOWN (no false PASS).
const OOB_STORE: &str = r#"
define void @maybe_oob(i64 %i) {
entry:
  %buf = alloca [8 x i32], align 4
  %c0 = icmp sle i64 0, %i
  br i1 %c0, label %check, label %done
check:
  %c1 = icmp slt i64 %i, 16
  br i1 %c1, label %body, label %done
body:
  %p = getelementptr inbounds i32, ptr %buf, i64 %i
  store i32 0, ptr %p, align 4
  br label %done
done:
  ret void
}
"#;

/// A real `phi`-based loop `for i in 0..16 { buf[i] = 0 }` over `[16 x i32]`.
/// Exercises the frontend's PHI→block-argument lowering together with the
/// loop-invariant handling in the analysis core.
const PHI_LOOP: &str = r#"
define void @loop_store() {
entry:
  %buf = alloca [16 x i32], align 4
  br label %head
head:
  %i = phi i64 [ 0, %entry ], [ %ni, %body ]
  %c = icmp slt i64 %i, 16
  br i1 %c, label %body, label %done
body:
  %p = getelementptr inbounds i32, ptr %buf, i64 %i
  store i32 0, ptr %p, align 4
  %ni = add i64 %i, 1
  br label %head
done:
  ret void
}
"#;

#[test]
fn llvm_phi_loop_verifies_pass() {
    let module = LlvmFrontend
        .lower(LlvmInput {
            source: PHI_LOOP.into(),
            name: "loop".into(),
        })
        .expect("frontend lowers the loop .ll");
    // The PHI became a block parameter; the loop body's array write is proved
    // in bounds from the interval invariant (i >= 0) plus the guard (i < 16).
    let report = verify_module(&module, &Config::default());
    assert_eq!(report.verdict, Verdict::Pass, "report: {report:?}");
}

/// A `.ll` in the shape `rustc --emit=llvm-ir` produces: a module header
/// (`source_filename`, `target …`), a mangled function name, function
/// attributes (`unnamed_addr #0 !dbg !6`), `; preds = …` label comments,
/// per-instruction `!dbg` metadata, an `attributes #0 = { … }` block, and a
/// trailing metadata section. All of it must be tolerated and the function
/// verified PASS.
const RUSTC_STYLE: &str = r##"
; ModuleID = 'example.cgu.0'
source_filename = "example.cgu.0"
target datalayout = "e-m:e-i64:64-f80:128-n8:16:32:64-S128"
target triple = "x86_64-unknown-linux-gnu"

; example::make_and_store
define void @_ZN7example14make_and_store17h0123456789abcdefE(i64 %i) unnamed_addr #0 !dbg !6 {
start:
  %buf = alloca [8 x i32], align 4, !dbg !11
  %c0 = icmp sle i64 0, %i, !dbg !12
  br i1 %c0, label %bb1, label %bb3, !dbg !12

bb1:                                              ; preds = %start
  %c1 = icmp slt i64 %i, 8, !dbg !13
  br i1 %c1, label %bb2, label %bb3, !dbg !13

bb2:                                              ; preds = %bb1
  %p = getelementptr inbounds i32, ptr %buf, i64 %i, !dbg !14
  store i32 0, ptr %p, align 4, !dbg !14
  br label %bb3, !dbg !14

bb3:                                              ; preds = %bb2, %bb1, %start
  ret void, !dbg !15
}

attributes #0 = { noinline nounwind optnone uwtable "target-cpu"="x86-64" }

!llvm.module.flags = !{!0, !1}
!llvm.dbg.cu = !{!4}
!0 = !{i32 8, !"PIC Level", i32 2}
!6 = distinct !DISubprogram(name: "make_and_store", scope: !7, file: !7, line: 1, unit: !4)
"##;

#[test]
fn llvm_rustc_style_module_verifies_pass() {
    let module = LlvmFrontend
        .lower(LlvmInput {
            source: RUSTC_STYLE.into(),
            name: "example".into(),
        })
        .expect("frontend tolerates rustc-style noise");
    assert_eq!(module.functions.len(), 1);
    assert!(module.functions[0].name.starts_with("_ZN7example"));
    let report = verify_module(&module, &Config::default());
    assert_eq!(report.verdict, Verdict::Pass, "report: {report:?}");
}

/// A pointer parameter with a `dereferenceable(32)` contract (as `rustc` emits
/// for `&mut [i32; 8]`): the guarded store through it verifies PASS, with the
/// `param-contracts` assumption recorded.
const DEREF_PARAM: &str = r#"
define void @store_through(i64 noundef %i, ptr noalias noundef align 4 dereferenceable(32) %buf) unnamed_addr #0 {
start:
  %c = icmp ult i64 %i, 8
  br i1 %c, label %body, label %done
body:
  %p = getelementptr inbounds i32, ptr %buf, i64 %i
  store i32 0, ptr %p, align 4
  br label %done
done:
  ret void
}
"#;

#[test]
fn llvm_dereferenceable_param_verifies_pass() {
    let module = LlvmFrontend
        .lower(LlvmInput {
            source: DEREF_PARAM.into(),
            name: "deref".into(),
        })
        .expect("lower");
    let report = verify_module(&module, &Config::default());
    assert_eq!(report.verdict, Verdict::Pass, "report: {report:?}");
    assert!(report.assumptions.iter().any(|a| a.id == "param-contracts"));
}

/// Soundness: a `readonly` pointer parameter must NOT let a *write* through it
/// be proved — the contract grants read access only.
const READONLY_PARAM: &str = r#"
define void @write_readonly(ptr readonly align 4 dereferenceable(32) %buf) unnamed_addr #0 {
start:
  %p = getelementptr inbounds i32, ptr %buf, i64 0
  store i32 0, ptr %p, align 4
  ret void
}
"#;

#[test]
fn llvm_write_to_readonly_param_is_not_pass() {
    let module = LlvmFrontend
        .lower(LlvmInput {
            source: READONLY_PARAM.into(),
            name: "ro".into(),
        })
        .expect("lower");
    let report = verify_module(&module, &Config::default());
    // The write's `valid_write` obligation cannot be proved (region is RO).
    let wrote_ok = report.functions[0].outcomes.iter().any(|o| {
        o.obligation.property == csolver_core::SafetyProperty::ValidWrite
            && matches!(o.result, csolver_core::ObligationResult::Proven(_))
    });
    assert!(!wrote_ok, "writing a readonly param must not be proved valid");
}

/// A real `rustc -O` shape: a local array initialized with **vector** stores
/// (`<4 x i32>`), bracketed by `llvm.lifetime` intrinsics, then a guarded
/// `buf[i]` load. Vectors are modelled by their byte size and the lifetime
/// intrinsics are no-ops, so the whole function verifies PASS.
const VECTORIZED: &str = r#"
define noundef i32 @pick(i64 noundef %i) unnamed_addr #0 {
start:
  %buf = alloca [32 x i8], align 16
  call void @llvm.lifetime.start.p0(i64 32, ptr nonnull %buf)
  store <4 x i32> <i32 1, i32 2, i32 3, i32 4>, ptr %buf, align 16
  %0 = getelementptr inbounds nuw i8, ptr %buf, i64 16
  store <4 x i32> <i32 5, i32 6, i32 7, i32 8>, ptr %0, align 16
  %_3 = icmp ult i64 %i, 8
  br i1 %_3, label %bb2, label %bb4
bb4:
  %_0.sroa.0.0 = phi i32 [ %2, %bb2 ], [ 0, %start ]
  call void @llvm.lifetime.end.p0(i64 32, ptr nonnull %buf)
  ret i32 %_0.sroa.0.0
bb2:
  %1 = getelementptr inbounds nuw i32, ptr %buf, i64 %i
  %2 = load i32, ptr %1, align 4
  br label %bb4
}
"#;

#[test]
fn llvm_vectorized_function_verifies_pass() {
    let module = LlvmFrontend
        .lower(LlvmInput {
            source: VECTORIZED.into(),
            name: "vec".into(),
        })
        .expect("lower vectorized .ll");
    let report = verify_module(&module, &Config::default());
    assert_eq!(report.verdict, Verdict::Pass, "report: {report:?}");
}

/// A module with a verifiable function plus one using an unsupported construct
/// (`select`). The good one is still verified PASS; the unsupported one is
/// reported UNKNOWN (not silently dropped), so the module is UNKNOWN.
const MIXED: &str = r#"
define void @good(i64 %i) {
entry:
  %buf = alloca [8 x i32], align 4
  %c0 = icmp sle i64 0, %i
  br i1 %c0, label %check, label %done
check:
  %c1 = icmp slt i64 %i, 8
  br i1 %c1, label %body, label %done
body:
  %p = getelementptr inbounds i32, ptr %buf, i64 %i
  store i32 0, ptr %p, align 4
  br label %done
done:
  ret void
}

define i32 @uses_indirectbr(ptr %p, i32 %v) {
entry:
  indirectbr ptr %p, [label %done]
done:
  %old = add i32 %v, 1
  ret i32 %old
}
"#;

#[test]
fn llvm_per_function_recovery() {
    let module = LlvmFrontend
        .lower(LlvmInput {
            source: MIXED.into(),
            name: "mixed".into(),
        })
        .expect("module parses despite one unsupported function");

    // The supported function lowered; the other is recorded as unanalyzed.
    assert_eq!(module.functions.len(), 1);
    assert_eq!(module.functions[0].name, "good");
    assert!(module.unanalyzed.iter().any(|(n, _)| n == "uses_indirectbr"));

    let report = verify_module(&module, &Config::default());
    // Module is UNKNOWN (one function not analyzed), but `good` is PASS.
    assert_eq!(report.verdict, Verdict::Unknown);
    let good = report.functions.iter().find(|f| f.function == "good").unwrap();
    assert_eq!(good.verdict, Verdict::Pass);
    let bad = report.functions.iter().find(|f| f.function == "uses_indirectbr").unwrap();
    assert_eq!(bad.verdict, Verdict::Unknown);
}

/// A `switch` dispatch (`match x { 0 => …, 1 => …, _ => … }`) over a local
/// `[4 x i32]`: each arm does an in-bounds store, and the three edges merge at
/// the return block. Exercises the frontend's `switch` lowering end-to-end
/// through the unchanged analysis core. Every access is in bounds → PASS.
const SWITCH_DISPATCH: &str = r#"
define void @classify(i64 %x) {
entry:
  %buf = alloca [4 x i32], align 4
  switch i64 %x, label %def [ i64 0, label %a i64 1, label %b ]
a:
  %pa = getelementptr inbounds i32, ptr %buf, i64 0
  store i32 10, ptr %pa, align 4
  br label %def
b:
  %pb = getelementptr inbounds i32, ptr %buf, i64 1
  store i32 20, ptr %pb, align 4
  br label %def
def:
  %pd = getelementptr inbounds i32, ptr %buf, i64 3
  store i32 30, ptr %pd, align 4
  ret void
}
"#;

#[test]
fn llvm_switch_dispatch_verifies_pass() {
    let module = LlvmFrontend
        .lower(LlvmInput {
            source: SWITCH_DISPATCH.into(),
            name: "switch".into(),
        })
        .expect("frontend lowers the switch .ll");
    assert!(module.unanalyzed.is_empty(), "switch function is analyzed, not dropped");
    let report = verify_module(&module, &Config::default());
    assert_eq!(report.verdict, Verdict::Pass, "report: {report:?}");
    assert!(report.functions[0].outcomes.iter().all(|o| o.verdict() == Verdict::Pass));
}

/// Soundness: an out-of-bounds store inside a `switch` arm must not be proved
/// PASS — `switch` lowering must not weaken the bounds check. The arm writes
/// `buf[7]` into a `[4 x i32]`.
const SWITCH_OOB: &str = r#"
define void @bad_arm(i64 %x) {
entry:
  %buf = alloca [4 x i32], align 4
  switch i64 %x, label %def [ i64 0, label %a ]
a:
  %pa = getelementptr inbounds i32, ptr %buf, i64 7
  store i32 10, ptr %pa, align 4
  br label %def
def:
  ret void
}
"#;

#[test]
fn llvm_switch_arm_out_of_bounds_is_not_pass() {
    let module = LlvmFrontend
        .lower(LlvmInput {
            source: SWITCH_OOB.into(),
            name: "switchoob".into(),
        })
        .expect("lower");
    let report = verify_module(&module, &Config::default());
    assert_ne!(report.verdict, Verdict::Pass, "OOB store in a switch arm must not pass");
}

/// Real `rustc -O` shape of `get(s: &[i32], i) -> if i < s.len() { s[i] } else
/// { -1 }`: the slice `(ptr %s.0, i64 %s.1)` is recognized, the access is proved
/// in bounds from `i < len`, and the `slice-abi` assumption is recorded.
const SLICE_GET: &str = r#"
define noundef i32 @get(ptr noalias noundef nonnull readonly align 4 %s.0, i64 noundef %s.1, i64 noundef %i) unnamed_addr #0 {
start:
  %_3 = icmp ult i64 %i, %s.1
  br i1 %_3, label %bb2, label %bb4
bb4:
  %_0.sroa.0.0 = phi i32 [ %1, %bb2 ], [ -1, %start ]
  ret i32 %_0.sroa.0.0
bb2:
  %0 = getelementptr inbounds nuw i32, ptr %s.0, i64 %i
  %1 = load i32, ptr %0, align 4
  br label %bb4
}
"#;

#[test]
fn llvm_slice_indexed_access_verifies_pass() {
    let module = LlvmFrontend
        .lower(LlvmInput {
            source: SLICE_GET.into(),
            name: "slice".into(),
        })
        .expect("lower");
    let report = verify_module(&module, &Config::default());
    assert_eq!(report.verdict, Verdict::Pass, "report: {report:?}");
    assert!(report.assumptions.iter().any(|a| a.id == "slice-abi"));
}

/// Soundness: a slice access WITHOUT a bounds guard must not be proved in
/// bounds (the index is unconstrained against the length).
const SLICE_UNCHECKED: &str = r#"
define i32 @get_unchecked(ptr align 4 %s.0, i64 %s.1, i64 %i) unnamed_addr #0 {
start:
  %p = getelementptr inbounds i32, ptr %s.0, i64 %i
  %v = load i32, ptr %p, align 4
  ret i32 %v
}
"#;

#[test]
fn llvm_unguarded_slice_access_is_not_pass() {
    let module = LlvmFrontend
        .lower(LlvmInput {
            source: SLICE_UNCHECKED.into(),
            name: "unchecked".into(),
        })
        .expect("lower");
    let report = verify_module(&module, &Config::default());
    let in_bounds_proved = report.functions[0].outcomes.iter().any(|o| {
        o.obligation.property == csolver_core::SafetyProperty::InBounds
            && matches!(o.result, csolver_core::ObligationResult::Proven(_))
    });
    assert!(!in_bounds_proved, "unguarded slice access must not prove in-bounds");
}

/// An index-based loop over a slice (`for i in 0..s.len() { ... s[i] ... }`):
/// the loop invariant `i >= 0`, the guard `i < len`, and the slice contract
/// (region size `len * 4`) combine to prove every iteration's access in bounds.
const SLICE_INDEX_LOOP: &str = r#"
define i32 @sum(ptr noundef nonnull readonly align 4 %s.0, i64 noundef %s.1) unnamed_addr #0 {
start:
  br label %head
head:
  %i = phi i64 [ 0, %start ], [ %ni, %body ]
  %acc = phi i32 [ 0, %start ], [ %nacc, %body ]
  %c = icmp ult i64 %i, %s.1
  br i1 %c, label %body, label %done
body:
  %p = getelementptr inbounds i32, ptr %s.0, i64 %i
  %x = load i32, ptr %p, align 4
  %nacc = add i32 %acc, %x
  %ni = add i64 %i, 1
  br label %head
done:
  ret i32 %acc
}
"#;

#[test]
fn llvm_index_loop_over_slice_verifies_pass() {
    let module = LlvmFrontend
        .lower(LlvmInput {
            source: SLICE_INDEX_LOOP.into(),
            name: "sumloop".into(),
        })
        .expect("lower");
    let report = verify_module(&module, &Config::default());
    assert_eq!(report.verdict, Verdict::Pass, "report: {report:?}");
}

/// Regression: a call argument with `align N @global` must not mistake the
/// alignment value for the operand (this broke `rustc`'s `panic_bounds_check`
/// calls, which pass `ptr align 8 @alloc…`).
const CALL_ALIGN_GLOBAL: &str = r#"
define void @caller() unnamed_addr #0 {
start:
  call void @sink(i64 1, i64 7, ptr align 8 @glob)
  ret void
}
"#;

#[test]
fn llvm_call_with_align_global_arg_parses() {
    let module = LlvmFrontend
        .lower(LlvmInput {
            source: CALL_ALIGN_GLOBAL.into(),
            name: "callalign".into(),
        })
        .expect("call with `align N @global` argument parses");
    assert_eq!(module.functions.len(), 1);
    assert!(module.unanalyzed.is_empty());
}

/// The fully-optimized `for x in s { … }` over `s: &[i32]` as `rustc -O` emits
/// it after loop rotation: a **pointer-walking** loop (`iter != end`, bottom-test
/// — load before the exit check), guarded by an `is_empty` preheader test. This
/// is the real compiled shape the equality-exit pointer-induction analysis is for.
const PTR_WALK: &str = r#"
define void @walk(ptr noalias noundef nonnull readonly align 4 %s.0, i64 noundef %s.1) unnamed_addr #0 {
start:
  %end = getelementptr inbounds i32, ptr %s.0, i64 %s.1
  %empty = icmp eq ptr %s.0, %end
  br i1 %empty, label %done, label %body
body:
  %iter = phi ptr [ %s.0, %start ], [ %next, %body ]
  %x = load i32, ptr %iter, align 4
  %next = getelementptr inbounds i32, ptr %iter, i64 1
  %atend = icmp eq ptr %next, %end
  br i1 %atend, label %done, label %body
done:
  ret void
}
"#;

#[test]
fn llvm_pointer_walk_loop_verifies_pass() {
    let module = LlvmFrontend
        .lower(LlvmInput {
            source: PTR_WALK.into(),
            name: "walk".into(),
        })
        .expect("lower the pointer-walk .ll");
    assert!(module.unanalyzed.is_empty(), "the walk lowers, not dropped");
    let report = verify_module(&module, &Config::default());
    assert_eq!(report.verdict, Verdict::Pass, "report: {report:?}");
    assert!(report.assumptions.iter().any(|a| a.id == "slice-abi"));
}

/// Soundness: the same pointer walk WITHOUT the `is_empty` preheader guard. On an
/// empty slice the unconditional first load reads out of bounds, so it must not
/// be proved PASS — the rotated-walk base case is unprovable without the guard.
const PTR_WALK_NOGUARD: &str = r#"
define void @walk_noguard(ptr noalias noundef nonnull readonly align 4 %s.0, i64 noundef %s.1) unnamed_addr #0 {
start:
  %end = getelementptr inbounds i32, ptr %s.0, i64 %s.1
  br label %body
body:
  %iter = phi ptr [ %s.0, %start ], [ %next, %body ]
  %x = load i32, ptr %iter, align 4
  %next = getelementptr inbounds i32, ptr %iter, i64 1
  %atend = icmp eq ptr %next, %end
  br i1 %atend, label %done, label %body
done:
  ret void
}
"#;

#[test]
fn llvm_pointer_walk_without_guard_is_not_pass() {
    let module = LlvmFrontend
        .lower(LlvmInput {
            source: PTR_WALK_NOGUARD.into(),
            name: "walknoguard".into(),
        })
        .expect("lower");
    let report = verify_module(&module, &Config::default());
    assert_ne!(report.verdict, Verdict::Pass, "an unguarded pointer walk must not pass");
}

/// `memcpy`/`memset` safety: a copy/fill of `len` bytes is proved when both the
/// destination (write) and source (read) are valid for `len` bytes. A copy of
/// 16 bytes between `dereferenceable(16)` pointers verifies; copying 32 does not.
const MEM_INTRINSICS: &str = r#"
declare void @llvm.memcpy.p0.p0.i64(ptr, ptr, i64, i1)
declare void @llvm.memset.p0.i64(ptr, i8, i64, i1)
define void @copy16(ptr align 1 dereferenceable(16) %dst, ptr align 1 dereferenceable(16) %src) unnamed_addr #0 {
entry:
  call void @llvm.memcpy.p0.p0.i64(ptr %dst, ptr %src, i64 16, i1 false)
  ret void
}
define void @set16(ptr align 1 dereferenceable(16) %dst) unnamed_addr #0 {
entry:
  call void @llvm.memset.p0.i64(ptr %dst, i8 0, i64 16, i1 false)
  ret void
}
define void @copy_oob(ptr align 1 dereferenceable(16) %dst, ptr align 1 dereferenceable(16) %src) unnamed_addr #0 {
entry:
  call void @llvm.memcpy.p0.p0.i64(ptr %dst, ptr %src, i64 32, i1 false)
  ret void
}
"#;

#[test]
fn llvm_memcpy_memset_safety() {
    let module = LlvmFrontend
        .lower(LlvmInput {
            source: MEM_INTRINSICS.into(),
            name: "mem".into(),
        })
        .expect("lower");
    let report = verify_module(&module, &Config::default());

    let verdict_of = |name: &str| {
        report
            .functions
            .iter()
            .find(|f| f.function == name)
            .unwrap()
            .verdict
    };
    assert_eq!(verdict_of("copy16"), Verdict::Pass);
    assert_eq!(verdict_of("set16"), Verdict::Pass);
    // Soundness: copying 32 bytes into a 16-byte region must not be proved.
    assert_ne!(verdict_of("copy_oob"), Verdict::Pass);
}

#[test]
fn llvm_out_of_bounds_store_is_not_pass() {
    let module = LlvmFrontend
        .lower(LlvmInput {
            source: OOB_STORE.into(),
            name: "oob".into(),
        })
        .expect("frontend lowers the .ll");
    let report = verify_module(&module, &Config::default());
    // Soundness: must not be PASS (the access can exceed the 8-element buffer).
    assert_ne!(report.verdict, Verdict::Pass);
}

/// Positive control for every "0 FAILs on the real-crate sweep" claim: a
/// *definite* (constant-index) out-of-bounds store through the LLVM path must
/// verify to `FAIL` — not merely non-PASS. If this stops failing, a clean FAIL
/// column in a sweep is a muted engine, not a clean corpus.
#[test]
fn llvm_definite_oob_store_fails() {
    let src = r#"
define void @oob() {
start:
  %buf = alloca [4 x i32], align 4
  %p = getelementptr inbounds i32, ptr %buf, i64 5
  store i32 0, ptr %p, align 4
  ret void
}
"#;
    let module = LlvmFrontend
        .lower(LlvmInput { source: src.into(), name: "oob".into() })
        .expect("frontend lowers the .ll");
    let report = verify_module(&module, &Config::default());
    assert_eq!(report.verdict, Verdict::Fail, "a definite OOB store must FAIL");
}

/// A recognized C/kernel allocator (`malloc`/`kmalloc`/…) lowers to a heap `Alloc`,
/// so a heap buffer's size is known and bugs through it are found. Four checks in one
/// module: a guarded index PASSes, a constant-OOB read FAILs, a use-after-free FAILs,
/// and a double-free FAILs — the temporal/spatial obligations a modeled allocation
/// carries. (A `Call` to an opaque `malloc` would leave all four UNKNOWN.)
#[test]
fn allocator_calls_are_modeled_as_heap_allocations() {
    let guarded = r#"
define i64 @f(i64 %i) {
entry:
  %p = call ptr @malloc(i64 64)
  store i64 7, ptr %p, align 8
  %ok = icmp ult i64 %i, 8
  br i1 %ok, label %in, label %out
in:
  %q = getelementptr i64, ptr %p, i64 %i
  %v = load i64, ptr %q, align 8
  call void @free(ptr %p)
  ret i64 %v
out:
  call void @free(ptr %p)
  ret i64 -1
}
declare ptr @malloc(i64)
declare void @free(ptr)
"#;
    let m = LlvmFrontend.lower(LlvmInput { source: guarded.into(), name: "g".into() }).expect("lower");
    assert_eq!(verify_module(&m, &Config::default()).verdict, Verdict::Pass,
        "a guarded index into a malloc'd buffer proves");

    let oob = r#"
define i64 @f() {
entry:
  %p = call ptr @malloc(i64 64)
  %q = getelementptr i64, ptr %p, i64 9
  %v = load i64, ptr %q, align 8
  call void @free(ptr %p)
  ret i64 %v
}
declare ptr @malloc(i64)
declare void @free(ptr)
"#;
    let m = LlvmFrontend.lower(LlvmInput { source: oob.into(), name: "o".into() }).expect("lower");
    assert_eq!(verify_module(&m, &Config::default()).verdict, Verdict::Fail,
        "a constant OOB read past a malloc'd 64-byte buffer must FAIL");

    let uaf = r#"
define i64 @f() {
entry:
  %p = call ptr @malloc(i64 64)
  store i64 7, ptr %p, align 8
  call void @free(ptr %p)
  %v = load i64, ptr %p, align 8
  ret i64 %v
}
declare ptr @malloc(i64)
declare void @free(ptr)
"#;
    let m = LlvmFrontend.lower(LlvmInput { source: uaf.into(), name: "u".into() }).expect("lower");
    assert_eq!(verify_module(&m, &Config::default()).verdict, Verdict::Fail,
        "a read after free of a malloc'd buffer must FAIL");

    let df = r#"
define void @f() {
entry:
  %p = call ptr @kmalloc(i64 64, i64 0)
  call void @kfree(ptr %p)
  call void @kfree(ptr %p)
  ret void
}
declare ptr @kmalloc(i64, i64)
declare void @kfree(ptr)
"#;
    let m = LlvmFrontend.lower(LlvmInput { source: df.into(), name: "d".into() }).expect("lower");
    assert_eq!(verify_module(&m, &Config::default()).verdict, Verdict::Fail,
        "a kmalloc'd buffer freed twice must FAIL (double free)");
}

/// Bug-finding refutes an OOB indexed by a **unit-stride counting induction**: the
/// inclusive `for (i = 0; i <= 16; i++) a[i]` writes `a[16]`, one past a 16-element
/// array. Sound because a unit-stride single-exit loop reaches every guard-admitted
/// index, so the witness `i = 16` is genuinely reached. The controls must NOT refute
/// (false positive): a half-open (`i < 16`) safe loop, a stride-2 loop (skips indices),
/// and an early-`break` loop (an iteration can be skipped, so not single-exit).
#[test]
fn bug_finding_refutes_off_by_one_loop() {
    let bugs = Config { bug_finding: true, ..Config::default() };
    let verdict = |src: &str| {
        let m = LlvmFrontend.lower(LlvmInput { source: src.into(), name: "l".into() }).expect("lower");
        verify_module(&m, &bugs).verdict
    };
    // Inclusive `i <= 16` over a[16], unit stride, single exit → writes a[16] → FAIL.
    let oob = r#"
define i64 @f() {
entry:
  %a = alloca [16 x i64], align 16
  br label %head
head:
  %k = phi i64 [ 0, %entry ], [ %kn, %body ]
  %c = icmp sle i64 %k, 16
  br i1 %c, label %body, label %after
body:
  %p = getelementptr [16 x i64], ptr %a, i64 0, i64 %k
  store i64 %k, ptr %p, align 8
  %kn = add i64 %k, 1
  br label %head
after:
  ret i64 0
}
"#;
    assert_eq!(verdict(oob), Verdict::Fail, "inclusive-bound unit-stride loop writes a[16]");

    // Half-open `i < 16`: safe.
    assert_ne!(verdict(&oob.replace("sle i64 %k, 16", "slt i64 %k, 16")), Verdict::Fail,
        "a half-open loop is safe — no false positive");
    // Stride 2: not every index is reached, so an OOB index is not guaranteed hit.
    assert_ne!(verdict(&oob.replace("add i64 %k, 1", "add i64 %k, 2")), Verdict::Fail,
        "a strided loop is not unit-stride — must not refute");
    // Early break (a second exit from the body): an iteration can be skipped.
    let brk = r#"
define i64 @f() {
entry:
  %a = alloca [16 x i64], align 16
  br label %head
head:
  %k = phi i64 [ 0, %entry ], [ %kn, %body ]
  %c = icmp sle i64 %k, 16
  br i1 %c, label %body, label %after
body:
  %p = getelementptr [16 x i64], ptr %a, i64 0, i64 %k
  store i64 %k, ptr %p, align 8
  %kn = add i64 %k, 1
  %brk = icmp eq i64 %k, 3
  br i1 %brk, label %after, label %head
after:
  ret i64 0
}
"#;
    assert_ne!(verdict(brk), Verdict::Fail, "an early break breaks single-exit — must not refute");
}

/// Bug-finding mode also refutes a *temporal* violation (use-after-free) reached past
/// an over-approximated path — a free after an init loop, then a read of the freed
/// pointer. Strict verification stays UNKNOWN (the free/loop made the path inexact);
/// a free with no later use must not be a false positive in either mode.
#[test]
fn bug_finding_refutes_use_after_free_past_a_loop() {
    let uaf = r#"
define i64 @f(i64 %i) {
entry:
  %p = call ptr @malloc(i64 64)
  br label %head
head:
  %k = phi i64 [ 0, %entry ], [ %kn, %body ]
  %done = icmp uge i64 %k, 8
  br i1 %done, label %after, label %body
body:
  %pk = getelementptr i64, ptr %p, i64 %k
  store i64 %k, ptr %pk, align 8
  %kn = add i64 %k, 1
  br label %head
after:
  call void @free(ptr %p)
  %v = load i64, ptr %p, align 8
  ret i64 %v
}
declare ptr @malloc(i64)
declare void @free(ptr)
"#;
    let m = LlvmFrontend.lower(LlvmInput { source: uaf.into(), name: "u".into() }).expect("lower");
    let bugs = Config { bug_finding: true, ..Config::default() };
    assert_ne!(verify_module(&m, &Config::default()).verdict, Verdict::Fail,
        "strict mode does not refute a temporal violation past an inexact path");
    assert_eq!(verify_module(&m, &bugs).verdict, Verdict::Fail,
        "bug-finding refutes a use-after-free reached past an init loop");

    // Control: the same loop + free, but no use after — must not be a false positive.
    let safe = r#"
define void @f() {
entry:
  %p = call ptr @malloc(i64 64)
  br label %head
head:
  %k = phi i64 [ 0, %entry ], [ %kn, %body ]
  %done = icmp uge i64 %k, 8
  br i1 %done, label %after, label %body
body:
  %pk = getelementptr i64, ptr %p, i64 %k
  store i64 %k, ptr %pk, align 8
  %kn = add i64 %k, 1
  br label %head
after:
  call void @free(ptr %p)
  ret void
}
declare ptr @malloc(i64)
declare void @free(ptr)
"#;
    let m = LlvmFrontend.lower(LlvmInput { source: safe.into(), name: "s".into() }).expect("lower");
    assert_ne!(verify_module(&m, &bugs).verdict, Verdict::Fail,
        "a free with no later use must not be a false positive");
}

/// An OOB indexed by an **unsigned** parameter — `buf[idx]` where `idx` is `unsigned`
/// zero-extended to pointer width (`gep i8, buf, zext(idx)`), the pervasive C form.
/// The index must be widened to pointer width before the offset arithmetic, else it
/// mixes widths and no bound holds. Refuted in bug-finding mode (witness `idx = UINT_MAX`).
#[test]
fn bug_finding_refutes_unsigned_index_oob() {
    // `buf` is stored to (so the read is initialized — the OOB, not an uninit read,
    // is what is tested), then indexed by the zero-extended unsigned parameter.
    let oob = r#"
define i64 @f(i32 %idx) {
entry:
  %buf = alloca [16 x i8], align 16
  call void @llvm.memset.p0.i64(ptr %buf, i8 0, i64 16, i1 false)
  %z = zext i32 %idx to i64
  %p = getelementptr inbounds i8, ptr %buf, i64 %z
  %v = load i8, ptr %p, align 1
  %w = sext i8 %v to i64
  ret i64 %w
}
declare void @llvm.memset.p0.i64(ptr, i8, i64, i1)
"#;
    let m = LlvmFrontend.lower(LlvmInput { source: oob.into(), name: "u".into() }).expect("lower");
    let bugs = Config { bug_finding: true, ..Config::default() };
    assert_eq!(verify_module(&m, &bugs).verdict, Verdict::Fail,
        "an OOB indexed by a zero-extended unsigned parameter is refuted");
    // The guarded sibling (`idx < 16`) is safe — no false positive.
    let safe = r#"
define i64 @f(i32 %idx) {
entry:
  %buf = alloca [16 x i8], align 16
  call void @llvm.memset.p0.i64(ptr %buf, i8 0, i64 16, i1 false)
  %ok = icmp ult i32 %idx, 16
  br i1 %ok, label %in, label %out
out:
  ret i64 -1
in:
  %z = zext i32 %idx to i64
  %p = getelementptr inbounds i8, ptr %buf, i64 %z
  %v = load i8, ptr %p, align 1
  %w = sext i8 %v to i64
  ret i64 %w
}
declare void @llvm.memset.p0.i64(ptr, i8, i64, i1)
"#;
    let m = LlvmFrontend.lower(LlvmInput { source: safe.into(), name: "s".into() }).expect("lower");
    assert_ne!(verify_module(&m, &bugs).verdict, Verdict::Fail, "a guarded unsigned index is safe");
}

/// The opt-in `assume_valid_params`: a field access through a raw pointer parameter
/// of known (debug-info) pointee size proves — the framework/kernel entry ABI passes
/// a valid pointer. UNKNOWN by default (a raw pointer may dangle); PASS under the
/// assumption, which the report surfaces as `param-valid`. This is the dominant
/// `UNKNOWN` cause in per-TU kernel/driver code.
#[test]
fn assume_valid_params_contracts_raw_pointer_params() {
    // `struct dev { i32 id; [8 x i64] buf }`; read `d->buf[3]`, in bounds of the
    // 72-byte instance. Needs `-g` debug info for the pointee size, so hand-write it.
    let src = r#"
%struct.dev = type { i32, [8 x i64] }
define i64 @read_field(ptr %d) !dbg !4 {
entry:
  %p = getelementptr %struct.dev, ptr %d, i64 0, i32 1, i64 3
  %v = load i64, ptr %p, align 8
  ret i64 %v
}
!llvm.dbg.cu = !{!0}
!llvm.module.flags = !{!3}
!0 = distinct !DICompileUnit(language: DW_LANG_C11, file: !1, emissionKind: FullDebug)
!1 = !DIFile(filename: "d.c", directory: "/")
!3 = !{i32 2, !"Debug Info Version", i32 3}
!4 = distinct !DISubprogram(name: "read_field", scope: !1, file: !1, line: 1, type: !5, unit: !0, retainedNodes: !9)
!5 = !DISubroutineType(types: !6)
!6 = !{!7, !8}
!7 = !DIBasicType(name: "long", size: 64, encoding: DW_ATE_signed)
!8 = !DIDerivedType(tag: DW_TAG_pointer_type, baseType: !10, size: 64)
!10 = !DICompositeType(tag: DW_TAG_structure_type, name: "dev", size: 576)
!9 = !{!11}
!11 = !DILocalVariable(name: "d", arg: 1, scope: !4, file: !1, type: !8)
"#;
    let m = LlvmFrontend.lower(LlvmInput { source: src.into(), name: "d".into() }).expect("lower");
    // Default: a raw pointer parameter is uncontracted → UNKNOWN.
    assert_ne!(verify_module(&m, &Config::default()).verdict, Verdict::Pass,
        "a raw pointer parameter is not assumed valid by default");
    // Opt-in: the framework-valid-pointer assumption makes the field access prove.
    let cfg = Config { assume_valid_params: true, ..Config::default() };
    assert_eq!(verify_module(&m, &cfg).verdict, Verdict::Pass,
        "assume_valid_params contracts the raw pointer param to its pointee size");

    // Kernel IR is built without debug info, so the pointee size must also be
    // inferable from the parameter's *use* (`gep %struct.dev, ptr %d, 0, …`).
    let no_dwarf = r#"
%struct.dev = type { i32, [8 x i64] }
define i64 @read_field(ptr %d) {
entry:
  %p = getelementptr %struct.dev, ptr %d, i64 0, i32 1, i64 3
  %v = load i64, ptr %p, align 8
  ret i64 %v
}
"#;
    let m = LlvmFrontend.lower(LlvmInput { source: no_dwarf.into(), name: "n".into() }).expect("lower");
    assert_ne!(verify_module(&m, &Config::default()).verdict, Verdict::Pass);
    assert_eq!(verify_module(&m, &cfg).verdict, Verdict::Pass,
        "the pointee size is inferred from the gep-base type when debug info is absent");
}

/// `assume_valid_params` also recovers a **loaded** raw pointer field: `d->child->
/// data[2]` where `child` is a `struct child *` member. Under the opt-in, the loaded
/// `child` is materialised as a valid `struct child` (from debug info), so the access
/// through it proves — the dominant `UNKNOWN` cause on real kernel code. UNKNOWN by
/// default (a raw pointer field may hold null / a dangling value).
#[test]
fn assume_valid_params_recovers_loaded_pointer_fields() {
    // struct child { i32; [4 x i64] }; struct dev { i32; child* }. Access d->child->
    // data[2] (offset 8 in child) — in bounds of the 40-byte child. With DWARF: `dev`
    // has a raw-pointer member `child` at offset 8 pointing at `struct child`.
    let src = r#"
%struct.child = type { i32, [4 x i64] }
%struct.dev = type { i32, ptr }
define i64 @read_child(ptr %d) !dbg !4 {
entry:
  %c = getelementptr inbounds i8, ptr %d, i64 8
  %child = load ptr, ptr %c, align 8
  %p = getelementptr inbounds i8, ptr %child, i64 24
  %v = load i64, ptr %p, align 8
  ret i64 %v
}
!llvm.dbg.cu = !{!0}
!llvm.module.flags = !{!3}
!0 = distinct !DICompileUnit(language: DW_LANG_C11, file: !1, emissionKind: FullDebug)
!1 = !DIFile(filename: "d.c", directory: "/")
!3 = !{i32 2, !"Debug Info Version", i32 3}
!4 = distinct !DISubprogram(name: "read_child", scope: !1, file: !1, type: !5, unit: !0, retainedNodes: !20)
!5 = !DISubroutineType(types: !6)
!6 = !{!7, !8}
!7 = !DIBasicType(name: "long", size: 64)
!8 = !DIDerivedType(tag: DW_TAG_pointer_type, baseType: !9, size: 64)
!9 = !DICompositeType(tag: DW_TAG_structure_type, name: "dev", size: 128, elements: !10)
!10 = !{!11, !12}
!11 = !DIDerivedType(tag: DW_TAG_member, name: "id", baseType: !7, size: 32, offset: 0)
!12 = !DIDerivedType(tag: DW_TAG_member, name: "child", baseType: !13, size: 64, offset: 64)
!13 = !DIDerivedType(tag: DW_TAG_pointer_type, baseType: !14, size: 64)
!14 = !DICompositeType(tag: DW_TAG_structure_type, name: "child", size: 320)
!20 = !{!21}
!21 = !DILocalVariable(name: "d", arg: 1, scope: !4, file: !1, type: !8)
"#;
    let m = LlvmFrontend.lower(LlvmInput { source: src.into(), name: "c".into() }).expect("lower");
    assert_ne!(verify_module(&m, &Config::default()).verdict, Verdict::Pass,
        "a loaded raw pointer field is not assumed valid by default");
    let cfg = Config { assume_valid_params: true, ..Config::default() };
    assert_eq!(verify_module(&m, &cfg).verdict, Verdict::Pass,
        "assume_valid_params materialises the loaded child pointer as a valid struct");
}

/// Soundness of `--assume-valid-params` under bug-finding: an assumed-valid pointer's
/// pointee size is a *guess* (from debug info / use), not a proven allocation bound. The
/// pervasive kernel `container_of` idiom steps **backward** off the member pointer to the
/// enclosing struct — a negative *constant* offset. That must never be reported as an OOB
/// (it would be a false FAIL); only an access whose offset is driven by a *genuine input*
/// may refute against an assumed region.
#[test]
fn assume_valid_params_does_not_false_fail_on_container_of() {
    // The refutable assumed-region path: `d->child` is a loaded raw-pointer field
    // materialised (RefWitness) as a valid 40-byte `struct child`. `container_of` steps
    // 16 bytes **back** off that member pointer to reach the enclosing struct — a constant
    // negative offset, before the region base. Its size is only a guess, so this must NOT
    // FAIL (before the fix it did, with an empty witness — the kernel false positive).
    let src = r#"
%struct.child = type { i32, [4 x i64] }
%struct.dev = type { i32, ptr }
define i64 @up(ptr %d) !dbg !4 {
entry:
  %c = getelementptr inbounds i8, ptr %d, i64 8
  %child = load ptr, ptr %c, align 8
  %b = getelementptr inbounds i8, ptr %child, i64 -16
  %v = load i64, ptr %b, align 8
  ret i64 %v
}
!llvm.dbg.cu = !{!0}
!llvm.module.flags = !{!3}
!0 = distinct !DICompileUnit(language: DW_LANG_C11, file: !1, emissionKind: FullDebug)
!1 = !DIFile(filename: "d.c", directory: "/")
!3 = !{i32 2, !"Debug Info Version", i32 3}
!4 = distinct !DISubprogram(name: "up", scope: !1, file: !1, type: !5, unit: !0, retainedNodes: !20)
!5 = !DISubroutineType(types: !6)
!6 = !{!7, !8}
!7 = !DIBasicType(name: "long", size: 64)
!8 = !DIDerivedType(tag: DW_TAG_pointer_type, baseType: !9, size: 64)
!9 = !DICompositeType(tag: DW_TAG_structure_type, name: "dev", size: 128, elements: !10)
!10 = !{!11, !12}
!11 = !DIDerivedType(tag: DW_TAG_member, name: "id", baseType: !7, size: 32, offset: 0)
!12 = !DIDerivedType(tag: DW_TAG_member, name: "child", baseType: !13, size: 64, offset: 64)
!13 = !DIDerivedType(tag: DW_TAG_pointer_type, baseType: !14, size: 64)
!14 = !DICompositeType(tag: DW_TAG_structure_type, name: "child", size: 320)
!20 = !{!21}
!21 = !DILocalVariable(name: "d", arg: 1, scope: !4, file: !1, type: !8)
"#;
    let m = LlvmFrontend.lower(LlvmInput { source: src.into(), name: "u".into() }).expect("lower");
    let cfg = Config { assume_valid_params: true, bug_finding: true, ..Config::default() };
    assert_ne!(verify_module(&m, &cfg).verdict, Verdict::Fail,
        "a constant backward (container_of) offset off an assumed region is not a bug");

    // A *genuine* input-driven OOB against a RefWitness-materialised assumed region (the
    // refutable path: a loaded raw-pointer field, `d->child`) is still caught. `child`
    // points at a 40-byte `struct child`; indexing `child->data[idx]` with an unbounded
    // parameter `idx` reaches out of it — that is a real, input-driven OOB, not an artifact
    // of the assumed size, so it must FAIL even after the container_of suppression.
    let genuine = r#"
%struct.child = type { i32, [4 x i64] }
%struct.dev = type { i32, ptr }
define i64 @oob(ptr %d, i64 %idx) !dbg !4 {
entry:
  %c = getelementptr inbounds i8, ptr %d, i64 8
  %child = load ptr, ptr %c, align 8
  %p = getelementptr %struct.child, ptr %child, i64 0, i32 1, i64 %idx
  %v = load i64, ptr %p, align 8
  ret i64 %v
}
!llvm.dbg.cu = !{!0}
!llvm.module.flags = !{!3}
!0 = distinct !DICompileUnit(language: DW_LANG_C11, file: !1, emissionKind: FullDebug)
!1 = !DIFile(filename: "d.c", directory: "/")
!3 = !{i32 2, !"Debug Info Version", i32 3}
!4 = distinct !DISubprogram(name: "oob", scope: !1, file: !1, type: !5, unit: !0, retainedNodes: !20)
!5 = !DISubroutineType(types: !6)
!6 = !{!7, !8, !7}
!7 = !DIBasicType(name: "long", size: 64)
!8 = !DIDerivedType(tag: DW_TAG_pointer_type, baseType: !9, size: 64)
!9 = !DICompositeType(tag: DW_TAG_structure_type, name: "dev", size: 128, elements: !10)
!10 = !{!11, !12}
!11 = !DIDerivedType(tag: DW_TAG_member, name: "id", baseType: !7, size: 32, offset: 0)
!12 = !DIDerivedType(tag: DW_TAG_member, name: "child", baseType: !13, size: 64, offset: 64)
!13 = !DIDerivedType(tag: DW_TAG_pointer_type, baseType: !14, size: 64)
!14 = !DICompositeType(tag: DW_TAG_structure_type, name: "child", size: 320)
!20 = !{!21}
!21 = !DILocalVariable(name: "d", arg: 1, scope: !4, file: !1, type: !8)
"#;
    let m = LlvmFrontend.lower(LlvmInput { source: genuine.into(), name: "g".into() }).expect("lower");
    assert_eq!(verify_module(&m, &cfg).verdict, Verdict::Fail,
        "an input-driven OOB off a RefWitness-materialised assumed region is still a genuine bug");
}

/// `callbr` (inline-asm goto, pervasive in the kernel for static keys) must not drop
/// the function: it lowers to an asm havoc plus a branch to every target. An OOB in
/// the fallthrough block (reached after the callbr) is still found.
#[test]
fn callbr_is_analyzed_not_dropped() {
    let src = r#"
define i64 @f(i64 %i) {
entry:
  %a = alloca [8 x i64], align 8
  callbr void asm sideeffect "", "!i,~{memory}"() to label %cont [label %err]
cont:
  %p = getelementptr [8 x i64], ptr %a, i64 0, i64 %i
  store i64 1, ptr %p, align 8
  ret i64 0
err:
  ret i64 -1
}
"#;
    let m = LlvmFrontend.lower(LlvmInput { source: src.into(), name: "cb".into() }).expect("lower");
    assert!(m.unanalyzed.is_empty(), "callbr must not drop the function: {:?}", m.unanalyzed);
    let bugs = Config { bug_finding: true, ..Config::default() };
    assert_eq!(verify_module(&m, &bugs).verdict, Verdict::Fail,
        "an OOB in the callbr fallthrough is found");
}

/// A gep with a **variable index below the first level** (`p->arr[j]` →
/// `gep %S, ptr, 0, 1, %j`) must lower to a PtrOffset chain (field offset folded,
/// then a scaled variable step), not drop the function. A safe in-bounds nested
/// access with a guarded variable index proves under closed-world.
#[test]
fn variable_mid_index_gep_lowers_to_a_chain() {
    let src = r#"
%struct.s = type { i32, [4 x i64] }
define i64 @f(i64 %j) {
entry:
  %s = alloca %struct.s, align 8
  %ok = icmp ult i64 %j, 4
  br i1 %ok, label %in, label %out
in:
  %p = getelementptr %struct.s, ptr %s, i64 0, i32 1, i64 %j
  store i64 7, ptr %p, align 8
  %v = load i64, ptr %p, align 8
  ret i64 %v
out:
  ret i64 -1
}
"#;
    let m = LlvmFrontend.lower(LlvmInput { source: src.into(), name: "vm".into() }).expect("lower");
    assert!(m.unanalyzed.is_empty(), "variable-mid-index gep must not drop the function: {:?}", m.unanalyzed);
    let cfg = Config { closed_world: true, ..Config::default() };
    assert_eq!(verify_module(&m, &cfg).verdict, Verdict::Pass,
        "a guarded in-bounds variable nested access proves (the chain offsets are correct)");
}

/// In bug-finding mode a scalar parameter is a genuine adversarial input only for an
/// **exported** function (externally reachable, so an attacker may pick the value).
/// An **internal** function's parameters are supplied by in-module callers
/// (caller-constrained), so refuting on a freely-chosen index would be a false
/// positive — the real cause of false FAILs on internal kernel helpers indexed by a
/// bounded enum. Same body, two linkages: exported FAILs, internal does not.
#[test]
fn bug_finding_only_refutes_exported_function_params() {
    let src = r#"
define i64 @exported(i64 %i) {
entry:
  %a = alloca [8 x i64], align 8
  %p = getelementptr [8 x i64], ptr %a, i64 0, i64 %i
  store i64 1, ptr %p, align 8
  ret i64 0
}
define internal i64 @internal(i64 %i) {
entry:
  %a = alloca [8 x i64], align 8
  %p = getelementptr [8 x i64], ptr %a, i64 0, i64 %i
  store i64 1, ptr %p, align 8
  ret i64 0
}
define i64 @caller() {
entry:
  %r = call i64 @internal(i64 3)
  ret i64 %r
}
"#;
    let m = LlvmFrontend.lower(LlvmInput { source: src.into(), name: "x".into() }).expect("lower");
    let bugs = Config { bug_finding: true, ..Config::default() };
    let report = verify_module(&m, &bugs);
    let verdict_of =
        |name: &str| report.functions.iter().find(|f| f.function == name).map(|f| f.verdict);
    assert_eq!(verdict_of("exported"), Some(Verdict::Fail),
        "an exported function's unchecked index parameter is a bug candidate");
    assert_ne!(verdict_of("internal"), Some(Verdict::Fail),
        "an internal function's caller-constrained parameter must not be a false positive");
}

/// A **multi-level** nested gep (`gep %Outer, ptr, 0, 1, 2` — field 1 of Outer, then
/// field/index 2 within it) must lower to the exact padded byte offset, not drop the
/// whole function. Pervasive in real C/kernel IR. The offset must be correct, not just
/// non-dropped: a safe nested access proves in bounds (a wrong offset would not), and
/// the function is analysed (no `unanalyzed` entry).
#[test]
fn nested_multi_level_gep_resolves_the_offset() {
    // Outer = { i32 x, {i32,i64} in, [4 x i64] arr }; read in.b then arr[3], both in
    // bounds → PASS proves the nested offsets are right. A whole-program local.
    let src = r#"
%struct.inner = type { i32, i64 }
%struct.outer = type { i32, %struct.inner, [4 x i64] }
define i64 @f() {
entry:
  %o = alloca %struct.outer, align 8
  %pb = getelementptr inbounds %struct.outer, ptr %o, i64 0, i32 1, i32 1
  store i64 5, ptr %pb, align 8
  %b = load i64, ptr %pb, align 8
  %pa = getelementptr inbounds %struct.outer, ptr %o, i64 0, i32 2, i64 3
  store i64 7, ptr %pa, align 8
  %a = load i64, ptr %pa, align 8
  %s = add i64 %b, %a
  ret i64 %s
}
"#;
    let m = LlvmFrontend.lower(LlvmInput { source: src.into(), name: "n".into() }).expect("lower");
    assert!(m.unanalyzed.is_empty(), "a nested gep must not drop the function: {:?}", m.unanalyzed);
    let cfg = Config { closed_world: true, ..Config::default() };
    assert_eq!(verify_module(&m, &cfg).verdict, Verdict::Pass,
        "in-bounds nested field + array accesses prove — the padded offsets are correct");
}

/// A Linux user-copy with an unchecked, caller-controlled length overruns the kernel
/// buffer — `copy_from_user(buf64, ubuf, n)` with free `n`. It lowers to a refutable
/// bulk write, so the overflow is a FAIL with a witness; the length-checked sibling
/// (`n <= 64`) PASSes. `copy_to_user` reads its kernel buffer (arg 1) analogously.
#[test]
fn user_copy_unchecked_length_overflows_the_kernel_buffer() {
    let oob = r#"
define i64 @f(ptr %ubuf, i64 %n) {
entry:
  %buf = alloca [64 x i8], align 16
  %r = call i64 @copy_from_user(ptr %buf, ptr %ubuf, i64 %n)
  %v = load i8, ptr %buf, align 1
  %w = sext i8 %v to i64
  ret i64 %w
}
declare i64 @copy_from_user(ptr, ptr, i64)
"#;
    let m = LlvmFrontend.lower(LlvmInput { source: oob.into(), name: "u".into() }).expect("lower");
    assert_eq!(verify_module(&m, &Config::default()).verdict, Verdict::Fail,
        "an unchecked user-controlled copy_from_user length overruns the kernel buffer");

    let safe = r#"
define i64 @f(ptr %ubuf, i64 %n) {
entry:
  %buf = alloca [64 x i8], align 16
  %ok = icmp ule i64 %n, 64
  br i1 %ok, label %do, label %skip
do:
  %r = call i64 @copy_from_user(ptr %buf, ptr %ubuf, i64 %n)
  %v = load i8, ptr %buf, align 1
  %w = sext i8 %v to i64
  ret i64 %w
skip:
  ret i64 -22
}
declare i64 @copy_from_user(ptr, ptr, i64)
"#;
    let m = LlvmFrontend.lower(LlvmInput { source: safe.into(), name: "s".into() }).expect("lower");
    assert_ne!(verify_module(&m, &Config::default()).verdict, Verdict::Fail,
        "a length-checked user-copy must not be a false positive");
}

/// The archetypal kernel bug: copy a struct from userspace, then use one of its
/// fields as the length of a second copy into a fixed buffer. The field is untrusted
/// (user-controlled) — a genuine adversarial input — so an unchecked length overruns
/// the buffer (FAIL), while a length-checked sibling stays PASS (no false positive).
/// Exercises user-taint propagation (`UserFill` region) + `zext` width handling (the
/// `i32` field widens to the `i64` length).
#[test]
fn user_copy_field_used_as_length_is_an_overflow() {
    let vuln = r#"
%struct.req = type { i32, i32 }
define i64 @f(ptr %uarg) {
entry:
  %r = alloca %struct.req, align 4
  %buf = alloca [128 x i8], align 16
  %e0 = call i64 @copy_from_user(ptr %r, ptr %uarg, i64 8)
  %len32 = load i32, ptr %r, align 4
  %len = zext i32 %len32 to i64
  %e1 = call i64 @copy_from_user(ptr %buf, ptr %uarg, i64 %len)
  %v = load i8, ptr %buf, align 1
  %w = sext i8 %v to i64
  ret i64 %w
}
declare i64 @copy_from_user(ptr, ptr, i64)
"#;
    let m = LlvmFrontend.lower(LlvmInput { source: vuln.into(), name: "v".into() }).expect("lower");
    assert_eq!(verify_module(&m, &Config { bug_finding: true, ..Config::default() }).verdict, Verdict::Fail,
        "a user-copied length field driving a second copy overruns the buffer");

    let safe = r#"
%struct.req = type { i32, i32 }
define i64 @f(ptr %uarg) {
entry:
  %r = alloca %struct.req, align 4
  %buf = alloca [128 x i8], align 16
  %e0 = call i64 @copy_from_user(ptr %r, ptr %uarg, i64 8)
  %len32 = load i32, ptr %r, align 4
  %len = zext i32 %len32 to i64
  %ok = icmp ule i64 %len, 128
  br i1 %ok, label %do, label %skip
do:
  %e1 = call i64 @copy_from_user(ptr %buf, ptr %uarg, i64 %len)
  %v = load i8, ptr %buf, align 1
  %w = sext i8 %v to i64
  ret i64 %w
skip:
  ret i64 -22
}
declare i64 @copy_from_user(ptr, ptr, i64)
"#;
    let m = LlvmFrontend.lower(LlvmInput { source: safe.into(), name: "s".into() }).expect("lower");
    assert_ne!(verify_module(&m, &Config { bug_finding: true, ..Config::default() }).verdict, Verdict::Fail,
        "a length-checked user field must not be a false positive (the guard on the widened value holds)");
}

/// Inline assembly must not drop the whole function (kernel C is saturated with it).
/// It lowers to an opaque, memory-clobbering call: the function stays analyzed, an
/// OOB past the asm is still found (bug-finding), and a pointer reloaded across an
/// asm memory clobber loses provenance (no false PASS).
#[test]
fn inline_asm_is_an_opaque_havoc_not_a_dropped_function() {
    // OOB store past an 8-elem local, with an intervening inline asm.
    let oob = r#"
define i64 @f(i64 %i) {
entry:
  %a = alloca [8 x i64], align 16
  %junk = call i64 asm sideeffect "nop", "=r,~{memory}"()
  %p = getelementptr [8 x i64], ptr %a, i64 0, i64 %i
  store i64 %junk, ptr %p, align 8
  %v = load i64, ptr %a, align 8
  ret i64 %v
}
"#;
    let m = LlvmFrontend.lower(LlvmInput { source: oob.into(), name: "a".into() }).expect("lower");
    assert!(m.unanalyzed.is_empty(), "inline asm must not drop the function: {:?}", m.unanalyzed);
    let bugs = Config { bug_finding: true, ..Config::default() };
    assert_eq!(verify_module(&m, &bugs).verdict, Verdict::Fail,
        "an OOB store past inline asm is found in bug-finding mode");

    // Soundness: a pointer stored, then reloaded across an asm *memory* clobber, has
    // lost provenance — its deref must NOT be a false PASS.
    let clob = r#"
define i64 @f(ptr %p) {
entry:
  %slot = alloca ptr, align 8
  store ptr %p, ptr %slot, align 8
  %junk = call i64 asm sideeffect "nop", "=r,~{memory}"()
  %q = load ptr, ptr %slot, align 8
  %v = load i64, ptr %q, align 8
  ret i64 %v
}
"#;
    let m = LlvmFrontend.lower(LlvmInput { source: clob.into(), name: "c".into() }).expect("lower");
    assert_ne!(verify_module(&m, &bugs).verdict, Verdict::Pass,
        "a pointer reloaded across an asm memory clobber must not verify");
}

/// Bug-finding mode: an OOB whose index is a genuine parameter, reached *after* an
/// init loop that makes the path inexact, is refuted (FAIL + witness) only under
/// `bug_finding` — strict verification stays UNKNOWN (the exact-path gate). The
/// safe, guarded sibling must NOT become a false positive under `bug_finding`.
#[test]
fn bug_finding_refutes_oob_past_an_init_loop() {
    // `p = malloc(64); for(k<8) p[k]=k; return p[i];` — OOB when i >= 8, i genuine.
    let oob = r#"
define i64 @f(i64 %i) {
entry:
  %p = call ptr @malloc(i64 64)
  br label %head
head:
  %k = phi i64 [ 0, %entry ], [ %kn, %body ]
  %done = icmp uge i64 %k, 8
  br i1 %done, label %after, label %body
body:
  %pk = getelementptr i64, ptr %p, i64 %k
  store i64 %k, ptr %pk, align 8
  %kn = add i64 %k, 1
  br label %head
after:
  %q = getelementptr i64, ptr %p, i64 %i
  %v = load i64, ptr %q, align 8
  ret i64 %v
}
declare ptr @malloc(i64)
"#;
    let m = LlvmFrontend.lower(LlvmInput { source: oob.into(), name: "b".into() }).expect("lower");
    // Strict: the init loop makes the path inexact, so refutation is off → UNKNOWN.
    assert_ne!(verify_module(&m, &Config::default()).verdict, Verdict::Fail,
        "strict mode does not refute past an inexact (loop) path");
    // Bug-finding: the OOB index is a genuine parameter, so the witness is reachable.
    let bugs = Config { bug_finding: true, ..Config::default() };
    assert_eq!(verify_module(&m, &bugs).verdict, Verdict::Fail,
        "bug-finding refutes an OOB reached by a genuine input past an init loop");

    // The safe, guarded sibling: `if (i < 8) p[i]` — must NOT be a false positive.
    let safe = r#"
define i64 @f(i64 %i) {
entry:
  %p = call ptr @malloc(i64 64)
  br label %head
head:
  %k = phi i64 [ 0, %entry ], [ %kn, %body ]
  %done = icmp uge i64 %k, 8
  br i1 %done, label %after, label %body
body:
  %pk = getelementptr i64, ptr %p, i64 %k
  store i64 %k, ptr %pk, align 8
  %kn = add i64 %k, 1
  br label %head
after:
  %ok = icmp ult i64 %i, 8
  br i1 %ok, label %in, label %out
in:
  %q = getelementptr i64, ptr %p, i64 %i
  %v = load i64, ptr %q, align 8
  ret i64 %v
out:
  ret i64 -1
}
declare ptr @malloc(i64)
"#;
    let m = LlvmFrontend.lower(LlvmInput { source: safe.into(), name: "s".into() }).expect("lower");
    assert_ne!(verify_module(&m, &bugs).verdict, Verdict::Fail,
        "a guarded index must not be a false positive even in bug-finding mode");
}

/// Soundness control: a *zeroing* allocator (`kzalloc`/`calloc`) returns initialized
/// memory, so it is deliberately NOT modeled as a plain `Alloc` (that region reads as
/// uninitialized). Reading a freshly-`kzalloc`'d buffer must therefore NOT be a false
/// "uninitialized read" FAIL — it stays a sound non-FAIL.
#[test]
fn zeroing_allocator_is_not_a_false_uninit_fail() {
    let src = r#"
define i64 @f() {
entry:
  %p = call ptr @kzalloc(i64 64, i64 0)
  %v = load i64, ptr %p, align 8
  ret i64 %v
}
declare ptr @kzalloc(i64, i64)
"#;
    let m = LlvmFrontend.lower(LlvmInput { source: src.into(), name: "z".into() }).expect("lower");
    assert_ne!(verify_module(&m, &Config::default()).verdict, Verdict::Fail,
        "reading zero-initialized kzalloc memory must not be a false uninit FAIL");
}

/// End-to-end proof that *multi-block* return summaries reach verdicts: `@at`
/// has rustc's guard shape (a checking call, a diverging panic block, then
/// `ret gep(p, i)`), and `@caller` stores through its result. Only if the
/// summary rebuilds the returned pointer with the alloca's provenance can the
/// store's bounds be proven — before, any multi-block callee returned an opaque
/// pointer and this was UNKNOWN.
#[test]
fn llvm_multi_block_pointer_helper_is_transparent() {
    let src = r#"
define internal ptr @at(ptr %p, i64 %i) {
start:
  %c = call i1 @check(i64 %i)
  br i1 %c, label %ok, label %bad
bad:
  call void @panic()
  unreachable
ok:
  %q = getelementptr inbounds i32, ptr %p, i64 %i
  ret ptr %q
}

define void @caller() {
start:
  %buf = alloca [8 x i32], align 4
  %q = call ptr @at(ptr %buf, i64 2)
  store i32 7, ptr %q, align 4
  ret void
}
"#;
    let module = LlvmFrontend
        .lower(LlvmInput { source: src.into(), name: "m".into() })
        .expect("frontend lowers the .ll");
    let report = verify_module(&module, &Config::default());
    let caller = report
        .functions
        .iter()
        .find(|f| f.function == "caller")
        .expect("caller verified");
    assert_eq!(
        caller.verdict,
        Verdict::Pass,
        "the store through the helper's return must prove via the summary: {caller:?}"
    );
}

/// Interprocedural contract synthesis: `@init` is `define internal`, its
/// address is never taken, and both call sites pass constant-size allocas
/// (32 B and 16 B). The synthesized contract is the *weakest* guarantee —
/// 16 bytes — so `@init`'s store at offset 8 proves PASS, and the proof
/// surfaces the dedicated `internal-call-contract` assumption.
#[test]
fn llvm_internal_callee_gets_a_call_site_contract() {
    let src = r#"
define internal void @init(ptr %p) {
start:
  %q = getelementptr inbounds i8, ptr %p, i64 8
  store i32 7, ptr %q, align 4
  ret void
}

define void @a() {
start:
  %buf = alloca [32 x i8], align 8
  call void @init(ptr %buf)
  ret void
}

define void @b() {
start:
  %buf = alloca [16 x i8], align 8
  call void @init(ptr %buf)
  ret void
}
"#;
    let module = LlvmFrontend
        .lower(LlvmInput { source: src.into(), name: "m".into() })
        .expect("frontend lowers the .ll");
    let report = verify_module(&module, &Config::default());
    let callee = report.functions.iter().find(|f| f.function == "init").expect("init");
    assert_eq!(callee.verdict, Verdict::Pass, "store within the weakest call-site contract: {callee:?}");
    assert!(
        report.assumptions.iter().any(|a| a.id == "internal-call-contract"),
        "the synthesized contract names its own trust basis"
    );
}

/// The four ways synthesis must refuse, each a soundness condition:
/// an *exported* callee (external callers unknown), an internal callee whose
/// *address is taken* (indirect calls unknown), a call site whose argument is
/// *not statically derivable*, and — the weakest-contract check — an access
/// beyond the *minimum* of the site guarantees must stay unproven.
#[test]
fn llvm_contract_synthesis_refuses_unsound_cases() {
    let verdict_of = |src: &str, fname: &str| {
        let module = LlvmFrontend
            .lower(LlvmInput { source: src.into(), name: "m".into() })
            .expect("lower");
        let report = verify_module(&module, &Config::default());
        report.functions.iter().find(|f| f.function == fname).expect(fname).verdict
    };

    // Exported: not internal — external callers could pass anything.
    let exported = r#"
define void @init(ptr %p) {
start:
  store i32 7, ptr %p, align 4
  ret void
}
define void @a() {
start:
  %buf = alloca [16 x i8], align 8
  call void @init(ptr %buf)
  ret void
}
"#;
    assert_ne!(verdict_of(exported, "init"), Verdict::Pass, "exported callee must not inherit");

    // Address taken: `@init` escapes as a value — unseen indirect call sites.
    let escaped = r#"
define internal void @init(ptr %p) {
start:
  store i32 7, ptr %p, align 4
  ret void
}
define void @a() {
start:
  %buf = alloca [16 x i8], align 8
  call void @init(ptr %buf)
  call void @register(ptr @init)
  ret void
}
"#;
    assert_ne!(verdict_of(escaped, "init"), Verdict::Pass, "address-taken callee must not inherit");

    // Underivable site: one caller passes a *loaded* pointer.
    let underivable = r#"
define internal void @init(ptr %p) {
start:
  store i32 7, ptr %p, align 4
  ret void
}
define void @a() {
start:
  %buf = alloca [16 x i8], align 8
  call void @init(ptr %buf)
  ret void
}
define void @b(ptr %h) {
start:
  %p = load ptr, ptr %h, align 8
  call void @init(ptr %p)
  ret void
}
"#;
    assert_ne!(verdict_of(underivable, "init"), Verdict::Pass, "one underivable site poisons");

    // Weakest contract: sites pass 32 B and 8 B; the access at offset 8..12
    // exceeds the 8-byte minimum and must stay unproven.
    let min_fold = r#"
define internal void @init(ptr %p) {
start:
  %q = getelementptr inbounds i8, ptr %p, i64 8
  store i32 7, ptr %q, align 4
  ret void
}
define void @a() {
start:
  %buf = alloca [32 x i8], align 8
  call void @init(ptr %buf)
  ret void
}
define void @b() {
start:
  %buf = alloca [8 x i8], align 8
  call void @init(ptr %buf)
  ret void
}
"#;
    assert_ne!(verdict_of(min_fold, "init"), Verdict::Pass, "access beyond the minimum site size");
}

/// Fixpoint grounding: `@outer`'s contract is synthesized from `@main`'s alloca
/// (round 1); `@inner`'s only site forwards `@outer`'s parameter, so it needs
/// round 2 — derivable only through the *earlier-round* contract. The chain is
/// inductively grounded in a real allocation; no contract justifies itself.
#[test]
fn llvm_contract_synthesis_reaches_a_fixpoint_through_chains() {
    let src = r#"
define internal void @inner(ptr %p) {
start:
  %q = getelementptr inbounds i8, ptr %p, i64 8
  store i32 7, ptr %q, align 4
  ret void
}

define internal void @outer(ptr %p) {
start:
  call void @inner(ptr %p)
  ret void
}

define void @main() {
start:
  %buf = alloca [16 x i8], align 8
  call void @outer(ptr %buf)
  ret void
}
"#;
    let module = LlvmFrontend
        .lower(LlvmInput { source: src.into(), name: "m".into() })
        .expect("lower");
    let report = verify_module(&module, &Config::default());
    let inner = report.functions.iter().find(|f| f.function == "inner").expect("inner");
    assert_eq!(inner.verdict, Verdict::Pass, "round-2 chain must ground: {inner:?}");
}

/// Global/static memory modelling: a `@table = constant [8 x i32]` is a live,
/// initialized, readable region of its declared size. A guarded in-bounds read
/// proves PASS (surfacing the `global-memory` assumption); the folded
/// `getelementptr (i8, ptr @g, i64 16)` constant keeps its base and offset and
/// is checked against the same region.
#[test]
fn llvm_global_reads_prove_against_the_declared_size() {
    let src = r#"
@table = internal unnamed_addr constant [8 x i32] zeroinitializer, align 4
@pair = private unnamed_addr constant <{ [16 x i8], [16 x i8] }> zeroinitializer, align 16

define i32 @first() {
start:
  %v = load i32, ptr @table, align 4
  ret i32 %v
}

define i128 @second_half() {
start:
  %v = load i128, ptr getelementptr inbounds (i8, ptr @pair, i64 16), align 16
  ret i128 %v
}
"#;
    let module = LlvmFrontend
        .lower(LlvmInput { source: src.into(), name: "m".into() })
        .expect("lower");
    let report = verify_module(&module, &Config::default());
    assert_eq!(report.verdict, Verdict::Pass, "both global reads prove: {report:?}");
    assert!(
        report.assumptions.iter().any(|a| a.id == "global-memory"),
        "proofs name the global-memory trust basis"
    );
}

/// The soundness side of global modelling: an access *beyond* the declared
/// size must not prove (the region is exactly as big as declared), and a store
/// to a `constant` definition must not prove (no write permission).
#[test]
fn llvm_global_modelling_refuses_oob_and_constant_writes() {
    let verdict_of = |src: &str| {
        let module = LlvmFrontend
            .lower(LlvmInput { source: src.into(), name: "m".into() })
            .expect("lower");
        verify_module(&module, &Config::default()).verdict
    };

    let oob = r#"
@small = internal constant [4 x i8] zeroinitializer, align 1

define i32 @past_end() {
start:
  %v = load i32, ptr getelementptr inbounds (i8, ptr @small, i64 2), align 1
  ret i32 %v
}
"#;
    assert_ne!(verdict_of(oob), Verdict::Pass, "2..6 of a 4-byte global is OOB");

    let write_const = r#"
@ro = internal constant [4 x i8] zeroinitializer, align 4

define void @clobber() {
start:
  store i32 7, ptr @ro, align 4
  ret void
}
"#;
    assert_ne!(verdict_of(write_const), Verdict::Pass, "a constant is not writable");

    // A *mutable* global (`global`, not `constant`) accepts the same store.
    let write_mut = r#"
@rw = internal global [4 x i8] zeroinitializer, align 4

define void @set() {
start:
  store i32 7, ptr @rw, align 4
  ret void
}
"#;
    assert_eq!(verdict_of(write_mut), Verdict::Pass, "a mutable global is writable");
}

/// Optimized-IR constructs, in one fixture: `icmp samesign`, `freeze`,
/// `insertelement`, a `metadata` call argument, and a hyphenated block label
/// (`bb9thread-pre-split.i`, from jump threading) — each previously dropped the
/// whole function.
#[test]
fn llvm_optimized_ir_constructs_parse() {
    let src = r#"
define i64 @f(i64 %x, ptr %p) {
start:
  %c = icmp samesign ult i64 %x, 8
  %fz = freeze i64 %x
  %v = insertelement <2 x i64> poison, i64 %fz, i64 0
  call void @llvm.experimental.noalias.scope.decl(metadata !3)
  br i1 %c, label %bb9thread-pre-split.i, label %done
bb9thread-pre-split.i:
  ret i64 %fz
done:
  ret i64 0
}
"#;
    let module = LlvmFrontend
        .lower(LlvmInput { source: src.into(), name: "m".into() })
        .expect("lower");
    assert!(module.unanalyzed.is_empty(), "all constructs parse: {:?}", module.unanalyzed);
}

/// A `switch`'s *default* edge carries `value != k` for every case. Without it
/// a refutation on the default path could pick a case value — an infeasible
/// witness, seen as a false FAIL on rustc's jump-threaded slice-length
/// switches: `switch len [0 → ret, 1 → ret]; default: load slice[1]` is
/// reachable only with `len >= 2`, so the load must NOT be refuted. The
/// positive control: the same load *without* the switch guard stays refutable
/// through the case edge that reaches it.
#[test]
fn llvm_switch_default_edge_constrains_the_scrutinee() {
    let guarded = r#"
define i8 @get(ptr align 1 %s, i64 %len) {
start:
  %c = icmp ult i64 1, %len
  switch i64 %len, label %big [
    i64 0, label %empty
    i64 1, label %empty
  ]
big:
  %p = getelementptr inbounds i8, ptr %s, i64 1
  %v = load i8, ptr %p, align 1
  ret i8 %v
empty:
  ret i8 0
}
"#;
    let module = LlvmFrontend
        .lower(LlvmInput { source: guarded.into(), name: "m".into() })
        .expect("lower");
    let report = verify_module(&module, &Config::default());
    let f = &report.functions[0];
    assert!(
        f.outcomes.iter().all(|o| o.verdict() != Verdict::Fail),
        "the default edge implies len >= 2 — no obligation may be refuted: {f:?}"
    );
}

/// A struct-field gep (`gep {S}, ptr, i64 %i, i32 K`) strides by `sizeof(S)`
/// and lands on the *exact padded field offset*. `{ i32, i64 }` pads field 1
/// to offset 8 (size 16): with `%i < 2` over a 32-byte table the access
/// proves; without the guard it must not (the offset arithmetic is real).
#[test]
fn llvm_struct_field_gep_uses_the_padded_offset() {
    let make = |guarded: bool| {
        let guard = if guarded {
            "  %c = icmp ult i64 %i, 2\n  br i1 %c, label %ok, label %out\nok:\n"
        } else {
            "  br label %ok\nok:\n"
        };
        format!(
            r#"
@table = internal constant [2 x {{ i32, i64 }}] zeroinitializer, align 8

define i64 @snd(i64 %i) {{
start:
{guard}  %p = getelementptr inbounds {{ i32, i64 }}, ptr @table, i64 %i, i32 1
  %v = load i64, ptr %p, align 8
  ret i64 %v
out:
  ret i64 0
}}
"#
        )
    };
    let verdict = |src: String| {
        let module = LlvmFrontend
            .lower(LlvmInput { source: src, name: "m".into() })
            .expect("lower");
        verify_module(&module, &Config::default()).verdict
    };
    assert_eq!(verdict(make(true)), Verdict::Pass, "guarded field access proves");
    assert_ne!(verdict(make(false)), Verdict::Pass, "unguarded index must not prove");
}

/// `atomicrmw`/`cmpxchg` are read-modify-writes: both accesses carry their
/// full memory obligations (an opaque placeholder would silently drop them —
/// an unchecked OOB atomicrmw would be a false PASS one level up). A guarded
/// in-bounds RMW on an alloca proves; a definitely-OOB one FAILs.
#[test]
fn llvm_atomic_rmw_keeps_obligations_both_directions() {
    let verdict_of = |src: &str| {
        let module = LlvmFrontend
            .lower(LlvmInput { source: src.into(), name: "m".into() })
            .expect("lower");
        verify_module(&module, &Config::default()).verdict
    };

    let ok = r#"
define i64 @bump(i64 %v) {
start:
  %cell = alloca [8 x i8], align 8
  store i64 0, ptr %cell, align 8
  %old = atomicrmw add ptr %cell, i64 %v monotonic, align 8
  %pair = cmpxchg ptr %cell, i64 0, i64 1 acquire acquire, align 8
  ret i64 %old
}
"#;
    assert_eq!(verdict_of(ok), Verdict::Pass, "in-bounds RMWs on a live alloca prove");

    let oob = r#"
define void @past(i32 %v) {
start:
  %cell = alloca [4 x i8], align 4
  %p = getelementptr inbounds i8, ptr %cell, i64 2
  %old = atomicrmw add ptr %p, i32 %v monotonic, align 4
  ret void
}
"#;
    assert_eq!(verdict_of(oob), Verdict::Fail, "an OOB atomicrmw (2..6 of 4) must FAIL");
}

/// DWARF debug-info recovery: LLVM's opaque `ptr` erases the pointee type, but
/// `-g` metadata (`!DIDerivedType(DW_TAG_pointer_type, name: "&mut T", …)`)
/// records it. A reference parameter with no `dereferenceable` attribute is
/// recovered as a live region of the pointee's size — so accesses through it
/// prove, resting on the `debuginfo` assumption. This is the cross-language
/// lever (rustc/clang/swiftc all emit `!DI…`). A raw pointer is NOT recovered.
#[test]
fn llvm_debuginfo_recovers_reference_pointee_size() {
    let with_di = r#"
define i64 @read_self(ptr align 8 %self) !dbg !7 {
start:
  %f = getelementptr inbounds i8, ptr %self, i64 8
  %v = load i64, ptr %f, align 8
  ret i64 %v
}
!5 = distinct !DICompileUnit(language: DW_LANG_Rust, file: !6)
!7 = distinct !DISubprogram(name: "read_self", spFlags: DISPFlagLocalToUnit | DISPFlagDefinition)
!42 = !DILocalVariable(name: "self", arg: 1, scope: !7, type: !39)
!39 = !DIDerivedType(tag: DW_TAG_pointer_type, name: "&mut Rand32", baseType: !9, size: 64)
!9 = !DICompositeType(tag: DW_TAG_structure_type, name: "Rand32", size: 128)
"#;
    let module = LlvmFrontend
        .lower(LlvmInput { source: with_di.into(), name: "m".into() })
        .expect("lower");
    let report = verify_module(&module, &Config::default());
    assert_eq!(report.verdict, Verdict::Pass, "the field read proves via DWARF: {report:?}");
    assert!(
        report.assumptions.iter().any(|a| a.id == "debuginfo"),
        "the proof discloses its debug-info trust basis"
    );

    // The soundness control: the same IR *without* the debug metadata leaves the
    // pointer uncontracted, so the access cannot be proved (UNKNOWN, not PASS).
    let without_di = with_di.lines().take_while(|l| !l.starts_with("!")).collect::<Vec<_>>().join("\n");
    let module = LlvmFrontend
        .lower(LlvmInput { source: without_di, name: "m".into() })
        .expect("lower");
    assert_ne!(
        verify_module(&module, &Config::default()).verdict,
        Verdict::Pass,
        "without debug info the pointee size is unknown — must not prove"
    );
}

/// DWARF struct-member recovery: a `load ptr` reading a *reference field* of a
/// debug-typed struct (`load ptr, gep(&mut Wrap, offset)` where the member at
/// that offset is a `&u8`) yields a valid reference, so a read through it
/// proves. LLVM's opaque `ptr` erased the field type; the `!DI…` members recover
/// it. This is the pattern that dominates reference-heavy code — C structs with
/// pointer members, C++ classes with `T&`/`T*` fields, Rust structs holding
/// borrows. A raw-pointer field is NOT recovered (validity not guaranteed).
#[test]
fn llvm_debuginfo_recovers_reference_struct_member() {
    let src = r#"
define i8 @read_field(ptr align 8 %self) !dbg !7 {
start:
  %f = getelementptr inbounds i8, ptr %self, i64 8
  %inner = load ptr, ptr %f, align 8
  %v = load i8, ptr %inner, align 1
  ret i8 %v
}
!5 = distinct !DICompileUnit(language: DW_LANG_Rust, file: !6)
!7 = distinct !DISubprogram(name: "read_field", spFlags: DISPFlagDefinition)
!42 = !DILocalVariable(name: "self", arg: 1, scope: !7, type: !39)
!39 = !DIDerivedType(tag: DW_TAG_pointer_type, name: "&mut Wrap", baseType: !9, size: 64)
!9 = !DICompositeType(tag: DW_TAG_structure_type, name: "Wrap", size: 128, elements: !12)
!12 = !{!13, !15}
!13 = !DIDerivedType(tag: DW_TAG_member, name: "tag", baseType: !14, size: 64, offset: 0)
!14 = !DIBasicType(name: "u64", size: 64)
!15 = !DIDerivedType(tag: DW_TAG_member, name: "inner", baseType: !16, size: 64, offset: 64)
!16 = !DIDerivedType(tag: DW_TAG_pointer_type, name: "&u8", baseType: !17, size: 64)
!17 = !DIBasicType(name: "u8", size: 8)
"#;
    let module = LlvmFrontend
        .lower(LlvmInput { source: src.into(), name: "m".into() })
        .expect("lower");
    let report = verify_module(&module, &Config::default());
    assert_eq!(report.verdict, Verdict::Pass, "read through the recovered field ref proves: {report:?}");

    // Reading a raw-pointer field must not be recovered (a `*const u8` member):
    // the deref through it stays unproven.
    let raw = src.replace(r#"name: "&u8""#, r#"name: "*const u8""#);
    let module = LlvmFrontend
        .lower(LlvmInput { source: raw, name: "m".into() })
        .expect("lower");
    assert_ne!(
        verify_module(&module, &Config::default()).verdict,
        Verdict::Pass,
        "a raw-pointer field grants no validity — the deref must not prove"
    );
}

/// Cross-language DWARF recovery on clang-format metadata: a C++ reference
/// parameter (`Point&`, a `DW_TAG_reference_type`) — with clang's `distinct`
/// node prefix — is recovered as a valid region, so field reads prove. Validated
/// against real clang++ output in `tests/dwarf-corpus`; this pins the format.
#[test]
fn llvm_debuginfo_recovers_cpp_reference_clang_format() {
    let src = r#"
define i64 @sum_ref(ptr align 8 %0) !dbg !7 {
start:
  %a = load i64, ptr %0, align 8
  %p = getelementptr inbounds i8, ptr %0, i64 8
  %b = load i64, ptr %p, align 8
  %s = add i64 %a, %b
  ret i64 %s
}
!7 = distinct !DISubprogram(name: "sum_ref", spFlags: DISPFlagDefinition)
!117 = !DILocalVariable(name: "p", arg: 1, scope: !7, type: !107)
!107 = !DIDerivedType(tag: DW_TAG_reference_type, baseType: !108, size: 64)
!108 = distinct !DICompositeType(tag: DW_TAG_structure_type, name: "Point", size: 128, align: 64, elements: !109)
!109 = !{}
"#;
    let module = LlvmFrontend
        .lower(LlvmInput { source: src.into(), name: "m".into() })
        .expect("lower");
    let report = verify_module(&module, &Config::default());
    assert_eq!(report.verdict, Verdict::Pass, "C++ reference param recovered: {report:?}");
    assert!(report.assumptions.iter().any(|a| a.id == "debuginfo"));
}

/// Language-aware soundness: a `*const T` pointer named `&`-style would be a
/// Rust reference, but under a *non-Rust* compile unit (C/D/Zig emit
/// `DW_TAG_pointer_type` for raw pointers) it must NOT be recovered — those
/// pointers can dangle. Only `DW_TAG_reference_type` (C++ `T&`, D `ref`) is
/// recovered without a Rust language tag. Guards against a cross-language
/// false PASS.
#[test]
fn llvm_debuginfo_non_rust_raw_pointer_not_recovered() {
    // A `DW_TAG_pointer_type` under a C compile unit — a raw pointer, even though
    // (hypothetically) `&`-named — must not be contracted.
    let c_like = r#"
define i64 @f(ptr align 8 %0) !dbg !7 {
start:
  %v = load i64, ptr %0, align 8
  ret i64 %v
}
!5 = distinct !DICompileUnit(language: DW_LANG_C11, file: !6)
!42 = !DILocalVariable(name: "p", arg: 1, scope: !7, type: !39)
!7 = distinct !DISubprogram(name: "f")
!39 = !DIDerivedType(tag: DW_TAG_pointer_type, name: "&whatever", baseType: !9, size: 64)
!9 = !DICompositeType(tag: DW_TAG_structure_type, name: "S", size: 128)
"#;
    let module = LlvmFrontend
        .lower(LlvmInput { source: c_like.into(), name: "m".into() })
        .expect("lower");
    assert_ne!(
        verify_module(&module, &Config::default()).verdict,
        Verdict::Pass,
        "a raw pointer under a non-Rust language must not be recovered"
    );

    // The same node under a Rust compile unit IS a reference → recovered.
    let rust = c_like.replace("DW_LANG_C11", "DW_LANG_Rust");
    let module = LlvmFrontend
        .lower(LlvmInput { source: rust, name: "m".into() })
        .expect("lower");
    assert_eq!(
        verify_module(&module, &Config::default()).verdict,
        Verdict::Pass,
        "the same `&`-named pointer under Rust is a reference → recovered"
    );
}

/// Closed-world contract synthesis: an **exported** (non-internal) function whose
/// pointer parameter is uncontracted is UNKNOWN by default (its callers might be
/// anywhere), but under `closed_world` the module's call sites are taken to be
/// all of them — here the sole caller passes a live 16-byte alloca, so the two
/// i64 loads become provable.
const CLOSED_WORLD: &str = r#"
define i64 @sum_pair(ptr %p) {
entry:
  %a = load i64, ptr %p, align 8
  %q = getelementptr inbounds i8, ptr %p, i64 8
  %b = load i64, ptr %q, align 8
  %s = add i64 %a, %b
  ret i64 %s
}
define i64 @main() {
entry:
  %buf = alloca [2 x i64], align 8
  %r = call i64 @sum_pair(ptr %buf)
  ret i64 %r
}
"#;

#[test]
fn closed_world_synthesizes_exported_contract() {
    let module = LlvmFrontend
        .lower(LlvmInput { source: CLOSED_WORLD.into(), name: "cw".into() })
        .expect("lower");

    // Default (open world): the exported callee's `%p` is uncontracted → UNKNOWN.
    assert_ne!(
        verify_module(&module, &Config::default()).verdict,
        Verdict::Pass,
        "an exported function's raw pointer parameter must not be recovered without closed-world"
    );

    // Closed-world: synthesized from the 16-byte-alloca call site → PASS.
    let cfg = Config { closed_world: true, ..Config::default() };
    assert_eq!(
        verify_module(&module, &cfg).verdict,
        Verdict::Pass,
        "closed-world recovers the exported parameter from its sole (16-byte) call site"
    );
}

/// Soundness control for closed-world: the synthesized contract is the *weakest*
/// guarantee across call sites. With one caller passing 16 bytes and another only
/// 8, the offset-8 load must stay unprovable — no false PASS.
const CLOSED_WORLD_WEAKEST: &str = r#"
define i64 @sum_pair(ptr %p) {
entry:
  %a = load i64, ptr %p, align 8
  %q = getelementptr inbounds i8, ptr %p, i64 8
  %b = load i64, ptr %q, align 8
  %s = add i64 %a, %b
  ret i64 %s
}
define i64 @big() {
entry:
  %buf = alloca [2 x i64], align 8
  %r = call i64 @sum_pair(ptr %buf)
  ret i64 %r
}
define i64 @small() {
entry:
  %one = alloca i64, align 8
  %r = call i64 @sum_pair(ptr %one)
  ret i64 %r
}
"#;

#[test]
fn closed_world_takes_weakest_call_site_guarantee() {
    let module = LlvmFrontend
        .lower(LlvmInput { source: CLOSED_WORLD_WEAKEST.into(), name: "cww".into() })
        .expect("lower");
    // Even under closed-world, one 8-byte caller caps the contract at 8 bytes,
    // so reading at offset 8 cannot be proven — must NOT be a false PASS.
    let cfg = Config { closed_world: true, ..Config::default() };
    assert_ne!(
        verify_module(&module, &cfg).verdict,
        Verdict::Pass,
        "the weakest (8-byte) guarantee must leave the offset-8 read unprovable"
    );
}

/// Member-provenance: a raw pointer **member** is dereferenced in the callee but
/// carries no validity from its type. Under closed-world the caller provably
/// stores `&x` into that field (byte offset 8) before the call, so the callee's
/// load of the field yields a valid pointer and the deref proves. `main` builds a
/// `{ i64, ptr }` on the stack, writes `&x` into the pointer field, and calls.
const MEMBER_PROV: &str = r#"
define i32 @read_member(ptr %w) {
entry:
  %f = getelementptr inbounds i8, ptr %w, i64 8
  %data = load ptr, ptr %f, align 8
  %v = load i32, ptr %data, align 4
  ret i32 %v
}
define i32 @main() {
entry:
  %x = alloca i32, align 4
  %w = alloca [16 x i8], align 8
  store i32 7, ptr %x, align 4
  %f = getelementptr inbounds i8, ptr %w, i64 8
  store ptr %x, ptr %f, align 8
  %r = call i32 @read_member(ptr %w)
  ret i32 %r
}
"#;

#[test]
fn closed_world_member_provenance_recovers_raw_pointer_member() {
    let module = LlvmFrontend
        .lower(LlvmInput { source: MEMBER_PROV.into(), name: "mp".into() })
        .expect("lower");

    // Without member-provenance (open world) the dereferenced field pointer has
    // no provenance → UNKNOWN.
    assert_ne!(
        verify_module(&module, &Config::default()).verdict,
        Verdict::Pass,
        "a raw pointer member deref must not be recovered without whole-program info"
    );
    // Closed-world: the field is provably filled with &x at the sole call site.
    let cfg = Config { closed_world: true, ..Config::default() };
    assert_eq!(
        verify_module(&module, &cfg).verdict,
        Verdict::Pass,
        "member-provenance recovers the field pointer stored by the caller"
    );
}

/// Soundness control: if a call site leaves the pointer field unwritten, the
/// callee's deref must stay unprovable even under closed-world — no false PASS.
const MEMBER_PROV_UNSET: &str = r#"
define i32 @read_member(ptr %w) {
entry:
  %f = getelementptr inbounds i8, ptr %w, i64 8
  %data = load ptr, ptr %f, align 8
  %v = load i32, ptr %data, align 4
  ret i32 %v
}
define i32 @main() {
entry:
  %w = alloca [16 x i8], align 8
  %r = call i32 @read_member(ptr %w)
  ret i32 %r
}
"#;

#[test]
fn closed_world_member_provenance_declines_unwritten_field() {
    let module = LlvmFrontend
        .lower(LlvmInput { source: MEMBER_PROV_UNSET.into(), name: "mpu".into() })
        .expect("lower");
    let cfg = Config { closed_world: true, ..Config::default() };
    assert_ne!(
        verify_module(&module, &cfg).verdict,
        Verdict::Pass,
        "an unwritten pointer field must leave the deref unprovable (no false PASS)"
    );
}

/// Member-provenance through a **struct-typed** field gep (`gep %S, ptr, 0, 0`),
/// the shape clang emits at -O0 for `s->q`. It lowers to a two-step PtrOffset
/// chain whose intermediate `local_defs` also treats as a region root; the field
/// slot must still be attributed to the aggregate the caller passes, not to that
/// intermediate. Here field 0 is the pointer, filled with `&x` before the call.
const MEMBER_PROV_STRUCT_GEP: &str = r#"
%struct.P = type { ptr }
define i64 @deref_field(ptr %s) {
entry:
  %f = getelementptr inbounds %struct.P, ptr %s, i32 0, i32 0
  %q = load ptr, ptr %f, align 8
  %v = load i64, ptr %q, align 8
  ret i64 %v
}
define i64 @use() {
entry:
  %x = alloca i64, align 8
  %p = alloca %struct.P, align 8
  store i64 7, ptr %x, align 8
  %f = getelementptr inbounds %struct.P, ptr %p, i32 0, i32 0
  store ptr %x, ptr %f, align 8
  %r = call i64 @deref_field(ptr %p)
  ret i64 %r
}
"#;

#[test]
fn closed_world_member_provenance_through_struct_gep() {
    let module = LlvmFrontend
        .lower(LlvmInput { source: MEMBER_PROV_STRUCT_GEP.into(), name: "mpsg".into() })
        .expect("lower");
    // Open world: the loaded field pointer has no provenance → UNKNOWN.
    assert_ne!(
        verify_module(&module, &Config::default()).verdict,
        Verdict::Pass,
        "a struct-field pointer deref must not be recovered without whole-program info"
    );
    // Closed-world: the field slot roots to the passed aggregate, so the caller's
    // `&x` store is credited and the deref proves.
    let cfg = Config { closed_world: true, ..Config::default() };
    assert_eq!(
        verify_module(&module, &cfg).verdict,
        Verdict::Pass,
        "the field guarantee must attach to the aggregate, not the struct-gep intermediate"
    );
}

/// Soundness control for member-provenance escape tracking: after the caller
/// fills the field, it passes the aggregate to an **external** function that
/// could rewrite the field, then calls the member reader with no re-store. The
/// field guarantee must be dropped — a raw external call is never silently
/// ignored (that would be a false PASS).
const MEMBER_PROV_ESCAPE: &str = r#"
declare void @clobber(ptr)
define i32 @read_member(ptr %w) {
entry:
  %f = getelementptr inbounds i8, ptr %w, i64 8
  %data = load ptr, ptr %f, align 8
  %v = load i32, ptr %data, align 4
  ret i32 %v
}
define i32 @main() {
entry:
  %x = alloca i32, align 4
  %w = alloca [16 x i8], align 8
  store i32 7, ptr %x, align 4
  %f = getelementptr inbounds i8, ptr %w, i64 8
  store ptr %x, ptr %f, align 8
  call void @clobber(ptr %w)
  %r = call i32 @read_member(ptr %w)
  ret i32 %r
}
"#;

#[test]
fn closed_world_member_provenance_respects_escape_via_external_call() {
    let module = LlvmFrontend
        .lower(LlvmInput { source: MEMBER_PROV_ESCAPE.into(), name: "mpe".into() })
        .expect("lower");
    let cfg = Config { closed_world: true, ..Config::default() };
    assert_ne!(
        verify_module(&module, &cfg).verdict,
        Verdict::Pass,
        "an external call that may rewrite the field must drop the guarantee (no false PASS)"
    );
}

/// Contract synthesis through a constant `getelementptr`: C passes an array
/// argument as `&a[0]` (a gep into the alloca), never the alloca itself. Under
/// closed-world the callee's parameter must still be contracted from that gep —
/// here `reads` (two i64 loads) is called with `&a[0]` of a `[2 x i64]`, so it
/// gets a 16-byte region and proves.
const GEP_ARG: &str = r#"
define i64 @reads(ptr %p) {
entry:
  %a = load i64, ptr %p, align 8
  %q = getelementptr i64, ptr %p, i64 1
  %b = load i64, ptr %q, align 8
  %s = add i64 %a, %b
  ret i64 %s
}
define i64 @main() {
entry:
  %arr = alloca [2 x i64], align 8
  %p0 = getelementptr i64, ptr %arr, i64 0
  %r = call i64 @reads(ptr %p0)
  ret i64 %r
}
"#;

#[test]
fn closed_world_synthesizes_through_constant_gep_arg() {
    let module = LlvmFrontend
        .lower(LlvmInput { source: GEP_ARG.into(), name: "gep".into() })
        .expect("lower");
    let cfg = Config { closed_world: true, ..Config::default() };
    assert_eq!(
        verify_module(&module, &cfg).verdict,
        Verdict::Pass,
        "an array argument passed as &a[0] must contract the parameter"
    );
}

/// Soundness control: a gep to `&a[1]` of a two-element array leaves only 8 bytes,
/// so a callee reading `p[1]` (offset 8) is out of bounds — the reduced-size
/// guarantee must keep it unprovable, never a false PASS.
const GEP_ARG_OOB: &str = r#"
define i64 @reads(ptr %p) {
entry:
  %a = load i64, ptr %p, align 8
  %q = getelementptr i64, ptr %p, i64 1
  %b = load i64, ptr %q, align 8
  %s = add i64 %a, %b
  ret i64 %s
}
define i64 @main() {
entry:
  %arr = alloca [2 x i64], align 8
  %p1 = getelementptr i64, ptr %arr, i64 1
  %r = call i64 @reads(ptr %p1)
  ret i64 %r
}
"#;

#[test]
fn closed_world_gep_arg_reduces_size_soundly() {
    let module = LlvmFrontend
        .lower(LlvmInput { source: GEP_ARG_OOB.into(), name: "gepoob".into() })
        .expect("lower");
    let cfg = Config { closed_world: true, ..Config::default() };
    assert_ne!(
        verify_module(&module, &cfg).verdict,
        Verdict::Pass,
        "&a[1] leaves 8 bytes; reading p[1] past it must not be a false PASS"
    );
}

/// mem2reg promotes spilled locals to SSA, so an `-O0`-style loop — pointer and
/// counter both spilled to allocas and reloaded each iteration — becomes
/// analyzable: the counter is an induction variable again, so `p[i]` (i in
/// [0,4), region 4×i64) proves in bounds under closed-world.
const SPILLED_LOOP: &str = r#"
define i64 @sum4(ptr %p) {
entry:
  %pa = alloca ptr, align 8
  %sa = alloca i64, align 8
  %ia = alloca i64, align 8
  store ptr %p, ptr %pa, align 8
  store i64 0, ptr %sa, align 8
  store i64 0, ptr %ia, align 8
  br label %head
head:
  %i = load i64, ptr %ia, align 8
  %c = icmp slt i64 %i, 4
  br i1 %c, label %body, label %exit
body:
  %pv = load ptr, ptr %pa, align 8
  %iv = load i64, ptr %ia, align 8
  %q = getelementptr i64, ptr %pv, i64 %iv
  %x = load i64, ptr %q, align 8
  %sv = load i64, ptr %sa, align 8
  %sn = add i64 %sv, %x
  store i64 %sn, ptr %sa, align 8
  %in = add i64 %iv, 1
  store i64 %in, ptr %ia, align 8
  br label %head
exit:
  %r = load i64, ptr %sa, align 8
  ret i64 %r
}
define i64 @main() {
entry:
  %arr = alloca [4 x i64], align 8
  %p0 = getelementptr i64, ptr %arr, i64 0
  %r = call i64 @sum4(ptr %p0)
  ret i64 %r
}
"#;

#[test]
fn mem2reg_promotes_spilled_loop_to_provable() {
    let module = LlvmFrontend
        .lower(LlvmInput { source: SPILLED_LOOP.into(), name: "spill".into() })
        .expect("lower");
    let cfg = Config { closed_world: true, ..Config::default() };
    assert_eq!(
        verify_module(&module, &cfg).verdict,
        Verdict::Pass,
        "a spilled -O0 counter loop must become provable after mem2reg"
    );
}

/// Soundness control for mem2reg: promoting the counter must not mask a genuine
/// out-of-bounds access. `sum` reads `p[0..8)` but the caller supplies only 4
/// elements — the bounds obligation must remain unproven (no false PASS).
const SPILLED_LOOP_OOB: &str = r#"
define i64 @sum8(ptr %p) {
entry:
  %sa = alloca i64, align 8
  %ia = alloca i64, align 8
  store i64 0, ptr %sa, align 8
  store i64 0, ptr %ia, align 8
  br label %head
head:
  %i = load i64, ptr %ia, align 8
  %c = icmp slt i64 %i, 8
  br i1 %c, label %body, label %exit
body:
  %iv = load i64, ptr %ia, align 8
  %q = getelementptr i64, ptr %p, i64 %iv
  %x = load i64, ptr %q, align 8
  %sv = load i64, ptr %sa, align 8
  %sn = add i64 %sv, %x
  store i64 %sn, ptr %sa, align 8
  %in = add i64 %iv, 1
  store i64 %in, ptr %ia, align 8
  br label %head
exit:
  %r = load i64, ptr %sa, align 8
  ret i64 %r
}
define i64 @main() {
entry:
  %arr = alloca [4 x i64], align 8
  %p0 = getelementptr i64, ptr %arr, i64 0
  %r = call i64 @sum8(ptr %p0)
  ret i64 %r
}
"#;

#[test]
fn mem2reg_preserves_out_of_bounds_obligation() {
    let module = LlvmFrontend
        .lower(LlvmInput { source: SPILLED_LOOP_OOB.into(), name: "spilloob".into() })
        .expect("lower");
    let cfg = Config { closed_world: true, ..Config::default() };
    assert_ne!(
        verify_module(&module, &cfg).verdict,
        Verdict::Pass,
        "promoting the counter must not hide the p[0..8) over-read of a 4-element buffer"
    );
}

/// Interval guard refinement + loop-bound import: a clamped variable-length loop
/// `if (n>4) n=4; for(i=0;i<n;i++) p[i]` is safe because the clamp bounds `n<=4`
/// and the region is 4 elements. The interval domain derives `n<=4` from the
/// `else` edge of the clamp; the symbolic loop imports that bound, so `i<n<=4`
/// proves `p[i]` in bounds under closed-world.
const CLAMPED_LOOP: &str = r#"
define i64 @clamped(ptr %p, i64 %n) {
entry:
  %c = icmp sgt i64 %n, 4
  br i1 %c, label %clamp, label %pre
clamp:
  br label %pre
pre:
  %nb = phi i64 [ 4, %clamp ], [ %n, %entry ]
  br label %head
head:
  %i = phi i64 [ 0, %pre ], [ %inext, %body ]
  %lt = icmp slt i64 %i, %nb
  br i1 %lt, label %body, label %exit
body:
  %q = getelementptr i64, ptr %p, i64 %i
  %x = load i64, ptr %q, align 8
  %inext = add i64 %i, 1
  br label %head
exit:
  ret i64 0
}
define i64 @main() {
entry:
  %arr = alloca [4 x i64], align 8
  %p0 = getelementptr i64, ptr %arr, i64 0
  %r = call i64 @clamped(ptr %p0, i64 8)
  ret i64 %r
}
"#;

#[test]
fn guard_refinement_proves_clamped_loop() {
    let module = LlvmFrontend
        .lower(LlvmInput { source: CLAMPED_LOOP.into(), name: "clamp".into() })
        .expect("lower");
    let cfg = Config { closed_world: true, ..Config::default() };
    assert_eq!(
        verify_module(&module, &cfg).verdict,
        Verdict::Pass,
        "a loop whose bound is clamped to the region size must prove via guard refinement"
    );
}

/// Soundness control: the same loop clamped to 8 over a 4-element region reads out
/// of bounds — the refined bound `n<=8` does not prove `i<4`, so it stays UNKNOWN.
#[test]
fn guard_refinement_over_clamp_is_not_pass() {
    let src = CLAMPED_LOOP.replace("sgt i64 %n, 4", "sgt i64 %n, 8").replace("[ 4, %clamp ]", "[ 8, %clamp ]");
    let module = LlvmFrontend
        .lower(LlvmInput { source: src, name: "clampoob".into() })
        .expect("lower");
    let cfg = Config { closed_world: true, ..Config::default() };
    assert_ne!(
        verify_module(&module, &cfg).verdict,
        Verdict::Pass,
        "a bound clamped larger than the region must not falsely prove in-bounds"
    );
}

/// Member-provenance through a double pointer, past an unrelated `memset`: `**pp`
/// where the caller stores `&v` into `vp` and passes `&vp`. A local buffer
/// initializer (`memset buf`) between the store and the call must not wipe the
/// field guarantee — it writes `buf`, not `vp` — so `*pp` stays a valid pointer.
const DOUBLE_PTR_MEMSET: &str = r#"
declare void @llvm.memset.p0.i64(ptr, i8, i64, i1)
define i64 @f_pp(ptr %pp) {
entry:
  %inner = load ptr, ptr %pp, align 8
  %val = load i64, ptr %inner, align 8
  ret i64 %val
}
define i64 @main() {
entry:
  %v = alloca i64, align 8
  %vp = alloca ptr, align 8
  %buf = alloca [16 x i8], align 8
  store i64 5, ptr %v, align 8
  store ptr %v, ptr %vp, align 8
  call void @llvm.memset.p0.i64(ptr %buf, i8 0, i64 16, i1 false)
  %r = call i64 @f_pp(ptr %vp)
  ret i64 %r
}
"#;

#[test]
fn member_provenance_survives_unrelated_memset() {
    let module = LlvmFrontend
        .lower(LlvmInput { source: DOUBLE_PTR_MEMSET.into(), name: "pp".into() })
        .expect("lower");
    let cfg = Config { closed_world: true, ..Config::default() };
    assert_eq!(
        verify_module(&module, &cfg).verdict,
        Verdict::Pass,
        "a memset of an unrelated buffer must not drop the double-pointer field guarantee"
    );
}

/// Soundness control: a `memset` of the field's own slot (`memset vp`) *does*
/// overwrite the stored pointer, so the guarantee is correctly dropped and the
/// dereference stays UNKNOWN — no false PASS.
#[test]
fn member_provenance_dropped_by_memset_of_the_field() {
    let src = DOUBLE_PTR_MEMSET.replace(
        "call void @llvm.memset.p0.i64(ptr %buf, i8 0, i64 16, i1 false)",
        "call void @llvm.memset.p0.i64(ptr %vp, i8 0, i64 8, i1 false)",
    );
    let module = LlvmFrontend
        .lower(LlvmInput { source: src, name: "ppc".into() })
        .expect("lower");
    let cfg = Config { closed_world: true, ..Config::default() };
    assert_ne!(
        verify_module(&module, &cfg).verdict,
        Verdict::Pass,
        "a memset that overwrites the pointer field must drop the guarantee (no false PASS)"
    );
}

/// The precondition sidecar: an annotated buffer API `sum(p, n)` whose pointer is
/// uncontracted (UNKNOWN in isolation) verifies once the caller-declared
/// precondition "`p` is valid for `n` 8-byte elements" is applied — the `i < n`
/// loop then proves `p[i]` in bounds, resting on the `precondition` assumption.
const BUFFER_API: &str = r#"
define i64 @sum(ptr %p, i64 %n) {
entry:
  br label %head
head:
  %i = phi i64 [ 0, %entry ], [ %inext, %body ]
  %acc = phi i64 [ 0, %entry ], [ %nacc, %body ]
  %lt = icmp slt i64 %i, %n
  br i1 %lt, label %body, label %exit
body:
  %q = getelementptr i64, ptr %p, i64 %i
  %x = load i64, ptr %q, align 8
  %nacc = add i64 %acc, %x
  %inext = add i64 %i, 1
  br label %head
exit:
  ret i64 %acc
}
"#;

#[test]
fn precondition_sidecar_verifies_annotated_buffer_api() {
    let mut module = LlvmFrontend
        .lower(LlvmInput { source: BUFFER_API.into(), name: "api".into() })
        .expect("lower");
    // Uncontracted in isolation → UNKNOWN.
    assert_ne!(verify_module(&module, &Config::default()).verdict, Verdict::Pass);

    // With the precondition `sum 0 elements 1 8` → PASS.
    let pre = csolver_verifier::precond::parse("sum 0 elements 1 8").expect("parse");
    let n = csolver_verifier::precond::apply(&mut module, &pre).expect("apply");
    assert_eq!(n, 1, "one precondition applied");
    assert_eq!(
        verify_module(&module, &Config::default()).verdict,
        Verdict::Pass,
        "the declared buffer precondition proves the indexed loop"
    );
}

/// The sentinel-scan engine bound: a `strlen`-shaped loop `while (s[n]) n++` over
/// a region declared null-terminated (`cstring`) verifies — the scan cannot pass
/// the terminator, which lies before the end. Language-agnostic: any "scan until a
/// zero element" loop.
const SENTINEL_SCAN: &str = r#"
define i64 @scan(ptr %s) {
entry:
  br label %head
head:
  %n = phi i64 [ 0, %entry ], [ %nn, %body ]
  %q = getelementptr i8, ptr %s, i64 %n
  %c = load i8, ptr %q, align 1
  %z = icmp eq i8 %c, 0
  br i1 %z, label %exit, label %body
body:
  %nn = add i64 %n, 1
  br label %head
exit:
  ret i64 %n
}
"#;

#[allow(clippy::expect_used)] // a test helper, like the `#[test]` bodies it serves
fn verify_with_pre(src: &str, name: &str, pre: &str) -> Verdict {
    let mut module = LlvmFrontend
        .lower(LlvmInput { source: src.into(), name: name.into() })
        .expect("lower");
    let p = csolver_verifier::precond::parse(pre).expect("parse pre");
    csolver_verifier::precond::apply(&mut module, &p).expect("apply pre");
    verify_module(&module, &Config::default()).verdict
}

#[test]
fn sentinel_scan_over_cstring_verifies() {
    // Without the precondition the unbounded scan is UNKNOWN; with it, PASS.
    let bare = LlvmFrontend
        .lower(LlvmInput { source: SENTINEL_SCAN.into(), name: "s".into() })
        .expect("lower");
    assert_ne!(verify_module(&bare, &Config::default()).verdict, Verdict::Pass);
    assert_eq!(verify_with_pre(SENTINEL_SCAN, "s", "scan 0 cstring 4096"), Verdict::Pass);
}

/// Soundness control: a loop that loads `s[n]` but whose exit is *not* the
/// sentinel test (`n < m`, not `s[n] == 0`) may run past the terminator, so the
/// scan bound must not apply — UNKNOWN even with the `cstring` precondition.
#[test]
fn sentinel_scan_requires_exit_on_the_loaded_value() {
    let src = r#"
define i64 @f(ptr %s, i64 %m) {
entry:
  br label %head
head:
  %n = phi i64 [ 0, %entry ], [ %nn, %body ]
  %q = getelementptr i8, ptr %s, i64 %n
  %c = load i8, ptr %q, align 1
  %lt = icmp slt i64 %n, %m
  br i1 %lt, label %body, label %exit
body:
  %nn = add i64 %n, 1
  br label %head
exit:
  ret i64 %n
}
"#;
    assert_ne!(verify_with_pre(src, "f", "f 0 cstring 4096"), Verdict::Pass);
}

/// Soundness control: a stride-2 scan can step over the terminator, so the bound
/// must not apply — UNKNOWN even with the `cstring` precondition.
#[test]
fn sentinel_scan_requires_unit_stride() {
    let src = r#"
define i64 @f(ptr %s) {
entry:
  br label %head
head:
  %n = phi i64 [ 0, %entry ], [ %nn, %body ]
  %q = getelementptr i8, ptr %s, i64 %n
  %c = load i8, ptr %q, align 1
  %z = icmp eq i8 %c, 0
  br i1 %z, label %exit, label %body
body:
  %nn = add i64 %n, 2
  br label %head
exit:
  ret i64 %n
}
"#;
    assert_ne!(verify_with_pre(src, "f", "f 0 cstring 4096"), Verdict::Pass);
}

/// The `-O0` scan shape: an `i32` counter sign-extended to `i64` before indexing
/// (`gep i8, s, sext(n)`), so the GEP index is a *cast* of the induction, not a
/// copy of it. The scan bound must still recognize the induction through the
/// widening — else clang's default `-O0`/`-g` C output stays spuriously UNKNOWN.
#[test]
fn sentinel_scan_through_sext_index_verifies() {
    let src = r#"
define i32 @scan(ptr %s) {
entry:
  br label %head
head:
  %n = phi i32 [ 0, %entry ], [ %nn, %body ]
  %w = sext i32 %n to i64
  %q = getelementptr i8, ptr %s, i64 %w
  %c = load i8, ptr %q, align 1
  %z = icmp eq i8 %c, 0
  br i1 %z, label %exit, label %body
body:
  %nn = add i32 %n, 1
  br label %head
exit:
  ret i32 %n
}
"#;
    // Without the precondition UNKNOWN; with `cstring`, the sext-index scan verifies.
    let bare = LlvmFrontend
        .lower(LlvmInput { source: src.into(), name: "s".into() })
        .expect("lower");
    assert_ne!(verify_module(&bare, &Config::default()).verdict, Verdict::Pass);
    assert_eq!(verify_with_pre(src, "s", "scan 0 cstring 4096"), Verdict::Pass);
}

/// Memory written before a branch and read after the reconvergence must survive
/// the merge — a store identical on every incoming edge definitely holds. Here a
/// pointer stored into a (non-promotable, aggregate) slot before an `if` is loaded
/// and dereferenced after it; the deref proves only because the store's provenance
/// is kept across the merge.
const MERGE_MEMORY: &str = r#"
define i64 @merged(ptr %p, i1 %c) {
entry:
  %slot = alloca [1 x ptr], align 8
  %s0 = getelementptr [1 x ptr], ptr %slot, i64 0, i64 0
  store ptr %p, ptr %s0, align 8
  br i1 %c, label %a, label %b
a:
  br label %m
b:
  br label %m
m:
  %q = load ptr, ptr %s0, align 8
  %v = load i64, ptr %q, align 8
  ret i64 %v
}
define i64 @main() {
entry:
  %x = alloca i64, align 8
  %r = call i64 @merged(ptr %x, i1 1)
  ret i64 %r
}
"#;

#[test]
fn heap_survives_a_control_flow_merge() {
    let module = LlvmFrontend
        .lower(LlvmInput { source: MERGE_MEMORY.into(), name: "mm".into() })
        .expect("lower");
    let cfg = Config { closed_world: true, ..Config::default() };
    assert_eq!(
        verify_module(&module, &cfg).verdict,
        Verdict::Pass,
        "a store identical on all merge edges must be readable after the merge"
    );
}

/// Soundness control: when the two branches store *different* pointers into the
/// slot, the address is ambiguous after the merge, so the later deref must stay
/// UNKNOWN — no false PASS.
#[test]
fn heap_merge_drops_addresses_the_paths_disagree_on() {
    let src = r#"
define i64 @merged(ptr %p, i1 %c) {
entry:
  %slot = alloca [1 x ptr], align 8
  %s0 = getelementptr [1 x ptr], ptr %slot, i64 0, i64 0
  br i1 %c, label %a, label %b
a:
  store ptr %p, ptr %s0, align 8
  br label %m
b:
  store ptr null, ptr %s0, align 8
  br label %m
m:
  %q = load ptr, ptr %s0, align 8
  %v = load i64, ptr %q, align 8
  ret i64 %v
}
define i64 @main() {
entry:
  %x = alloca i64, align 8
  %r = call i64 @merged(ptr %x, i1 1)
  ret i64 %r
}
"#;
    let module = LlvmFrontend.lower(LlvmInput { source: src.into(), name: "mmd".into() }).expect("lower");
    let cfg = Config { closed_world: true, ..Config::default() };
    assert_ne!(
        verify_module(&module, &cfg).verdict,
        Verdict::Pass,
        "an address the paths disagree on must not be provable after the merge"
    );
}

/// The two branches store *different but both-valid* pointers (`p` vs `p+1`) into
/// the slot; the merge JOINs them into a guarded select rather than dropping the
/// slot, so the later deref proves in bounds for both — a real UNKNOWN→PASS flip
/// that heap *intersection* (drop-on-disagree) could not make. Cross-language: any
/// `slot = c ? p : p+k; *slot` with both offsets in bounds.
const MERGE_JOIN: &str = r#"
define i64 @joined(ptr %p, i1 %c) {
entry:
  %slot = alloca [1 x ptr], align 8
  %s0 = getelementptr [1 x ptr], ptr %slot, i64 0, i64 0
  br i1 %c, label %a, label %b
a:
  store ptr %p, ptr %s0, align 8
  br label %m
b:
  %p1 = getelementptr i64, ptr %p, i64 1
  store ptr %p1, ptr %s0, align 8
  br label %m
m:
  %q = load ptr, ptr %s0, align 8
  %v = load i64, ptr %q, align 8
  ret i64 %v
}
define i64 @main() {
entry:
  %x = alloca [2 x i64], align 8
  %x0 = getelementptr [2 x i64], ptr %x, i64 0, i64 0
  %r = call i64 @joined(ptr %x0, i1 1)
  ret i64 %r
}
"#;

#[test]
fn heap_merge_joins_differing_but_valid_pointer_stores() {
    let module = LlvmFrontend
        .lower(LlvmInput { source: MERGE_JOIN.into(), name: "mj".into() })
        .expect("lower");
    let cfg = Config { closed_world: true, ..Config::default() };
    assert_eq!(
        verify_module(&module, &cfg).verdict,
        Verdict::Pass,
        "a slot holding p on one edge and p+1 on the other joins to a select both in bounds"
    );
}

/// A pointer that is a `select`/PHI of two *different* valid regions (`c ? &a : &b`)
/// is no longer opaque: an access through it is proved in bounds for each
/// alternative under its guard. Language-agnostic (any `cond ? p : q`).
const SELECT_PTR: &str = r#"
define i64 @sel(ptr %a, ptr %b, i1 %c) {
entry:
  br i1 %c, label %ta, label %tb
ta:
  br label %m
tb:
  br label %m
m:
  %p = phi ptr [ %a, %ta ], [ %b, %tb ]
  %v = load i64, ptr %p, align 8
  ret i64 %v
}
define i64 @main() {
entry:
  %x = alloca i64, align 8
  %y = alloca i64, align 8
  %r = call i64 @sel(ptr %x, ptr %y, i1 1)
  ret i64 %r
}
"#;

#[test]
fn select_of_two_valid_pointers_verifies() {
    let module = LlvmFrontend
        .lower(LlvmInput { source: SELECT_PTR.into(), name: "sel".into() })
        .expect("lower");
    let cfg = Config { closed_world: true, ..Config::default() };
    assert_eq!(
        verify_module(&module, &cfg).verdict,
        Verdict::Pass,
        "an access through a select of two valid pointers is in bounds for both"
    );
}

/// Soundness control: when one alternative is too small for the access, the join
/// access must stay UNKNOWN — the multi-provenance proves *each* branch, so a
/// branch that is out of bounds fails the conjunction (no false PASS).
#[test]
fn select_of_pointers_requires_both_in_bounds() {
    let src = r#"
define i64 @sel(ptr %a, ptr %b, i1 %c) {
entry:
  br i1 %c, label %ta, label %tb
ta:
  br label %m
tb:
  br label %m
m:
  %p = phi ptr [ %a, %ta ], [ %b, %tb ]
  %q = getelementptr i64, ptr %p, i64 2
  %v = load i64, ptr %q, align 8
  ret i64 %v
}
define i64 @main() {
entry:
  %arr = alloca [4 x i64], align 8
  %a0 = getelementptr i64, ptr %arr, i64 0
  %y = alloca i64, align 8
  %r = call i64 @sel(ptr %a0, ptr %y, i1 1)
  ret i64 %r
}
"#;
    let module = LlvmFrontend.lower(LlvmInput { source: src.into(), name: "seloob".into() }).expect("lower");
    let cfg = Config { closed_world: true, ..Config::default() };
    assert_ne!(
        verify_module(&module, &cfg).verdict,
        Verdict::Pass,
        "p[2] via the 1-element alternative is out of bounds — no false PASS"
    );
}

/// End-to-end provenance/capability enforcement through the **file-driven contracts**, on a
/// faithful reproduction of the CVE-2026-31431 "Copy Fail" AEAD in-place chain: a page is
/// labelled `foreign` by `af_alg_sendpage`, its provenance flows through `crypto_aead_copy_sgl`
/// and `aead_request_set_crypt` into the request, and `crypto_aead_encrypt` requires the
/// request's destination to grant `write` — which `foreign` does not → FAIL. This exercises
/// `label`/`propagate`/`require` (data/provenance.contract) end to end through real API names.
#[test]
fn copy_fail_provenance_chain_is_refused() {
    // The same page pointer is threaded through the chain (mirroring the in-place src=dst
    // reuse); the opaque calls havoc the heap but the region provenance survives, so the
    // final capability requirement sees the foreign label. Needs bug-finding (the calls make
    // the path inexact, exactly as on real kernel code).
    let src = r#"
declare void @af_alg_sendpage(ptr, ptr)
declare void @crypto_aead_copy_sgl(ptr, ptr, ptr, i64)
declare void @aead_request_set_crypt(ptr, ptr, ptr, i64, ptr)
declare i32 @crypto_aead_encrypt(ptr)
define void @recvmsg(ptr %sk, ptr %tfm, ptr %iv) {
entry:
  %page = alloca [16 x i8], align 16
  %rsgl = alloca [16 x i8], align 16
  %req = alloca [16 x i8], align 16
  call void @af_alg_sendpage(ptr %sk, ptr %page)
  call void @crypto_aead_copy_sgl(ptr %tfm, ptr %page, ptr %rsgl, i64 16)
  call void @aead_request_set_crypt(ptr %req, ptr %rsgl, ptr %rsgl, i64 16, ptr %iv)
  %e = call i32 @crypto_aead_encrypt(ptr %req)
  ret void
}
"#;
    let module = LlvmFrontend
        .lower(LlvmInput { source: src.into(), name: "aead".into() })
        .expect("lower");
    let cfg = Config { bug_finding: true, ..Config::default() };
    assert_eq!(
        verify_module(&module, &cfg).verdict,
        Verdict::Fail,
        "a foreign page reaching an AEAD write destination must be refused (write-capability)"
    );

    // Control: without the labelling source, the same chain is not a violation.
    let safe = src.replace("  call void @af_alg_sendpage(ptr %sk, ptr %page)\n", "");
    let module = LlvmFrontend
        .lower(LlvmInput { source: safe, name: "aead_safe".into() })
        .expect("lower");
    assert_ne!(
        verify_module(&module, &cfg).verdict,
        Verdict::Fail,
        "with no foreign label, an unlabelled destination grants write — no false FAIL"
    );
}

/// **Member-provenance for labels**: a `foreign` region's provenance survives a round-trip
/// through a struct-field store/load (the alias-aware heap returns the same region, which
/// keeps its labels), even across an intervening opaque call that havocs the heap. This is
/// the building block that lets provenance reach a `require` through pointer fields
/// (e.g. `req->dst`), rather than only through direct call arguments.
#[test]
fn provenance_survives_a_field_store_load() {
    let src = r#"
declare void @af_alg_sendpage(ptr, ptr)
declare i32 @crypto_aead_encrypt(ptr)
define void @f(ptr %sk) {
entry:
  %page = alloca [16 x i8], align 16
  %slot = alloca ptr, align 8
  call void @af_alg_sendpage(ptr %sk, ptr %page)
  store ptr %page, ptr %slot, align 8
  %p2 = load ptr, ptr %slot, align 8
  %e = call i32 @crypto_aead_encrypt(ptr %p2)
  ret void
}
"#;
    let module = LlvmFrontend
        .lower(LlvmInput { source: src.into(), name: "memprov".into() })
        .expect("lower");
    let cfg = Config { bug_finding: true, ..Config::default() };
    assert_eq!(
        verify_module(&module, &cfg).verdict,
        Verdict::Fail,
        "the foreign label must survive the store/load and reach the write-capability check"
    );
}

/// **General effect-summary inference**: an *internal wrapper* `@wrap` around a provenance
/// primitive (`sg_set_page`) carries **no hand-written contract**, yet the analysis derives
/// its provenance-transfer summary (dst absorbs src) from its body and applies it at the call
/// site — so a `foreign` page flows through the wrapper into the scatterlist and the AEAD
/// write is refused. This is what lets provenance coverage scale without a contract per wrapper.
#[test]
fn derived_provenance_transfer_through_an_internal_wrapper() {
    let base = r#"
declare void @af_alg_sendpage(ptr, ptr)
declare void @sg_set_page(ptr, ptr)
declare i32 @crypto_aead_encrypt(ptr)
define internal void @wrap(ptr %sgl, ptr %page) {
  PRIMITIVE
  ret void
}
define void @f(ptr %sk) {
entry:
  %page = alloca [16 x i8], align 16
  %sgl = alloca [16 x i8], align 16
  call void @af_alg_sendpage(ptr %sk, ptr %page)
  call void @wrap(ptr %sgl, ptr %page)
  %e = call i32 @crypto_aead_encrypt(ptr %sgl)
  ret void
}
"#;
    let cfg = Config { bug_finding: true, ..Config::default() };
    // The wrapper propagates provenance (it calls the primitive) → derived → FAIL.
    let src = base.replace("  PRIMITIVE\n", "  call void @sg_set_page(ptr %sgl, ptr %page)\n");
    let module = LlvmFrontend.lower(LlvmInput { source: src, name: "w".into() }).expect("lower");
    assert_eq!(
        verify_module(&module, &cfg).verdict,
        Verdict::Fail,
        "the wrapper's provenance transfer is derived (no contract on @wrap) and applied"
    );
    // Control: a wrapper that does NOT propagate leaves the scatterlist unlabelled → no FAIL.
    let src = base.replace("  PRIMITIVE\n", "");
    let module = LlvmFrontend.lower(LlvmInput { source: src, name: "w2".into() }).expect("lower");
    assert_ne!(
        verify_module(&module, &cfg).verdict,
        Verdict::Fail,
        "a wrapper with no provenance effect must not taint the scatterlist — no false FAIL"
    );
}

/// **Read-consistency for unwritten memory**: two reads of the same never-written location
/// must agree (unwritten memory holds one fixed unknown value). Here `%a` and `%b` load the
/// same field of a `dereferenceable` parameter, so `%c = %a - %b` is provably `0`, hence
/// `arr[%c]` is `arr[0]` — in bounds. Without read-consistency the two loads would be distinct
/// fresh values, `%c` unknown, and the indexed access unprovable (UNKNOWN). PASS rests on the
/// `param-contracts` assumption (the dereferenceable region), not on the read-consistency,
/// which is the correct memory semantics.
#[test]
fn two_reads_of_an_unwritten_field_agree() {
    let src = r#"
define i32 @f(ptr dereferenceable(8) align 8 %p) {
entry:
  %arr = alloca [1 x i32], align 4
  store i32 0, ptr %arr, align 4
  %a = load i64, ptr %p, align 8
  %b = load i64, ptr %p, align 8
  %c = sub i64 %a, %b
  %e = getelementptr [1 x i32], ptr %arr, i64 0, i64 %c
  %v = load i32, ptr %e, align 4
  ret i32 %v
}
"#;
    let module = LlvmFrontend.lower(LlvmInput { source: src.into(), name: "rc".into() }).expect("lower");
    assert_eq!(
        verify_module(&module, &Config::default()).verdict,
        Verdict::Pass,
        "two loads of the same unwritten field agree, so arr[a-b] = arr[0] is in bounds"
    );
}

/// **Materialised-field region identity**: two loads of the *same* raw-pointer field
/// (`d->child`) now resolve to the **same** materialised region, so an in-place op whose
/// `src` and `dst` both come from that field is recognised as `src == dst`. Here `d->child`
/// is labelled `foreign` and then used in-place (`require-if-alias`) → refused. Without field
/// identity the two loads would be distinct regions and the aliasing would be missed. This is
/// the building block that carries the in-place gate through struct-field indirection (the
/// shape real crypto code uses: `areq->first_rsgl.sgl.sg`).
#[test]
fn same_field_loaded_twice_is_one_region() {
    let src = r#"
%struct.child = type { i32, [4 x i64] }
%struct.dev = type { i32, ptr }
declare void @af_alg_sendpage(ptr, ptr)
declare void @aead_request_set_crypt(ptr, ptr, ptr, i64, ptr)
define void @f(ptr %d, ptr %iv) !dbg !4 {
entry:
  %c1 = getelementptr inbounds i8, ptr %d, i64 8
  %child1 = load ptr, ptr %c1, align 8
  %c2 = getelementptr inbounds i8, ptr %d, i64 8
  %child2 = load ptr, ptr %c2, align 8
  call void @af_alg_sendpage(ptr %d, ptr %child1)
  call void @aead_request_set_crypt(ptr %d, ptr %child1, ptr %child2, i64 16, ptr %iv)
  ret void
}
!llvm.dbg.cu = !{!0}
!llvm.module.flags = !{!3}
!0 = distinct !DICompileUnit(language: DW_LANG_C11, file: !1, emissionKind: FullDebug)
!1 = !DIFile(filename: "d.c", directory: "/")
!3 = !{i32 2, !"Debug Info Version", i32 3}
!4 = distinct !DISubprogram(name: "f", scope: !1, file: !1, type: !5, unit: !0, retainedNodes: !20)
!5 = !DISubroutineType(types: !6)
!6 = !{null, !8, !8}
!8 = !DIDerivedType(tag: DW_TAG_pointer_type, baseType: !9, size: 64)
!9 = !DICompositeType(tag: DW_TAG_structure_type, name: "dev", size: 128, elements: !10)
!10 = !{!11, !12}
!11 = !DIDerivedType(tag: DW_TAG_member, name: "id", baseType: !7, size: 32, offset: 0)
!7 = !DIBasicType(name: "int", size: 32)
!12 = !DIDerivedType(tag: DW_TAG_member, name: "child", baseType: !13, size: 64, offset: 64)
!13 = !DIDerivedType(tag: DW_TAG_pointer_type, baseType: !14, size: 64)
!14 = !DICompositeType(tag: DW_TAG_structure_type, name: "child", size: 320)
!20 = !{!21}
!21 = !DILocalVariable(name: "d", arg: 1, scope: !4, file: !1, type: !8)
"#;
    let module = LlvmFrontend.lower(LlvmInput { source: src.into(), name: "fid".into() }).expect("lower");
    let cfg = Config { bug_finding: true, assume_valid_params: true, ..Config::default() };
    assert_eq!(
        verify_module(&module, &cfg).verdict,
        Verdict::Fail,
        "two loads of d->child are one region, so the in-place foreign write is refused"
    );
}

/// **In-place-aliasing precision gate** (`require-if-alias`): the precise Copy-Fail signature is
/// an in-place crypto op (`aead_request_set_crypt` with `src == dst`) writing a `foreign` page.
/// The VULNERABLE in-place form (src and dst the same foreign region) is refused; the PATCHED
/// out-of-place form (a distinct fresh destination) is not — so the gate never false-FAILs the
/// safe copy, which is what makes reaching for cross-syscall provenance sound.
#[test]
fn inplace_write_to_foreign_is_refused_out_of_place_is_not() {
    let template = r#"
declare void @af_alg_sendpage(ptr, ptr)
declare void @aead_request_set_crypt(ptr, ptr, ptr, i64, ptr)
define void @recvmsg(ptr %sk, ptr %iv) {
entry:
  %page = alloca [16 x i8], align 16
  %dst = alloca [16 x i8], align 16
  %req = alloca [16 x i8], align 16
  call void @af_alg_sendpage(ptr %sk, ptr %page)
  call void @aead_request_set_crypt(ptr %req, ptr %page, ptr DEST, i64 16, ptr %iv)
  ret void
}
"#;
    let cfg = Config { bug_finding: true, ..Config::default() };
    // Vulnerable: in-place — src == dst == the foreign page.
    let module = LlvmFrontend
        .lower(LlvmInput { source: template.replace("DEST", "%page"), name: "vuln".into() })
        .expect("lower");
    assert_eq!(
        verify_module(&module, &cfg).verdict,
        Verdict::Fail,
        "in-place crypto (src==dst) over a foreign page must be refused"
    );
    // Patched: out-of-place — a distinct, fresh destination.
    let module = LlvmFrontend
        .lower(LlvmInput { source: template.replace("DEST", "%dst"), name: "safe".into() })
        .expect("lower");
    assert_ne!(
        verify_module(&module, &cfg).verdict,
        Verdict::Fail,
        "out-of-place crypto (src != dst) must NOT fire — no false FAIL on the patched path"
    );
}
