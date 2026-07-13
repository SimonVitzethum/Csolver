use super::*;

pub const GUARDED_STORE: &str = r#"
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
pub const OOB_STORE: &str = r#"
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
pub const PHI_LOOP: &str = r#"
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
pub const RUSTC_STYLE: &str = r##"
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
pub const DEREF_PARAM: &str = r#"
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
pub const READONLY_PARAM: &str = r#"
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
pub const VECTORIZED: &str = r#"
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
pub const MIXED: &str = r#"
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
pub const SWITCH_DISPATCH: &str = r#"
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
pub const SWITCH_OOB: &str = r#"
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
pub const SLICE_GET: &str = r#"
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
pub const SLICE_UNCHECKED: &str = r#"
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
pub const SLICE_INDEX_LOOP: &str = r#"
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
pub const CALL_ALIGN_GLOBAL: &str = r#"
define void @caller() unnamed_addr #0 {
start:
  call void @sink(i64 1, i64 7, ptr align 8 @glob)
  ret void
}
"#;
