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

define i32 @uses_callbr(ptr %p, i32 %v) {
entry:
  callbr void asm "", ""() to label %done []
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
    assert!(module.unanalyzed.iter().any(|(n, _)| n == "uses_callbr"));

    let report = verify_module(&module, &Config::default());
    // Module is UNKNOWN (one function not analyzed), but `good` is PASS.
    assert_eq!(report.verdict, Verdict::Unknown);
    let good = report.functions.iter().find(|f| f.function == "good").unwrap();
    assert_eq!(good.verdict, Verdict::Pass);
    let bad = report.functions.iter().find(|f| f.function == "uses_callbr").unwrap();
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
