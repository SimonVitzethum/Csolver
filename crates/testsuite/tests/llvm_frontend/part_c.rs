use super::*;

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

/// A `list_for_each_entry` cursor's backward `container_of` (`pos = cursor − offsetof(member)`)
/// stays **in-object**: the loop-pointer materialisation now places the cursor at the member
/// offset inside its *whole node* (recovered from the typed container gep), so the subtraction
/// lands at the node base instead of underflowing a member-sized region. Under
/// `--assume-valid-loop-ptrs` the container access and the walk decide (was 5 UNKNOWN — the
/// dominant real-kernel list-walk residual — now at most a lone alignment tail).
#[test]
fn list_for_each_entry_container_of_stays_in_object() {
    let src = r#"
%struct.node = type { i64, %struct.list_head }
%struct.list_head = type { ptr, ptr }
@head = internal global %struct.list_head zeroinitializer
define i64 @walk() {
entry:
  %first = load ptr, ptr @head, align 8
  br label %loop
loop:
  %it = phi ptr [ %first, %entry ], [ %next, %body ]
  %isend = icmp eq ptr %it, @head
  br i1 %isend, label %done, label %body
body:
  %pos = getelementptr i8, ptr %it, i64 -8
  %valp = getelementptr %struct.node, ptr %pos, i64 0, i32 0
  %v = load i64, ptr %valp, align 8
  %nextp = getelementptr %struct.list_head, ptr %it, i64 0, i32 0
  %next = load ptr, ptr %nextp, align 8
  br label %loop
done:
  ret i64 0
}
"#;
    let m = LlvmFrontend.lower(LlvmInput { source: src.into(), name: "c".into() }).expect("lower");
    let cfg = Config { assume_valid_params: true, assume_valid_loop_ptrs: true, bug_finding: true, ..Config::default() };
    let rep = verify_module(&m, &cfg);
    let walk = rep.functions.iter().find(|f| f.function == "walk").expect("walk report");
    assert!(walk.count(Verdict::Unknown) <= 1,
        "the container_of list-walk decides except at most an alignment tail, got {} unknown",
        walk.count(Verdict::Unknown));
    assert!(walk.count(Verdict::Pass) >= 18, "most obligations proven, got {}", walk.count(Verdict::Pass));
}

/// A2: an internal helper's uncontracted pointer parameter is sized from the **typed pointer
/// its caller passes** — the interprocedural pointer-contract synthesis now grounds a
/// call site from the argument's pointee hint (not only a constant `alloca`). The helper reads
/// `p[10]` (offset 40, in bounds of the 64-byte `struct dev` the caller passes); under
/// `--assume-valid-params` the synthesized contract sizes `p` and the read PROVES. UNKNOWN by
/// default (no flag ⇒ no hint grounding ⇒ the parameter stays uncontracted).
#[test]
fn a2_internal_param_sized_from_caller_typed_pointer() {
    // The caller types `%d` as a `struct.dev` (64 bytes) via a `getelementptr %struct.dev`,
    // giving `%d` a pointee hint with no DWARF needed; that hint grounds the call site so the
    // helper's parameter is synthesized at 64 bytes.
    let src = r#"
%struct.dev = type { [16 x i32] }
define internal i32 @helper(ptr %p) {
entry:
  %q = getelementptr inbounds i8, ptr %p, i64 40
  %v = load i32, ptr %q, align 4
  ret i32 %v
}
define i32 @caller(ptr %d) {
entry:
  %t = getelementptr %struct.dev, ptr %d, i64 0, i32 0, i64 0
  %r = call i32 @helper(ptr %d)
  ret i32 %r
}
"#;
    let m = LlvmFrontend.lower(LlvmInput { source: src.into(), name: "c".into() }).expect("lower");
    assert_ne!(verify_module(&m, &Config::default()).verdict, Verdict::Pass,
        "without the flag the helper's parameter stays uncontracted → UNKNOWN");
    let cfg = Config { assume_valid_params: true, ..Config::default() };
    assert_eq!(verify_module(&m, &cfg).verdict, Verdict::Pass,
        "the synthesized contract sizes the helper's parameter from the caller's typed pointer");
}

/// A **field-accessor call** (`get_child(d)` returning `d->child`) is summarized as
/// `RetSummary::ValidRef`, so a caller that indexes the returned pointer sizes it instead of
/// falling to an opaque `POrigin::Call` (the dominant `opaque call result` UNKNOWN cause). Under
/// `--assume-valid-params` the access through the call result is decided (the callee's loaded
/// raw-pointer field is `assumed`); UNKNOWN by default. This is the interprocedural face of the
/// loaded-field recovery above — the recovery now survives a call boundary.
#[test]
fn field_accessor_call_result_is_sized_under_assume_valid_params() {
    // struct child { i32; [4 x i64] }; struct dev { i32; child* }.
    // get_child(d) = d->child (a raw-pointer field, typed by DWARF).
    // caller(d)    = get_child(d)->data[2]  — offset 24 into the 40-byte child, in bounds.
    let src = r#"
%struct.child = type { i32, [4 x i64] }
%struct.dev = type { i32, ptr }
define ptr @get_child(ptr %d) !dbg !4 {
entry:
  %c = getelementptr inbounds i8, ptr %d, i64 8
  %child = load ptr, ptr %c, align 8
  ret ptr %child
}
define i64 @caller(ptr %d) {
entry:
  %child = call ptr @get_child(ptr %d)
  %p = getelementptr inbounds i8, ptr %child, i64 24
  %v = load i64, ptr %p, align 8
  ret i64 %v
}
!llvm.dbg.cu = !{!0}
!llvm.module.flags = !{!3}
!0 = distinct !DICompileUnit(language: DW_LANG_C11, file: !1, emissionKind: FullDebug)
!1 = !DIFile(filename: "d.c", directory: "/")
!3 = !{i32 2, !"Debug Info Version", i32 3}
!4 = distinct !DISubprogram(name: "get_child", scope: !1, file: !1, type: !5, unit: !0, retainedNodes: !20)
!5 = !DISubroutineType(types: !6)
!6 = !{!8, !8}
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
        "a field-accessor call result is not assumed valid by default");
    let cfg = Config { assume_valid_params: true, ..Config::default() };
    assert_eq!(verify_module(&m, &cfg).verdict, Verdict::Pass,
        "the ValidRef return summary sizes the call result so the access proves");
}

/// An `i128`/`u128` checked multiply must not crash the analysis: its no-overflow goal would
/// need a 256-bit (`2·128`) product, past the bit-precise domain. It is skipped (stays UNKNOWN),
/// never a `BitVector` width panic — the crypto (`u128` multiply) case that whole-program
/// reachability surfaces and that previously aborted whole scans.
#[test]
fn i128_checked_multiply_does_not_panic() {
    let src = r#"
declare {i128, i1} @llvm.umul.with.overflow.i128(i128, i128)
define i128 @f(i128 %a, i128 %b) {
entry:
  %m = mul nuw i128 %a, %b
  ret i128 %m
}
"#;
    let m = LlvmFrontend.lower(LlvmInput { source: src.into(), name: "c".into() }).expect("lower");
    // The point is that verification completes without panicking (the verdict itself is
    // immaterial — the wide mul is soundly left undecided).
    let _ = verify_module(&m, &Config { bug_finding: true, ..Config::default() }).verdict;
}

/// A bounded shift amount proves `NoShiftOverflow`; an unbounded one is a genuine bug. The
/// operand bound is fed from the sound interval analysis (instruction-precise, so a value
/// derived earlier in the same block carries its range). Bug-finding mode, where the arithmetic
/// UB obligation is enumerated: a shift by `%s & 63 ∈ [0,63]` PASSES; a shift by an unconstrained
/// amount FAILS with a witness. This regression-guards the interval-fact seeding around the
/// shift/div/overflow checks (a true bound only ever *adds* a proof — never a false verdict).
#[test]
fn bounded_shift_amount_proves_and_unbounded_is_refuted() {
    let cfg = Config { bug_finding: true, ..Config::default() };
    let masked = r#"
define i64 @f(i64 %x, i64 %s) {
entry:
  %m = and i64 %s, 63
  %r = shl i64 %x, %m
  ret i64 %r
}
"#;
    let m = LlvmFrontend.lower(LlvmInput { source: masked.into(), name: "c".into() }).expect("lower");
    assert_eq!(verify_module(&m, &cfg).verdict, Verdict::Pass,
        "a shift amount bounded to [0,63] proves in range");
    let unmasked = r#"
define i64 @f(i64 %x, i64 %s) {
entry:
  %r = shl i64 %x, %s
  ret i64 %r
}
"#;
    let u = LlvmFrontend.lower(LlvmInput { source: unmasked.into(), name: "c".into() }).expect("lower");
    assert_eq!(verify_module(&u, &cfg).verdict, Verdict::Fail,
        "an unbounded shift amount is a genuine shift-overflow bug");
}

/// A pointer laundered through `llvm.launder.invariant.group` keeps its provenance: an access
/// through the laundered pointer is decided exactly as through the original. Without forwarding
/// the intrinsic's result the pointer would be havoc'd to a fresh scalar (the `intrinsic/asm`
/// scalar-as-pointer UNKNOWN cause) and the safe store would go UNKNOWN. In-bounds ⇒ PASS; the
/// out-of-bounds counterpart still refutes (provenance is preserved, not fabricated).
#[test]
fn launder_invariant_group_preserves_pointer_provenance() {
    let mk = |off: i64| format!(r#"
declare ptr @llvm.launder.invariant.group.p0(ptr)
define void @f() {{
entry:
  %arr = alloca [4 x i32], align 4
  %p = call ptr @llvm.launder.invariant.group.p0(ptr %arr)
  %q = getelementptr inbounds i32, ptr %p, i64 {off}
  store i32 7, ptr %q, align 4
  ret void
}}
"#);
    let safe = LlvmFrontend.lower(LlvmInput { source: mk(2).into(), name: "c".into() }).expect("lower");
    assert_eq!(verify_module(&safe, &Config::default()).verdict, Verdict::Pass,
        "an in-bounds store through a laundered pointer proves (provenance preserved)");
    let oob = LlvmFrontend.lower(LlvmInput { source: mk(9).into(), name: "c".into() }).expect("lower");
    assert_eq!(verify_module(&oob, &Config::default()).verdict, Verdict::Fail,
        "an out-of-bounds store through a laundered pointer still refutes");
}

/// `--assume-field-invariants` also assumes a **guarded array index** is in-bounds: the kernel
/// idiom `if (i >= n) return -EINVAL; … arr[i]`, where the guard's bound `n` is the array's own
/// length (a struct invariant the type system does not record). The per-path solver havocs the
/// bound and reports a spurious OOB at `i = UINT_MAX`; the flag trusts the guard. It must fire
/// only for an index the path actually bounds — an *unguarded* access stays refuted.
#[test]
fn assume_field_invariants_trusts_a_guarded_array_index() {
    let src = r#"
define void @guarded(i32 %i, i32 %n) {
entry:
  %arr = alloca [16 x i32], align 4
  %c = icmp uge i32 %i, %n
  br i1 %c, label %fail, label %ok
fail:
  ret void
ok:
  %idx = zext i32 %i to i64
  %p = getelementptr inbounds [16 x i32], ptr %arr, i64 0, i64 %idx
  store i32 42, ptr %p, align 4
  ret void
}
define void @unguarded(i32 %i) {
entry:
  %arr = alloca [16 x i32], align 4
  %idx = zext i32 %i to i64
  %p = getelementptr inbounds [16 x i32], ptr %arr, i64 0, i64 %idx
  store i32 42, ptr %p, align 4
  ret void
}
"#;
    let m = LlvmFrontend.lower(LlvmInput { source: src.into(), name: "g".into() }).expect("lower");
    let verdict = |name: &str, cfg: &Config| {
        verify_module(&m, cfg).functions.into_iter().find(|f| f.function == name).expect(name).verdict
    };
    let bugs = Config { bug_finding: true, entry_patterns: Some(vec!["guarded".into(), "unguarded".into()]), ..Config::default() };
    // By default the guarded access is refuted (the index is only bounded by an unconstrained `n`).
    assert_eq!(verdict("guarded", &bugs), Verdict::Fail, "guarded index refutes without the flag");
    let assume = Config { assume_field_invariants: true, ..bugs.clone() };
    // With the flag, the guard is trusted — the guarded access no longer refutes …
    assert_ne!(verdict("guarded", &assume), Verdict::Fail, "the guarded index is assumed in-bounds");
    // … but an unguarded access is still refuted (the assumption does not over-apply).
    assert_eq!(verdict("unguarded", &assume), Verdict::Fail, "an unguarded access is not assumed safe");
}

/// A Rust slice reference `&mut [T]` built via `from_raw_parts` erases to a bare pointer at
/// `-O`, but its length survives as a fat-pointer fragment in debug info
/// (`#dbg_value(iN len, !V, fragment 64 64)`). Recovering `len` sizes the backing region
/// `len * sizeof(T)`, so a constant-index access into it proves in-bounds (under
/// `--assume-valid-params`, the same gate as any raw-pointer region — the backing's
/// *validity* is the unsafe caller's contract). Without the flag the pointer stays opaque.
#[test]
fn slice_from_raw_parts_length_sizes_the_region() {
    // `s: &mut [i64]` of length 4 (region = 32 bytes) at an int-to-pointer address; two
    // in-bounds stores (`s[0]` at offset 0, `s[3]` at offset 24..32).
    let src = r#"
define void @slice_store(i64 %addr) !dbg !4 {
entry:
  %p = inttoptr i64 %addr to ptr, !dbg !20
    #dbg_value(ptr %p, !21, !DIExpression(DW_OP_LLVM_fragment, 0, 64), !20)
    #dbg_value(i64 4, !21, !DIExpression(DW_OP_LLVM_fragment, 64, 64), !20)
  store i64 7, ptr %p, align 8, !dbg !20
  %q = getelementptr inbounds i64, ptr %p, i64 3, !dbg !20
  store i64 8, ptr %q, align 8, !dbg !20
  ret void
}
!llvm.dbg.cu = !{!0}
!llvm.module.flags = !{!3}
!0 = distinct !DICompileUnit(language: DW_LANG_Rust, file: !1, emissionKind: FullDebug)
!1 = !DIFile(filename: "s.rs", directory: "/")
!3 = !{i32 2, !"Debug Info Version", i32 3}
!4 = distinct !DISubprogram(name: "slice_store", scope: !1, file: !1, type: !5, unit: !0, retainedNodes: !30)
!5 = !DISubroutineType(types: !6)
!6 = !{null, !7}
!7 = !DIBasicType(name: "u64", size: 64)
!12 = !DICompositeType(tag: DW_TAG_structure_type, name: "&mut [i64]", size: 128, align: 64, elements: !13)
!13 = !{}
!20 = !DILocation(line: 1, scope: !4)
!21 = !DILocalVariable(name: "s", scope: !4, file: !1, type: !12)
!30 = !{!21}
"#;
    let m = LlvmFrontend.lower(LlvmInput { source: src.into(), name: "s".into() }).expect("lower");
    assert_ne!(verify_module(&m, &Config::default()).verdict, Verdict::Pass,
        "an int-to-pointer slice is not assumed valid by default");
    let cfg = Config { assume_valid_params: true, ..Config::default() };
    assert_eq!(verify_module(&m, &cfg).verdict, Verdict::Pass,
        "the recovered slice length (4) sizes a 32-byte region, so both stores prove in-bounds");
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
