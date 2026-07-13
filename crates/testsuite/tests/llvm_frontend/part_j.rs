use super::*;

/// **Read-consistency on an opaque object's fields.** The real crypto worker reads
/// `req->src` and `req->dst` off an *opaque* request (a call result reached through an
/// alloca round-trip), not a stack `alloca` whose stores forward. Two reads of the same
/// `(opaque-base, offset)` with no intervening write must return the SAME value, so an
/// in-place op (src and dst both that field) is recognised and refused. Sound: the value
/// is a fresh unknown either way — read-consistency only adds an equality between two
/// reads of one location, never a false PASS, and the out-of-place case (distinct field)
/// still does not fire.
#[test]
fn opaque_field_read_consistency_recognises_in_place() {
    let base = r#"
declare void @af_alg_sendpage(ptr, ptr)
declare void @aead_request_set_crypt(ptr, ptr, ptr, i32, ptr)
declare ptr @alloc_req()
define void @f(ptr %sk) {
entry:
  %slot = alloca ptr, align 8
  %areq = call ptr @alloc_req()
  store ptr %areq, ptr %slot, align 8
  call void @af_alg_sendpage(ptr %sk, ptr %areq)
  %r1 = load ptr, ptr %slot, align 8
  %f1 = getelementptr inbounds i8, ptr %r1, i64 16
  %src = load ptr, ptr %f1, align 8
  %r2 = load ptr, ptr %slot, align 8
  %f2 = getelementptr inbounds i8, ptr %r2, i64 SRCOFF
  %dst = load ptr, ptr %f2, align 8
  call void @aead_request_set_crypt(ptr %areq, ptr %src, ptr %dst, i32 0, ptr null)
  ret void
}
"#;
    let cfg = Config { bug_finding: true, ..Config::default() };
    // In-place: src and dst read the SAME opaque field (offset 16) → the two reads agree
    // (read-consistency) → recognised as an in-place write of a foreign field → refused.
    let m = LlvmFrontend
        .lower(LlvmInput { source: base.replace("SRCOFF", "16"), name: "ip".into() })
        .expect("lower");
    assert_eq!(verify_module(&m, &cfg).verdict, Verdict::Fail,
        "two reads of the same opaque field must alias → in-place foreign write refused");
    // Out-of-place: src and dst read DIFFERENT fields (16 vs 24) → distinct values → no fire.
    let m = LlvmFrontend
        .lower(LlvmInput { source: base.replace("SRCOFF", "24"), name: "oop".into() })
        .expect("lower");
    assert_ne!(verify_module(&m, &cfg).verdict, Verdict::Fail,
        "distinct opaque fields do not alias — no false FAIL");
}

/// **Taint-on-read chains through plain field loads**: the seeded socket's `foreign` provenance
/// flows `sk → ctx → child` across two levels of ordinary pointer-field loads (not just DWARF
/// raw-pointer/RefWitness fields), and the in-place write of the twice-loaded `child` is refused.
/// This is the `sk → ctx → tsgl_src` shape the real crypto worker uses (minus its list walk).
#[test]
fn taint_on_read_chains_through_plain_loads() {
    let src = r#"
%struct.child = type { i32, [4 x i64] }
%struct.dev = type { i32, ptr }
declare void @aead_request_set_crypt(ptr, ptr, ptr, i64, ptr)
define void @_aead_recvmsg(ptr %sk, ptr %iv) !dbg !4 {
entry:
  %pctx = getelementptr inbounds i8, ptr %sk, i64 8
  %ctx = load ptr, ptr %pctx, align 8
  %c1 = getelementptr inbounds i8, ptr %ctx, i64 8
  %child1 = load ptr, ptr %c1, align 8
  %c2 = getelementptr inbounds i8, ptr %ctx, i64 8
  %child2 = load ptr, ptr %c2, align 8
  call void @aead_request_set_crypt(ptr %sk, ptr %child1, ptr %child2, i64 16, ptr %iv)
  ret void
}
!llvm.dbg.cu = !{!0}
!llvm.module.flags = !{!3}
!0 = distinct !DICompileUnit(language: DW_LANG_C11, file: !1, emissionKind: FullDebug)
!1 = !DIFile(filename: "d.c", directory: "/")
!3 = !{i32 2, !"Debug Info Version", i32 3}
!4 = distinct !DISubprogram(name: "_aead_recvmsg", scope: !1, file: !1, type: !5, unit: !0, retainedNodes: !20)
!5 = !DISubroutineType(types: !6)
!6 = !{null, !8, !8}
!8 = !DIDerivedType(tag: DW_TAG_pointer_type, baseType: !9, size: 64)
!9 = !DICompositeType(tag: DW_TAG_structure_type, name: "dev", size: 128, elements: !10)
!10 = !{!11, !12}
!7 = !DIBasicType(name: "int", size: 32)
!11 = !DIDerivedType(tag: DW_TAG_member, name: "id", baseType: !7, size: 32, offset: 0)
!12 = !DIDerivedType(tag: DW_TAG_member, name: "child", baseType: !13, size: 64, offset: 64)
!13 = !DIDerivedType(tag: DW_TAG_pointer_type, baseType: !14, size: 64)
!14 = !DICompositeType(tag: DW_TAG_structure_type, name: "child", size: 320)
!20 = !{!21}
!21 = !DILocalVariable(name: "sk", arg: 1, scope: !4, file: !1, type: !8)
"#;
    let module = LlvmFrontend.lower(LlvmInput { source: src.into(), name: "chain".into() }).expect("lower");
    let cfg = Config { bug_finding: true, assume_valid_params: true, ..Config::default() };
    assert_eq!(verify_module(&module, &cfg).verdict, Verdict::Fail,
        "the seeded socket's foreign provenance flows sk->ctx->child through plain loads");
}

/// **Whole-object cross-syscall seed (Track-A (c))**: a `seed arg0 foreign` contract on
/// `_aead_recvmsg` labels its socket at ENTRY (the object may hold a page a sibling syscall
/// spliced in). With no explicit label in the body, the socket is foreign, its raw-pointer
/// field inherits that (taint-on-read), and an in-place op on the field is refused — while the
/// same function under a *different name* (no seed) is not. The whole (a)+(b)+(c) chain,
/// end-to-end, driven only by the entry seed; and only the in-place sink fires, so it never
/// false-FAILs the out-of-place (patched) path.
#[test]
fn a_seeded_sink_treats_its_object_as_foreign() {
    let body = r#"
%struct.child = type { i32, [4 x i64] }
%struct.dev = type { i32, ptr }
declare void @aead_request_set_crypt(ptr, ptr, ptr, i64, ptr)
define void @NAME(ptr %sk, ptr %iv) !dbg !4 {
entry:
  %c1 = getelementptr inbounds i8, ptr %sk, i64 8
  %child1 = load ptr, ptr %c1, align 8
  %c2 = getelementptr inbounds i8, ptr %sk, i64 8
  %child2 = load ptr, ptr %c2, align 8
  call void @aead_request_set_crypt(ptr %sk, ptr %child1, ptr %child2, i64 16, ptr %iv)
  ret void
}
!llvm.dbg.cu = !{!0}
!llvm.module.flags = !{!3}
!0 = distinct !DICompileUnit(language: DW_LANG_C11, file: !1, emissionKind: FullDebug)
!1 = !DIFile(filename: "d.c", directory: "/")
!3 = !{i32 2, !"Debug Info Version", i32 3}
!4 = distinct !DISubprogram(name: "NAME", scope: !1, file: !1, type: !5, unit: !0, retainedNodes: !20)
!5 = !DISubroutineType(types: !6)
!6 = !{null, !8, !8}
!8 = !DIDerivedType(tag: DW_TAG_pointer_type, baseType: !9, size: 64)
!9 = !DICompositeType(tag: DW_TAG_structure_type, name: "dev", size: 128, elements: !10)
!10 = !{!11, !12}
!7 = !DIBasicType(name: "int", size: 32)
!11 = !DIDerivedType(tag: DW_TAG_member, name: "id", baseType: !7, size: 32, offset: 0)
!12 = !DIDerivedType(tag: DW_TAG_member, name: "child", baseType: !13, size: 64, offset: 64)
!13 = !DIDerivedType(tag: DW_TAG_pointer_type, baseType: !14, size: 64)
!14 = !DICompositeType(tag: DW_TAG_structure_type, name: "child", size: 320)
!20 = !{!21}
!21 = !DILocalVariable(name: "sk", arg: 1, scope: !4, file: !1, type: !8)
"#;
    let cfg = Config { bug_finding: true, assume_valid_params: true, ..Config::default() };
    // Seeded sink: the entry seed makes the socket foreign → in-place field write refused.
    let m = LlvmFrontend
        .lower(LlvmInput { source: body.replace("NAME", "_aead_recvmsg"), name: "s".into() })
        .expect("lower");
    assert_eq!(verify_module(&m, &cfg).verdict, Verdict::Fail,
        "the entry seed makes the socket foreign; its in-place field write is refused");
    // The identical body under a non-seeded name is not a violation (no false FAIL).
    let m = LlvmFrontend
        .lower(LlvmInput { source: body.replace("NAME", "unseeded_fn"), name: "u".into() })
        .expect("lower");
    assert_ne!(verify_module(&m, &cfg).verdict, Verdict::Fail,
        "with no seed, the object is not foreign — no false FAIL");
}

/// **Taint-on-read through an opaque object (Track-A (a)+(b))**: an object parameter is
/// labelled `foreign` (its opaque provenance identity, which flows through `gep`), and a raw-
/// pointer field loaded from it inherits that provenance (taint-on-read); two loads of the
/// field resolve to one region (field identity keyed by the opaque id), so an in-place op on
/// the field is refused. This is the full source→sink shape a cross-syscall seed will drive.
#[test]
fn a_field_of_a_foreign_object_is_foreign_and_gated_in_place() {
    let src = r#"
%struct.child = type { i32, [4 x i64] }
%struct.dev = type { i32, ptr }
declare void @af_alg_sendpage(ptr, ptr)
declare void @aead_request_set_crypt(ptr, ptr, ptr, i64, ptr)
define void @f(ptr %d, ptr %iv) !dbg !4 {
entry:
  call void @af_alg_sendpage(ptr %iv, ptr %d)
  %c1 = getelementptr inbounds i8, ptr %d, i64 8
  %child1 = load ptr, ptr %c1, align 8
  %c2 = getelementptr inbounds i8, ptr %d, i64 8
  %child2 = load ptr, ptr %c2, align 8
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
!7 = !DIBasicType(name: "int", size: 32)
!11 = !DIDerivedType(tag: DW_TAG_member, name: "id", baseType: !7, size: 32, offset: 0)
!12 = !DIDerivedType(tag: DW_TAG_member, name: "child", baseType: !13, size: 64, offset: 64)
!13 = !DIDerivedType(tag: DW_TAG_pointer_type, baseType: !14, size: 64)
!14 = !DICompositeType(tag: DW_TAG_structure_type, name: "child", size: 320)
!20 = !{!21}
!21 = !DILocalVariable(name: "d", arg: 1, scope: !4, file: !1, type: !8)
"#;
    let module = LlvmFrontend.lower(LlvmInput { source: src.into(), name: "taint".into() }).expect("lower");
    let cfg = Config { bug_finding: true, assume_valid_params: true, ..Config::default() };
    assert_eq!(verify_module(&module, &cfg).verdict, Verdict::Fail,
        "a field of a foreign object inherits foreign and its in-place write is refused");

    // A **store** between the two field loads reassigns the field, so the two references are
    // *different* objects — the materialised-field cache must be dropped, else they would be
    // treated as one region and `require-if-alias` would fire spuriously (a false FAIL). This
    // guards the fix for that (found by the DeepSeek review).
    let with_store = src.replace(
        "  %c2 = getelementptr inbounds i8, ptr %d, i64 8",
        "  store ptr %iv, ptr %c1, align 8\n  %c2 = getelementptr inbounds i8, ptr %d, i64 8",
    );
    let module = LlvmFrontend.lower(LlvmInput { source: with_store, name: "taint_store".into() }).expect("lower");
    assert_ne!(verify_module(&module, &cfg).verdict, Verdict::Fail,
        "a store between the loads breaks field identity — no false FAIL");
}

/// **Opaque-pointer provenance (Track-A groundwork)**: a raw-pointer *parameter* is opaque
/// provenance, not a region, yet it can now be labelled (on its holding SSA register) and the
/// in-place gate works on it — without modelling it as a region (which would false-PASS its
/// null/liveness/bounds). Here `%sk` is labelled `foreign` and used in-place (`src == dst`)
/// → refused; the out-of-place form (distinct pointers) is not. This is what lets a future
/// whole-object cross-syscall seed label the socket object at all.
#[test]
fn an_opaque_parameter_is_labelable_and_gated_in_place() {
    let base = r#"
declare void @af_alg_sendpage(ptr, ptr)
declare void @aead_request_set_crypt(ptr, ptr, ptr, i64, ptr)
define void @f(ptr %sk, ptr %other, ptr %iv) {
entry:
  call void @af_alg_sendpage(ptr %iv, ptr %sk)
  call void @aead_request_set_crypt(ptr %iv, ptr %sk, ptr DST, i64 16, ptr %iv)
  ret void
}
"#;
    let cfg = Config { bug_finding: true, ..Config::default() };
    // In-place: src == dst == the labelled opaque parameter → refused.
    let m = LlvmFrontend
        .lower(LlvmInput { source: base.replace("DST", "%sk"), name: "ip".into() })
        .expect("lower");
    assert_eq!(verify_module(&m, &cfg).verdict, Verdict::Fail,
        "an in-place op on a foreign-labelled opaque parameter is refused");
    // Out-of-place: a distinct pointer → not aliased → no fire (no false FAIL).
    let m = LlvmFrontend
        .lower(LlvmInput { source: base.replace("DST", "%other"), name: "oop".into() })
        .expect("lower");
    assert_ne!(verify_module(&m, &cfg).verdict, Verdict::Fail,
        "distinct pointers are not aliased — no false FAIL");
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
