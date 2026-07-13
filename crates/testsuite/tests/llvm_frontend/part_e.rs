use super::*;

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
pub const CLOSED_WORLD: &str = r#"
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
pub const CLOSED_WORLD_WEAKEST: &str = r#"
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
pub const MEMBER_PROV: &str = r#"
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
pub const MEMBER_PROV_UNSET: &str = r#"
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
pub const MEMBER_PROV_STRUCT_GEP: &str = r#"
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
pub const MEMBER_PROV_ESCAPE: &str = r#"
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
pub const GEP_ARG: &str = r#"
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
pub const GEP_ARG_OOB: &str = r#"
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
pub const SPILLED_LOOP: &str = r#"
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
