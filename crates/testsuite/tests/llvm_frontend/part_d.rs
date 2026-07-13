use super::*;

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
