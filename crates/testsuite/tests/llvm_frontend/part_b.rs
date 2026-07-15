use super::*;

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
pub(crate) const PTR_WALK: &str = r#"
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
pub(crate) const PTR_WALK_NOGUARD: &str = r#"
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
pub(crate) const MEM_INTRINSICS: &str = r#"
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
    assert_eq!(csolver_verifier::verify_module_with_threads(&m, &cfg, 1).verdict, Verdict::Pass,
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
    assert_eq!(csolver_verifier::verify_module_with_threads(&m, &cfg, 1).verdict, Verdict::Pass,
        "the pointee size is inferred from the gep-base type when debug info is absent");
}

/// `ioremap(phys, size)` maps device registers: a live, `size`-byte, externally *initialized*
/// region. Unlike a plain allocator (fresh, uninitialized), a register READ is valid — but a
/// provably out-of-bounds register access is still refuted. No flag: like `malloc`, the mapping
/// really is `size` bytes (NULL-on-failure rests on `alloc-succeeds`).
#[test]
fn ioremap_is_an_initialized_sized_mmio_region() {
    let ok = r#"
define i32 @rd(i64 %phys) {
  %p = call ptr @ioremap(i64 %phys, i64 64)
  %g = getelementptr i8, ptr %p, i64 60
  %v = load i32, ptr %g, align 4
  ret i32 %v
}
declare ptr @ioremap(i64, i64)
"#;
    let m = LlvmFrontend.lower(LlvmInput { source: ok.into(), name: "io".into() }).expect("lower");
    // An in-bounds register read proves — the region is initialized (no false uninit-read FAIL).
    assert_eq!(
        verify_module(&m, &Config { bug_finding: true, ..Config::default() }).verdict,
        Verdict::Pass,
        "an in-bounds MMIO register read is valid (initialized, sized)",
    );

    let oob = r#"
define i32 @rd(i64 %phys) {
  %p = call ptr @ioremap(i64 %phys, i64 64)
  %g = getelementptr i8, ptr %p, i64 128
  %v = load i32, ptr %g, align 4
  ret i32 %v
}
declare ptr @ioremap(i64, i64)
"#;
    let m = LlvmFrontend.lower(LlvmInput { source: oob.into(), name: "io".into() }).expect("lower");
    // A provably out-of-bounds register access (offset 128 into a 64-byte mapping) is a bug.
    assert_eq!(
        verify_module(&m, &Config { bug_finding: true, ..Config::default() }).verdict,
        Verdict::Fail,
        "an out-of-bounds MMIO access is still refuted (the region stays bounds-refutable)",
    );
}

/// A device-tree-sized mapping (`of_iomap`) has no static size, so a register access through
/// it can only rest on trust. The return is labelled `iomem`; the label survives the gep, and
/// under `--assume-valid-mmio` a register access through it is prove-only valid. Off by default
/// (a symbolic register offset could genuinely overrun), so it stays soundly UNKNOWN.
#[test]
fn iomem_register_access_is_trusted_only_under_the_flag() {
    let ir = r#"
define i32 @rd(ptr %node) {
  %io = call ptr @of_iomap(ptr %node, i32 0)
  %g = getelementptr i8, ptr %io, i64 16
  %v = load i32, ptr %g, align 4
  ret i32 %v
}
declare ptr @of_iomap(ptr, i32)
"#;
    let m = LlvmFrontend.lower(LlvmInput { source: ir.into(), name: "io".into() }).expect("lower");
    assert_ne!(
        verify_module(&m, &Config { bug_finding: true, ..Config::default() }).verdict,
        Verdict::Pass,
        "a register access through an unsized MMIO mapping is not proved by default",
    );
    let cfg = Config { bug_finding: true, assume_valid_mmio: true, ..Config::default() };
    assert_eq!(
        csolver_verifier::verify_module_with_threads(&m, &cfg, 1).verdict,
        Verdict::Pass,
        "under --assume-valid-mmio the iomem-labelled register access is trusted",
    );
}

/// A QEMU MMIO dispatch handler (`.read`/`.write` of a `MemoryRegionOps` passed to
/// `memory_region_init_io(..., size)`) is only ever called by the memory core, which guarantees
/// `1 <= size <= 8`. Modelling that (Module::mmio_handlers) is precision, not an assumption:
/// without it, treating the handler as an entry with a free `size` refutes a division `x / size`
/// (size 0 => division by zero) the dispatch never produces -- a false FAIL.
#[test]
fn mmio_dispatch_bound_removes_the_false_positive() {
    let ir = r#"
@dev_ops = internal constant { ptr, ptr } { ptr @dev_read, ptr @dev_write }

define i64 @dev_read(ptr %opaque, i64 %addr, i32 %size) {
  %s64 = zext i32 %size to i64
  %q = udiv i64 %addr, %s64
  ret i64 %q
}
define void @dev_write(ptr %opaque, i64 %addr, i32 %size) { ret void }

define void @dev_init(ptr %mr, ptr %owner, ptr %opaque) {
  call void @memory_region_init_io(ptr %mr, ptr %owner, ptr @dev_ops, ptr %opaque, ptr null, i64 32)
  ret void
}
declare void @memory_region_init_io(ptr, ptr, ptr, ptr, ptr, i64)
"#;
    let m = LlvmFrontend.lower(LlvmInput { source: ir.into(), name: "q".into() }).expect("lower");

    // Control: a NON-handler function with the same `x / size` shape and a free `size` is
    // refuted (size can be 0) -- so the test proves the fix is specific to MMIO handlers.
    let free = r#"
define i64 @plain(i64 %addr, i32 %size) {
  %s64 = zext i32 %size to i64
  %q = udiv i64 %addr, %s64
  ret i64 %q
}
"#;
    let mf = LlvmFrontend.lower(LlvmInput { source: free.into(), name: "p".into() }).expect("lower");
    let cfg_free = Config { bug_finding: true, entry_patterns: Some(vec!["plain".into()]), ..Config::default() };
    let rf = verify_module(&mf, &cfg_free);
    let plain = rf.functions.iter().find(|f| f.function == "plain").expect("plain");
    assert_eq!(
        plain.verdict, Verdict::Fail,
        "a plain function with a free divisor is correctly refuted (division by zero)",
    );

    // The MMIO handler: the dispatch bound `size >= 1` proves the division safe instead of
    // refuting it -- the false positive is gone, and it is a proof (not merely UNKNOWN).
    let cfg = Config { bug_finding: true, entry_patterns: Some(vec!["dev_read".into()]), ..Config::default() };
    let r = verify_module(&m, &cfg);
    let dev_read = r.functions.iter().find(|f| f.function == "dev_read").expect("dev_read");
    assert_eq!(
        dev_read.verdict, Verdict::Pass,
        "the MMIO dispatch bound proves `addr / size` cannot divide by zero (size >= 1)",
    );
}

/// The MMIO dispatch bound propagates interprocedurally: a handler `h_read` calls an internal
/// helper `reg_read(regs, addr, size)` passing its own `size`. The scalar-precondition synthesis
/// carries the handler's `1 <= size <= 8` to the helper's `size` parameter, so a `addr / size`
/// in the helper is proven safe instead of refuted -- the remaining false positives from
/// register.c-style dispatch helpers. The helper is internal (its callers are complete), which
/// is exactly QEMU's `register_read_memory`.
#[test]
fn mmio_size_bound_propagates_to_dispatch_helper() {
    let ir = r#"
@dev_ops = internal constant { ptr, ptr } { ptr @h_read, ptr @h_write }
define internal i64 @reg_read(ptr %regs, i64 %addr, i32 %size) {
  %s64 = zext i32 %size to i64
  %q = udiv i64 %addr, %s64
  ret i64 %q
}
define i64 @h_read(ptr %opaque, i64 %addr, i32 %size) {
  %r = call i64 @reg_read(ptr %opaque, i64 %addr, i32 %size)
  ret i64 %r
}
define void @h_write(ptr %opaque, i64 %addr, i32 %size) { ret void }
define void @dev_init(ptr %mr, ptr %owner, ptr %opaque) {
  call void @memory_region_init_io(ptr %mr, ptr %owner, ptr @dev_ops, ptr %opaque, ptr null, i64 32)
  ret void
}
declare void @memory_region_init_io(ptr, ptr, ptr, ptr, ptr, i64)
"#;
    let m = LlvmFrontend.lower(LlvmInput { source: ir.into(), name: "q".into() }).expect("lower");
    // Only the handler is an attacker entry; the helper is an internal callee whose only caller
    // is the handler, so its `size` inherits the [1,8] dispatch bound.
    let cfg = Config { bug_finding: true, entry_patterns: Some(vec!["h_read".into()]), ..Config::default() };
    let r = verify_module(&m, &cfg);
    let helper = r.functions.iter().find(|f| f.function == "reg_read").expect("reg_read");
    assert_eq!(
        helper.verdict, Verdict::Pass,
        "the dispatch bound must propagate to the helper's size, proving `addr / size` safe",
    );
}
