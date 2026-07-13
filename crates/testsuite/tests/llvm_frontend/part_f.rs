use super::*;

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
pub const SPILLED_LOOP_OOB: &str = r#"
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
pub const CLAMPED_LOOP: &str = r#"
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
pub const DOUBLE_PTR_MEMSET: &str = r#"
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
pub const BUFFER_API: &str = r#"
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
pub const SENTINEL_SCAN: &str = r#"
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
pub const MERGE_MEMORY: &str = r#"
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
pub const MERGE_JOIN: &str = r#"
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
