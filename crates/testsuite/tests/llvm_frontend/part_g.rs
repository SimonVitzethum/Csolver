use super::*;

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
pub const SELECT_PTR: &str = r#"
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
/// **Division / modulo by zero (`NoDivByZero`).** A `/` or `%` whose divisor is an unguarded
/// attacker-reachable parameter can be zero → UB, refuted with a witness. A constant non-zero
/// divisor, and a divisor guarded non-zero on the path, are safe (no false FAIL).
#[test]
fn division_by_zero_is_flagged() {
    let cfg = Config { bug_finding: true, ..Config::default() };
    let lower = |src: &str| LlvmFrontend.lower(LlvmInput { source: src.into(), name: "d".into() }).expect("lower");
    // sdiv by an unguarded parameter → the divisor can be zero → FAIL.
    let racy = lower("define i32 @divp(i32 %a, i32 %b) {\nb:\n  %q = sdiv i32 %a, %b\n  ret i32 %q\n}\n");
    assert_eq!(verify_module(&racy, &cfg).verdict, Verdict::Fail, "division by an unguarded param can be zero");
    // urem by the same → also flagged (modulo by zero is UB too).
    let rem = lower("define i32 @remp(i32 %a, i32 %b) {\nb:\n  %q = urem i32 %a, %b\n  ret i32 %q\n}\n");
    assert_eq!(verify_module(&rem, &cfg).verdict, Verdict::Fail, "modulo by an unguarded param can be zero");
    // A constant non-zero divisor is safe.
    let konst = lower("define i32 @divc(i32 %a) {\nb:\n  %q = sdiv i32 %a, 2\n  ret i32 %q\n}\n");
    assert_ne!(verify_module(&konst, &cfg).verdict, Verdict::Fail, "division by a non-zero constant is safe");
    // A divisor guarded non-zero on the path is safe (no false FAIL).
    let guarded = lower(
        "define i32 @divg(i32 %a, i32 %b) {\nentry:\n  %nz = icmp ne i32 %b, 0\n  \
         br i1 %nz, label %do, label %skip\ndo:\n  %q = sdiv i32 %a, %b\n  ret i32 %q\nskip:\n  ret i32 0\n}\n",
    );
    assert_ne!(verify_module(&guarded, &cfg).verdict, Verdict::Fail, "a divisor guarded != 0 is safe");
}

/// **Shift past the bit width (`NoShiftOverflow`).** A `<<`/`>>` by an unguarded parameter can
/// reach or exceed the operand width → UB (poison). A constant in-range shift, and a shift guarded
/// `< width` on the path, are safe.
#[test]
fn shift_overflow_is_flagged() {
    let cfg = Config { bug_finding: true, ..Config::default() };
    let lower = |src: &str| LlvmFrontend.lower(LlvmInput { source: src.into(), name: "s".into() }).expect("lower");
    // shl by an unguarded i32 parameter (can be >= 32) → FAIL.
    let racy = lower("define i32 @shlp(i32 %a, i32 %b) {\nb:\n  %q = shl i32 %a, %b\n  ret i32 %q\n}\n");
    assert_eq!(verify_module(&racy, &cfg).verdict, Verdict::Fail, "a shift by an unguarded param can exceed the width");
    // A constant in-range shift is safe.
    let konst = lower("define i32 @shlc(i32 %a) {\nb:\n  %q = shl i32 %a, 3\n  ret i32 %q\n}\n");
    assert_ne!(verify_module(&konst, &cfg).verdict, Verdict::Fail, "a constant in-range shift is safe");
    // A shift guarded < 32 on the path is safe (no false FAIL).
    let guarded = lower(
        "define i32 @shlg(i32 %a, i32 %b) {\nentry:\n  %ok = icmp ult i32 %b, 32\n  \
         br i1 %ok, label %do, label %skip\ndo:\n  %q = shl i32 %a, %b\n  ret i32 %q\nskip:\n  ret i32 0\n}\n",
    );
    assert_ne!(verify_module(&guarded, &cfg).verdict, Verdict::Fail, "a shift guarded < width is safe");
}

/// **Signed/unsigned arithmetic overflow (`NoArithOverflow`).** An `add nsw`/`nuw` (or
/// `sub`/`mul`) on an unguarded attacker-reachable parameter can wrap → UB, refuted with a
/// witness. Only the `nsw`/`nuw`-flagged form carries the obligation: plain wrapping `add`
/// raises nothing. A bounded/guarded operand is safe (no false FAIL).
#[test]
fn arithmetic_overflow_is_flagged() {
    let cfg = Config { bug_finding: true, ..Config::default() };
    let lower = |src: &str| LlvmFrontend.lower(LlvmInput { source: src.into(), name: "o".into() }).expect("lower");
    // add nsw of two unguarded i32 params → can overflow → FAIL.
    let sadd = lower("define i32 @a(i32 %a, i32 %b) {\nb:\n  %q = add nsw i32 %a, %b\n  ret i32 %q\n}\n");
    assert_eq!(verify_module(&sadd, &cfg).verdict, Verdict::Fail, "add nsw of two unguarded params can overflow");
    // mul nuw of two unguarded params → can overflow → FAIL.
    let umul = lower("define i32 @m(i32 %a, i32 %b) {\nb:\n  %q = mul nuw i32 %a, %b\n  ret i32 %q\n}\n");
    assert_eq!(verify_module(&umul, &cfg).verdict, Verdict::Fail, "mul nuw of two unguarded params can overflow");
    // The SAME add without a no-wrap flag wraps legally → no obligation, no FAIL.
    let wrap = lower("define i32 @w(i32 %a, i32 %b) {\nb:\n  %q = add i32 %a, %b\n  ret i32 %q\n}\n");
    assert_ne!(verify_module(&wrap, &cfg).verdict, Verdict::Fail, "plain wrapping add carries no obligation");
    // add nsw of small constants cannot overflow → safe.
    let konst = lower("define i32 @k(i32 %a) {\nb:\n  %q = add nsw i32 1, 2\n  ret i32 %q\n}\n");
    assert_ne!(verify_module(&konst, &cfg).verdict, Verdict::Fail, "add nsw of small constants is safe");
}

/// **Dangling return / use-after-return (`NoDanglingDeref`).** A function that returns the
/// address of one of its own `alloca` locals hands the caller a pointer into a frame that dies
/// on return. Refuted with a witness (bug-finding). Returning a parameter or heap pointer, and
/// returning a non-pointer, are safe (no false FAIL).
#[test]
fn dangling_stack_return_is_flagged() {
    let cfg = Config { bug_finding: true, ..Config::default() };
    let lower = |src: &str| LlvmFrontend.lower(LlvmInput { source: src.into(), name: "r".into() }).expect("lower");
    // return &local → dangling.
    let bad = lower("define ptr @f() {\nb:\n  %p = alloca i32, align 4\n  ret ptr %p\n}\n");
    assert_eq!(verify_module(&bad, &cfg).verdict, Verdict::Fail, "returning the address of a local is a dangling return");
    // return a parameter pointer → fine (the caller owns it).
    let param = lower("define ptr @g(ptr %x) {\nb:\n  ret ptr %x\n}\n");
    assert_ne!(verify_module(&param, &cfg).verdict, Verdict::Fail, "returning a parameter pointer is safe");
    // return a scalar → not a pointer, nothing to flag.
    let scalar = lower("define i32 @h() {\nb:\n  ret i32 7\n}\n");
    assert_ne!(verify_module(&scalar, &cfg).verdict, Verdict::Fail, "returning a scalar is safe");
}

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
  %req = alloca [96 x i8], align 8
  call void @af_alg_sendpage(ptr %sk, ptr %page)
  store ptr %page, ptr %slot, align 8
  %p2 = load ptr, ptr %slot, align 8
  %s = getelementptr inbounds i8, ptr %req, i64 64
  store ptr %p2, ptr %s, align 8
  %d = getelementptr inbounds i8, ptr %req, i64 72
  store ptr %p2, ptr %d, align 8
  %e = call i32 @crypto_aead_encrypt(ptr %req)
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
  %req = alloca [96 x i8], align 8
  call void @af_alg_sendpage(ptr %sk, ptr %page)
  call void @wrap(ptr %sgl, ptr %page)
  %s = getelementptr inbounds i8, ptr %req, i64 64
  store ptr %sgl, ptr %s, align 8
  %d = getelementptr inbounds i8, ptr %req, i64 72
  store ptr %sgl, ptr %d, align 8
  %e = call i32 @crypto_aead_encrypt(ptr %req)
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

/// **Inlined-request in-place check (`require-if-alias-fields`)**: on a real optimized kernel the
/// crypto API is `static inline`, so there is no `aead_request_set_crypt` call — `req->src`/`req->dst`
/// are set by field STORES. The contract reads those two fields back from the request (at their byte
/// offsets) at the `crypto_aead_encrypt(req)` sink and applies the in-place-alias capability check:
/// a foreign page stored to BOTH src and dst (in-place) is refused; a distinct dst (patched) is not.
/// General — any operation on a descriptor with in-place src/dst pointer fields.
#[test]
fn inlined_request_in_place_write_of_a_foreign_page_is_refused() {
    let base = r#"
declare void @af_alg_sendpage(ptr, ptr)
declare i32 @crypto_aead_encrypt(ptr)
define void @f(ptr %sk, ptr %page) {
entry:
  %req = alloca [96 x i8], align 8
  call void @af_alg_sendpage(ptr %sk, ptr %page)
  %src = getelementptr inbounds i8, ptr %req, i64 64
  store ptr %page, ptr %src, align 8
  %dst = getelementptr inbounds i8, ptr %req, i64 72
  store ptr DSTVAL, ptr %dst, align 8
  %e = call i32 @crypto_aead_encrypt(ptr %req)
  ret void
}
"#;
    let cfg = Config { bug_finding: true, ..Config::default() };
    // In-place: the foreign page is stored to BOTH src (64) and dst (72) → refused.
    let m = LlvmFrontend
        .lower(LlvmInput { source: base.replace("DSTVAL", "%page"), name: "ip".into() })
        .expect("lower");
    assert_eq!(verify_module(&m, &cfg).verdict, Verdict::Fail,
        "an inlined in-place crypto op (req->src == req->dst == foreign) is refused");
    // Out-of-place: a distinct dst → no fire (no false FAIL).
    let m = LlvmFrontend
        .lower(LlvmInput { source: base.replace("DSTVAL", "%sk"), name: "oop".into() })
        .expect("lower");
    assert_ne!(verify_module(&m, &cfg).verdict, Verdict::Fail,
        "a distinct dst (patched out-of-place) does not fire — no false FAIL");
}

/// **Double-fetch of user memory (TOCTOU, G3).** Two `copy_from_user` reads from a
/// provably-aliasing user source on one path are a double-fetch: user memory is
/// adversary-controlled, so a value validated on the first read can differ on the second.
/// Refuted only for a **must-aliasing** re-fetch — a re-fetch of a *different* user
/// address (or a single fetch) does not fire, so there is no false FAIL.
#[test]
fn double_fetch_of_user_memory_is_refused() {
    let cfg = Config { bug_finding: true, ..Config::default() };
    let df = |name: &str, body: &str| -> Verdict {
        let src = format!(
            "declare i64 @copy_from_user(ptr, ptr, i64)\n\
             define void @{name}(ptr %u1, ptr %u2, ptr %k) {{\nentry:\n{body}  ret void\n}}\n"
        );
        let m = LlvmFrontend.lower(LlvmInput { source: src, name: name.into() }).expect("lower");
        verify_module(&m, &cfg).verdict
    };
    // Same user address fetched twice → double-fetch → FAIL.
    assert_eq!(
        df("dbl", "  %a = call i64 @copy_from_user(ptr %k, ptr %u1, i64 8)\n  \
                    %b = call i64 @copy_from_user(ptr %k, ptr %u1, i64 8)\n"),
        Verdict::Fail, "two copy_from_user from the same user address is a double-fetch"
    );
    // Distinct user addresses → not a double-fetch (no false FAIL).
    assert_ne!(
        df("dist", "  %a = call i64 @copy_from_user(ptr %k, ptr %u1, i64 8)\n  \
                     %b = call i64 @copy_from_user(ptr %k, ptr %u2, i64 8)\n"),
        Verdict::Fail, "distinct user addresses are not a double-fetch"
    );
}

/// **Sleep-in-atomic (G7).** A call that may sleep (`mutex_lock`/`schedule`/…) must not run
/// while a **spinlock is held** — it deadlocks or corrupts the scheduler. A per-path
/// structural typestate: a spinlock enters atomic context; a matched unlock (or any call
/// handed the lock base) leaves it; a *sleepable* mutex never enters it. Refuted only when a
/// spinlock is definitely held at the sleeping call (no false FAIL under a mutex-only hold).
#[test]
fn sleep_in_atomic_context_is_refused() {
    let cfg = Config { bug_finding: true, ..Config::default() };
    let sia = |name: &str, body: &str| -> Verdict {
        let src = format!(
            "declare void @spin_lock(ptr)\n\
             declare void @spin_unlock(ptr)\n\
             declare void @mutex_lock(ptr)\n\
             declare void @schedule()\n\
             define void @{name}(ptr %l, ptr %m) {{\nentry:\n{body}  ret void\n}}\n"
        );
        let m = LlvmFrontend.lower(LlvmInput { source: src, name: name.into() }).expect("lower");
        verify_module(&m, &cfg).verdict
    };
    // Blocking mutex_lock while a spinlock is held → sleep-in-atomic → FAIL.
    assert_eq!(
        sia("sleep_spin", "  call void @spin_lock(ptr %l)\n  call void @mutex_lock(ptr %m)\n"),
        Verdict::Fail, "a blocking mutex_lock while a spinlock is held is sleep-in-atomic"
    );
    // schedule() while a spinlock is held → FAIL.
    assert_eq!(
        sia("sched_spin", "  call void @spin_lock(ptr %l)\n  call void @schedule()\n"),
        Verdict::Fail, "schedule() while a spinlock is held is sleep-in-atomic"
    );
    // Spinlock released before the sleeping call → no atomic context → no fire.
    assert_ne!(
        sia("released", "  call void @spin_lock(ptr %l)\n  call void @spin_unlock(ptr %l)\n  \
                          call void @mutex_lock(ptr %m)\n"),
        Verdict::Fail, "a sleeping call after the spinlock is released is not sleep-in-atomic"
    );
    // Only a (sleepable) mutex held → sleeping is legal, not atomic context (no false FAIL).
    assert_ne!(
        sia("mutex_only", "  call void @mutex_lock(ptr %l)\n  call void @schedule()\n"),
        Verdict::Fail, "a sleeping call under a mutex-only hold is not sleep-in-atomic"
    );
}

/// **Directional taint lattice (injection J / info-flow, roadmap #3).** A value derived from
/// an untrusted source (`recv`/`copy_from_user`) must not reach an unsafe sink (`system`)
/// without a sanitiser. Exercises the whole pipeline: region taint-on-read → **scalar** taint
/// through arithmetic → store propagates taint back to a region → sink refutes; a recognised
/// sanitiser (`realpath`, result untainted) clears it; an untainted kernel buffer passes.
#[test]
fn tainted_value_reaching_an_unsafe_sink_is_refused() {
    let cfg = Config { bug_finding: true, ..Config::default() };
    let verdict = |name: &str, src: &str| -> Verdict {
        let m = LlvmFrontend.lower(LlvmInput { source: src.into(), name: name.into() }).expect("lower");
        verify_module(&m, &cfg).verdict
    };
    // Full scalar flow: recv taints buf; a byte is loaded (scalar taint-on-read), +1
    // (propagation), stored into kb2 (region taint), then system(kb2) — a tainted sink.
    let flow = r#"
declare i64 @recv(i32, ptr, i64, i32)
declare i32 @system(ptr)
define void @f(i32 %fd) {
  %buf = alloca [64 x i8], align 1
  %kb2 = alloca [64 x i8], align 1
  %r = call i64 @recv(i32 %fd, ptr %buf, i64 64, i32 0)
  %b = load i8, ptr %buf, align 1
  %b1 = add i8 %b, 1
  store i8 %b1, ptr %kb2, align 1
  %rc = call i32 @system(ptr %kb2)
  ret void
}
"#;
    assert_eq!(verdict("flow", flow), Verdict::Fail,
        "a user-tainted value flowing through arithmetic + memory into system() is refused");
    // A sanitiser (realpath → untainted result) clears the taint before the sink.
    let sanitized = r#"
declare i64 @recv(i32, ptr, i64, i32)
declare i32 @system(ptr)
declare ptr @realpath(ptr, ptr)
define void @f(i32 %fd, ptr %out) {
  %buf = alloca [64 x i8], align 1
  %r = call i64 @recv(i32 %fd, ptr %buf, i64 64, i32 0)
  %clean = call ptr @realpath(ptr %buf, ptr %out)
  %rc = call i32 @system(ptr %clean)
  ret void
}
"#;
    assert_ne!(verdict("san", sanitized), Verdict::Fail,
        "a sanitised value does not fire the tainted-sink check");
    // An untainted kernel pointer to a sink is fine (no source, no false FAIL).
    let clean = r#"
declare i32 @system(ptr)
define void @f(ptr %kbuf) {
  %rc = call i32 @system(ptr %kbuf)
  ret void
}
"#;
    assert_ne!(verdict("clean", clean), Verdict::Fail,
        "an untainted pointer to system() is not a tainted sink");
}
