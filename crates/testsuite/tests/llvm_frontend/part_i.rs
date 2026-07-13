use super::*;

/// **Cross-syscall use-after-close (typestate).** One entry (`sys_close`) closes the stream held by
/// a global (`fclose`), another entry (`sys_use`) operates on it (`fflush`, which forbids a closed
/// handle) — both reaching it through the same global root. Invoking close then use is a
/// use-after-close *across separate syscalls*: the typestate persists on the global handle, which
/// the per-function and interprocedural (call-graph) analyses cannot see (there is no call edge).
#[test]
fn cross_entry_use_after_close_typestate_is_detected() {
    let cfg = Config { bug_finding: true, ..Config::default() };
    let src = "\
        @stream = global ptr null, align 8\n\
        declare i32 @fclose(ptr)\ndeclare i32 @fflush(ptr)\n\
        define void @sys_close() {\n\
          %p = load ptr, ptr @stream, align 8\n  %r = call i32 @fclose(ptr %p)\n  ret void\n}\n\
        define void @sys_use() {\n\
          %p = load ptr, ptr @stream, align 8\n  %r = call i32 @fflush(ptr %p)\n  ret void\n}\n";
    let m = LlvmFrontend.lower(LlvmInput { source: src.into(), name: "cs".into() }).expect("lower");
    let ts = verify_module(&m, &cfg).cross_entry_typestate(|n| n.starts_with("sys_"));
    assert!(
        ts.iter().any(|w| w.location.contains("g:stream") && w.entries.0 == "sys_close"),
        "close-then-use across entries on a shared global stream is a cross-syscall use-after-close: {ts:?}"
    );
}

/// **Deferred reclamation beyond RCU.** Hazard pointers and epoch-based reclamation share RCU's
/// shape: an object retired/protected for lock-free readers must not be plain-`kfree`d until the
/// safe point (a hazard scan / epoch advance). The same `reclaim` typestate that guards RCU guards
/// these, so a retire-then-free without the safe point is refused; with it, it is safe.
#[test]
fn hazard_pointer_and_epoch_reclamation_are_guarded() {
    let cfg = Config { bug_finding: true, ..Config::default() };
    let verdict = |decls: &str, body: &str| -> Verdict {
        let src = format!(
            "declare void @kfree(ptr)\n{decls}\
             define void @f(ptr %n) {{\n{body}  ret void\n}}\n"
        );
        let m = LlvmFrontend.lower(LlvmInput { source: src, name: "h".into() }).expect("lower");
        verify_module(&m, &cfg).verdict
    };
    // Epoch: retire then free with no epoch advance → reader UAF.
    assert_eq!(
        verdict("declare void @ebr_retire(ptr)\n",
            "  call void @ebr_retire(ptr %n)\n  call void @kfree(ptr %n)\n"),
        Verdict::Fail, "freeing an epoch-retired node before the epoch advance is a violation"
    );
    // Epoch: retire, advance, then free → safe.
    assert_ne!(
        verdict("declare void @ebr_retire(ptr)\ndeclare void @ebr_advance()\n",
            "  call void @ebr_retire(ptr %n)\n  call void @ebr_advance()\n  call void @kfree(ptr %n)\n"),
        Verdict::Fail, "an epoch advance before the free is safe"
    );
    // Hazard pointers: protect then free with no scan → violation.
    assert_eq!(
        verdict("declare void @hazptr_protect(ptr)\n",
            "  call void @hazptr_protect(ptr %n)\n  call void @kfree(ptr %n)\n"),
        Verdict::Fail, "freeing a hazard-protected node before the scan is a violation"
    );
}

/// **Cross-thread use-after-free.** One function frees an object (`kfree`) while another
/// concurrently dereferences it, under *disjoint* locks — nothing orders the free before the
/// use, so it is a cross-thread UAF. A common lock orders them (no finding).
#[test]
fn cross_thread_use_after_free_is_detected() {
    let cfg = Config { bug_finding: true, ..Config::default() };
    let module = |la: &str, lb: &str| {
        let src = format!(
            "@obj = global ptr null, align 8\n@la = global i32 0\n@lb = global i32 0\n\
             declare void @spin_lock(ptr)\ndeclare void @spin_unlock(ptr)\ndeclare void @kfree(ptr)\n\
             define void @freer() {{\n  call void @spin_lock(ptr @{la})\n  \
               %p = load ptr, ptr @obj, align 8\n  call void @kfree(ptr %p)\n  \
               call void @spin_unlock(ptr @{la})\n  ret void\n}}\n\
             define i32 @user() {{\n  call void @spin_lock(ptr @{lb})\n  \
               %p = load ptr, ptr @obj, align 8\n  %v = load i32, ptr %p, align 4\n  \
               call void @spin_unlock(ptr @{lb})\n  ret i32 %v\n}}\n"
        );
        let m = LlvmFrontend.lower(LlvmInput { source: src, name: "u".into() }).expect("lower");
        verify_module(&m, &cfg)
    };
    // Disjoint locks → cross-thread UAF.
    let racy = module("la", "lb");
    assert_eq!(racy.cross_thread_uaf().len(), 1, "a concurrent free vs use under disjoint locks is a UAF");
    assert!(!racy.cross_thread_uaf()[0].double_free);
    // Same lock → ordered → no finding.
    assert!(module("la", "la").cross_thread_uaf().is_empty(), "a common lock orders free vs use");
}

/// **Userspace pthread data race (G1), lockset / Eraser.** The same Eraser lockset check works on
/// POSIX-threads code: a global written under a `pthread_mutex` in one function and read without
/// it in another is a candidate race; reading under the same mutex is consistent → not flagged.
/// This is the userspace-repurposing counterpart of the kernel `spin_lock` case.
#[test]
fn inconsistently_locked_global_is_a_race_with_pthread_mutex() {
    let cfg = Config { bug_finding: true, ..Config::default() };
    let module = |reader_body: &str| {
        let src = format!(
            "@counter = global i32 0, align 4\n@lk = global i64 0, align 8\n\
             declare void @pthread_mutex_lock(ptr)\ndeclare void @pthread_mutex_unlock(ptr)\n\
             define void @writer() {{\n  call void @pthread_mutex_lock(ptr @lk)\n  \
               store i32 1, ptr @counter, align 4\n  call void @pthread_mutex_unlock(ptr @lk)\n  ret void\n}}\n\
             define i32 @reader() {{\n{reader_body}}}\n"
        );
        let m = LlvmFrontend.lower(LlvmInput { source: src, name: "pt".into() }).expect("lower");
        verify_module(&m, &cfg)
    };
    let racy = module("  %v = load i32, ptr @counter, align 4\n  ret i32 %v\n");
    let races = racy.data_races();
    assert_eq!(races.len(), 1, "an unlocked read of a pthread_mutex-protected global is a race: {races:?}");
    assert_eq!(races[0].location, "g:counter@0");
    // Reader taking the same pthread_mutex → consistent lockset → no race.
    let safe = module("  call void @pthread_mutex_lock(ptr @lk)\n  %v = load i32, ptr @counter, align 4\n  \
                        call void @pthread_mutex_unlock(ptr @lk)\n  ret i32 %v\n");
    assert!(safe.data_races().is_empty(), "a consistently pthread_mutex-locked global is not flagged");
}

/// **Data race (G1), lockset / Eraser.** A global written under a lock in one function and
/// accessed without that lock in another is a candidate race (inconsistent lockset, a write,
/// two functions). Consistent locking on every access is not flagged (no false positive).
#[test]
fn inconsistently_locked_global_is_a_candidate_race() {
    let cfg = Config { bug_finding: true, ..Config::default() };
    let module = |reader_body: &str| {
        let src = format!(
            "@counter = global i32 0, align 4\n@lk = global i32 0, align 4\n\
             declare void @spin_lock(ptr)\ndeclare void @spin_unlock(ptr)\n\
             define void @writer() {{\n  call void @spin_lock(ptr @lk)\n  \
               store i32 1, ptr @counter, align 4\n  call void @spin_unlock(ptr @lk)\n  ret void\n}}\n\
             define i32 @reader() {{\n{reader_body}}}\n"
        );
        let m = LlvmFrontend.lower(LlvmInput { source: src, name: "r".into() }).expect("lower");
        verify_module(&m, &cfg)
    };
    // Reader without the lock → inconsistent lockset → candidate race.
    let racy = module("  %v = load i32, ptr @counter, align 4\n  ret i32 %v\n");
    let races = racy.data_races();
    assert_eq!(races.len(), 1, "an unlocked read of a lock-protected global is a candidate race: {races:?}");
    assert_eq!(races[0].location, "g:counter@0");
    assert_eq!(races[0].functions, vec!["reader".to_string(), "writer".to_string()]);
    // Reader with the same lock → consistent → no race.
    let safe = module("  call void @spin_lock(ptr @lk)\n  %v = load i32, ptr @counter, align 4\n  \
                        call void @spin_unlock(ptr @lk)\n  ret i32 %v\n");
    assert!(safe.data_races().is_empty(), "a consistently-locked global is not flagged");
    // Hardening: a `volatile`/`atomic` reader (READ_ONCE) is race-free by construction — even
    // with a disjoint lockset it is not flagged.
    let atomic = module("  %v = load volatile i32, ptr @counter, align 4\n  ret i32 %v\n");
    assert!(atomic.data_races().is_empty(), "an atomic/volatile access is not a data race");
}

/// **Data-race hardening: RCU read-side.** A reader inside an RCU read-side critical section
/// (`rcu_read_lock`…`rcu_read_unlock`) is race-free with a concurrent updater by the RCU
/// contract — so an unlocked RCU read of a lock-written global is not flagged, while the same
/// read *without* RCU is.
#[test]
fn rcu_protected_read_is_not_a_data_race() {
    let cfg = Config { bug_finding: true, ..Config::default() };
    let module = |reader_body: &str| {
        let src = format!(
            "@shared = global i32 0, align 4\n@lk = global i32 0, align 4\n\
             declare void @spin_lock(ptr)\ndeclare void @spin_unlock(ptr)\n\
             declare void @rcu_read_lock()\ndeclare void @rcu_read_unlock()\n\
             define void @writer() {{\n  call void @spin_lock(ptr @lk)\n  \
               store i32 1, ptr @shared, align 4\n  call void @spin_unlock(ptr @lk)\n  ret void\n}}\n\
             define i32 @reader() {{\n{reader_body}}}\n"
        );
        let m = LlvmFrontend.lower(LlvmInput { source: src, name: "r".into() }).expect("lower");
        verify_module(&m, &cfg)
    };
    // Reader under RCU → race-free by the RCU contract.
    let rcu = module("  call void @rcu_read_lock()\n  %v = load i32, ptr @shared, align 4\n  \
                      call void @rcu_read_unlock()\n  ret i32 %v\n");
    assert!(rcu.data_races().is_empty(), "an RCU read-side access is not flagged");
    // The same read without RCU → flagged (control).
    let plain = module("  %v = load i32, ptr @shared, align 4\n  ret i32 %v\n");
    assert_eq!(plain.data_races().len(), 1, "the same read without RCU is a candidate race");
}

/// **The remaining typestate/taint classes (TOCTOU G2, refcount G8, leak K, type-confusion H,
/// secret side-channel L).** All contract-driven on the general typestate + taint engines.
#[test]
fn toctou_refcount_leak_typeconfusion_and_secret_are_refused() {
    let cfg = Config { bug_finding: true, ..Config::default() };
    let decls = "declare i32 @access(ptr, i32)\ndeclare void @schedule()\ndeclare i32 @open(ptr, i32)\n\
                 declare void @kref_get(ptr)\ndeclare void @kref_put(ptr)\n\
                 declare ptr @fopen(ptr, ptr)\ndeclare i32 @fclose(ptr)\n\
                 declare void @init_as_request(ptr)\ndeclare void @handle_request(ptr)\n\
                 declare i64 @load_secret_key(ptr)\n";
    let v = |sig: &str, body: &str| -> Verdict {
        let src = format!("{decls}define {sig} {{\n{body}}}\n");
        let m = LlvmFrontend.lower(LlvmInput { source: src, name: "t".into() }).expect("lower");
        verify_module(&m, &cfg).verdict
    };
    // G2 TOCTOU: check → yield (schedule) → use is a race; no yield is fine.
    assert_eq!(v("void @f(ptr %p)",
        "  %c = call i32 @access(ptr %p, i32 0)\n  call void @schedule()\n  \
           %o = call i32 @open(ptr %p, i32 0)\n  ret void\n"),
        Verdict::Fail, "check→yield→use is a TOCTOU race");
    assert_ne!(v("void @f(ptr %p)",
        "  %c = call i32 @access(ptr %p, i32 0)\n  %o = call i32 @open(ptr %p, i32 0)\n  ret void\n"),
        Verdict::Fail, "check→use with no yield is fine");
    // G8 refcount underflow: a get establishes the count, two puts drop it below zero.
    assert_eq!(v("void @f(ptr %o)", "  call void @kref_get(ptr %o)\n  \
                  call void @kref_put(ptr %o)\n  call void @kref_put(ptr %o)\n  ret void\n"),
        Verdict::Fail, "a put below an in-scope get is an underflow");
    // A balanced get/put is fine; and a bare put on a parameter (the caller holds the ref, unknown
    // count) is NOT an underflow — sound, no false positive on a plain drop helper.
    assert_ne!(v("void @f(ptr %o)", "  call void @kref_get(ptr %o)\n  call void @kref_put(ptr %o)\n  ret void\n"),
        Verdict::Fail, "a balanced get/put is fine");
    assert_ne!(v("void @f(ptr %o)", "  call void @kref_put(ptr %o)\n  ret void\n"),
        Verdict::Fail, "a bare put on a parameter is not an underflow (caller holds it)");
    // K leak: an open handle neither closed nor returned.
    assert_eq!(v("void @f(ptr %p, ptr %m)", "  %h = call ptr @fopen(ptr %p, ptr %m)\n  ret void\n"),
        Verdict::Fail, "an unclosed, unreturned FILE* is a leak");
    assert_ne!(v("void @f(ptr %p, ptr %m)",
        "  %h = call ptr @fopen(ptr %p, ptr %m)\n  %r = call i32 @fclose(ptr %h)\n  ret void\n"),
        Verdict::Fail, "a closed handle is not a leak");
    // H type confusion: a typed op on an object of the wrong (unset) type.
    assert_eq!(v("void @f(ptr %o)", "  call void @handle_request(ptr %o)\n  ret void\n"),
        Verdict::Fail, "a typed op on a mis-typed object is type confusion");
    assert_ne!(v("void @f(ptr %o)", "  call void @init_as_request(ptr %o)\n  call void @handle_request(ptr %o)\n  ret void\n"),
        Verdict::Fail, "a correctly-typed object passes");
    // L secret side-channel: a branch on a secret-derived value.
    assert_eq!(v("i32 @f(ptr %k)",
        "  %r = call i64 @load_secret_key(ptr %k)\n  %b = load i8, ptr %k, align 1\n  \
           %c = icmp ne i8 %b, 0\n  br i1 %c, label %t, label %e\n\
         t:\n  ret i32 1\ne:\n  ret i32 0\n"),
        Verdict::Fail, "branching on a secret-derived value is a timing side channel");
}

/// **Generalised typestate tracker (use-after-close B / missing-check E, roadmap #4).** A
/// contract-driven per-resource protocol: `fopen`→`file.open`, `fclose`→`file.closed` and
/// refuses a closed handle; a `fread`/second `fclose` on a closed handle is refused
/// (use-after-close / double-close). A separate `perm` protocol: a `security_check` marks an
/// object checked, and `privileged_write` requires it — a missing check is refused. Correct
/// orderings pass (no false FAIL).
#[test]
fn typestate_protocol_violations_are_refused() {
    let cfg = Config { bug_finding: true, ..Config::default() };
    let decls = "declare ptr @fopen(ptr, ptr)\ndeclare i32 @fclose(ptr)\n\
                 declare i64 @fread(ptr, i64, i64, ptr)\n\
                 declare void @privileged_write(ptr)\ndeclare void @security_check(ptr)\n";
    let verdict = |name: &str, body: &str| -> Verdict {
        let src = format!("{decls}define void @{name}(ptr %path, ptr %mode, ptr %buf, ptr %obj) {{\n{body}  ret void\n}}\n");
        let m = LlvmFrontend.lower(LlvmInput { source: src, name: name.into() }).expect("lower");
        verify_module(&m, &cfg).verdict
    };
    // Double-close → violation.
    assert_eq!(
        verdict("dc", "  %f = call ptr @fopen(ptr %path, ptr %mode)\n  \
                        %a = call i32 @fclose(ptr %f)\n  %b = call i32 @fclose(ptr %f)\n"),
        Verdict::Fail, "closing an already-closed handle is a double-close"
    );
    // Use-after-close (fread after fclose) → violation.
    assert_eq!(
        verdict("uac", "  %f = call ptr @fopen(ptr %path, ptr %mode)\n  \
                         %a = call i32 @fclose(ptr %f)\n  \
                         %n = call i64 @fread(ptr %buf, i64 1, i64 16, ptr %f)\n"),
        Verdict::Fail, "reading a closed handle is use-after-close"
    );
    // Correct open → read → close order: no violation.
    assert_ne!(
        verdict("ok", "  %f = call ptr @fopen(ptr %path, ptr %mode)\n  \
                        %n = call i64 @fread(ptr %buf, i64 1, i64 16, ptr %f)\n  \
                        %a = call i32 @fclose(ptr %f)\n"),
        Verdict::Fail, "open→read→close is a correct protocol run"
    );
    // Missing permission check → violation.
    assert_eq!(
        verdict("mc", "  call void @privileged_write(ptr %obj)\n"),
        Verdict::Fail, "a privileged op on an unchecked resource is a missing-check"
    );
    // Checked before use: no violation.
    assert_ne!(
        verdict("chk", "  call void @security_check(ptr %obj)\n  call void @privileged_write(ptr %obj)\n"),
        Verdict::Fail, "a checked resource passes the privileged op"
    );
}

/// **ABBA lock-order cycle (G6).** Two functions acquire two locks (two fields of the
/// same struct type, so two stable cross-function *classes*) in the **opposite order**:
/// `f` takes field-0 then field-1, `g` takes field-1 then field-0. The whole-program
/// lock-order graph then has edges `S@0→S@8` and `S@8→S@0` — a 2-cycle, a potential ABBA
/// **Seqlock writers are locks.** `write_seqlock` mutually excludes writers, so it participates
/// in lock-order analysis exactly like a spinlock: taking a spinlock while holding a seqlock in
/// one path and the opposite order in another is an ABBA cycle.
#[test]
fn seqlock_writer_participates_in_lock_order() {
    let cfg = Config { bug_finding: true, ..Config::default() };
    let src = "\
        @sl = global i32 0\n@sp = global i32 0\n\
        declare void @write_seqlock(ptr)\ndeclare void @write_sequnlock(ptr)\n\
        declare void @spin_lock(ptr)\ndeclare void @spin_unlock(ptr)\n\
        define void @writer() {\n\
          call void @write_seqlock(ptr @sl)\n  call void @spin_lock(ptr @sp)\n\
          call void @spin_unlock(ptr @sp)\n  call void @write_sequnlock(ptr @sl)\n  ret void\n}\n\
        define void @other() {\n\
          call void @spin_lock(ptr @sp)\n  call void @write_seqlock(ptr @sl)\n\
          call void @write_sequnlock(ptr @sl)\n  call void @spin_unlock(ptr @sp)\n  ret void\n}\n";
    let m = LlvmFrontend.lower(LlvmInput { source: src.into(), name: "sq".into() }).expect("lower");
    let cycles = verify_module(&m, &cfg).lock_order_cycles();
    assert_eq!(cycles.len(), 1, "seqlock-vs-spinlock opposite order is an ABBA cycle: {cycles:?}");
}

/// deadlock. Distinct objects (`%x`/`%y`) are used so the base identities differ (no AA
/// self-deadlock false positive). A consistent order (both `f`-style) has no cycle.
#[test]
fn abba_lock_order_cycle_is_detected() {
    let cfg = Config { bug_finding: true, ..Config::default() };
    let module = |gbody: &str| -> csolver_verifier::ModuleReport {
        let src = format!(
            "%s = type {{ i64, i64 }}\n\
             declare void @spin_lock(ptr)\n\
             declare void @spin_unlock(ptr)\n\
             define void @f(ptr %x, ptr %y) {{\n\
               %a = getelementptr %s, ptr %x, i32 0, i32 0\n\
               %b = getelementptr %s, ptr %y, i32 0, i32 1\n\
               call void @spin_lock(ptr %a)\n\
               call void @spin_lock(ptr %b)\n\
               call void @spin_unlock(ptr %b)\n\
               call void @spin_unlock(ptr %a)\n\
               ret void\n\
             }}\n\
             define void @g(ptr %x, ptr %y) {{\n{gbody}  ret void\n}}\n"
        );
        let m = LlvmFrontend.lower(LlvmInput { source: src, name: "lo".into() }).expect("lower");
        verify_module(&m, &cfg)
    };
    // Opposite order in g → ABBA cycle.
    let abba = module(
        "  %b = getelementptr %s, ptr %y, i32 0, i32 1\n  \
           %a = getelementptr %s, ptr %x, i32 0, i32 0\n  \
           call void @spin_lock(ptr %b)\n  call void @spin_lock(ptr %a)\n  \
           call void @spin_unlock(ptr %a)\n  call void @spin_unlock(ptr %b)\n",
    );
    let cycles = abba.lock_order_cycles();
    assert_eq!(cycles.len(), 1, "an opposite lock-acquire order is an ABBA cycle: {cycles:?}");
    assert_eq!(cycles[0].classes.len(), 2, "the cycle has two lock classes");
    // Same order in g → no cycle.
    let consistent = module(
        "  %a = getelementptr %s, ptr %x, i32 0, i32 0\n  \
           %b = getelementptr %s, ptr %y, i32 0, i32 1\n  \
           call void @spin_lock(ptr %a)\n  call void @spin_lock(ptr %b)\n  \
           call void @spin_unlock(ptr %b)\n  call void @spin_unlock(ptr %a)\n",
    );
    assert!(consistent.lock_order_cycles().is_empty(), "a consistent lock order is not a cycle");
}

/// **A loop-guarded foreign write is refused, not left spurious-UNKNOWN.** The AAD copy
/// in the real crypto worker sits behind a `br` whose condition is loop-carried; such a
/// condition can reach the executor wider than `i1`, and using it directly as a boolean
/// guard is unencodable — which made the whole path condition spuriously UNSAT, so the
/// (real) capability violation was recorded UNKNOWN instead of refuted. Coercing a
/// non-`i1` condition to `c != 0` (LLVM truthiness) fixes it: the write of a `foreign`
/// page behind a loop-carried guard now FAILs.
#[test]
fn loop_guarded_foreign_write_is_refused() {
    let src = r#"
declare void @af_alg_sendpage(ptr, ptr)
declare i32 @crypto_aead_copy_sgl(ptr, ptr, ptr, i32)
declare i1 @more()
define void @f(ptr %sk, ptr %tfm, ptr %src, ptr %foreign) {
entry:
  call void @af_alg_sendpage(ptr %sk, ptr %foreign)
  br label %loop
loop:
  %i = phi i32 [ 0, %entry ], [ %ni, %latch ]
  %c = call i1 @more()
  br i1 %c, label %write, label %exit
write:
  %r = call i32 @crypto_aead_copy_sgl(ptr %tfm, ptr %src, ptr %foreign, i32 16)
  br label %latch
latch:
  %ni = add i32 %i, 1
  br label %loop
exit:
  ret void
}
"#;
    let cfg = Config { bug_finding: true, ..Config::default() };
    let m = LlvmFrontend.lower(LlvmInput { source: src.into(), name: "l".into() }).expect("lower");
    assert_eq!(verify_module(&m, &cfg).verdict, Verdict::Fail,
        "a foreign write behind a loop-carried guard must be refused, not spurious-UNKNOWN");
}

/// **Provenance flows through a `switch` (mem2reg critical-edge splitting).** A `foreign`
/// pointer is stored to a stack slot, the CFG passes through a `switch` whose default edge
/// targets a multi-predecessor block, and the slot is reloaded past it and written via the
/// AAD-copy sink. Only if mem2reg promotes the slot — which needs a PHI on the critical
/// switch edge, enabled by edge-splitting — does the `foreign` label survive the switch and
/// reach the destination, so the write-capability gate fires. This is the real crypto
/// worker's shape (a request pointer reloaded across a switch) in miniature.
#[test]
fn provenance_flows_through_a_switch() {
    let src = r#"
declare void @af_alg_sendpage(ptr, ptr)
declare i32 @crypto_aead_copy_sgl(ptr, ptr, ptr, i32)
declare i32 @pick()
define void @f(ptr %sk, ptr %tfm, ptr %src, ptr %foreign) {
entry:
  %slot = alloca ptr, align 8
  call void @af_alg_sendpage(ptr %sk, ptr %foreign)
  store ptr %foreign, ptr %slot, align 8
  %sel = call i32 @pick()
  switch i32 %sel, label %merge [i32 0, label %c0]
c0:
  store ptr %foreign, ptr %slot, align 8
  br label %merge
merge:
  %q = load ptr, ptr %slot, align 8
  %r = call i32 @crypto_aead_copy_sgl(ptr %tfm, ptr %src, ptr %q, i32 16)
  ret void
}
"#;
    let cfg = Config { bug_finding: true, ..Config::default() };
    let m = LlvmFrontend.lower(LlvmInput { source: src.into(), name: "s".into() }).expect("lower");
    assert_eq!(verify_module(&m, &cfg).verdict, Verdict::Fail,
        "the foreign label must survive the switch (slot promoted via edge-splitting) and \
         fire the AAD-copy write-capability gate");
}

/// **The AAD-copy sink (CVE-2026-31431).** The Copy-Fail bug is the in-place copy of the
/// *associated data*: `crypto_aead_copy_sgl(null_tfm, src, dst, len)` writes `dst`, which
/// in the vulnerable build is the socket's RX scatterlist and may hold a `foreign`
/// (read-only, spliced-in) page. The contract requires `dst` (arg2) to grant `write`; a
/// `foreign` dst provably lacks it → refused. A non-foreign dst (the patched out-of-place
/// copy, into a fresh writable buffer) does not fire — no false FAIL.
#[test]
fn aad_copy_to_foreign_destination_is_refused() {
    let cfg = Config { bug_finding: true, ..Config::default() };
    // Vulnerable: the dst was labelled `foreign` (a page spliced in) → refused.
    let vuln = r#"
declare void @af_alg_sendpage(ptr, ptr)
declare i32 @crypto_aead_copy_sgl(ptr, ptr, ptr, i32)
define void @f(ptr %sk, ptr %tfm, ptr %src, ptr %dst) {
  call void @af_alg_sendpage(ptr %sk, ptr %dst)
  %r = call i32 @crypto_aead_copy_sgl(ptr %tfm, ptr %src, ptr %dst, i32 16)
  ret void
}
"#;
    let m = LlvmFrontend.lower(LlvmInput { source: vuln.into(), name: "v".into() }).expect("lower");
    assert_eq!(verify_module(&m, &cfg).verdict, Verdict::Fail,
        "AAD copy into a foreign destination is refused (Copy-Fail)");
    // Control: an unlabelled (writable) dst — the patched out-of-place copy — does not fire.
    let ok = r#"
declare i32 @crypto_aead_copy_sgl(ptr, ptr, ptr, i32)
define void @f(ptr %tfm, ptr %src, ptr %dst) {
  %r = call i32 @crypto_aead_copy_sgl(ptr %tfm, ptr %src, ptr %dst, i32 16)
  ret void
}
"#;
    let m = LlvmFrontend.lower(LlvmInput { source: ok.into(), name: "o".into() }).expect("lower");
    assert_ne!(verify_module(&m, &cfg).verdict, Verdict::Fail,
        "AAD copy into a non-foreign destination does not fire — no false FAIL");
}

/// **`dereferenceable(N)` sizes a global authoritatively.** A call-site
/// `dereferenceable(N)` on a bare `@g` operand is clang's byte-size guarantee for the
/// global (derived from its type), so it corrects a size our own type-layout computation
/// gets wrong (e.g. a 1-byte packed-struct discrepancy that would otherwise refute an
/// exactly-sized `memcpy` into the global). Here the global's *declared* type is 1 byte,
/// yet a `memcpy` of 8 asserts `dereferenceable(8)` — with the hint the copy is in bounds;
/// without any hint an over-sized copy is (soundly) refuted.
#[test]
fn dereferenceable_hint_sizes_a_global() {
    let with_hint = r#"
@g = external global i8
@s = internal constant [8 x i8] zeroinitializer
define void @f() {
  call void @llvm.memcpy.p0.p0.i64(ptr dereferenceable(8) @g, ptr @s, i64 8, i1 false)
  ret void
}
declare void @llvm.memcpy.p0.p0.i64(ptr, ptr, i64, i1)
"#;
    let cfg = Config { bug_finding: true, ..Config::default() };
    let m = LlvmFrontend.lower(LlvmInput { source: with_hint.into(), name: "h".into() }).expect("lower");
    assert_ne!(verify_module(&m, &cfg).verdict, Verdict::Fail,
        "dereferenceable(8) sizes @g to 8 bytes → the 8-byte memcpy is in bounds");
    // Control: no dereferenceable hint, a 1-byte-typed global, an 8-byte copy → refuted.
    let no_hint = with_hint.replace("dereferenceable(8) ", "");
    let m = LlvmFrontend.lower(LlvmInput { source: no_hint, name: "n".into() }).expect("lower");
    assert_eq!(verify_module(&m, &cfg).verdict, Verdict::Fail,
        "without a hint an 8-byte copy into a 1-byte global is refuted");
}
