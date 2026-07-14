use super::*;

/// **Atomicity violation via two-thread interleaving (subsystem 4 — a genuine second
/// timeline).** A read-modify-write of a global split across *two* critical sections: every
/// access holds the lock, so the lockset (Eraser) pass sees **no** race — yet another
/// function's write can interleave in the gap between the read and the dependent write, a lost
/// update. The interleaving product finds it with a witness; the lockset pass does not.
#[test]
fn split_critical_section_rmw_is_an_atomicity_violation() {
    let cfg = Config { bug_finding: true, ..Config::default() };
    let src = r#"
@counter = global i32 0, align 4
@L = global i32 0, align 4
declare void @spin_lock(ptr)
declare void @spin_unlock(ptr)
declare void @work()
define void @incrementer() {
  call void @spin_lock(ptr @L)
  %t = load i32, ptr @counter, align 4
  call void @spin_unlock(ptr @L)
  call void @work()
  call void @spin_lock(ptr @L)
  %n = add i32 %t, 1
  store i32 %n, ptr @counter, align 4
  call void @spin_unlock(ptr @L)
  ret void
}
define void @resetter() {
  call void @spin_lock(ptr @L)
  store i32 0, ptr @counter, align 4
  call void @spin_unlock(ptr @L)
  ret void
}
"#;
    let m = LlvmFrontend.lower(LlvmInput { source: src.into(), name: "a".into() }).expect("lower");
    let report = verify_module(&m, &cfg);
    // The lockset pass is silent — `counter` is consistently locked.
    assert!(report.data_races().is_empty(), "consistent locking → no lockset race");
    // The interleaving product finds the lost update, with a witness.
    let v = report.atomicity_violations();
    assert_eq!(v.len(), 1, "a split-critical-section RMW is an atomicity violation: {v:?}");
    assert_eq!(v[0].location, "g:counter@0");
    // The witness schedules the resetter's write between the incrementer's read and write.
    use csolver_verifier::interleave::Event;
    let sched = &v[0].schedule;
    let inc_read = sched.iter().position(|(n, e)| n == "incrementer" && matches!(e, Event::Read(_))).unwrap();
    // The resetter's `counter = 0` is an *independent* (constant) write → plain `Write`; the
    // incrementer's `counter = t + 1` derives from the load → a dependent `Rmw` (the lost update).
    let res_write = sched.iter().position(|(n, e)| n == "resetter" && matches!(e, Event::Write(_))).unwrap();
    let inc_write = sched.iter().position(|(n, e)| n == "incrementer" && matches!(e, Event::Rmw(_))).unwrap();
    assert!(inc_read < res_write && res_write < inc_write, "witness realises read < foreign-write < write");
}

/// **Store-buffer / missing-barrier weak-memory bug (subsystem 4, weak memory).** Two threads
/// each write one flag and then read the other's, with no barrier between — under a weak memory
/// model (TSO/ARM) both reads may observe the stale value, an outcome sequential consistency
/// forbids (the Dekker / store-buffer litmus). A barrier (`smp_mb`) between the write and read
/// in both threads fixes it — the detector is barrier-aware.
#[test]
fn store_buffer_without_barrier_is_a_weak_memory_bug() {
    let cfg = Config { bug_finding: true, ..Config::default() };
    let module = |mid: &str| {
        let src = format!(
            "@x = global i32 0, align 4\n@y = global i32 0, align 4\ndeclare void @smp_mb()\n\
             define i32 @t1() {{\n  store i32 1, ptr @x, align 4\n{mid}  \
               %v = load i32, ptr @y, align 4\n  ret i32 %v\n}}\n\
             define i32 @t2() {{\n  store i32 1, ptr @y, align 4\n{mid}  \
               %v = load i32, ptr @x, align 4\n  ret i32 %v\n}}\n"
        );
        let m = LlvmFrontend.lower(LlvmInput { source: src, name: "sb".into() }).expect("lower");
        verify_module(&m, &cfg)
    };
    // No barrier → the store-buffer litmus is a weak-memory bug.
    let bad = module("");
    assert_eq!(bad.store_buffer_bugs().len(), 1, "store-buffer with no barrier is a weak-memory bug");
    // A full barrier between each write and read forbids the reordering.
    let good = module("  call void @smp_mb()\n");
    assert!(good.store_buffer_bugs().is_empty(), "an smp_mb barrier fixes the store-buffer bug");
}

/// **Message-passing / publish (operational weak-memory model, subsystem 4 — full semantics).**
/// A producer writes `data` then `flag`; a consumer reads `flag` then `data`. Under the PSO
/// store-buffer model the producer's two writes can become visible out of order, so the consumer
/// can observe `flag=set` but `data=stale` — an outcome no sequentially-consistent execution
/// allows (non-robust). The **write barrier** `smp_wmb` between the two publishes fixes it. This
/// is the case the syntactic store-buffer (W→R) check does not catch — it needs the operational
/// model.
#[test]
fn message_passing_without_wmb_is_a_weak_memory_bug() {
    let cfg = Config { bug_finding: true, ..Config::default() };
    // `pbar` goes between the producer's two writes, `cbar` between the consumer's two reads.
    let module = |pbar: &str, cbar: &str| {
        let src = format!(
            "@data = global i32 0, align 4\n@flag = global i32 0, align 4\n\
             declare void @smp_wmb()\ndeclare void @smp_rmb()\n\
             define void @producer() {{\n  store i32 42, ptr @data, align 4\n{pbar}  \
               store i32 1, ptr @flag, align 4\n  ret void\n}}\n\
             define i32 @consumer() {{\n  %f = load i32, ptr @flag, align 4\n{cbar}  \
               %d = load i32, ptr @data, align 4\n  ret i32 %d\n}}\n"
        );
        let m = LlvmFrontend.lower(LlvmInput { source: src, name: "mp".into() }).expect("lower");
        verify_module(&m, &cfg)
    };
    // No barriers → the publish can be observed out of order (non-SC-robust).
    let bad = module("", "");
    assert_eq!(bad.weak_memory_bugs().len(), 1, "message passing with no barriers is not SC-robust");
    // The syntactic store-buffer (W→R) check does NOT catch this (it is a W→W / R→R reorder).
    assert!(bad.store_buffer_bugs().is_empty(), "MP is not a store-buffer (W->R) shape");
    // A write barrier alone is not enough — the consumer's reads still reorder (ARM R→R).
    let wmb_only = module("  call void @smp_wmb()\n", "");
    assert_eq!(wmb_only.weak_memory_bugs().len(), 1, "smp_wmb alone leaves the consumer R->R reorder");
    // Both a write barrier (producer) and a read barrier (consumer) restore robustness.
    let good = module("  call void @smp_wmb()\n", "  call void @smp_rmb()\n");
    assert!(good.weak_memory_bugs().is_empty(), "smp_wmb + smp_rmb fix the publish protocol");
}

/// The **combined** release/acquire calls (`smp_store_release`/`smp_load_acquire`) now carry
/// the flag access, not just the fence — so the message-passing handoff is modelled from one
/// call. Both together are robust (the negative control: the added flag access must not
/// fabricate a bug), but a release publish read by a *plain* load (a missing acquire) is a real
/// R→R-reorder bug that was invisible before (the producer never modelled the flag write).
#[test]
fn release_acquire_calls_model_the_flag_and_catch_a_missing_acquire() {
    let cfg = Config { bug_finding: true, ..Config::default() };
    let module = |consumer_load: &str| {
        let src = format!(
            "@data = global i32 0, align 4\n@flag = global i32 0, align 4\n\
             declare void @smp_store_release(ptr, i32)\ndeclare i32 @smp_load_acquire(ptr)\n\
             define void @producer() {{\n  store i32 42, ptr @data, align 4\n  \
               call void @smp_store_release(ptr @flag, i32 1)\n  ret void\n}}\n\
             define i32 @consumer() {{\n  {consumer_load}  \
               %d = load i32, ptr @data, align 4\n  ret i32 %d\n}}\n"
        );
        let m = LlvmFrontend.lower(LlvmInput { source: src, name: "ra".into() }).expect("lower");
        verify_module(&m, &cfg)
    };
    // Release publish + acquire consume → ordered on both sides → robust (no false bug from
    // the newly-modelled flag access).
    let good = module("%f = call i32 @smp_load_acquire(ptr @flag)\n");
    assert!(good.weak_memory_bugs().is_empty(), "release + acquire is SC-robust");
    // Release publish + a PLAIN load of the flag (no acquire) → the consumer's two reads
    // reorder (ARM R→R), so it can see the flag set but the data stale — a real bug now that
    // the producer's release models the flag write.
    let bad = module("%f = load i32, ptr @flag, align 4\n");
    assert_eq!(bad.weak_memory_bugs().len(), 1, "a release read by a plain load misses the acquire barrier");
}

/// **Happens-before via thread create/join (operational weak memory).** A store-buffer shape is
/// a weak-memory bug when the two functions run concurrently — but not when one is `pthread_create`d
/// and `pthread_join`ed by the other: the join orders the child before the parent's later read.
#[test]
fn spawn_join_happens_before_removes_the_weak_memory_bug() {
    let cfg = Config { bug_finding: true, ..Config::default() };
    // Concurrent store-buffer: a weak-memory bug.
    let concurrent = r#"
@x = global i32 0, align 4
@y = global i32 0, align 4
define i32 @child() {
  store i32 1, ptr @y, align 4
  %v = load i32, ptr @x, align 4
  ret i32 %v
}
define i32 @a() {
  store i32 1, ptr @x, align 4
  %v = load i32, ptr @y, align 4
  ret i32 %v
}
"#;
    let m = LlvmFrontend.lower(LlvmInput { source: concurrent.into(), name: "c".into() }).expect("lower");
    assert_eq!(verify_module(&m, &cfg).weak_memory_bugs().len(), 1, "concurrent SB is a weak-memory bug");
    // The parent spawns and joins the child → happens-before orders them → no bug.
    let ordered = r#"
@x = global i32 0, align 4
@y = global i32 0, align 4
declare i32 @pthread_create(ptr, ptr, ptr, ptr)
declare i32 @pthread_join(ptr, ptr)
define i32 @child() {
  store i32 1, ptr @y, align 4
  %v = load i32, ptr @x, align 4
  ret i32 %v
}
define i32 @a(ptr %t, ptr %attr, ptr %arg) {
  store i32 1, ptr @x, align 4
  %r = call i32 @pthread_create(ptr %t, ptr %attr, ptr @child, ptr %arg)
  %j = call i32 @pthread_join(ptr %t, ptr null)
  %v = load i32, ptr @y, align 4
  ret i32 %v
}
"#;
    let m = LlvmFrontend.lower(LlvmInput { source: ordered.into(), name: "o".into() }).expect("lower");
    assert!(verify_module(&m, &cfg).weak_memory_bugs().is_empty(),
        "a spawned-then-joined child is ordered by happens-before — no weak-memory bug");
}

/// **Address dependency (`rcu_dereference` pointer-chase, operational weak memory).** A
/// consumer that reads a published pointer and then dereferences it (`p = load gp; v = load *p`)
/// has an **address dependency** — the second load is ordered after the first, so a write
/// barrier on the producer alone makes the publish robust (no read barrier needed). A consumer
/// reading a *separate* location still needs a read barrier.
#[test]
fn address_dependency_needs_no_read_barrier() {
    let cfg = Config { bug_finding: true, ..Config::default() };
    // Pointer-chase consumer: `%p = load @gp; %v = load %p` — the second load is address-dependent.
    let dep = r#"
@gp = global ptr null, align 8
@obj = global i32 0, align 4
declare void @smp_wmb()
define void @producer() {
  store i32 42, ptr @obj, align 4
  call void @smp_wmb()
  store ptr @obj, ptr @gp, align 8
  ret void
}
define i32 @consumer() {
  %p = load ptr, ptr @gp, align 8
  %v = load i32, ptr %p, align 4
  ret i32 %v
}
"#;
    let m = LlvmFrontend.lower(LlvmInput { source: dep.into(), name: "d".into() }).expect("lower");
    assert!(verify_module(&m, &cfg).weak_memory_bugs().is_empty(),
        "an address-dependent consumer read is ordered — smp_wmb alone suffices");
}

/// **IRIW — Independent Reads of Independent Writes (operational weak memory, >2 threads).** A
/// **four-thread** litmus needing non-multi-copy-atomicity: two writers to `x` and `y`, two
/// readers observing them in opposite orders. No pair exhibits it — the whole-program group
/// product does. Full barriers between each reader's two reads restore robustness.
#[test]
fn iriw_is_a_weak_memory_bug() {
    let cfg = Config { bug_finding: true, ..Config::default() };
    let module = |rbar: &str| {
        let src = format!(
            "@x = global i32 0, align 4\n@y = global i32 0, align 4\ndeclare void @smp_mb()\n\
             define void @w1() {{\n  store i32 1, ptr @x, align 4\n  ret void\n}}\n\
             define void @w2() {{\n  store i32 1, ptr @y, align 4\n  ret void\n}}\n\
             define i32 @r1() {{\n  %a = load i32, ptr @x, align 4\n{rbar}  \
               %b = load i32, ptr @y, align 4\n  ret i32 %b\n}}\n\
             define i32 @r2() {{\n  %a = load i32, ptr @y, align 4\n{rbar}  \
               %b = load i32, ptr @x, align 4\n  ret i32 %b\n}}\n"
        );
        let m = LlvmFrontend.lower(LlvmInput { source: src, name: "iriw".into() }).expect("lower");
        verify_module(&m, &cfg)
    };
    // No barriers → IRIW is observable (non-SC-robust) — a 4-thread group product finds it.
    let bad = module("");
    assert_eq!(bad.weak_memory_bugs().len(), 1, "IRIW is not SC-robust under non-MCA");
    assert_eq!(bad.weak_memory_bugs()[0].threads.len(), 4, "the witness spans all four threads");
    // A full barrier between each reader's two reads restores a consistent global view.
    let good = module("  call void @smp_mb()\n");
    assert!(good.weak_memory_bugs().is_empty(), "full barriers between the reads fix IRIW");
}

/// **Inline-asm memory operand (safety through asm).** An inline asm with a memory operand
/// (`=*m`) writes through its pointer argument — a use-after-free / OOB / null committed *through*
/// the asm is now caught (a precise access obligation on the pointer), and a `~{memory}`-clobber
/// asm no longer false-flags a later free as a double-free (a clobber writes, it does not free).
#[test]
fn inline_asm_memory_operand_is_checked() {
    let cfg = Config { bug_finding: true, ..Config::default() };
    let verdict = |name: &str, body: &str| -> Verdict {
        let src = format!(
            "declare ptr @kmalloc(i64, i32)\ndeclare void @kfree(ptr)\n\
             define void @{name}() {{\n{body}  ret void\n}}\n"
        );
        let m = LlvmFrontend.lower(LlvmInput { source: src, name: name.into() }).expect("lower");
        verify_module(&m, &cfg).verdict
    };
    // asm writes *p AFTER free → use-after-free through the asm memory operand.
    assert_eq!(
        verdict("uaf", "  %p = call ptr @kmalloc(i64 8, i32 0)\n  call void @kfree(ptr %p)\n  \
                         call void asm sideeffect \"movb $1, $0\", \"=*m,r\"(ptr %p, i8 0)\n"),
        Verdict::Fail, "a write through a freed inline-asm memory operand is a UAF"
    );
    // asm writes *p while live, then free → safe. (Also: the memclobber asm must not be
    // treated as a free, else the kfree would be a spurious double-free.)
    assert_ne!(
        verdict("ok", "  %p = call ptr @kmalloc(i64 8, i32 0)\n  \
                        call void asm sideeffect \"movb $1, $0\", \"=*m,r\"(ptr %p, i8 0)\n  \
                        call void @kfree(ptr %p)\n"),
        Verdict::Fail, "a write through a live operand then free is safe"
    );
    // A memory-clobber asm before a free is not a double-free (a clobber writes, not frees).
    assert_ne!(
        verdict("clob", "  %p = call ptr @kmalloc(i64 8, i32 0)\n  \
                          call void asm sideeffect \"mfence\", \"~{memory}\"()\n  \
                          call void @kfree(ptr %p)\n"),
        Verdict::Fail, "a memory-clobber asm does not free — no double-free"
    );
}

/// **Interprocedural reference count (object lifetime across functions).** A `get`/`put`
/// protocol (`sock_hold`/`sock_put`) balances across a *call*: the callee's net refcount effect
/// is composed into the caller (`Summary.refcount_effect`), so a put that drops the count below
/// an in-scope get — even when the extra put lives in a helper function — is an underflow
/// (premature free / UAF). A balanced hold/put across functions is fine; a bare put on a
/// parameter (unknown caller-held count) is not flagged.
#[test]
fn interprocedural_refcount_underflow() {
    let cfg = Config { bug_finding: true, ..Config::default() };
    let module = |caller_body: &str| {
        let src = format!(
            "declare void @sock_hold(ptr)\ndeclare void @sock_put(ptr)\n\
             define void @release(ptr %sk) {{\n  call void @sock_put(ptr %sk)\n  ret void\n}}\n\
             define void @caller(ptr %sk) {{\n{caller_body}  ret void\n}}\n"
        );
        let m = LlvmFrontend.lower(LlvmInput { source: src, name: "rc".into() }).expect("lower");
        verify_module(&m, &cfg)
    };
    // hold once, then put twice (one direct, one via the helper) → underflow across the call.
    assert_eq!(
        module("  call void @sock_hold(ptr %sk)\n  call void @sock_put(ptr %sk)\n  call void @release(ptr %sk)\n").verdict,
        Verdict::Fail, "a put below an in-scope get, composed through a call, underflows"
    );
    // hold once, put once (via the helper) → balanced.
    assert_ne!(
        module("  call void @sock_hold(ptr %sk)\n  call void @release(ptr %sk)\n").verdict,
        Verdict::Fail, "a balanced hold/put across functions is fine"
    );
    // the helper alone (a bare put on a parameter) is not an underflow — the caller holds it.
    assert_ne!(
        module("  call void @release(ptr %sk)\n").verdict,
        Verdict::Fail, "a bare put on a parameter is sound (unknown caller-held count)"
    );
}

/// **RCU grace-period violation.** An object published to RCU readers (`rcu_assign_pointer`)
/// must not be freed with a plain `kfree` until a grace period elapses (`synchronize_rcu`) —
/// else a concurrent reader dereferences freed memory. A publish-then-free without the grace
/// period is refused; with `synchronize_rcu` between them it is not.
#[test]
fn rcu_grace_period_violation_is_refused() {
    let cfg = Config { bug_finding: true, ..Config::default() };
    let verdict = |body: &str| -> Verdict {
        let src = format!(
            "@gp = global ptr null, align 8\ndeclare void @rcu_assign_pointer(ptr, ptr)\n\
             declare void @synchronize_rcu()\ndeclare void @kfree(ptr)\n\
             define void @f(ptr %old) {{\n{body}  ret void\n}}\n"
        );
        let m = LlvmFrontend.lower(LlvmInput { source: src, name: "r".into() }).expect("lower");
        verify_module(&m, &cfg).verdict
    };
    // Publish then free without a grace period → violation.
    assert_eq!(
        verdict("  call void @rcu_assign_pointer(ptr @gp, ptr %old)\n  call void @kfree(ptr %old)\n"),
        Verdict::Fail, "freeing a still-published RCU object without a grace period is a violation"
    );
    // Publish, synchronize_rcu, then free → the grace period makes it safe.
    assert_ne!(
        verdict("  call void @rcu_assign_pointer(ptr @gp, ptr %old)\n  \
                   call void @synchronize_rcu()\n  call void @kfree(ptr %old)\n"),
        Verdict::Fail, "a grace period before the free is safe"
    );
}

/// **Inline-asm register dataflow reaches a proof.** A `xor $0, $0` zero idiom binds the output to
/// a provable `0`; used as an index into a 4-element global array it is in bounds, so the load
/// proves — whereas an opaque (havoc'd) asm output would leave the index unknown. This exercises
/// the semantic decode end-to-end: the modeled value flows into the bounds obligation.
#[test]
fn inline_asm_semantic_value_proves_bounds() {
    let cfg = Config::default(); // strict (not bug-finding): an opaque index would stay UNKNOWN
    let src = "\
        @arr = global [4 x i32] zeroinitializer, align 16\n\
        define i32 @f() {\n\
          %i = call i64 asm \"xor $0, $0\", \"=r\"()\n\
          %p = getelementptr inbounds [4 x i32], ptr @arr, i64 0, i64 %i\n\
          %v = load i32, ptr %p, align 4\n  ret i32 %v\n}\n";
    let m = LlvmFrontend.lower(LlvmInput { source: src.into(), name: "a".into() }).expect("lower");
    assert_eq!(
        verify_module(&m, &cfg).verdict,
        Verdict::Pass,
        "the `xor`-zeroed index is provably 0, so the array load is in bounds"
    );
}

/// **Concurrent reference-count race.** One thread does an *unchecked* get (`sock_hold`) on a
/// shared object while another concurrently does a put (`sock_put`) that may drop the last
/// reference — with disjoint locks, nothing orders the get before the final put, so the get can
/// raise a count that already reached zero (resurrecting a freed object → UAF). A *checked* get
/// (`refcount_inc_not_zero`) refuses that and does not race.
#[test]
fn concurrent_refcount_race_is_detected() {
    let cfg = Config { bug_finding: true, ..Config::default() };
    let races = |getter: &str| -> Vec<csolver_verifier::RefcountRaceWitness> {
        let src = format!(
            "@obj = global ptr null, align 8\n\
             declare void @{getter}(ptr)\ndeclare void @sock_put(ptr)\n\
             define void @thread_get() {{\n  %p = load ptr, ptr @obj, align 8\n  \
               call void @{getter}(ptr %p)\n  ret void\n}}\n\
             define void @thread_put() {{\n  %p = load ptr, ptr @obj, align 8\n  \
               call void @sock_put(ptr %p)\n  ret void\n}}\n"
        );
        let m = LlvmFrontend.lower(LlvmInput { source: src, name: "rc".into() }).expect("lower");
        verify_module(&m, &cfg).refcount_races()
    };
    // Unchecked get concurrent with a put → race on the shared object.
    let racy = races("sock_hold");
    assert!(
        racy.iter().any(|w| w.location.contains("g:obj")),
        "an unchecked get racing a concurrent put is a refcount race: {racy:?}"
    );
    // Checked get (`*_inc_not_zero`) → no race event, no finding.
    let safe = races("refcount_inc_not_zero");
    assert!(
        !safe.iter().any(|w| w.location.contains("g:obj")),
        "a checked get (`_not_zero`) does not race the put: {safe:?}"
    );
}

/// **Cross-syscall UAF through a container lookup (fd table / global idr).** The shared object is
/// not a bare global but is fetched from a persistent kernel container keyed by a syscall argument:
/// `fget(fd)` (the process file table) and `idr_find(&global_idr, id)`. One entry frees the looked-up
/// object, another dereferences its lookup — the object survives between the two syscalls via the
/// container, so it composes on the same root (`deref:g:@files@0` / `deref:g:my_idr@0`).
#[test]
fn cross_entry_uaf_through_fdtable_and_idr_lookup() {
    let cfg = Config { bug_finding: true, ..Config::default() };
    let uaf_locations = |src: String| -> Vec<String> {
        let m = LlvmFrontend.lower(LlvmInput { source: src, name: "cl".into() }).expect("lower");
        verify_module(&m, &cfg)
            .cross_entry_uaf(|n| n.starts_with("sys_"))
            .into_iter()
            .map(|w| w.location)
            .collect()
    };
    // fd table: `fget(fd)` in two entries — one frees the file, the other reads it.
    let fd = uaf_locations(
        "declare ptr @fget(i32)\ndeclare void @kfree(ptr)\n\
         define void @sys_close(i32 %fd) {\n  %f = call ptr @fget(i32 %fd)\n  \
           call void @kfree(ptr %f)\n  ret void\n}\n\
         define i32 @sys_read(i32 %fd) {\n  %f = call ptr @fget(i32 %fd)\n  \
           %v = load i32, ptr %f, align 4\n  ret i32 %v\n}\n"
            .into(),
    );
    assert!(
        fd.iter().any(|l| l.contains("@files")),
        "fget(fd) object freed in one entry and used in another is a cross-syscall UAF: {fd:?}"
    );
    // Global idr: `idr_find(&my_idr, id)` — the container is a global, so it persists across syscalls.
    let idr = uaf_locations(
        "@my_idr = global i8 0\ndeclare ptr @idr_find(ptr, i32)\ndeclare void @kfree(ptr)\n\
         define void @sys_del(i32 %id) {\n  %o = call ptr @idr_find(ptr @my_idr, i32 %id)\n  \
           call void @kfree(ptr %o)\n  ret void\n}\n\
         define i32 @sys_get(i32 %id) {\n  %o = call ptr @idr_find(ptr @my_idr, i32 %id)\n  \
           %v = load i32, ptr %o, align 4\n  ret i32 %v\n}\n"
            .into(),
    );
    assert!(
        idr.iter().any(|l| l.contains("my_idr")),
        "idr_find on a GLOBAL idr composes across syscalls: {idr:?}"
    );
}

/// **Cross-syscall (cross-entry) use-after-free.** Two entry points with *no common caller* — a
/// `close` that frees the object held by a global and a `read` that dereferences that same global —
/// compose into a use-after-free: the attacker invokes `close` then `read`, and the global still
/// points at freed memory (the freeing entry never cleared it). This is sequential, not concurrent
/// (no lock orders them), and is invisible to the interprocedural summary (there is no call edge).
#[test]
fn cross_entry_syscall_use_after_free_is_detected() {
    let cfg = Config { bug_finding: true, ..Config::default() };
    // `sys_close` frees the object reachable from @dev without nulling @dev (dangling);
    // `sys_read` loads @dev and dereferences it → cross-entry UAF on `deref:g:dev@0`.
    let src = "\
        @dev = global ptr null, align 8\n\
        declare void @kfree(ptr)\n\
        define void @sys_close() {\n\
          %p = load ptr, ptr @dev, align 8\n  call void @kfree(ptr %p)\n  ret void\n}\n\
        define i32 @sys_read() {\n\
          %p = load ptr, ptr @dev, align 8\n  %v = load i32, ptr %p, align 4\n  ret i32 %v\n}\n";
    let m = LlvmFrontend.lower(LlvmInput { source: src.into(), name: "ce".into() }).expect("lower");
    let report = verify_module(&m, &cfg);
    let uaf = report.cross_entry_uaf(|n| n.starts_with("sys_"));
    assert!(
        uaf.iter().any(|w| !w.double_free && w.location.contains("g:dev")),
        "close-then-read across entries on a shared global is a cross-entry UAF: {uaf:?}"
    );

    // If `sys_close` nulls @dev after the free (clears the dangling root), there is no UAF.
    let safe_src = "\
        @dev = global ptr null, align 8\n\
        declare void @kfree(ptr)\n\
        define void @sys_close() {\n\
          %p = load ptr, ptr @dev, align 8\n  call void @kfree(ptr %p)\n  \
          store ptr null, ptr @dev, align 8\n  ret void\n}\n\
        define i32 @sys_read() {\n\
          %p = load ptr, ptr @dev, align 8\n  %v = load i32, ptr %p, align 4\n  ret i32 %v\n}\n";
    let m2 = LlvmFrontend.lower(LlvmInput { source: safe_src.into(), name: "ce".into() }).expect("lower");
    let uaf2 = verify_module(&m2, &cfg).cross_entry_uaf(|n| n.starts_with("sys_"));
    assert!(
        !uaf2.iter().any(|w| w.location.contains("g:dev")),
        "clearing the global root after the free removes the cross-entry UAF: {uaf2:?}"
    );
}
