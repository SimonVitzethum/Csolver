use super::Event::*;
use super::*;

fn thread(name: &str, events: Vec<Event>) -> Thread {
    Thread { name: name.into(), events }
}

// A split-critical-section RMW: x is always under L, but A releases L between read and
// write, so B's write slips in — a lost update the lockset pass cannot see.
#[test]
fn split_critical_section_rmw_is_an_atomicity_violation() {
    let a = thread("A", vec![
        Acquire("L".into()), Read("x".into()), Release("L".into()),
        Acquire("L".into()), Rmw("x".into()), Release("L".into()),
    ]);
    let b = thread("B", vec![Acquire("L".into()), Write("x".into()), Release("L".into())]);
    let w = atomicity_violation(&a, &b).expect("a split-CS RMW is an atomicity violation");
    assert_eq!(w.location, "x");
    // The witness must contain B's write between A's read and A's dependent (Rmw) write.
    let a_writes = w.schedule.iter().position(|(n, e)| n == "A" && matches!(e, Rmw(_))).unwrap();
    let b_writes = w.schedule.iter().position(|(n, e)| n == "B" && matches!(e, Write(_))).unwrap();
    let a_reads = w.schedule.iter().position(|(n, e)| n == "A" && matches!(e, Read(_))).unwrap();
    assert!(a_reads < b_writes && b_writes < a_writes, "witness realises R_A < W_B < W_A");
}

// A single continuous critical section holds L across the whole RMW → mutual exclusion
// forbids B's write from interleaving → no violation.
#[test]
fn continuously_locked_rmw_is_safe() {
    let a = thread("A", vec![
        Acquire("L".into()), Read("x".into()), Rmw("x".into()), Release("L".into()),
    ]);
    let b = thread("B", vec![Acquire("L".into()), Write("x".into()), Release("L".into())]);
    assert!(atomicity_violation(&a, &b).is_none(), "a continuously-locked RMW is atomic");
}

// Different locks: A's RMW under La, B's write under Lb — no mutual exclusion, so B slips
// into A's (even single-CS) RMW. A genuine race the interleaving exposes.
#[test]
fn disjoint_locks_allow_interruption() {
    let a = thread("A", vec![
        Acquire("La".into()), Read("x".into()), Rmw("x".into()), Release("La".into()),
    ]);
    let b = thread("B", vec![Acquire("Lb".into()), Write("x".into()), Release("Lb".into())]);
    assert!(atomicity_violation(&a, &b).is_some(), "disjoint locks do not order the RMW");
}

// Dependent-RMW precision: `R(x) … W(x)` where the closing write is INDEPENDENT of the read
// (a plain `Write` = `x = const`, not `x = x+1`) is NOT a lost update — nothing was computed
// from stale data. Only a dependent `Rmw` closing write realises the violation.
#[test]
fn independent_write_after_read_is_not_a_lost_update() {
    // A reads x then unconditionally overwrites it with a constant (plain Write); B writes x
    // in between (disjoint locks). No value was derived from the read → no atomicity violation.
    let a = thread("A", vec![
        Acquire("La".into()), Read("x".into()), Write("x".into()), Release("La".into()),
    ]);
    let b = thread("B", vec![Acquire("Lb".into()), Write("x".into()), Release("Lb".into())]);
    assert!(
        atomicity_violation(&a, &b).is_none(),
        "an independent (constant) overwrite is not a lost update"
    );
    // The SAME shape with a dependent Rmw closing write IS a violation (control).
    let a2 = thread("A", vec![
        Acquire("La".into()), Read("x".into()), Rmw("x".into()), Release("La".into()),
    ]);
    assert!(
        atomicity_violation(&a2, &b).is_some(),
        "a dependent read-modify-write IS a lost update"
    );
}

// No conflicting write from B → no violation.
#[test]
fn no_conflicting_write_is_safe() {
    let a = thread("A", vec![Read("x".into()), Rmw("x".into())]);
    let b = thread("B", vec![Read("x".into())]); // B only reads
    assert!(atomicity_violation(&a, &b).is_none(), "a read-only other thread cannot cause a lost update");
}

// Store-buffer litmus: T1 writes x then reads y, T2 writes y then reads x, no barriers →
// under weak memory both reads may observe stale values (a missing-barrier bug).
#[test]
fn store_buffer_without_barrier_is_a_violation() {
    let t1 = thread("t1", vec![Write("x".into()), Read("y".into())]);
    let t2 = thread("t2", vec![Write("y".into()), Read("x".into())]);
    let v = store_buffer_violations(&[t1, t2]);
    assert_eq!(v.len(), 1, "the store-buffer litmus with no barrier is a weak-memory bug");
}

// A full barrier between the write and the read in both threads forbids the reordering.
#[test]
fn store_buffer_with_barrier_is_safe() {
    let t1 = thread("t1", vec![Write("x".into()), Fence, Read("y".into())]);
    let t2 = thread("t2", vec![Write("y".into()), Fence, Read("x".into())]);
    assert!(store_buffer_violations(&[t1, t2]).is_empty(), "a barrier between W and R fixes it");
}

// Cross-thread use-after-free: one thread frees an object while another accesses it, with
// disjoint locksets (nothing orders them).
#[test]
fn cross_thread_use_after_free() {
    let freer = thread("freer", vec![Acquire("a".into()), Free("obj".into()), Release("a".into())]);
    let user = thread("user", vec![Acquire("b".into()), Read("obj".into()), Release("b".into())]);
    let v = find_cross_thread_uaf(&[freer, user]);
    assert_eq!(v.len(), 1, "a concurrent free vs use is a cross-thread UAF");
    assert!(!v[0].double_free);
    // Under a common lock the free and use are ordered → no candidate.
    let f2 = thread("freer", vec![Acquire("L".into()), Free("obj".into()), Release("L".into())]);
    let u2 = thread("user", vec![Acquire("L".into()), Read("obj".into()), Release("L".into())]);
    assert!(find_cross_thread_uaf(&[f2, u2]).is_empty(), "a common lock orders free vs use");
}

// ABA: one thread CAS-es a location while another concurrently modifies it (disjoint locks).
#[test]
fn aba_cas_with_concurrent_modification() {
    let cas = thread("popper", vec![Cas("head".into())]);
    let modif = thread("pusher", vec![Write("head".into())]);
    assert_eq!(find_aba(&[cas, modif]).len(), 1, "a CAS concurrent with a modification is ABA-susceptible");
    // Under a common lock the CAS and the modification are ordered → no candidate.
    let c2 = thread("popper", vec![Acquire("L".into()), Cas("head".into()), Release("L".into())]);
    let m2 = thread("pusher", vec![Acquire("L".into()), Write("head".into()), Release("L".into())]);
    assert!(find_aba(&[c2, m2]).is_empty(), "a common lock orders the CAS and the modification");
}

// Cross-thread double-free: two threads free the same object with disjoint locksets.
#[test]
fn cross_thread_double_free() {
    let a = thread("a", vec![Free("obj".into())]);
    let b = thread("b", vec![Free("obj".into())]);
    let v = find_cross_thread_uaf(&[a, b]);
    assert_eq!(v.len(), 1);
    assert!(v[0].double_free, "two concurrent frees are a double-free");
}

// Self-concurrency: a *spawned* handler that frees a shared object races a second instance of
// itself — the double-close / double-free-by-the-same-handler race. Only detectable by pairing
// the handler against a clone of itself (the gap the three lockset detectors previously had).
#[test]
fn spawned_handler_races_itself_double_free() {
    let spawner = thread("main", vec![Spawn("handler".into()), Spawn("handler".into())]);
    let handler = thread("handler", vec![Free("obj".into())]);
    let v = find_cross_thread_uaf(&[spawner, handler]);
    assert!(
        v.iter().any(|w| w.double_free && w.location == "obj"),
        "two instances of a spawned free-ing handler are a double-free: {v:?}"
    );
    // A handler that is never spawned is not self-raced (no concurrency evidence).
    let lone = thread("handler", vec![Free("obj".into())]);
    assert!(find_cross_thread_uaf(&[lone]).is_empty(), "an un-spawned handler is not self-raced");
    // Two instances that both free under the SAME lock are serialized → not a race.
    let sp = thread("main", vec![Spawn("h".into())]);
    let locked = thread("h", vec![Acquire("L".into()), Free("obj".into()), Release("L".into())]);
    assert!(
        find_cross_thread_uaf(&[sp, locked]).is_empty(),
        "a common lock serializes the two instances"
    );
}

// Self-concurrency also closes the refcount-race gap: a spawned handler's unchecked get racing
// a second instance's put on the same object.
#[test]
fn spawned_handler_races_itself_refcount() {
    let spawner = thread("main", vec![Spawn("h".into())]);
    let handler = thread("h", vec![RefGet("sk".into()), RefPut("sk".into())]);
    let v = find_refcount_races(&[spawner, handler]);
    assert!(
        v.iter().any(|w| w.location == "sk"),
        "a spawned handler's get races a second instance's put: {v:?}"
    );
}

// Thread-lifetime happens-before: a parent that frees an object only AFTER `Join`-ing the
// worker that used it is not racing — the worker finished first. The lockset check alone
// (disjoint locks) would flag it; the join ordering must suppress the false positive.
#[test]
fn free_after_join_is_not_a_uaf() {
    let worker = thread("worker", vec![Read("obj".into())]);
    let parent = thread("parent", vec![Spawn("worker".into()), Join, Free("obj".into())]);
    assert!(
        find_cross_thread_uaf(&[parent, worker]).is_empty(),
        "the worker is joined before the free — they are ordered, not concurrent"
    );
}

// But a free BEFORE the join (still inside the worker's lifetime) IS a race: the parent frees
// while the worker may still be reading.
#[test]
fn free_before_join_is_a_uaf() {
    let worker = thread("worker", vec![Read("obj".into())]);
    let parent = thread("parent", vec![Spawn("worker".into()), Free("obj".into()), Join]);
    assert_eq!(
        find_cross_thread_uaf(&[parent, worker]).len(),
        1,
        "the free happens inside the worker's lifetime (before the join) — a real UAF"
    );
}

// The lifetime ordering also suppresses a refcount-race false positive: an unchecked get in a
// worker that the parent joins before its put cannot race that put.
#[test]
fn refcount_get_before_parent_joins_then_puts_is_ordered() {
    let worker = thread("worker", vec![RefGet("sk".into())]);
    let parent = thread("parent", vec![Spawn("worker".into()), Join, RefPut("sk".into())]);
    assert!(
        find_refcount_races(&[parent, worker]).is_empty(),
        "the worker (and its get) is joined before the put — ordered, not a race"
    );
}

// A lock release/acquire is also a full barrier → no store-buffer reordering.
#[test]
fn lock_acts_as_a_barrier() {
    let t1 = thread("t1", vec![Write("x".into()), Release("L".into()), Read("y".into())]);
    let t2 = thread("t2", vec![Write("y".into()), Release("L".into()), Read("x".into())]);
    assert!(store_buffer_violations(&[t1, t2]).is_empty(), "a lock op is a barrier");
}

// --- Operational weak-memory (PSO) robustness ------------------------------------------

// Store-buffer litmus: under the operational model both reads can observe the initial value
// — an outcome no SC execution allows → non-robust.
#[test]
fn operational_store_buffer_is_non_robust() {
    let t1 = thread("t1", vec![Write("x".into()), Read("y".into())]);
    let t2 = thread("t2", vec![Write("y".into()), Read("x".into())]);
    assert!(weak_memory_nonrobustness(&[t1, t2]).is_some(), "SB is not SC-robust");
}

// A full barrier between the write and read makes it robust.
#[test]
fn operational_store_buffer_with_mb_is_robust() {
    let t1 = thread("t1", vec![Write("x".into()), Fence, Read("y".into())]);
    let t2 = thread("t2", vec![Write("y".into()), Fence, Read("x".into())]);
    assert!(weak_memory_nonrobustness(&[t1, t2]).is_none(), "smp_mb restores robustness");
}

// Message-passing: producer writes data then flag; consumer reads flag then data. Under PSO
// the producer's two writes can be reordered, so the consumer can see flag=set, data=stale —
// non-SC. This is the case the store-buffer syntactic check does NOT catch.
#[test]
fn operational_message_passing_without_wmb_is_non_robust() {
    let producer = thread("producer", vec![Write("data".into()), Write("flag".into())]);
    let consumer = thread("consumer", vec![Read("flag".into()), Read("data".into())]);
    assert!(weak_memory_nonrobustness(&[producer, consumer]).is_some(),
        "message passing without smp_wmb is not SC-robust");
}

// ARM-style: with a write barrier on the producer but NO read barrier on the consumer, the
// consumer's two reads can still reorder (R→R), so it can see flag=set, data=stale.
#[test]
fn operational_message_passing_needs_read_barrier_too() {
    let producer = thread("producer", vec![Write("data".into()), WFence, Write("flag".into())]);
    let consumer = thread("consumer", vec![Read("flag".into()), Read("data".into())]);
    assert!(weak_memory_nonrobustness(&[producer, consumer]).is_some(),
        "wmb alone is not enough — the consumer's reads can still reorder (ARM R->R)");
}

// Both barriers: smp_wmb orders the publishes, smp_rmb orders the consumer's reads → robust.
#[test]
fn operational_message_passing_with_both_barriers_is_robust() {
    let producer = thread("producer", vec![Write("data".into()), WFence, Write("flag".into())]);
    let consumer = thread("consumer", vec![Read("flag".into()), RFence, Read("data".into())]);
    assert!(weak_memory_nonrobustness(&[producer, consumer]).is_none(),
        "smp_wmb + smp_rmb restore robustness");
}

// IRIW (Independent Reads of Independent Writes) — a **4-thread** litmus that needs
// non-multi-copy-atomicity: two writers to x and y, two readers seeing them in opposite
// orders. No pair of threads exhibits it; the whole product does.
#[test]
fn operational_iriw_is_non_robust() {
    let w1 = thread("w1", vec![Write("x".into())]);
    let w2 = thread("w2", vec![Write("y".into())]);
    let r1 = thread("r1", vec![Read("x".into()), Read("y".into())]);
    let r2 = thread("r2", vec![Read("y".into()), Read("x".into())]);
    assert!(weak_memory_nonrobustness(&[w1, w2, r1, r2]).is_some(),
        "IRIW is not SC-robust under non-multi-copy-atomicity");
}

// IRIW with full barriers between the readers' two reads is robust (the barriers force a
// consistent global view).
#[test]
fn operational_iriw_with_barriers_is_robust() {
    let w1 = thread("w1", vec![Write("x".into())]);
    let w2 = thread("w2", vec![Write("y".into())]);
    let r1 = thread("r1", vec![Read("x".into()), Fence, Read("y".into())]);
    let r2 = thread("r2", vec![Read("y".into()), Fence, Read("x".into())]);
    assert!(weak_memory_nonrobustness(&[w1, w2, r1, r2]).is_none(),
        "IRIW with full barriers between the reads is robust");
}

// Happens-before via spawn/join: the store-buffer shape is a bug when the two threads run
// concurrently, but NOT when one is spawned and joined by the other — the join orders the
// child's write before the parent's read.
#[test]
fn spawn_join_happens_before_removes_the_race() {
    // Concurrent: classic store buffer → non-robust.
    let a = thread("A", vec![Write("x".into()), Read("y".into())]);
    let b = thread("B", vec![Write("y".into()), Read("x".into())]);
    assert!(weak_memory_nonrobustness(&[a, b]).is_some(), "concurrent SB is a bug");
    // Spawned + joined: the parent spawns B, joins it, then does its own accesses — the
    // child is entirely ordered before the parent's read (no concurrency).
    let parent = thread("A", vec![
        Write("x".into()), Spawn("B".into()), Join, Read("y".into()),
    ]);
    let child = thread("B", vec![Write("y".into()), Read("x".into())]);
    assert!(weak_memory_nonrobustness(&[parent, child]).is_none(),
        "a spawned-then-joined child is ordered by happens-before — no race");
}

// Address dependency (rcu_dereference pointer-chase): the consumer's second read depends on
// the first read's value (its address), so it does NOT reorder — a write barrier on the
// producer alone makes the publish robust (no read barrier needed on the consumer).
#[test]
fn address_dependency_orders_the_dependent_read() {
    let prod = || thread("producer", vec![Write("obj".into()), WFence, Write("gp".into())]);
    // consumer: p = read gp; v = read *p  (the second is address-dependent → DepRead).
    let consumer = thread("consumer", vec![Read("gp".into()), DepRead("obj".into())]);
    assert!(weak_memory_nonrobustness(&[prod(), consumer]).is_none(),
        "an address-dependent read is ordered — smp_wmb alone suffices (rcu_dereference)");
    // Contrast: a plain (non-dependent) second read still needs a read barrier.
    let plain = thread("consumer", vec![Read("gp".into()), Read("obj".into())]);
    assert!(weak_memory_nonrobustness(&[prod(), plain]).is_some(),
        "a non-dependent second read can still reorder — needs smp_rmb");
}

// The child observes the parent's pre-spawn writes (release/acquire of thread creation).
#[test]
fn spawned_child_sees_parent_prior_writes() {
    let parent = thread("A", vec![Write("x".into()), Spawn("B".into()), Join]);
    let child = thread("B", vec![Read("x".into())]);
    // The only observation is child reads x = the parent's write (never the initial 0),
    // matching SC → robust (no anomaly).
    assert!(weak_memory_nonrobustness(&[parent, child]).is_none(),
        "the child sees the parent's pre-spawn write (thread-create HB)");
}

// Self-concurrency: a *spawned* worker doing an unlocked read-modify-write races with a
// second instance of itself (lost update). A worker that is never spawned is not flagged.
#[test]
fn spawned_self_concurrent_rmw_is_an_atomicity_violation() {
    let spawner = thread("main", vec![Spawn("worker".into()), Spawn("worker".into())]);
    let worker = thread("worker", vec![Read("counter".into()), Rmw("counter".into())]);
    let v = find_atomicity_violations(&[spawner, worker]);
    assert_eq!(v.len(), 1, "a spawned unlocked RMW loses updates against itself");
    // The same worker, never spawned, is not self-checked (no evidence of concurrency).
    let lone = thread("worker", vec![Read("counter".into()), Rmw("counter".into())]);
    assert!(find_atomicity_violations(&[lone]).is_empty(), "an un-spawned function is not self-raced");
}

// Cross-entry sequence closure — the basic two-syscall chain: `close` frees a global-rooted
// object, a later `use` derefs it. Attacker calls close then use → cross-syscall UAF.
#[test]
fn cross_entry_sequence_free_then_use_is_a_uaf() {
    let close = thread("sys_close", vec![Free("deref:g:obj@0".into())]);
    let uses = thread("sys_read", vec![Read("deref:g:obj@0".into())]);
    let v = find_cross_entry_uaf(&[close, uses]);
    assert_eq!(v.len(), 1, "close-then-read is a cross-entry UAF: {v:?}");
    assert!(!v[0].double_free && v[0].location == "deref:g:obj@0");
}

// PRECISION gain: the using entry RE-VALIDATES the handle before using it (`if (!x) x = open();
// use(x)` — modelled as a Clear/reassign of the slot then a Use). Even though another entry can
// leave the object Dangling, this entry is never dangerous → no false positive (the old
// order-insensitive pairwise fold reported it).
#[test]
fn cross_entry_reopen_before_use_is_not_a_uaf() {
    let close = thread("sys_close", vec![Free("deref:g:obj@0".into())]);
    // Re-open (write the slot `g:obj@0`) THEN use the object → safe.
    let reopen_use = thread(
        "sys_read",
        vec![Write("g:obj@0".into()), Read("deref:g:obj@0".into())],
    );
    assert!(
        find_cross_entry_uaf(&[close, reopen_use]).is_empty(),
        "an entry that re-opens the handle before using it is not a UAF"
    );
}

// Two DISTINCT entries both freeing the same global handle → cross-entry double-free. (The
// same syscall twice is NOT flagged — the handle layer rejects the re-invocation with EBADF.)
#[test]
fn cross_entry_two_entries_double_free() {
    let close = thread("sys_close", vec![Free("deref:g:obj@0".into())]);
    let ioctl_free = thread("sys_ioctl", vec![Free("deref:g:obj@0".into())]);
    let v = find_cross_entry_uaf(&[close, ioctl_free]);
    assert!(
        v.iter().any(|w| w.double_free && w.location == "deref:g:obj@0"),
        "two distinct entries freeing the same global handle is a double-free: {v:?}"
    );
    // A single freeing entry (only re-invocable as itself) is NOT a cross-entry double-free.
    assert!(
        find_cross_entry_uaf(&[thread("sys_close", vec![Free("deref:g:obj@0".into())])])
            .iter()
            .all(|w| !w.double_free),
        "the same syscall twice is not treated as a cross-entry double-free (EBADF-guarded)"
    );
}

// A parameter-local (non-global) object never fires — it cannot survive to another syscall.
#[test]
fn cross_entry_param_local_object_is_not_flagged() {
    let close = thread("a", vec![Free("{sock}@0".into())]);
    let uses = thread("b", vec![Read("{sock}@0".into())]);
    assert!(find_cross_entry_uaf(&[close, uses]).is_empty(), "a param-local object is not persistent");
}
