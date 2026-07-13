//! Bounded two-thread interleaving model checker (taxonomy subsystem 4 — a genuine second
//! timeline).
//!
//! The lockset data-race pass (`datarace`, G1) is a sound *abstraction* of the interleaving
//! product: for purely lock-based synchronisation, two accesses can be made concurrent in some
//! valid interleaving **iff** their locksets are disjoint — so Eraser already covers the
//! single-pair race. What it *cannot* see is an **atomicity violation** where every individual
//! access is correctly locked but a read-modify-write is split across two critical sections:
//!
//! ```text
//!   thread A:  lock(L); tmp = x;  unlock(L);   ...;   lock(L); x = tmp+1; unlock(L)
//!   thread B:  lock(L); x = 0;    unlock(L)
//! ```
//!
//! Here `x` is *always* accessed under `L`, so the lockset is consistent (no Eraser race) — yet
//! B's write can be scheduled in the gap where A holds no lock, between A's read of `x` and its
//! dependent write, producing a **lost update**. Detecting this needs an actual interleaving:
//! a valid schedule exhibiting `Read_A(x) < Write_B(x) < Write_A(x)`.
//!
//! This module enumerates valid interleavings of two event traces by DFS, enforcing **lock
//! mutual exclusion** (a lock held by one thread blocks the other from acquiring it), and
//! reports the first schedule that realises the lost-update pattern — a concrete witness. A
//! bug-finding heuristic: an `R(x)…W(x)` on one thread is treated as an atomic read-modify-write
//! (the write is assumed to depend on the read), and the two traces are assumed to be able to
//! run concurrently. Bounded, so a very long trace is truncated (soundly giving up, never a
//! false witness).

/// One shared-memory / synchronisation event in a thread's trace.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Event {
    /// Acquire the lock of the given class.
    Acquire(String),
    /// Release the lock of the given class.
    Release(String),
    /// Read the shared location of the given class.
    Read(String),
    /// A read whose **address depends on a prior read's value** (`p = load gp; x = load p->f` —
    /// the classic `rcu_dereference` pointer-chase). The address/data dependency orders it after
    /// the read it depends on, so it does **not** reorder (no `smp_rmb` needed) — modelled by
    /// treating it as non-reorderable while still observing a value.
    DepRead(String),
    /// Write the shared location of the given class.
    Write(String),
    /// A **read-modify-write** store — a write whose stored value derives from a load (`x = x + 1`).
    /// It is a write for every purpose (data-race, UAF, weak-memory, ABA all treat it as one), but
    /// the atomicity check additionally uses it to distinguish a genuine dependent RMW from an
    /// independent overwrite (`x = 5`): only a dependent closing write is a *lost update*, so a
    /// plain [`Event::Write`] interrupts another thread's RMW but does not itself realise one.
    Rmw(String),
    /// A full **memory barrier** (`smp_mb`/`mb`): orders this thread's prior writes before its
    /// subsequent reads (drains the store buffers) — the only barrier that fixes the
    /// store-buffer (W→R) reordering. A lock acquire/release is also a full barrier.
    Fence,
    /// A **write barrier** (`smp_wmb`): orders this thread's prior writes before its later
    /// writes (drains the store buffers before the next write becomes visible) — fixes the
    /// message-passing producer-side W→W reordering, but *not* the store-buffer W→R one.
    WFence,
    /// A **read barrier** (`smp_rmb`): orders this thread's prior reads before its later reads.
    RFence,
    /// **Spawn** the thread whose function is named — a happens-before edge: the child's events
    /// cannot execute before this point (`pthread_create`/`kthread_run`).
    Spawn(String),
    /// **Join** the threads this thread spawned — a happens-before edge: the parent's subsequent
    /// events execute after the joined children finish (`pthread_join`/`kthread_stop`). Also a
    /// full barrier.
    Join,
    /// **Free** the object of the given class (`kfree`/`Dealloc`). A concurrent free-vs-access or
    /// free-vs-free of the same object (disjoint locksets → not ordered) is a cross-thread
    /// use-after-free / double-free.
    Free(String),
    /// **Compare-and-swap** on the location of the given class. A concurrent modification (write
    /// or free) of the same location by another thread means the value can change A→B→A under the
    /// CAS — the ABA problem.
    Cas(String),
    /// **Unchecked reference-count get** (`kref_get`/`sock_hold`/… — not a `*_not_zero` variant) on
    /// the object of the given class. Concurrent with another thread's [`Event::RefPut`] that drops
    /// the last reference, it can raise a count that already reached zero — resurrecting a dying
    /// object into a use-after-free. A checked get emits no such event.
    RefGet(String),
    /// **Reference-count put** (`kref_put`/`sock_put`/…) on the object of the given class — it may
    /// drop the last reference and free. Concurrent with an unchecked [`Event::RefGet`] it is a
    /// refcount race.
    RefPut(String),
    /// A **typestate transition/requirement on a global-rooted object** (for the cross-entry /
    /// cross-syscall analysis). The payload is `k\u{1f}class\u{1f}proto\u{1f}state`, `k` ∈ {0=set,
    /// 1=require, 2=require-not}. A `set` of a state in one entry paired with a `require-not` of it
    /// in another is a cross-syscall use-after-state. Inert for every other check.
    Typestate(String),
}

/// A thread: a name and its ordered event trace.
pub struct Thread {
    /// The function/thread name (for the witness).
    pub name: String,
    /// The events in program order.
    pub events: Vec<Event>,
}

/// A witnessed atomicity violation: the location whose RMW was interrupted, and the schedule
/// (a list of `(thread-name, event)` steps) that realises `Read_A(x) < Write_B(x) < Write_A(x)`.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct AtomicityWitness {
    /// The shared location whose read-modify-write was interrupted.
    pub location: String,
    /// The interleaved schedule realising the lost update (thread name + event).
    pub schedule: Vec<(String, Event)>,
}

/// The single unavoidable **memory-safety ceiling**: the reachable interleaving / weak-memory state
/// space is worst-case exponential in the trace length, so one search must be bounded to keep memory
/// finite. This is *not* a recall knob — every search whose input-derived estimate falls within it is
/// explored *completely* (see [`search_budget`]); it only caps pathological inputs, and it is the
/// pivot for decomposing an intractable N-thread product into pairs ([`product_fits`]). ~500 000
/// small states is on the order of a hundred megabytes. Deterministic, so verdicts stay reproducible.
const SEARCH_CEILING: u64 = 500_000;

/// The input-derived state estimate for a search over the given per-thread trace lengths: the
/// interleaving product `∏(eᵢ+1)` scaled by a per-thread buffer/propagation factor that grows with
/// the thread count (`~4^threads` — the store-buffer-flush and cross-thread-propagation orderings a
/// wider product adds). Empirically this tracks the reachable-state count (the 4-thread IRIW litmus
/// reaches ~5 000; this estimates ~9 000). Saturating, so a huge group yields `u64::MAX`.
fn search_estimate(per_thread_events: &[usize]) -> u64 {
    let threads = per_thread_events.len() as u32;
    let mut product: u64 = 1;
    for &e in per_thread_events {
        product = product.saturating_mul(e as u64 + 1);
    }
    product.saturating_mul(4u64.saturating_pow(threads))
}

/// The exploration budget for a search over these traces: the input-derived estimate, capped at the
/// memory-safety ceiling. Generous for small traces (litmus explore fully) and scaling with the
/// input rather than a fixed magic count.
fn search_budget(per_thread_events: &[usize]) -> u64 {
    search_estimate(per_thread_events).min(SEARCH_CEILING)
}

/// Whether an N-thread product's estimated state space fits the ceiling — if so it is explored as
/// one simultaneous product (needed for genuine >2-thread effects like IRIW); if not, the search is
/// decomposed into pairs (each far smaller). Replaces a fixed maximum group size with an input-
/// derived decision.
fn product_fits(per_thread_events: &[usize]) -> bool {
    search_estimate(per_thread_events) <= SEARCH_CEILING
}

/// Build a [`Thread`] from an encoded `(kind, class)` trace (0=acquire,1=release,2=read,
/// 3=write) — the form the executor streams (`csolver_symbolic`).
pub fn trace_to_thread(name: &str, trace: &[(u8, String)]) -> Thread {
    let events = trace
        .iter()
        .map(|(k, c)| match k {
            0 => Event::Acquire(c.clone()),
            1 => Event::Release(c.clone()),
            2 => Event::Read(c.clone()),
            4 => Event::Fence,
            5 => Event::WFence,
            6 => Event::RFence,
            7 => Event::Spawn(c.clone()),
            8 => Event::Join,
            9 => Event::DepRead(c.clone()),
            10 => Event::Free(c.clone()),
            11 => Event::Cas(c.clone()),
            12 => Event::RefGet(c.clone()),
            13 => Event::RefPut(c.clone()),
            14 => Event::Typestate(c.clone()),
            15 => Event::Rmw(c.clone()),
            _ => Event::Write(c.clone()),
        })
        .collect();
    Thread { name: name.into(), events }
}

impl Thread {
    /// The set of locations this thread **writes** (for pairing: only a writer can interrupt
    /// another thread's read-modify-write).
    fn written(&self) -> std::collections::BTreeSet<&str> {
        self.events
            .iter()
            .filter_map(|e| match e {
                Event::Write(x) | Event::Rmw(x) => Some(x.as_str()),
                _ => None,
            })
            .collect()
    }

    /// The set of locations this thread **touches** (reads or writes).
    fn touched(&self) -> std::collections::BTreeSet<&str> {
        self.events
            .iter()
            .filter_map(|e| match e {
                Event::Read(x) | Event::DepRead(x) | Event::Write(x) | Event::Rmw(x) => Some(x.as_str()),
                _ => None,
            })
            .collect()
    }
}

/// The set of function names that are **spawned** anywhere in the program (a `Spawn` target) —
/// concrete evidence they run concurrently, possibly in several threads at once.
fn spawned_names(threads: &[Thread]) -> std::collections::HashSet<String> {
    threads
        .iter()
        .flat_map(|t| t.events.iter())
        .filter_map(|e| match e {
            Event::Spawn(name) => Some(name.clone()),
            _ => None,
        })
        .collect()
}


// --- module split (mechanical refactor) ---
mod aba;
mod atomicity;
mod crossentry;
mod uaf;
mod weakmem;
mod weakmem_check;
#[cfg(test)]
#[path = "interleave/tests.rs"]
mod tests;
pub use aba::*;
pub use atomicity::*;
pub use crossentry::*;
pub use uaf::*;
pub use weakmem::*;
pub use weakmem_check::*;
