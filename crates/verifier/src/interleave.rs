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

/// Cap on explored schedule states — keeps the (worst-case exponential) DFS bounded. On
/// reaching it the search gives up (returns `None` for that pair), never a false witness.
const MAX_STATES: u64 = 200_000;

/// Cap on the number of thread pairs the whole-program search checks — the pairing is
/// quadratic, so a large program is bounded (best-effort recall, never a false witness).
const MAX_PAIRS: usize = 20_000;

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
                Event::Write(x) => Some(x.as_str()),
                _ => None,
            })
            .collect()
    }

    /// The set of locations this thread **touches** (reads or writes).
    fn touched(&self) -> std::collections::BTreeSet<&str> {
        self.events
            .iter()
            .filter_map(|e| match e {
                Event::Read(x) | Event::DepRead(x) | Event::Write(x) => Some(x.as_str()),
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

/// Whole-program atomicity search: over all thread traces, check every pair that shares a
/// location where at least one writes it, in both orders, and collect the witnessed atomicity
/// violations (one per location, most-relevant first). Bounded by [`MAX_PAIRS`].
pub fn find_atomicity_violations(threads: &[Thread]) -> Vec<AtomicityWitness> {
    let mut out: Vec<AtomicityWitness> = Vec::new();
    let mut seen_loc: std::collections::HashSet<String> = std::collections::HashSet::new();
    let mut pairs = 0usize;
    let spawned = spawned_names(threads);
    for i in 0..threads.len() {
        let ti_written = threads[i].written();
        let ti_touched = threads[i].touched();
        if ti_written.is_empty() && ti_touched.is_empty() {
            continue;
        }
        // Self-concurrency: a function that is *spawned* somewhere may run in several threads at
        // once — so it races with a second instance of itself (an unlocked `counter++` loses
        // updates). Check it against a renamed copy.
        if !ti_written.is_empty() && spawned.contains(&threads[i].name) {
            let copy = Thread { name: format!("{}#2", threads[i].name), events: threads[i].events.clone() };
            if let Some(w) = atomicity_violation(&threads[i], &copy) {
                if seen_loc.insert(w.location.clone()) {
                    out.push(w);
                }
            }
        }
        for j in (i + 1)..threads.len() {
            // Only pair threads sharing a location that at least one of them writes.
            let tj_touched = threads[j].touched();
            let tj_written = threads[j].written();
            let shares_write = ti_written.iter().any(|w| tj_touched.contains(w))
                || tj_written.iter().any(|w| ti_touched.contains(w));
            if !shares_write {
                continue;
            }
            if pairs >= MAX_PAIRS {
                return out;
            }
            pairs += 1;
            for w in [
                atomicity_violation(&threads[i], &threads[j]),
                atomicity_violation(&threads[j], &threads[i]),
            ]
            .into_iter()
            .flatten()
            {
                if seen_loc.insert(w.location.clone()) {
                    out.push(w);
                }
            }
        }
    }
    out.sort_by(|a, b| a.location.cmp(&b.location));
    out
}

/// A witnessed **store-buffer / missing-barrier** weak-memory bug: two threads each write one
/// location and then read the other's, with **no barrier** in between — so under a weak memory
/// model (TSO/ARM) both stores can be buffered and both reads observe the *stale* value, an
/// outcome sequential consistency forbids. The classic Dekker / store-buffer litmus; the fix
/// is a barrier (`smp_mb`) between each write and read.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct StoreBufferWitness {
    /// The two threads involved.
    pub threads: (String, String),
    /// The two locations: the first thread writes `a` then reads `b`; the second writes `b`
    /// then reads `a`.
    pub locations: (String, String),
}

/// The set of `(written, later-read)` location pairs a thread has with **no barrier** (a
/// fence, or any lock acquire/release — all full barriers) between the write and the read.
/// These are the writes a weak memory model may reorder after the read.
fn buffered_write_read_pairs(t: &Thread) -> std::collections::BTreeSet<(String, String)> {
    let mut pairs = std::collections::BTreeSet::new();
    // For each write, scan forward to reads until a barrier is hit.
    for (i, ev) in t.events.iter().enumerate() {
        let Event::Write(x) = ev else { continue };
        for later in &t.events[i + 1..] {
            match later {
                // Any barrier or thread-sync stops the reordering window for this write.
                Event::Fence | Event::Acquire(_) | Event::Release(_) | Event::Spawn(_) | Event::Join => break,
Event::Read(y) | Event::DepRead(y) if y != x => {
                    pairs.insert((x.clone(), y.clone()));
                }
                _ => {}
            }
        }
    }
    pairs
}

/// Whole-program store-buffer search: find every pair of threads exhibiting the store-buffer
/// litmus (`Ti: W(a)…R(b)` and `Tj: W(b)…R(a)`, no barrier in either window) — a missing-barrier
/// weak-memory bug. Bounded by [`MAX_PAIRS`]. Bug-finding: the reordering is only a bug if the
/// code relies on the SC outcome (a flag handshake / Dekker lock), so it is a candidate.
pub fn store_buffer_violations(threads: &[Thread]) -> Vec<StoreBufferWitness> {
    let pairs: Vec<_> = threads.iter().map(buffered_write_read_pairs).collect();
    let mut out = Vec::new();
    let mut seen: std::collections::HashSet<(String, String)> = std::collections::HashSet::new();
    let mut checked = 0usize;
    for i in 0..threads.len() {
        for j in (i + 1)..threads.len() {
            if checked >= MAX_PAIRS {
                return out;
            }
            checked += 1;
            for (a, b) in &pairs[i] {
                // Thread j must write `b` then read `a` (the mirrored litmus).
                if pairs[j].contains(&(b.clone(), a.clone())) {
                    // Canonicalise the location pair so the mirror is not reported twice.
                    let key = if a <= b { (a.clone(), b.clone()) } else { (b.clone(), a.clone()) };
                    if seen.insert(key) {
                        out.push(StoreBufferWitness {
                            threads: (threads[i].name.clone(), threads[j].name.clone()),
                            locations: (a.clone(), b.clone()),
                        });
                    }
                }
            }
        }
    }
    out.sort_by(|x, y| x.locations.cmp(&y.locations));
    out
}

/// A witnessed **cross-thread use-after-free / double-free**: one thread frees an object while
/// another concurrently accesses (UAF) or frees (double-free) it — their locksets are disjoint,
/// so nothing orders the free before/after the other operation.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct FreeUseWitness {
    /// The freed object's class.
    pub location: String,
    /// The threads: the one that frees, and the one that concurrently uses/frees.
    pub threads: (String, String),
    /// `true` for a double-free (both free), `false` for a use-after-free.
    pub double_free: bool,
}

/// A `(class, lockset)` list — an event's location class and the lock classes held at it.
type ClassLocksets = Vec<(String, std::collections::BTreeSet<String>)>;

/// Per-thread, the `(class, lockset)` of every free and every access (read/write) — the lockset
/// being the lock classes held at that event (Acquire/Release tracked along the trace).
fn free_and_access_locksets(t: &Thread) -> (ClassLocksets, ClassLocksets) {
    let mut held: std::collections::BTreeSet<String> = std::collections::BTreeSet::new();
    let mut frees = Vec::new();
    let mut accesses = Vec::new();
    for e in &t.events {
        match e {
            Event::Acquire(l) => {
                held.insert(l.clone());
            }
            Event::Release(l) => {
                held.remove(l);
            }
            Event::Free(x) => frees.push((x.clone(), held.clone())),
            Event::Read(x) | Event::DepRead(x) | Event::Write(x) => {
                accesses.push((x.clone(), held.clone()))
            }
            _ => {}
        }
    }
    (frees, accesses)
}

/// Whole-program **cross-thread use-after-free / double-free** search: a free in one thread and a
/// concurrent access (UAF) or free (double-free) of the same object in another thread, with
/// **disjoint locksets** (nothing orders them). Bounded by [`MAX_PAIRS`]. A bug-finding
/// heuristic — like Eraser it does not model refcounts or ownership that may order them.
pub fn find_cross_thread_uaf(threads: &[Thread]) -> Vec<FreeUseWitness> {
    let per: Vec<_> = threads.iter().map(free_and_access_locksets).collect();
    let mut out = Vec::new();
    let mut seen: std::collections::HashSet<(String, bool)> = std::collections::HashSet::new();
    let mut checked = 0usize;
    for i in 0..threads.len() {
        for j in 0..threads.len() {
            if i == j || checked >= MAX_PAIRS {
                continue;
            }
            checked += 1;
            // A free in `i` vs an access in `j`, disjoint locksets → use-after-free.
            for (fx, fl) in &per[i].0 {
                for (ax, al) in &per[j].1 {
                    if fx == ax && fl.is_disjoint(al) && seen.insert((fx.clone(), false)) {
                        out.push(FreeUseWitness {
                            location: fx.clone(),
                            threads: (threads[i].name.clone(), threads[j].name.clone()),
                            double_free: false,
                        });
                    }
                }
                // A free in `i` vs a free in `j` (i<j to avoid the mirror), disjoint → double-free.
                if i < j {
                    for (gx, gl) in &per[j].0 {
                        if fx == gx && fl.is_disjoint(gl) && seen.insert((fx.clone(), true)) {
                            out.push(FreeUseWitness {
                                location: fx.clone(),
                                threads: (threads[i].name.clone(), threads[j].name.clone()),
                                double_free: true,
                            });
                        }
                    }
                }
            }
        }
    }
    out.sort_by(|a, b| a.location.cmp(&b.location));
    out
}

/// A witnessed **cross-entry (cross-syscall) use-after-free / double-free**: one attacker-reachable
/// entry frees an object reachable from a shared *persistent* root (a global — an fd table, a
/// device pointer, …) without clearing that root, and a *separate* entry, with no common caller,
/// later dereferences (or frees) the same root. Unlike the cross-*thread* search this is a
/// **sequential** composition — the entries need not overlap in time (locks between them do not
/// order them); the attacker simply invokes the freeing syscall (`close`) and then the using one
/// (`read`/`ioctl`). The dangling shared root is what carries the freed pointer between them.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct CrossEntryWitness {
    /// The dangling global-rooted object's class.
    pub location: String,
    /// The entries: the one that frees, and the one that later uses (or the second free).
    pub entries: (String, String),
    /// `true` if the second entry also frees it (cross-entry double-free), else a use-after-free.
    pub double_free: bool,
}

/// Whether a class is rooted at a **global** — the only state that persists between independent
/// syscall entries. A parameter-derived object does not survive to another entry (no common
/// caller passes it), so it is excluded. Matches `g:name@off` and any `deref:` chased from one.
fn is_global_rooted(class: &str) -> bool {
    let mut core = class;
    while let Some(rest) = core.strip_prefix("deref:") {
        core = rest;
    }
    core.starts_with("g:")
}

/// The **root slot** of a dereferenced global class: `deref:g:obj@0` → `g:obj@0`. A write to this
/// slot in the freeing entry means it reassigned/cleared the global (no dangling) — we then skip.
fn root_slot(class: &str) -> &str {
    class.strip_prefix("deref:").unwrap_or(class)
}

/// Whole-program **cross-entry use-after-free / double-free** search: a free of a global-rooted
/// object in one entry (that does not clear the global root) and a later dereference (UAF) or free
/// (double-free) of the same object in a *different* entry. `entries` should be the attacker-
/// reachable entry functions' traces; the global-root restriction means only *persistent* shared
/// state is considered, so a param-passed object (which cannot survive to an unrelated entry) never
/// fires. Bounded by [`MAX_PAIRS`]. A bug-finding heuristic — it does not model an intervening
/// re-validation the two syscalls might both perform, so it reports candidates.
pub fn find_cross_entry_uaf(entries: &[Thread]) -> Vec<CrossEntryWitness> {
    use std::collections::BTreeSet;
    struct EntryEff {
        /// Global-rooted classes this entry frees.
        frees: Vec<String>,
        /// Global slots this entry writes (a reassign/clear of the root — removes the dangling).
        writes_slot: BTreeSet<String>,
        /// Global-rooted classes this entry dereferences (read/write through the root).
        uses: BTreeSet<String>,
    }
    let eff: Vec<EntryEff> = entries
        .iter()
        .map(|t| {
            let mut frees = Vec::new();
            let mut writes_slot = BTreeSet::new();
            let mut uses = BTreeSet::new();
            for e in &t.events {
                match e {
                    Event::Free(x) if is_global_rooted(x) => frees.push(x.clone()),
                    Event::Write(x) if is_global_rooted(x) => {
                        writes_slot.insert(x.clone());
                        uses.insert(x.clone());
                    }
                    Event::Read(x) | Event::DepRead(x) if is_global_rooted(x) => {
                        uses.insert(x.clone());
                    }
                    // A refcount put on a global object is a *release* — it may drop the last
                    // reference and free it — so it composes across entries exactly like a free
                    // (a later use or a second put in another entry is a UAF / double-put). An
                    // unchecked get is a use of the object.
                    Event::RefPut(x) if is_global_rooted(x) => frees.push(x.clone()),
                    Event::RefGet(x) if is_global_rooted(x) => {
                        uses.insert(x.clone());
                    }
                    _ => {}
                }
            }
            EntryEff { frees, writes_slot, uses }
        })
        .collect();
    let mut out = Vec::new();
    let mut seen: std::collections::HashSet<(String, bool)> = std::collections::HashSet::new();
    let mut checked = 0usize;
    for i in 0..entries.len() {
        for j in 0..entries.len() {
            if i == j || checked >= MAX_PAIRS {
                continue;
            }
            checked += 1;
            for fx in &eff[i].frees {
                // The freeing entry reassigned/cleared the global root → not left dangling, skip.
                if eff[i].writes_slot.contains(root_slot(fx)) {
                    continue;
                }
                // A later dereference of the same object in a different entry → cross-entry UAF.
                if eff[j].uses.contains(fx) && seen.insert((fx.clone(), false)) {
                    out.push(CrossEntryWitness {
                        location: fx.clone(),
                        entries: (entries[i].name.clone(), entries[j].name.clone()),
                        double_free: false,
                    });
                }
                // A second free of the same object in a different entry → cross-entry double-free.
                if i < j && eff[j].frees.contains(fx) && seen.insert((fx.clone(), true)) {
                    out.push(CrossEntryWitness {
                        location: fx.clone(),
                        entries: (entries[i].name.clone(), entries[j].name.clone()),
                        double_free: true,
                    });
                }
            }
        }
    }
    out.sort_by(|a, b| a.location.cmp(&b.location));
    out
}

/// A witnessed **cross-entry (cross-syscall) typestate violation**: one entry drives a global-
/// rooted object into a protocol state (e.g. `closed`/`freed`) and another, independently reachable
/// entry uses it while forbidding that state (a `require-not`). Invoking the first syscall then the
/// second is a use-after-close / use-after-free across the object's persistent global handle — the
/// typestate analogue of [`CrossEntryWitness`], carrying the full protocol/state provenance.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct CrossEntryTypestateWitness {
    /// The global-rooted object's class.
    pub location: String,
    /// The interned protocol id (shared module-wide, so it matches across entries).
    pub protocol: u32,
    /// The interned forbidden-state id.
    pub state: u32,
    /// The entries: the one that sets the forbidden state, and the one that uses it.
    pub entries: (String, String),
}

/// Parse a `Typestate` event payload `k\u{1f}class\u{1f}proto\u{1f}state` → `(k, class, proto,
/// state)`. `None` on a malformed payload.
fn parse_typestate(payload: &str) -> Option<(u8, &str, u32, u32)> {
    let mut it = payload.split('\u{1f}');
    let k: u8 = it.next()?.parse().ok()?;
    let class = it.next()?;
    let proto: u32 = it.next()?.parse().ok()?;
    let state: u32 = it.next()?.parse().ok()?;
    Some((k, class, proto, state))
}

/// Whole-program **cross-entry typestate** search: a `set` of a `(global-object, protocol, state)`
/// in one entry paired with a `require-not` of the same triple in a *different* entry — invoking the
/// setter then the user is a cross-syscall use-after-state (use-after-close / use-after-free on the
/// object's persistent global handle). Restricted to global-rooted objects (streamed as such), so a
/// parameter-local resource never fires. Bounded by [`MAX_PAIRS`]. A bug-finding heuristic — it does
/// not model an ordering guard (a re-open/re-check) the second syscall might perform.
pub fn find_cross_entry_typestate(entries: &[Thread]) -> Vec<CrossEntryTypestateWitness> {
    // Per entry: the (class, proto, state) it sets, and the ones it requires-not (the use side).
    type Triple = (String, u32, u32);
    let (sets, reqnots): (Vec<Vec<Triple>>, Vec<Vec<Triple>>) = entries
        .iter()
        .map(|t| {
            let (mut s, mut r) = (Vec::new(), Vec::new());
            for e in &t.events {
                if let Event::Typestate(p) = e {
                    if let Some((k, class, proto, state)) = parse_typestate(p) {
                        match k {
                            0 => s.push((class.to_string(), proto, state)),
                            2 => r.push((class.to_string(), proto, state)),
                            _ => {}
                        }
                    }
                }
            }
            (s, r)
        })
        .unzip();
    let mut out = Vec::new();
    let mut seen: std::collections::HashSet<Triple> = std::collections::HashSet::new();
    let mut checked = 0usize;
    for i in 0..entries.len() {
        for j in 0..entries.len() {
            if i == j || checked >= MAX_PAIRS {
                continue;
            }
            checked += 1;
            for set in &sets[i] {
                if reqnots[j].contains(set) && seen.insert(set.clone()) {
                    out.push(CrossEntryTypestateWitness {
                        location: set.0.clone(),
                        protocol: set.1,
                        state: set.2,
                        entries: (entries[i].name.clone(), entries[j].name.clone()),
                    });
                }
            }
        }
    }
    out.sort_by(|a, b| a.location.cmp(&b.location));
    out
}

/// A witnessed **ABA problem**: one thread compare-and-swaps a location while another thread
/// concurrently modifies it (write or free — the value can go A→B→A), with disjoint locksets so
/// nothing orders them. The CAS can then succeed on a stale premise.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct AbaWitness {
    /// The compare-and-swapped location's class.
    pub location: String,
    /// The threads: the one that CAS-es, and the one that concurrently modifies.
    pub threads: (String, String),
}

/// Per-thread, the `(class, lockset)` of every compare-and-swap and every modification (a write
/// or free) — used to match a CAS against a concurrent A→B→A modification.
fn cas_and_mod_locksets(t: &Thread) -> (ClassLocksets, ClassLocksets) {
    let mut held: std::collections::BTreeSet<String> = std::collections::BTreeSet::new();
    let mut cas = Vec::new();
    let mut modif = Vec::new();
    for e in &t.events {
        match e {
            Event::Acquire(l) => {
                held.insert(l.clone());
            }
            Event::Release(l) => {
                held.remove(l);
            }
            Event::Cas(x) => cas.push((x.clone(), held.clone())),
            Event::Write(x) | Event::Free(x) => modif.push((x.clone(), held.clone())),
            _ => {}
        }
    }
    (cas, modif)
}

/// Whole-program **ABA** search: a compare-and-swap of a location in one thread concurrent
/// (disjoint locksets) with a modification of the same location in another thread. Bounded by
/// [`MAX_PAIRS`]. A bug-finding heuristic — a real ABA also needs the value to actually recur,
/// which is not modelled, so it is a candidate.
pub fn find_aba(threads: &[Thread]) -> Vec<AbaWitness> {
    let per: Vec<_> = threads.iter().map(cas_and_mod_locksets).collect();
    let mut out = Vec::new();
    let mut seen: std::collections::HashSet<String> = std::collections::HashSet::new();
    let mut checked = 0usize;
    for i in 0..threads.len() {
        for j in 0..threads.len() {
            if i == j || checked >= MAX_PAIRS {
                continue;
            }
            checked += 1;
            for (cx, cl) in &per[i].0 {
                for (mx, ml) in &per[j].1 {
                    if cx == mx && cl.is_disjoint(ml) && seen.insert(cx.clone()) {
                        out.push(AbaWitness {
                            location: cx.clone(),
                            threads: (threads[i].name.clone(), threads[j].name.clone()),
                        });
                    }
                }
            }
        }
    }
    out.sort_by(|a, b| a.location.cmp(&b.location));
    out
}

/// A witnessed **concurrent reference-count race**: one thread does an *unchecked* get on an
/// object while another concurrently does a put that may drop the last reference — with disjoint
/// locksets, so nothing orders the get before the final put. The get can then raise a count that
/// already reached zero, resurrecting a freed object (use-after-free). The fix is a *checked* get
/// (`*_inc_not_zero` / `*_get_unless_zero`), which emits no [`Event::RefGet`] and so never fires.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct RefcountRaceWitness {
    /// The refcounted object's class.
    pub location: String,
    /// The threads: the one doing the unchecked get, and the one doing the concurrent put.
    pub threads: (String, String),
}

/// Per-thread, the `(class, lockset)` of every unchecked get and every put.
fn get_and_put_locksets(t: &Thread) -> (ClassLocksets, ClassLocksets) {
    let mut held: std::collections::BTreeSet<String> = std::collections::BTreeSet::new();
    let mut gets = Vec::new();
    let mut puts = Vec::new();
    for e in &t.events {
        match e {
            Event::Acquire(l) => {
                held.insert(l.clone());
            }
            Event::Release(l) => {
                held.remove(l);
            }
            Event::RefGet(x) => gets.push((x.clone(), held.clone())),
            Event::RefPut(x) => puts.push((x.clone(), held.clone())),
            _ => {}
        }
    }
    (gets, puts)
}

/// Whole-program **concurrent refcount race** search: an unchecked get of an object in one thread
/// concurrent (disjoint locksets) with a put of the same object in another thread. Bounded by
/// [`MAX_PAIRS`]. A bug-finding heuristic — a real race also needs the put to actually be the last
/// reference, which is not modelled, so it reports candidates.
pub fn find_refcount_races(threads: &[Thread]) -> Vec<RefcountRaceWitness> {
    let per: Vec<_> = threads.iter().map(get_and_put_locksets).collect();
    let mut out = Vec::new();
    let mut seen: std::collections::HashSet<String> = std::collections::HashSet::new();
    let mut checked = 0usize;
    for i in 0..threads.len() {
        for j in 0..threads.len() {
            if i == j || checked >= MAX_PAIRS {
                continue;
            }
            checked += 1;
            for (gx, gl) in &per[i].0 {
                for (px, pl) in &per[j].1 {
                    if gx == px && gl.is_disjoint(pl) && seen.insert(gx.clone()) {
                        out.push(RefcountRaceWitness {
                            location: gx.clone(),
                            threads: (threads[i].name.clone(), threads[j].name.clone()),
                        });
                    }
                }
            }
        }
    }
    out.sort_by(|a, b| a.location.cmp(&b.location));
    out
}

// ---------------------------------------------------------------------------------------------
// Operational weak-memory model (PSO — per-location store buffers) + SC-robustness check.
// ---------------------------------------------------------------------------------------------

/// A witnessed **weak-memory (SC-robustness) bug**: an execution under the operational
/// store-buffer model observes a read outcome that **no** sequentially-consistent execution can
/// produce — so the code is not robust against weak memory (a barrier is missing). Subsumes the
/// store-buffer (SB) and message-passing (MP, `smp_wmb`) litmus tests.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct WeakMemoryWitness {
    /// The threads involved.
    pub threads: Vec<String>,
    /// A human-readable description of the non-SC observation.
    pub description: String,
    /// The weak-memory schedule (thread name + step) realising the non-SC observation.
    pub schedule: Vec<(String, String)>,
}

/// Cap on operational-model states explored per run (SC or weak). Bounds the (large) reachable
/// set; on reaching it the run gives up — soundly (a missed non-SC observation is a recall
/// loss, never a false witness).
const MAX_OP_STATES: u64 = 400_000;

/// An in-flight write that has left its writer's store buffer and is **propagating** to the
/// other threads' memory views one at a time (non-multi-copy-atomicity — a store reaches
/// different CPUs at different times, which is what makes >2-thread litmus like IRIW possible).
#[derive(Clone, PartialEq, Eq, Hash)]
struct Pending {
    writer: usize,
    loc: String,
    tag: u32,
    // delivered[thread] = whether this write has reached that thread's view yet.
    delivered: Vec<bool>,
}

/// The operational state. `consumed` gives per-event execution (reads may reorder — ARM R→R);
/// `bufs` are per-thread per-location FIFO store buffers (PSO W→W reordering); **`views` are
/// per-thread memory views** and `pending` the in-flight writes still propagating between them
/// (non-multi-copy-atomicity — enables IRIW/WRC across >2 threads). `held`/`obs` as before.
#[derive(Clone, PartialEq, Eq, Hash)]
struct OpState {
    consumed: Vec<Vec<bool>>,
    bufs: Vec<std::collections::BTreeMap<String, Vec<u32>>>,
    // views[thread][location] = the value tag that thread currently observes.
    views: Vec<std::collections::BTreeMap<String, u32>>,
    // Writes still propagating to other threads' views (weak only).
    pending: Vec<Pending>,
    held: Vec<Vec<String>>,
    // spawned[thread] = whether the thread may run yet (a child starts false until its parent
    // executes the corresponding Spawn — a happens-before edge).
    spawned: Vec<bool>,
    obs: std::collections::BTreeMap<u32, u32>,
}

/// Whether thread `t`'s event `i` may execute now. Every earlier **non-read** (a write, barrier
/// or lock op) must already be consumed — those stay in program order. A **read** may addition-
/// ally execute *before* earlier reads when `reorder` (weak memory, ARM R→R reordering), so a
/// consumer's `R(flag);R(data)` can be observed out of order — a read barrier (`smp_rmb`, a
/// non-read) between them re-imposes order. A non-read requires *all* earlier events consumed.
fn takeable(events: &[Event], consumed: &[bool], i: usize, reorder: bool) -> bool {
    if consumed[i] {
        return false;
    }
    // Only a *plain* read reorders; an address-dependent read (`DepRead`) is ordered after
    // everything before it (its address needs the prior read's value).
    let cur_reorderable = reorder && matches!(events[i], Event::Read(_));
    for (j, e) in events.iter().enumerate().take(i) {
        if consumed[j] {
            continue;
        }
        // An earlier unconsumed read (plain or dependent) does not block a reorderable read;
        // anything else (a non-read, or any earlier event when this one is not a reorderable
        // read) blocks.
        let earlier_is_read = matches!(e, Event::Read(_) | Event::DepRead(_));
        if !(earlier_is_read && cur_reorderable) {
            return false;
        }
    }
    true
}

/// Precomputed static data for a set of threads: each write's value tag and each read's global
/// id (so an observation is comparable across the SC and weak runs), plus the thread-spawn
/// relation (`Spawn(name)` in one thread makes the thread named `name` its child).
struct OpProgram<'a> {
    threads: &'a [Thread],
    // write_tag[thread][event_index] = the unique value tag a Write event stores (else 0).
    write_tag: Vec<Vec<u32>>,
    // read_id[thread][event_index] = the global read id a Read event has (else u32::MAX).
    read_id: Vec<Vec<u32>>,
    // parent_of[thread] = the thread that spawns it (if any); such a thread starts unspawned.
    parent_of: Vec<Option<usize>>,
    // spawn_target[thread][event_index] = the child thread index a Spawn event targets (else None).
    spawn_target: Vec<Vec<Option<usize>>>,
}

impl<'a> OpProgram<'a> {
    fn new(threads: &'a [Thread]) -> OpProgram<'a> {
        let mut write_tag = Vec::with_capacity(threads.len());
        let mut read_id = Vec::with_capacity(threads.len());
        let mut spawn_target: Vec<Vec<Option<usize>>> = Vec::with_capacity(threads.len());
        let mut parent_of = vec![None; threads.len()];
        let index_of = |name: &str| threads.iter().position(|t| t.name == name);
        let mut next_tag = 1u32; // 0 = the initial value of every location
        let mut next_read = 0u32;
        for (ti, t) in threads.iter().enumerate() {
            let mut wt = vec![0u32; t.events.len()];
            let mut rd = vec![u32::MAX; t.events.len()];
            let mut sp = vec![None; t.events.len()];
            for (i, e) in t.events.iter().enumerate() {
                match e {
                    Event::Write(_) => {
                        wt[i] = next_tag;
                        next_tag += 1;
                    }
                    Event::Read(_) | Event::DepRead(_) => {
                        rd[i] = next_read;
                        next_read += 1;
                    }
                    Event::Spawn(name) => {
                        if let Some(c) = index_of(name) {
                            if c != ti {
                                sp[i] = Some(c);
                                parent_of[c] = Some(ti);
                            }
                        }
                    }
                    _ => {}
                }
            }
            write_tag.push(wt);
            read_id.push(rd);
            spawn_target.push(sp);
        }
        OpProgram { threads, write_tag, read_id, parent_of, spawn_target }
    }
}

/// The value thread `t` reads for location `x` in `st`: the latest entry in its own store
/// buffer for `x` (store-to-load forwarding), else the value in its own memory view (0 = init).
fn op_read(st: &OpState, t: usize, x: &str) -> u32 {
    if let Some(buf) = st.bufs[t].get(x) {
        if let Some(&v) = buf.last() {
            return v;
        }
    }
    st.views[t].get(x).copied().unwrap_or(0)
}

/// Whether all of thread `t`'s store buffers are empty (needed before a full/write barrier or a
/// lock op may execute — those drain the buffers).
fn bufs_empty(st: &OpState, t: usize) -> bool {
    st.bufs[t].values().all(|b| b.is_empty())
}

/// Whether thread `t` has any write still propagating to other threads' views. A full/write
/// barrier and a lock op block until this is clear — a conservative full sync that makes the
/// thread's prior writes globally visible (so a barrier restores multi-copy atomicity).
fn no_pending_from(st: &OpState, t: usize) -> bool {
    st.pending.iter().all(|p| p.writer != t)
}

/// Whether every in-flight write has already reached thread `t`'s view. A **full** barrier
/// additionally blocks on this, so after it `t`'s view is globally up to date — which is what
/// makes a full barrier between the two reads fix IRIW (the reader gets a consistent view).
fn no_pending_to(st: &OpState, t: usize) -> bool {
    st.pending.iter().all(|p| p.delivered[t])
}

/// Explore the reachable **terminal read-observations** of the program under the operational
/// model — `weak = false` gives sequential consistency (writes go straight to memory), `weak =
/// true` gives PSO (writes buffer per location and flush nondeterministically). Returns a map
/// from the observation (read id → tag) to one example schedule reaching it. Bounded.
fn op_reachable(
    prog: &OpProgram,
    weak: bool,
) -> std::collections::HashMap<std::collections::BTreeMap<u32, u32>, Vec<(usize, String)>> {
    let n = prog.threads.len();
    let init = OpState {
        consumed: prog.threads.iter().map(|t| vec![false; t.events.len()]).collect(),
        bufs: vec![std::collections::BTreeMap::new(); n],
        views: vec![std::collections::BTreeMap::new(); n],
        pending: Vec::new(),
        held: vec![Vec::new(); n],
        // A child thread only becomes runnable when its parent spawns it (happens-before).
        spawned: (0..n).map(|t| prog.parent_of[t].is_none()).collect(),
        obs: std::collections::BTreeMap::new(),
    };
    let mut out = std::collections::HashMap::new();
    let mut visited: std::collections::HashSet<OpState> = std::collections::HashSet::new();
    let mut budget = MAX_OP_STATES;
    let mut stack: Vec<(OpState, Vec<(usize, String)>)> = vec![(init, Vec::new())];
    while let Some((st, sched)) = stack.pop() {
        if budget == 0 {
            break;
        }
        budget -= 1;
        if !visited.insert(st.clone()) {
            continue;
        }
        // Terminal: every event executed, all buffers drained, all writes fully propagated.
        let done = (0..n).all(|t| st.consumed[t].iter().all(|&c| c) && bufs_empty(&st, t))
            && st.pending.is_empty();
        if done {
            out.entry(st.obs.clone()).or_insert_with(|| sched.clone());
            continue;
        }
        if weak {
            // (a) Nondeterministic buffer flushes: the head of some location's buffer leaves the
            // buffer, updates the writer's own view, and starts propagating to the others.
            for t in 0..n {
                let locs: Vec<String> = st.bufs[t].keys().cloned().collect();
                for x in locs {
                    if st.bufs[t].get(&x).is_some_and(|b| !b.is_empty()) {
                        let mut ns = st.clone();
                        let v = ns.bufs[t].get_mut(&x).map(|b| b.remove(0)).unwrap_or(0);
                        ns.views[t].insert(x.clone(), v);
                        let mut delivered = vec![false; n];
                        delivered[t] = true;
                        ns.pending.push(Pending { writer: t, loc: x.clone(), tag: v, delivered });
                        let mut nsched = sched.clone();
                        nsched.push((t, format!("flush {x}")));
                        stack.push((ns, nsched));
                    }
                }
            }
            // (b) Nondeterministic propagation: an in-flight write reaches another thread's view,
            // respecting per-writer-per-location FIFO (coherence) — an earlier pending write to
            // the same (writer, loc) must reach that thread first.
            for (pi, p) in st.pending.iter().enumerate() {
                for u in 0..n {
                    if p.delivered[u] {
                        continue;
                    }
                    let blocked = st.pending[..pi].iter().any(|q| {
                        q.writer == p.writer && q.loc == p.loc && !q.delivered[u]
                    });
                    if blocked {
                        continue;
                    }
                    let mut ns = st.clone();
                    ns.views[u].insert(p.loc.clone(), p.tag);
                    ns.pending[pi].delivered[u] = true;
                    if ns.pending[pi].delivered.iter().all(|&d| d) {
                        ns.pending.remove(pi);
                    }
                    let mut nsched = sched.clone();
                    nsched.push((u, format!("observe {}", p.loc)));
                    stack.push((ns, nsched));
                }
            }
        }
        // Thread steps: any takeable event (reads may reorder under weak memory).
        for t in 0..n {
            // Happens-before: a child thread runs only after its parent has spawned it.
            if !st.spawned[t] {
                continue;
            }
            let events = &prog.threads[t].events;
            for i in 0..events.len() {
                if !takeable(events, &st.consumed[t], i, weak) {
                    continue;
                }
                let ev = &events[i];
                let mut ns = st.clone();
                let step: String = match ev {
                    Event::Write(x) => {
                        let tag = prog.write_tag[t][i];
                        if weak {
                            ns.bufs[t].entry(x.clone()).or_default().push(tag);
                        } else {
                            // SC: a write is instantly visible to every thread (multi-copy atomic).
                            for u in 0..n {
                                ns.views[u].insert(x.clone(), tag);
                            }
                        }
                        format!("write {x}")
                    }
                    Event::Read(x) | Event::DepRead(x) => {
                        let v = op_read(&st, t, x);
                        ns.obs.insert(prog.read_id[t][i], v);
                        format!("read {x} -> {v}")
                    }
                    // A full or write barrier drains this thread's store buffers AND blocks until
                    // its prior writes have fully propagated (conservative full sync — restores
                    // multi-copy atomicity, so a barrier fixes the litmus). A read barrier orders
                    // reads across it (via `takeable`) and needs no buffer/propagation effect.
                    Event::Fence | Event::WFence => {
                        // Both drain the buffer and require this thread's writes to be globally
                        // propagated; a **full** barrier also requires this thread's view to be
                        // fully up to date (no write still owed to it) — fixing IRIW-style reads.
                        if !bufs_empty(&st, t) || !no_pending_from(&st, t) {
                            continue;
                        }
                        if matches!(ev, Event::Fence) && !no_pending_to(&st, t) {
                            continue;
                        }
                        "barrier".into()
                    }
                    Event::RFence => "read-barrier".into(),
                    // A free carries no value effect for the SC-robustness check (cross-thread
                    // UAF has its own detector, `find_cross_thread_uaf`).
                    Event::Free(x) => format!("free {x}"),
                    Event::Cas(x) => format!("cas {x}"),
                    // Refcount get/put carry no value effect for the SC-robustness check (the
                    // concurrent-refcount race has its own detector, `find_refcount_races`).
                    Event::RefGet(x) => format!("ref-get {x}"),
                    Event::RefPut(x) => format!("ref-put {x}"),
                    // A cross-entry typestate marker carries no value effect for the SC search;
                    // it is consumed as a plain step (it has its own detector).
                    Event::Typestate(_) => "typestate".into(),
                    // Spawn the named child: a happens-before edge (it may now run) with release
                    // semantics — the parent's prior writes are made globally visible first, so
                    // the child observes everything the parent did before the spawn.
                    Event::Spawn(name) => {
                        if !bufs_empty(&st, t) || !no_pending_from(&st, t) {
                            continue;
                        }
                        if let Some(c) = prog.spawn_target[t][i] {
                            ns.spawned[c] = true;
                        }
                        format!("spawn {name}")
                    }
                    // Join: a full barrier that blocks until every child this thread spawned has
                    // finished (all its events consumed) — the parent's later events happen after.
                    Event::Join => {
                        // Acquire semantics: every joined child must have finished *and* have its
                        // buffers drained and writes fully propagated, so the parent's later reads
                        // observe them.
                        let children_ok = (0..n).filter(|&c| prog.parent_of[c] == Some(t)).all(|c| {
                            st.consumed[c].iter().all(|&d| d)
                                && bufs_empty(&st, c)
                                && no_pending_from(&st, c)
                        });
                        if !children_ok || !bufs_empty(&st, t) || !no_pending_from(&st, t) {
                            continue;
                        }
                        "join".into()
                    }
                    // A lock op is a full barrier and enforces mutual exclusion.
                    Event::Acquire(l) => {
                        if (0..n).any(|o| o != t && st.held[o].contains(l))
                            || !bufs_empty(&st, t)
                            || !no_pending_from(&st, t)
                        {
                            continue;
                        }
                        ns.held[t].push(l.clone());
                        format!("acquire {l}")
                    }
                    Event::Release(l) => {
                        if !bufs_empty(&st, t) || !no_pending_from(&st, t) {
                            continue;
                        }
                        ns.held[t].retain(|h| h != l);
                        format!("release {l}")
                    }
                };
                ns.consumed[t][i] = true;
                let mut nsched = sched.clone();
                nsched.push((t, step));
                stack.push((ns, nsched));
            }
        }
    }
    out
}

/// **Operational weak-memory robustness check** (subsystem 4, full weak memory): run the set of
/// threads under both sequential consistency and the PSO store-buffer model; if the weak model
/// can produce a read-observation that no SC execution can, the code is **not SC-robust** — a
/// barrier is missing. Returns a witness (the non-SC observation + its weak schedule). Subsumes
/// the store-buffer (SB) and message-passing (MP) litmus tests, and is barrier-aware
/// (`smp_mb`/`smp_wmb`/lock ops drain the buffers, restoring robustness). Bounded.
pub fn weak_memory_nonrobustness(threads: &[Thread]) -> Option<WeakMemoryWitness> {
    // Only worth running when ≥2 threads share a location that at least one writes.
    if threads.len() < 2 {
        return None;
    }
    let prog = OpProgram::new(threads);
    let sc = op_reachable(&prog, false);
    let weak = op_reachable(&prog, true);
    // A weak observation absent from the SC set witnesses non-robustness.
    let (obs, sched) = weak.iter().find(|(o, _)| !sc.contains_key(*o))?;
    // Describe the offending reads (those that read a non-initial-vs-initial value differing
    // from every SC run is hard to phrase concisely; report the stale/reordered reads).
    let names: Vec<String> = threads.iter().map(|t| t.name.clone()).collect();
    let schedule: Vec<(String, String)> =
        sched.iter().map(|(t, s)| (names[*t].clone(), s.clone())).collect();
    let _ = obs;
    Some(WeakMemoryWitness {
        threads: names,
        description: "a read observes a value no sequentially-consistent execution allows \
                      (missing memory barrier)"
            .into(),
        schedule,
    })
}

/// Largest thread group checked as a single simultaneous weak-memory product — >2-thread litmus
/// (IRIW needs 4; some need 5–6) are found, while the (expensive) product stays bounded by the
/// per-run state cap. Larger groups fall back to pairwise.
const MAX_GROUP: usize = 6;

/// Whole-program weak-memory search. Threads that (transitively) share a location where at least
/// one writes form a **connected group**; a group of 2..=[`MAX_GROUP`] threads is checked as one
/// simultaneous product (so a >2-thread litmus like IRIW is caught), a larger group is checked
/// pairwise as a fallback. Bounded by [`MAX_PAIRS`].
pub fn find_weak_memory_bugs(threads: &[Thread]) -> Vec<WeakMemoryWitness> {
    let n = threads.len();
    let touched: Vec<_> = threads.iter().map(|t| t.touched()).collect();
    let written: Vec<_> = threads.iter().map(|t| t.written()).collect();
    let shares = |i: usize, j: usize| {
        written[i].iter().any(|w| touched[j].contains(w))
            || written[j].iter().any(|w| touched[i].contains(w))
    };
    // Union-find over the "shares a written location" relation → connected groups.
    let mut parent: Vec<usize> = (0..n).collect();
    fn find(parent: &mut [usize], x: usize) -> usize {
        let mut r = x;
        while parent[r] != r {
            r = parent[r];
        }
        let mut c = x;
        while parent[c] != r {
            let next = parent[c];
            parent[c] = r;
            c = next;
        }
        r
    }
    for i in 0..n {
        for j in (i + 1)..n {
            if shares(i, j) {
                let (ri, rj) = (find(&mut parent, i), find(&mut parent, j));
                if ri != rj {
                    parent[ri] = rj;
                }
            }
        }
    }
    let mut groups: std::collections::BTreeMap<usize, Vec<usize>> = std::collections::BTreeMap::new();
    for i in 0..n {
        let r = find(&mut parent, i);
        groups.entry(r).or_default().push(i);
    }

    let spawned = spawned_names(threads);
    let mut out = Vec::new();
    let mut checked = 0usize;
    // Self-concurrency: a *spawned* function may run in several threads at once, so check each
    // such writer against a second instance of itself (unbounded thread count).
    for (i, t) in threads.iter().enumerate() {
        if !written[i].is_empty() && spawned.contains(&t.name) {
            let copy = Thread { name: format!("{}#2", t.name), events: t.events.clone() };
            if let Some(w) = weak_memory_nonrobustness(&[clone_thread(t), copy]) {
                out.push(w);
            }
        }
    }
    for group in groups.values() {
        if group.len() < 2 || checked >= MAX_PAIRS {
            continue;
        }
        checked += 1;
        if group.len() <= MAX_GROUP {
            // Check the whole group as one simultaneous product.
            let ts: Vec<Thread> = group.iter().map(|&i| clone_thread(&threads[i])).collect();
            if let Some(w) = weak_memory_nonrobustness(&ts) {
                out.push(w);
            }
        } else {
            // Too large for a full product — fall back to pairwise within the group.
            for a in 0..group.len() {
                for b in (a + 1)..group.len() {
                    if !shares(group[a], group[b]) {
                        continue;
                    }
                    if let Some(w) = weak_memory_nonrobustness(&[
                        clone_thread(&threads[group[a]]),
                        clone_thread(&threads[group[b]]),
                    ]) {
                        out.push(w);
                        break;
                    }
                }
            }
        }
    }
    out
}

fn clone_thread(t: &Thread) -> Thread {
    Thread { name: t.name.clone(), events: t.events.clone() }
}

/// Search for an atomicity violation (lost update) between two threads: a valid interleaving
/// (respecting lock mutual exclusion + per-thread program order) in which one thread's write
/// to `x` lands between the other thread's read of `x` and its later dependent write of `x`.
/// Returns the first witnessing schedule, or `None` if none exists within the bound.
pub fn atomicity_violation(a: &Thread, b: &Thread) -> Option<AtomicityWitness> {
    let mut budget = MAX_STATES;
    let mut schedule: Vec<(usize, Event)> = Vec::new();
    // Per-thread: locks currently held, and locations read-but-not-yet-written (pending RMW).
    let mut st = State::default();
    let names = [a.name.as_str(), b.name.as_str()];
    let traces = [a.events.as_slice(), b.events.as_slice()];
    dfs(&traces, &names, &mut st, &mut schedule, &mut budget)
}

#[derive(Default, Clone)]
struct State {
    // Instruction pointer per thread.
    ip: [usize; 2],
    // Locks held per thread.
    held: [Vec<String>; 2],
    // Locations each thread has read and not yet written (an open RMW).
    pending: [Vec<String>; 2],
    // Locations of an open RMW on a thread that the *other* thread has already written into
    // (the interruption happened; a subsequent same-thread write is the lost update).
    interrupted: [Vec<String>; 2],
}

fn dfs(
    traces: &[&[Event]; 2],
    names: &[&str; 2],
    st: &mut State,
    schedule: &mut Vec<(usize, Event)>,
    budget: &mut u64,
) -> Option<AtomicityWitness> {
    if *budget == 0 {
        return None;
    }
    *budget -= 1;
    // Try stepping each thread from its current instruction pointer.
    for t in 0..2 {
        let other = 1 - t;
        let ip = st.ip[t];
        let Some(ev) = traces[t].get(ip) else { continue };
        // Lock mutual exclusion: an acquire of a lock the other thread holds is blocked now.
        if let Event::Acquire(l) = ev {
            if st.held[other].contains(l) {
                continue; // this thread cannot proceed until `other` releases `l`
            }
        }
        // Apply the event to a child state.
        let mut child = st.clone();
        child.ip[t] += 1;
        match ev {
            // A fence is a no-op for the sequentially-consistent lost-update search (the
            // interleaving is already a total order); it matters only for weak memory. Spawn/join
            // are likewise treated as plain steps here (the SC lost-update pattern is unaffected).
            Event::Fence | Event::WFence | Event::RFence | Event::Spawn(_) | Event::Join
| Event::Free(_) | Event::Cas(_) | Event::RefGet(_) | Event::RefPut(_) | Event::Typestate(_) => {}
            Event::Acquire(l) => child.held[t].push(l.clone()),
            Event::Release(l) => child.held[t].retain(|h| h != l),
            Event::Read(x) | Event::DepRead(x) => {
                if !child.pending[t].contains(x) {
                    child.pending[t].push(x.clone());
                }
            }
            Event::Write(x) => {
                // A write by `t` interrupts an open RMW of the OTHER thread on the same loc.
                if child.pending[other].contains(x) && !child.interrupted[other].contains(x) {
                    child.interrupted[other].push(x.clone());
                }
                // If `t` itself had an open, already-interrupted RMW on `x`, this dependent
                // write is the lost update — the atomicity violation is realised.
                let lost = child.interrupted[t].contains(x);
                child.pending[t].retain(|p| p != x);
                child.interrupted[t].retain(|p| p != x);
                schedule.push((t, ev.clone()));
                if lost {
                    return Some(AtomicityWitness {
                        location: x.clone(),
                        schedule: schedule
                            .iter()
                            .map(|(ti, e)| (names[*ti].to_string(), e.clone()))
                            .collect(),
                    });
                }
                if let Some(w) = dfs(traces, names, &mut child, schedule, budget) {
                    return Some(w);
                }
                schedule.pop();
                continue;
            }
        }
        schedule.push((t, ev.clone()));
        if let Some(w) = dfs(traces, names, &mut child, schedule, budget) {
            return Some(w);
        }
        schedule.pop();
    }
    None
}

#[cfg(test)]
mod tests {
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
            Acquire("L".into()), Write("x".into()), Release("L".into()),
        ]);
        let b = thread("B", vec![Acquire("L".into()), Write("x".into()), Release("L".into())]);
        let w = atomicity_violation(&a, &b).expect("a split-CS RMW is an atomicity violation");
        assert_eq!(w.location, "x");
        // The witness must contain B's write between A's read and A's write.
        let a_writes = w.schedule.iter().position(|(n, e)| n == "A" && matches!(e, Write(_))).unwrap();
        let b_writes = w.schedule.iter().position(|(n, e)| n == "B" && matches!(e, Write(_))).unwrap();
        let a_reads = w.schedule.iter().position(|(n, e)| n == "A" && matches!(e, Read(_))).unwrap();
        assert!(a_reads < b_writes && b_writes < a_writes, "witness realises R_A < W_B < W_A");
    }

    // A single continuous critical section holds L across the whole RMW → mutual exclusion
    // forbids B's write from interleaving → no violation.
    #[test]
    fn continuously_locked_rmw_is_safe() {
        let a = thread("A", vec![
            Acquire("L".into()), Read("x".into()), Write("x".into()), Release("L".into()),
        ]);
        let b = thread("B", vec![Acquire("L".into()), Write("x".into()), Release("L".into())]);
        assert!(atomicity_violation(&a, &b).is_none(), "a continuously-locked RMW is atomic");
    }

    // Different locks: A's RMW under La, B's write under Lb — no mutual exclusion, so B slips
    // into A's (even single-CS) RMW. A genuine race the interleaving exposes.
    #[test]
    fn disjoint_locks_allow_interruption() {
        let a = thread("A", vec![
            Acquire("La".into()), Read("x".into()), Write("x".into()), Release("La".into()),
        ]);
        let b = thread("B", vec![Acquire("Lb".into()), Write("x".into()), Release("Lb".into())]);
        assert!(atomicity_violation(&a, &b).is_some(), "disjoint locks do not order the RMW");
    }

    // No conflicting write from B → no violation.
    #[test]
    fn no_conflicting_write_is_safe() {
        let a = thread("A", vec![Read("x".into()), Write("x".into())]);
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
        let worker = thread("worker", vec![Read("counter".into()), Write("counter".into())]);
        let v = find_atomicity_violations(&[spawner, worker]);
        assert_eq!(v.len(), 1, "a spawned unlocked RMW loses updates against itself");
        // The same worker, never spawned, is not self-checked (no evidence of concurrency).
        let lone = thread("worker", vec![Read("counter".into()), Write("counter".into())]);
        assert!(find_atomicity_violations(&[lone]).is_empty(), "an un-spawned function is not self-raced");
    }
}
