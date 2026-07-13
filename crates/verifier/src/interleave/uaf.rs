use super::*;

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

/// A collected shared event: its location `class`, the `lockset` (lock classes held at it), and
/// `joined` — the set of peer thread **function names** this thread has already `Join`ed at this
/// point. An event whose `joined` contains a peer's name happens-*after* every event of that peer
/// (the child finished before this event ran), so the two are **not concurrent** and a pairing
/// between them is dropped — the thread-lifetime happens-before that the lockset check alone misses
/// (e.g. a parent that frees an object only *after* `kthread_stop`-ing the worker that used it).
pub(crate) type ClassLocksets = Vec<(String, std::collections::BTreeSet<String>, std::collections::BTreeSet<String>)>;

/// Track, along a thread's trace, the lockset held and the set of peer names already joined (a
/// `Join` joins every child spawned so far, per [`Event::Join`]). Call `record(class)` at each
/// event of interest to snapshot `(class, lockset, joined)`.
pub(crate) struct LifetimeTracker {
    held: std::collections::BTreeSet<String>,
    spawned: std::collections::BTreeSet<String>,
    joined: std::collections::BTreeSet<String>,
}
impl LifetimeTracker {
    pub(crate) fn new() -> Self {
        Self { held: Default::default(), spawned: Default::default(), joined: Default::default() }
    }
    /// Advance over a control/sync event; returns `true` if `e` was consumed here.
    pub(crate) fn step(&mut self, e: &Event) -> bool {
        match e {
            Event::Acquire(l) => { self.held.insert(l.clone()); true }
            Event::Release(l) => { self.held.remove(l); true }
            Event::Spawn(n) => { self.spawned.insert(n.clone()); true }
            // A join waits for every child spawned so far: they are all now happens-before.
            Event::Join => { self.joined.extend(std::mem::take(&mut self.spawned)); true }
            _ => false,
        }
    }
    pub(crate) fn snap(&self, class: &str) -> (String, std::collections::BTreeSet<String>, std::collections::BTreeSet<String>) {
        (class.to_string(), self.held.clone(), self.joined.clone())
    }
}

/// Two collected events are **lifetime-ordered** (one happens-before the other via a thread
/// join, so they are not concurrent) when either event happened after its thread joined the
/// other's thread. `a`/`b` are the collected records, `an`/`bn` their thread names.
pub(crate) fn lifetime_ordered(
    a: &(String, std::collections::BTreeSet<String>, std::collections::BTreeSet<String>),
    an: &str,
    b: &(String, std::collections::BTreeSet<String>, std::collections::BTreeSet<String>),
    bn: &str,
) -> bool {
    a.2.contains(bn) || b.2.contains(an)
}

/// Per-thread, the `(class, lockset, joined)` of every free and every access (read/write).
pub(crate) fn free_and_access_locksets(t: &Thread) -> (ClassLocksets, ClassLocksets) {
    let mut lt = LifetimeTracker::new();
    let mut frees = Vec::new();
    let mut accesses = Vec::new();
    for e in &t.events {
        if lt.step(e) {
            continue;
        }
        match e {
            Event::Free(x) => frees.push(lt.snap(x)),
            Event::Read(x) | Event::DepRead(x) | Event::Write(x) | Event::Rmw(x) => accesses.push(lt.snap(x)),
            _ => {}
        }
    }
    (frees, accesses)
}

/// Whole-program **cross-thread use-after-free / double-free** search: a free in one thread and a
/// concurrent access (UAF) or free (double-free) of the same object in another thread, with
/// **disjoint locksets** (nothing orders them). A bug-finding
/// heuristic — like Eraser it does not model refcounts or ownership that may order them.
pub fn find_cross_thread_uaf(threads: &[Thread]) -> Vec<FreeUseWitness> {
    let per: Vec<_> = threads.iter().map(free_and_access_locksets).collect();
    let mut out = Vec::new();
    let mut seen: std::collections::HashSet<(String, bool)> = std::collections::HashSet::new();
    // A free in `pa` (thread `na`) vs an access (UAF) or, when `do_double_free`, a free
    // (double-free) in `pb` (thread `nb`), disjoint locksets and not lifetime-ordered.
    let check = |pa: &(ClassLocksets, ClassLocksets),
                     na: &str,
                     pb: &(ClassLocksets, ClassLocksets),
                     nb: &str,
                     do_double_free: bool,
                     out: &mut Vec<FreeUseWitness>,
                     seen: &mut std::collections::HashSet<(String, bool)>| {
        for f in &pa.0 {
            for a in &pb.1 {
                if f.0 == a.0
                    && f.1.is_disjoint(&a.1)
                    && !lifetime_ordered(f, na, a, nb)
                    && seen.insert((f.0.clone(), false))
                {
                    out.push(FreeUseWitness {
                        location: f.0.clone(),
                        threads: (na.to_string(), nb.to_string()),
                        double_free: false,
                    });
                }
            }
            if do_double_free {
                for g in &pb.0 {
                    if f.0 == g.0
                        && f.1.is_disjoint(&g.1)
                        && !lifetime_ordered(f, na, g, nb)
                        && seen.insert((f.0.clone(), true))
                    {
                        out.push(FreeUseWitness {
                            location: f.0.clone(),
                            threads: (na.to_string(), nb.to_string()),
                            double_free: true,
                        });
                    }
                }
            }
        }
    };
    for i in 0..threads.len() {
        for j in 0..threads.len() {
            if i == j {
                continue;
            }
            // Double-free only for `i < j` (avoid the mirror); UAF for every ordered pair.
            check(&per[i], &threads[i].name, &per[j], &threads[j].name, i < j, &mut out, &mut seen);
        }
    }
    // Self-concurrency: a *spawned* function may run in several threads at once, so a free in one
    // instance racing an access/free of the same object in a second instance is a cross-thread
    // UAF / **double-free by the same handler** (the double-close race). Check it against a renamed
    // clone of itself — the same self-concurrency the atomicity/weak-memory passes already model.
    let spawned = spawned_names(threads);
    for i in 0..threads.len() {
        if !per[i].0.is_empty() && spawned.contains(&threads[i].name) {
            let self2 = format!("{}#2", threads[i].name);
            check(&per[i], &threads[i].name, &per[i], &self2, true, &mut out, &mut seen);
        }
    }
    out.sort_by(|a, b| a.location.cmp(&b.location));
    out
}
