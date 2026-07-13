use super::*;

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
pub(crate) fn cas_and_mod_locksets(t: &Thread) -> (ClassLocksets, ClassLocksets) {
    let mut lt = LifetimeTracker::new();
    let mut cas = Vec::new();
    let mut modif = Vec::new();
    for e in &t.events {
        if lt.step(e) {
            continue;
        }
        match e {
            Event::Cas(x) => cas.push(lt.snap(x)),
            Event::Write(x) | Event::Rmw(x) | Event::Free(x) => modif.push(lt.snap(x)),
            _ => {}
        }
    }
    (cas, modif)
}

/// Whole-program **ABA** search: a compare-and-swap of a location in one thread concurrent
/// (disjoint locksets) with a modification of the same location in another thread. Bounded by
/// A bug-finding heuristic — a real ABA also needs the value to actually recur,
/// which is not modelled, so it is a candidate.
pub fn find_aba(threads: &[Thread]) -> Vec<AbaWitness> {
    let per: Vec<_> = threads.iter().map(cas_and_mod_locksets).collect();
    let mut out = Vec::new();
    let mut seen: std::collections::HashSet<String> = std::collections::HashSet::new();
    // A CAS in `pa` (thread `na`) vs a concurrent modification in `pb` (thread `nb`).
    let check = |pa: &(ClassLocksets, ClassLocksets),
                     na: &str,
                     pb: &(ClassLocksets, ClassLocksets),
                     nb: &str,
                     out: &mut Vec<AbaWitness>,
                     seen: &mut std::collections::HashSet<String>| {
        for c in &pa.0 {
            for m in &pb.1 {
                if c.0 == m.0
                    && c.1.is_disjoint(&m.1)
                    && !lifetime_ordered(c, na, m, nb)
                    && seen.insert(c.0.clone())
                {
                    out.push(AbaWitness {
                        location: c.0.clone(),
                        threads: (na.to_string(), nb.to_string()),
                    });
                }
            }
        }
    };
    for i in 0..threads.len() {
        for j in 0..threads.len() {
            if i == j {
                continue;
            }
            check(&per[i], &threads[i].name, &per[j], &threads[j].name, &mut out, &mut seen);
        }
    }
    // Self-concurrency: a spawned function's CAS racing a second instance's modification.
    let spawned = spawned_names(threads);
    for i in 0..threads.len() {
        if !per[i].0.is_empty() && spawned.contains(&threads[i].name) {
            let self2 = format!("{}#2", threads[i].name);
            check(&per[i], &threads[i].name, &per[i], &self2, &mut out, &mut seen);
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
pub(crate) fn get_and_put_locksets(t: &Thread) -> (ClassLocksets, ClassLocksets) {
    let mut lt = LifetimeTracker::new();
    let mut gets = Vec::new();
    let mut puts = Vec::new();
    for e in &t.events {
        if lt.step(e) {
            continue;
        }
        match e {
            Event::RefGet(x) => gets.push(lt.snap(x)),
            Event::RefPut(x) => puts.push(lt.snap(x)),
            _ => {}
        }
    }
    (gets, puts)
}

/// Whole-program **concurrent refcount race** search: an unchecked get of an object in one thread
/// concurrent (disjoint locksets) with a put of the same object in another thread. Bounded by
/// A bug-finding heuristic — a real race also needs the put to actually be the last
/// reference, which is not modelled, so it reports candidates.
pub fn find_refcount_races(threads: &[Thread]) -> Vec<RefcountRaceWitness> {
    let per: Vec<_> = threads.iter().map(get_and_put_locksets).collect();
    let mut out = Vec::new();
    let mut seen: std::collections::HashSet<String> = std::collections::HashSet::new();
    // An unchecked get in `pa` (thread `na`) vs a concurrent put in `pb` (thread `nb`).
    let check = |pa: &(ClassLocksets, ClassLocksets),
                     na: &str,
                     pb: &(ClassLocksets, ClassLocksets),
                     nb: &str,
                     out: &mut Vec<RefcountRaceWitness>,
                     seen: &mut std::collections::HashSet<String>| {
        for g in &pa.0 {
            for p in &pb.1 {
                if g.0 == p.0
                    && g.1.is_disjoint(&p.1)
                    && !lifetime_ordered(g, na, p, nb)
                    && seen.insert(g.0.clone())
                {
                    out.push(RefcountRaceWitness {
                        location: g.0.clone(),
                        threads: (na.to_string(), nb.to_string()),
                    });
                }
            }
        }
    };
    for i in 0..threads.len() {
        for j in 0..threads.len() {
            if i == j {
                continue;
            }
            check(&per[i], &threads[i].name, &per[j], &threads[j].name, &mut out, &mut seen);
        }
    }
    // Self-concurrency: a spawned function's unchecked get racing a second instance's put.
    let spawned = spawned_names(threads);
    for i in 0..threads.len() {
        if !per[i].0.is_empty() && spawned.contains(&threads[i].name) {
            let self2 = format!("{}#2", threads[i].name);
            check(&per[i], &threads[i].name, &per[i], &self2, &mut out, &mut seen);
        }
    }
    out.sort_by(|a, b| a.location.cmp(&b.location));
    out
}

// ---------------------------------------------------------------------------------------------
// Operational weak-memory model (PSO — per-location store buffers) + SC-robustness check.
// ---------------------------------------------------------------------------------------------
