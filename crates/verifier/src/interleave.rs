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
    /// Write the shared location of the given class.
    Write(String),
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
                Event::Read(x) | Event::Write(x) => Some(x.as_str()),
                _ => None,
            })
            .collect()
    }
}

/// Whole-program atomicity search: over all thread traces, check every pair that shares a
/// location where at least one writes it, in both orders, and collect the witnessed atomicity
/// violations (one per location, most-relevant first). Bounded by [`MAX_PAIRS`].
pub fn find_atomicity_violations(threads: &[Thread]) -> Vec<AtomicityWitness> {
    let mut out: Vec<AtomicityWitness> = Vec::new();
    let mut seen_loc: std::collections::HashSet<String> = std::collections::HashSet::new();
    let mut pairs = 0usize;
    for i in 0..threads.len() {
        let ti_written = threads[i].written();
        let ti_touched = threads[i].touched();
        if ti_written.is_empty() && ti_touched.is_empty() {
            continue;
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
            Event::Acquire(l) => child.held[t].push(l.clone()),
            Event::Release(l) => child.held[t].retain(|h| h != l),
            Event::Read(x) => {
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
}
