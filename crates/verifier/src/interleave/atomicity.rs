use super::*;

/// Whole-program atomicity search: over all thread traces, check every pair that shares a
/// location where at least one writes it, in both orders, and collect the witnessed atomicity
/// violations (one per location, most-relevant first).
pub fn find_atomicity_violations(threads: &[Thread]) -> Vec<AtomicityWitness> {
    let mut out: Vec<AtomicityWitness> = Vec::new();
    let mut seen_loc: std::collections::HashSet<String> = std::collections::HashSet::new();
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
pub(crate) fn buffered_write_read_pairs(t: &Thread) -> std::collections::BTreeSet<(String, String)> {
    let mut pairs = std::collections::BTreeSet::new();
    // For each write, scan forward to reads until a barrier is hit.
    for (i, ev) in t.events.iter().enumerate() {
        let (Event::Write(x) | Event::Rmw(x)) = ev else { continue };
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
/// weak-memory bug. Bug-finding: the reordering is only a bug if the
/// code relies on the SC outcome (a flag handshake / Dekker lock), so it is a candidate.
pub fn store_buffer_violations(threads: &[Thread]) -> Vec<StoreBufferWitness> {
    let pairs: Vec<_> = threads.iter().map(buffered_write_read_pairs).collect();
    let mut out = Vec::new();
    let mut seen: std::collections::HashSet<(String, String)> = std::collections::HashSet::new();
    for i in 0..threads.len() {
        for j in (i + 1)..threads.len() {
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

pub(crate) fn clone_thread(t: &Thread) -> Thread {
    Thread { name: t.name.clone(), events: t.events.clone() }
}

/// Search for an atomicity violation (lost update) between two threads: a valid interleaving
/// (respecting lock mutual exclusion + per-thread program order) in which one thread's write
/// to `x` lands between the other thread's read of `x` and its later dependent write of `x`.
/// Returns the first witnessing schedule, or `None` if none exists within the bound.
pub fn atomicity_violation(a: &Thread, b: &Thread) -> Option<AtomicityWitness> {
    let mut budget = search_budget(&[a.events.len(), b.events.len()]);
    let mut schedule: Vec<(usize, Event)> = Vec::new();
    // Per-thread: locks currently held, and locations read-but-not-yet-written (pending RMW).
    let mut st = State::default();
    let names = [a.name.as_str(), b.name.as_str()];
    let traces = [a.events.as_slice(), b.events.as_slice()];
    dfs(&traces, &names, &mut st, &mut schedule, &mut budget)
}

#[derive(Default, Clone)]
pub(crate) struct State {
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

pub(crate) fn dfs(
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
            Event::Rmw(x) => {
                // A read-modify-write by `t` interrupts an open RMW of the OTHER thread on `x`.
                if child.pending[other].contains(x) && !child.interrupted[other].contains(x) {
                    child.interrupted[other].push(x.clone());
                }
                // If `t` itself had an open, already-interrupted RMW on `x`, this *dependent*
                // (load-derived) write is the lost update — the atomicity violation is realised.
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
            Event::Write(x) => {
                // A *plain* (independent) write interrupts the OTHER thread's open RMW — it changed
                // `x` under them — but it is NOT itself a lost update: its stored value does not
                // depend on a prior read of `x` (an `x = const` overwrite, not `x = x + 1`), so
                // nothing was computed from stale data. It just closes `t`'s own RMW window.
                if child.pending[other].contains(x) && !child.interrupted[other].contains(x) {
                    child.interrupted[other].push(x.clone());
                }
                child.pending[t].retain(|p| p != x);
                child.interrupted[t].retain(|p| p != x);
                schedule.push((t, ev.clone()));
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
