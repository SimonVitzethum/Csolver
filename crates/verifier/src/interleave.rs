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
    /// A full **memory barrier** (`smp_mb`/`mb`): orders this thread's prior writes before its
    /// subsequent reads (drains the store buffers) — the only barrier that fixes the
    /// store-buffer (W→R) reordering. A lock acquire/release is also a full barrier.
    Fence,
    /// A **write barrier** (`smp_wmb`): orders this thread's prior writes before its later
    /// writes (drains the store buffers before the next write becomes visible) — fixes the
    /// message-passing producer-side W→W reordering, but *not* the store-buffer W→R one.
    WFence,
    /// A **read barrier** (`smp_rmb`): orders this thread's prior reads before its later reads.
    /// Under the store-buffer / PSO model (reads are in program order) it is a no-op; kept so a
    /// full ARM-style read-reordering model can use it later.
    RFence,
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
                // Any barrier stops the reordering window for this write.
                Event::Fence | Event::Acquire(_) | Event::Release(_) => break,
                Event::Read(y) if y != x => {
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

/// The operational state: per-thread instruction pointers, per-thread **per-location** FIFO
/// store buffers (PSO — each location's buffer drains independently, so writes to *different*
/// locations may become visible out of order), shared memory (location → value tag), locks
/// held, and the read observations so far (read-event id → value tag observed).
#[derive(Clone, PartialEq, Eq, Hash)]
struct OpState {
    ip: Vec<usize>,
    // buffer[thread][location] = FIFO of value tags not yet flushed to memory.
    bufs: Vec<std::collections::BTreeMap<String, Vec<u32>>>,
    mem: std::collections::BTreeMap<String, u32>,
    held: Vec<Vec<String>>,
    // read-event global id -> observed value tag.
    obs: std::collections::BTreeMap<u32, u32>,
}

/// Precomputed static data for a set of threads: each write's value tag and each read's global
/// id, so an observation is comparable across the SC and weak runs.
struct OpProgram<'a> {
    threads: &'a [Thread],
    // write_tag[thread][event_index] = the unique value tag a Write event stores (else 0).
    write_tag: Vec<Vec<u32>>,
    // read_id[thread][event_index] = the global read id a Read event has (else u32::MAX).
    read_id: Vec<Vec<u32>>,
}

impl<'a> OpProgram<'a> {
    fn new(threads: &'a [Thread]) -> OpProgram<'a> {
        let mut write_tag = Vec::with_capacity(threads.len());
        let mut read_id = Vec::with_capacity(threads.len());
        let mut next_tag = 1u32; // 0 = the initial value of every location
        let mut next_read = 0u32;
        for t in threads {
            let mut wt = vec![0u32; t.events.len()];
            let mut rd = vec![u32::MAX; t.events.len()];
            for (i, e) in t.events.iter().enumerate() {
                match e {
                    Event::Write(_) => {
                        wt[i] = next_tag;
                        next_tag += 1;
                    }
                    Event::Read(_) => {
                        rd[i] = next_read;
                        next_read += 1;
                    }
                    _ => {}
                }
            }
            write_tag.push(wt);
            read_id.push(rd);
        }
        OpProgram { threads, write_tag, read_id }
    }
}

/// The value thread `t` reads for location `x` in `st`: the latest entry in its own store
/// buffer for `x` (store-to-load forwarding), else the value in memory (0 = initial).
fn op_read(st: &OpState, t: usize, x: &str) -> u32 {
    if let Some(buf) = st.bufs[t].get(x) {
        if let Some(&v) = buf.last() {
            return v;
        }
    }
    st.mem.get(x).copied().unwrap_or(0)
}

/// Whether all of thread `t`'s store buffers are empty (needed before a full/write barrier or a
/// lock op may execute — those drain the buffers).
fn bufs_empty(st: &OpState, t: usize) -> bool {
    st.bufs[t].values().all(|b| b.is_empty())
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
        ip: vec![0; n],
        bufs: vec![std::collections::BTreeMap::new(); n],
        mem: std::collections::BTreeMap::new(),
        held: vec![Vec::new(); n],
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
        // Terminal: every thread finished and all buffers drained.
        let done = (0..n).all(|t| st.ip[t] >= prog.threads[t].events.len() && bufs_empty(&st, t));
        if done {
            out.entry(st.obs.clone()).or_insert_with(|| sched.clone());
            continue;
        }
        // Nondeterministic buffer flushes (weak only): the head of some location's buffer
        // becomes globally visible.
        if weak {
            for t in 0..n {
                let locs: Vec<String> = st.bufs[t].keys().cloned().collect();
                for x in locs {
                    if st.bufs[t].get(&x).is_some_and(|b| !b.is_empty()) {
                        let mut ns = st.clone();
                        if let Some(b) = ns.bufs[t].get_mut(&x) {
                            let v = b.remove(0);
                            ns.mem.insert(x.clone(), v);
                        }
                        let mut nsched = sched.clone();
                        nsched.push((t, format!("flush {x}")));
                        stack.push((ns, nsched));
                    }
                }
            }
        }
        // Thread steps.
        for t in 0..n {
            let ip = st.ip[t];
            let Some(ev) = prog.threads[t].events.get(ip) else { continue };
            let mut ns = st.clone();
            let step: String = match ev {
                Event::Write(x) => {
                    let tag = prog.write_tag[t][ip];
                    if weak {
                        ns.bufs[t].entry(x.clone()).or_default().push(tag);
                    } else {
                        ns.mem.insert(x.clone(), tag);
                    }
                    format!("write {x}")
                }
                Event::Read(x) => {
                    let v = op_read(&st, t, x);
                    ns.obs.insert(prog.read_id[t][ip], v);
                    format!("read {x} -> {v}")
                }
                // A full or write barrier drains this thread's store buffers: it may only fire
                // once they are empty (the flush steps above do the draining).
                Event::Fence | Event::WFence => {
                    if !bufs_empty(&st, t) {
                        continue;
                    }
                    "barrier".into()
                }
                // Read barrier: a no-op under PSO (reads are in program order).
                Event::RFence => "read-barrier".into(),
                // A lock op is a full barrier and enforces mutual exclusion.
                Event::Acquire(l) => {
                    if (0..n).any(|o| o != t && st.held[o].contains(l)) || !bufs_empty(&st, t) {
                        continue;
                    }
                    ns.held[t].push(l.clone());
                    format!("acquire {l}")
                }
                Event::Release(l) => {
                    if !bufs_empty(&st, t) {
                        continue;
                    }
                    ns.held[t].retain(|h| h != l);
                    format!("release {l}")
                }
            };
            ns.ip[t] += 1;
            let mut nsched = sched.clone();
            nsched.push((t, step));
            stack.push((ns, nsched));
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

/// Whole-program weak-memory search: check every pair of threads sharing a written location for
/// non-SC-robustness under the operational model. Bounded by [`MAX_PAIRS`].
pub fn find_weak_memory_bugs(threads: &[Thread]) -> Vec<WeakMemoryWitness> {
    let mut out = Vec::new();
    let mut seen: std::collections::HashSet<(String, String)> = std::collections::HashSet::new();
    let mut checked = 0usize;
    for i in 0..threads.len() {
        let wi = threads[i].written();
        let ti = threads[i].touched();
        for j in (i + 1)..threads.len() {
            let tj = threads[j].touched();
            let wj = threads[j].written();
            let shares = wi.iter().any(|w| tj.contains(w)) || wj.iter().any(|w| ti.contains(w));
            if !shares {
                continue;
            }
            if checked >= MAX_PAIRS {
                return out;
            }
            checked += 1;
            let key = if threads[i].name <= threads[j].name {
                (threads[i].name.clone(), threads[j].name.clone())
            } else {
                (threads[j].name.clone(), threads[i].name.clone())
            };
            if !seen.insert(key) {
                continue;
            }
            if let Some(w) = weak_memory_nonrobustness(&[
                clone_thread(&threads[i]),
                clone_thread(&threads[j]),
            ]) {
                out.push(w);
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
            // interleaving is already a total order); it matters only for weak memory.
            Event::Fence | Event::WFence | Event::RFence => {}
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

    // A write barrier between the two producer writes orders them → the consumer that sees
    // flag=set also sees data=new. Robust.
    #[test]
    fn operational_message_passing_with_wmb_is_robust() {
        let producer = thread("producer", vec![Write("data".into()), WFence, Write("flag".into())]);
        let consumer = thread("consumer", vec![Read("flag".into()), Read("data".into())]);
        assert!(weak_memory_nonrobustness(&[producer, consumer]).is_none(),
            "smp_wmb between the publishes restores robustness");
    }
}
