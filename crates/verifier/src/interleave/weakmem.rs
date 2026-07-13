use super::*;

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

/// An in-flight write that has left its writer's store buffer and is **propagating** to the
/// other threads' memory views one at a time (non-multi-copy-atomicity — a store reaches
/// different CPUs at different times, which is what makes >2-thread litmus like IRIW possible).
#[derive(Clone, PartialEq, Eq, Hash)]
pub(crate) struct Pending {
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
pub(crate) struct OpState {
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
pub(crate) fn takeable(events: &[Event], consumed: &[bool], i: usize, reorder: bool) -> bool {
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
pub(crate) struct OpProgram<'a> {
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
    pub(crate) fn new(threads: &'a [Thread]) -> OpProgram<'a> {
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
                    Event::Write(_) | Event::Rmw(_) => {
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
pub(crate) fn op_read(st: &OpState, t: usize, x: &str) -> u32 {
    if let Some(buf) = st.bufs[t].get(x) {
        if let Some(&v) = buf.last() {
            return v;
        }
    }
    st.views[t].get(x).copied().unwrap_or(0)
}

/// Whether all of thread `t`'s store buffers are empty (needed before a full/write barrier or a
/// lock op may execute — those drain the buffers).
pub(crate) fn bufs_empty(st: &OpState, t: usize) -> bool {
    st.bufs[t].values().all(|b| b.is_empty())
}

/// Whether thread `t` has any write still propagating to other threads' views. A full/write
/// barrier and a lock op block until this is clear — a conservative full sync that makes the
/// thread's prior writes globally visible (so a barrier restores multi-copy atomicity).
pub(crate) fn no_pending_from(st: &OpState, t: usize) -> bool {
    st.pending.iter().all(|p| p.writer != t)
}

/// Whether every in-flight write has already reached thread `t`'s view. A **full** barrier
/// additionally blocks on this, so after it `t`'s view is globally up to date — which is what
/// makes a full barrier between the two reads fix IRIW (the reader gets a consistent view).
pub(crate) fn no_pending_to(st: &OpState, t: usize) -> bool {
    st.pending.iter().all(|p| p.delivered[t])
}

/// Explore the reachable **terminal read-observations** of the program under the operational
/// model — `weak = false` gives sequential consistency (writes go straight to memory), `weak =
/// true` gives PSO (writes buffer per location and flush nondeterministically). Returns a map
/// from the observation (read id → tag) to one example schedule reaching it. Bounded.
pub(crate) fn op_reachable(
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
    let mut budget = search_budget(&prog.threads.iter().map(|t| t.events.len()).collect::<Vec<_>>());
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
                    Event::Write(x) | Event::Rmw(x) => {
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
