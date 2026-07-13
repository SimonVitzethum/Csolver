use super::*;

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

/// Whether thread `t` has a **reorder window** — a program-order pair of shared-memory accesses to
/// *different* locations that the operational weak-memory model can reorder (so its effects can
/// become visible out of order). A non-SC observation is impossible without one, so a group in which
/// no thread has a window is provably SC-robust and the (expensive) product search can be skipped
/// entirely — an *exact* pruning (no witness is lost). The three reorderings the model realises,
/// each blocked by the barrier/lock that orders it:
/// - `W(x) … W(y)` (x≠y), no full or **write** barrier between — store-buffer W→W (PSO);
/// - `W(x) … R(y)` (x≠y), no full barrier between — store-buffer W→R (a write buffered past a read);
/// - `R(x) … R(y)` (x≠y), `R(y)` a *plain* read, no full or **read** barrier between — ARM R→R.
///
/// A lock acquire/release, spawn, join or full fence (`smp_mb`) is a full barrier; `smp_wmb` orders
/// W→W only, `smp_rmb` R→R only; an address-dependent read (`DepRead`) does not reorder.
pub(crate) fn has_reorder_window(t: &Thread) -> bool {
    let ev = &t.events;
    let is_full = |e: &Event| {
        matches!(e, Event::Fence | Event::Acquire(_) | Event::Release(_) | Event::Join | Event::Spawn(_))
    };
    for (q, eq) in ev.iter().enumerate() {
        match eq {
            // A write may be delayed past a *later* write (W→W) or read (W→R) on another location.
            Event::Write(yq) | Event::Rmw(yq) => {
                for ep in ev[..q].iter().rev() {
                    if is_full(ep) || matches!(ep, Event::WFence) {
                        break;
                    }
                    if matches!(ep, Event::Write(xp) | Event::Rmw(xp) if xp != yq) {
                        return true;
                    }
                }
            }
            // A read observes a write buffered before it (W→R), and a plain read may reorder before
            // an earlier read (R→R).
            Event::Read(yq) | Event::DepRead(yq) => {
                for ep in ev[..q].iter().rev() {
                    if is_full(ep) {
                        break;
                    }
                    if matches!(ep, Event::Write(xp) | Event::Rmw(xp) if xp != yq) {
                        return true;
                    }
                }
                // R→R reordering only applies when this read itself may reorder (a plain read).
                if matches!(eq, Event::Read(_)) {
                    for ep in ev[..q].iter().rev() {
                        if is_full(ep) || matches!(ep, Event::RFence) {
                            break;
                        }
                        if matches!(ep, Event::Read(xp) | Event::DepRead(xp) if xp != yq) {
                            return true;
                        }
                    }
                }
            }
            _ => {}
        }
    }
    false
}

/// Whole-program weak-memory search. Threads that (transitively) share a location where at least
/// one writes form a **connected group**; a group whose product fits the memory ceiling is checked as one
/// simultaneous product (so a >2-thread litmus like IRIW is caught), a larger group is checked
/// pairwise as a fallback. A group with no [`has_reorder_window`] thread
/// is skipped — provably SC-robust, so the product search would find nothing.
pub fn find_weak_memory_bugs(threads: &[Thread]) -> Vec<WeakMemoryWitness> {
    let n = threads.len();
    let touched: Vec<_> = threads.iter().map(|t| t.touched()).collect();
    let written: Vec<_> = threads.iter().map(|t| t.written()).collect();
    let window: Vec<bool> = threads.iter().map(has_reorder_window).collect();
    let shares = |i: usize, j: usize| {
        written[i].iter().any(|w| touched[j].contains(w))
            || written[j].iter().any(|w| touched[i].contains(w))
    };
    // Union-find over the "shares a written location" relation → connected groups.
    let mut parent: Vec<usize> = (0..n).collect();
    pub(crate) fn find(parent: &mut [usize], x: usize) -> usize {
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

    // The number of locations two threads share, capped at 2 (that is all the pruning needs). A
    // non-SC observation is about the *relative order* of accesses to ≥2 distinct locations; a
    // single shared location is coherence-ordered (all threads agree), so a pair (or self-pair)
    // sharing fewer than two locations is provably SC-robust — an exact prune, no witness lost.
    let shared_two = |a: &std::collections::BTreeSet<&str>, b: &std::collections::BTreeSet<&str>| {
        a.iter().filter(|x| b.contains(*x)).take(2).count() >= 2
    };
    let spawned = spawned_names(threads);
    let mut out = Vec::new();
    // Self-concurrency: a *spawned* function may run in several threads at once, so check each
    // such writer against a second instance of itself (unbounded thread count).
    for (i, t) in threads.iter().enumerate() {
        // A single self-concurrent thread can only be non-robust against a copy of itself if it has
        // a reorder window and touches ≥2 shared locations.
        if !written[i].is_empty() && window[i] && shared_two(&touched[i], &touched[i]) && spawned.contains(&t.name) {
            let copy = Thread { name: format!("{}#2", t.name), events: t.events.clone() };
            if let Some(w) = weak_memory_nonrobustness(&[clone_thread(t), copy]) {
                out.push(w);
            }
        }
    }
    for group in groups.values() {
        // Exact prune: no member has a reorder window ⇒ the group is SC-robust ⇒ no witness exists.
        if group.len() < 2 || !group.iter().any(|&i| window[i]) {
            continue;
        }
        // Exact prune: a non-SC witness needs two members that share ≥2 locations (a single shared
        // location is coherence-ordered). If no member pair does, the group is SC-robust.
        let group_pair_two = || {
            group.iter().enumerate().any(|(x, &i)| {
                group[x + 1..].iter().any(|&j| shared_two(&touched[i], &touched[j]))
            })
        };
        if !group_pair_two() {
            continue;
        }
        let group_events: Vec<usize> = group.iter().map(|&i| threads[i].events.len()).collect();
        if product_fits(&group_events) {
            // The whole-group product fits the memory ceiling — check it simultaneously.
            let ts: Vec<Thread> = group.iter().map(|&i| clone_thread(&threads[i])).collect();
            if let Some(w) = weak_memory_nonrobustness(&ts) {
                out.push(w);
            }
        } else {
            // The product exceeds the ceiling — decompose to pairwise within the group.
            for a in 0..group.len() {
                for b in (a + 1)..group.len() {
                    // A pair is SC-robust unless a thread has a reorder window, one writes a shared
                    // location, AND they share ≥2 locations (a single shared location is coherence-
                    // ordered). All three are necessary conditions — each an exact prune.
                    if !(window[group[a]] || window[group[b]])
                        || !shares(group[a], group[b])
                        || !shared_two(&touched[group[a]], &touched[group[b]])
                    {
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
