use super::*;

pub(crate) fn facts_scan(dir: &Path, closed_world: bool) -> Result<ExitCode, String> {
    let mut files = Vec::new();
    collect_ll(dir, &mut files);
    files.sort();
    if files.is_empty() {
        return Err(format!("no .ll files found under {}", dir.display()));
    }
    let cores = worker_count();
    eprintln!(
        "whole-program facts: streaming {} .ll files under {} … ({cores} workers)",
        files.len(),
        dir.display()
    );
    let start = std::time::Instant::now();
    let (facts, lowered, peak_rss) = stream_program_facts(dir, &files, closed_world);

    println!("== whole-program facts ==");
    println!("  files                : {} ({lowered} lowered)", files.len());
    println!("  functions            : {}", facts.n_functions);
    println!("  effect summaries     : {}", facts.summaries.len());
    println!("  scalar preconditions : {}", facts.scalars.len());
    println!("  pointer contracts    : {}", facts.ptr_contracts.len());
    println!("  field contracts      : {}", facts.field_contracts.len());
    println!("  peak RSS             : {peak_rss} MB");
    println!("  wall time            : {:.1}s", start.elapsed().as_secs_f64());
    Ok(ExitCode::SUCCESS)
}

pub(crate) fn scan_dir(dir: &Path, config: &Config, cross_file: bool, whole_program: bool) -> Result<ExitCode, String> {
    use std::sync::atomic::{AtomicUsize, Ordering};
    use std::sync::Mutex;

    let mut files = Vec::new();
    collect_ll(dir, &mut files);
    files.sort();
    if files.is_empty() {
        return Err(format!("no .ll files found under {}", dir.display()));
    }
    let total_files = files.len();

    // Whole-program pass 1 (2b): stream the four fact builders over the entire tree in
    // bounded memory to get every function's effect summary AND preconditions by name,
    // then verify (pass 2) with cross-file `Symbol` calls resolved and external callees'
    // preconditions overlaid against them. The facts are bit-identical to linking the
    // whole program, so cross-TU calls use their real summary and cross-file caller→callee
    // validation flows in — while peak RAM stays bounded by the compact facts, not a giant
    // linked module. The precondition overlay is only closed-world-sound, so pass `--closed-world`
    // to gain it; without it the maps are empty and only effect summaries apply.
    let facts = if whole_program {
        eprintln!(
            "whole-program (2b): pass 1 — streaming whole-program facts over {total_files} files …"
        );
        let (facts, lowered, peak_rss) = stream_program_facts(dir, &files, config.closed_world);
        eprintln!(
            "  … {} effect summaries, {} scalar / {} ptr / {} field preconditions \
             ({lowered} files lowered, peak RSS {peak_rss} MB); pass 2 — verifying",
            facts.name_summaries.len(),
            facts.name_scalars.len(),
            facts.name_ptr_contracts.len(),
            facts.name_field_contracts.len(),
        );
        Some(facts)
    } else {
        None
    };
    let wp_ctx = facts.as_ref().map(|f| f.context());

    // A **unit** of work: one file (normal per-TU scan) or one directory group linked into
    // a whole-program module (cross-file). Cross-file groups the .ll by their parent
    // directory — a subsystem's files (e.g. all of net/rds/) link together, so a caller's
    // validation flows into its callee across the file boundary.
    let units: Vec<(String, Vec<std::path::PathBuf>)> = if cross_file {
        let mut groups: std::collections::BTreeMap<String, Vec<std::path::PathBuf>> =
            std::collections::BTreeMap::new();
        for f in &files {
            let key = f.parent().unwrap_or(dir).strip_prefix(dir).unwrap_or(dir).display().to_string();
            groups.entry(key).or_default().push(f.clone());
        }
        groups.into_iter().collect()
    } else {
        files
            .iter()
            .map(|f| (f.display().to_string(), vec![f.clone()]))
            .collect()
    };
    let total_units = units.len();

    // Parallelise across UNITS (work-stealing). With many units (a big tree) each worker
    // takes a whole core; with few large units (cross-file groups) we also hand each unit
    // function-level threads, so the cores stay busy either way. Deterministic: per-unit
    // results are re-sorted into unit order and each verdict is thread-count independent.
    // `cores` is the machine's physical parallelism; `workers` is how many units run
    // concurrently (capped by `CSOLVER_JOBS` for memory, since each concurrent unit is a
    // resident module). The remaining cores are handed to each unit as function-level
    // threads, so a few large cross-file groups still saturate the machine instead of
    // pinning one core each. `CSOLVER_JOBS=N` therefore trades concurrent-module memory
    // (N modules resident) for intra-unit parallelism (cores/N threads each), without ever
    // leaving cores idle. The reservation-based backpressure (`await_memory`) throttles
    // starts further when several large analyses are in flight.
    let cores = std::thread::available_parallelism().map_or(1, |n| n.get());
    let job_cap = std::env::var("CSOLVER_JOBS").ok().and_then(|v| v.parse::<usize>().ok());
    let workers = job_cap.unwrap_or(cores).min(cores).min(total_units).max(1);
    // Symbolic execution and SAT solving are pointer-chasing (memory-latency-bound), so a
    // running thread stalls on cache misses and yields well under a full core. Modestly
    // *oversubscribing* threads (more than cores) hides that latency — while one thread waits
    // on memory another computes. `CSOLVER_THREADS_PER_UNIT=N` sets it explicitly (total
    // threads ≈ workers×N); the default keeps total ≈ cores.
    let threads_per_unit = std::env::var("CSOLVER_THREADS_PER_UNIT")
        .ok()
        .and_then(|v| v.parse::<usize>().ok())
        .unwrap_or((cores / workers).max(1))
        .max(1);
    eprintln!(
        "scanning {total_files} .ll files under {} … ({total_units} units, {workers} workers × {threads_per_unit} threads{})",
        dir.display(),
        if cross_file { ", cross-file" } else { "" }
    );

    let next = AtomicUsize::new(0);
    let done = AtomicUsize::new(0);
    let active = AtomicUsize::new(0);
    // Live findings counter + de-dup set: each bug is streamed to stderr the moment its
    // unit finishes (unbuffered, so a long scan surfaces bugs as they are found — visible
    // in `tail -f`), and the same bug appearing in many files is reported once.
    let found = AtomicUsize::new(0);
    let seen_find: Mutex<std::collections::HashSet<FindingKey>> = Mutex::new(std::collections::HashSet::new());
    // Byte-identical units are verified once (see `scan_one_unit`): skips re-analysis of
    // literally duplicated files and keeps the coverage counts free of those duplicates.
    let content_seen: Mutex<std::collections::HashSet<u64>> = Mutex::new(std::collections::HashSet::new());
    let results: Mutex<Vec<(usize, FileScan)>> = Mutex::new(Vec::with_capacity(total_units));
    // Units whose exploration hit the budget: deferred to a full-effort serial phase
    // instead of being counted as Unknown now (A3 — "pause the file until the others
    // are done, then finish it with the whole machine").
    let deferred: Mutex<Vec<usize>> = Mutex::new(Vec::new());

    std::thread::scope(|s| {
        for _ in 0..workers {
            s.spawn(|| loop {
                // Cooperative pause at the unit boundary (before claiming the next unit),
                // so a pause never interrupts an in-flight analysis. No-op unless
                // `CSOLVER_PAUSE_FILE` is set and present.
                await_unpause();
                let i = next.fetch_add(1, Ordering::Relaxed);
                if i >= total_units {
                    break;
                }
                // Memory backpressure: hold off starting this file while RAM is tight and
                // other files are still in flight (they free memory as they finish).
                await_memory(&active);
                active.fetch_add(1, Ordering::Relaxed);
                let (label, unit) = &units[i];
                let fs = scan_one_unit(unit, label, dir, config, cross_file, threads_per_unit, &content_seen, wp_ctx);
                active.fetch_sub(1, Ordering::Relaxed);
                let d = done.fetch_add(1, Ordering::Relaxed) + 1;
                if d.is_multiple_of(50) {
                    eprintln!("  … {d}/{total_units} units");
                }
                if fs.truncated {
                    // Deferred: its findings are re-produced (and streamed) in phase 2, so
                    // do not stream the discarded partial result here (avoids duplicates).
                    deferred.lock().unwrap_or_else(|p| p.into_inner()).push(i);
                } else {
                    stream_findings(&fs, &found, &seen_find);
                    results.lock().unwrap_or_else(|p| p.into_inner()).push((i, fs));
                }
            });
        }
    });

    // Phase 2: re-scan the budget-limited units serially with the clock disabled, so each
    // gets the full machine and a real chance to *decide* instead of an Unknown that was
    // only a resource limit. Serial (workers=1, all threads to one unit): the parallel pass
    // is done, so there is no contention to yield to. Deterministic: results are re-sorted.
    let mut deferred = deferred.into_inner().unwrap_or_else(|p| p.into_inner());
    if !deferred.is_empty() {
        deferred.sort_unstable();
        eprintln!("  deferred {} budget-limited unit(s) → full-effort re-scan …", deferred.len());
        let mut unbounded = config.clone();
        unbounded.time_budget = None;
        let all_threads = std::thread::available_parallelism().map_or(1, |n| n.get());
        for i in deferred {
            await_unpause();
            let (label, unit) = &units[i];
            let fs = scan_one_unit(unit, label, dir, &unbounded, cross_file, all_threads, &content_seen, wp_ctx);
            stream_findings(&fs, &found, &seen_find);
            results.lock().unwrap_or_else(|p| p.into_inner()).push((i, fs));
        }
    }

    // Aggregate in unit order (deterministic output).
    let mut all = results.into_inner().unwrap_or_else(|p| p.into_inner());
    all.sort_by_key(|(i, _)| *i);
    let (mut pass, mut fail, mut unknown, mut dropped, mut errored) = (0u64, 0u64, 0u64, 0u64, 0u64);
    let mut findings: Vec<Finding> = Vec::new();
    let mut lock_edges: Vec<(String, String, String)> = Vec::new();
    let mut race_accesses: Vec<(String, String, bool, Vec<String>)> = Vec::new();
    let mut race_traces: Vec<(String, Vec<(u8, String)>)> = Vec::new();
    let mut call_edges: Vec<(String, Vec<String>)> = Vec::new();
    let mut defined_fns: Vec<String> = Vec::new();
    let mut addr_taken: Vec<String> = Vec::new();
    let mut indirect_callers: Vec<String> = Vec::new();
    for (_, fs) in all {
        pass += fs.pass;
        fail += fs.fail;
        unknown += fs.unknown;
        dropped += fs.dropped;
        errored += fs.errored;
        findings.extend(fs.findings);
        lock_edges.extend(fs.lock_edges);
        race_accesses.extend(fs.race_accesses);
        race_traces.extend(fs.race_traces);
        call_edges.extend(fs.call_edges);
        defined_fns.extend(fs.defined_fns);
        addr_taken.extend(fs.addr_taken);
        indirect_callers.extend(fs.indirect_callers);
    }
    // De-duplicate the inventory: the same bug in many files (a duplicated / static-inline
    // function) is one finding, not N. Keeps the first (unit-ordered) occurrence.
    let mut seen: std::collections::HashSet<FindingKey> = std::collections::HashSet::new();
    findings.retain(|f| seen.insert(finding_key(f)));

    // Attack-surface reporting lens (opt-in `--attack-surface`): keep only findings in
    // functions directly reachable from a syscall / `*ioctl*` entry, dropping the internal
    // driver-callback mass that `--auto-entries` promotes to free-parameter entries and that
    // is reachable only through *indirect* ops dispatch. A pure reporting filter — verdicts
    // and the coverage counts below are unchanged, so it can never mask a false PASS; it only
    // narrows the printed violation inventory (trading recall for attack-surface precision).
    if config.attack_surface_only {
        let reach = attack_surface_reachable(&call_edges, &defined_fns);
        let before = findings.len();
        findings.retain(|f| reach.contains(&f.function));
        eprintln!(
            "  --attack-surface: {} of {before} findings kept (syscall/ioctl-reachable); {} internal-callback findings suppressed",
            findings.len(),
            before - findings.len(),
        );
    }

    let entry_patterns = config.entry_patterns.as_deref().unwrap_or(&[]);
    // Concurrency oracle for the whole-program scan: over the aggregated call graph, the set of
    // functions reachable from a concurrent seed — an attacker entry (`--entries`) or a spawned
    // thread / registered IRQ-work-timer handler (a `spawn` trace event). A function outside it is
    // single-threaded-reachable and cannot race, so the concurrent-* detectors skip it. Empty seed
    // (no entries, no spawn evidence) ⇒ `None` ⇒ pair-all, never dropping a real race.
    let concurrent = whole_program_concurrent(
        &call_edges,
        &race_traces,
        entry_patterns,
        &defined_fns,
        &addr_taken,
        &indirect_callers,
    );

    report_lock_cycles(&lock_edges);
    report_data_races(&race_accesses);
    report_atomicity(&race_traces, entry_patterns, concurrent.as_ref());
    report_scan(&findings, pass, fail, unknown, dropped, errored)
}

/// The set of functions that can run concurrently (for the whole-program concurrency oracle): the
/// direct-call-graph closure from a concurrent seed — functions matching an entry pattern, and the
/// targets of `spawn` events (kthread/pthread/work/irq/timer handlers). `None` when the seed is
/// empty (no entries and no spawn evidence): then the oracle does not fire and all threads are
/// paired, so a real race is never dropped. Direct calls only — a function reachable *solely* via an
/// indirect call from a concurrent context may be missed (a recall trade-off), which the spawn/irq/
/// work/timer handler seeds (themselves the indirect-call targets) largely cover.
pub(crate) fn whole_program_concurrent(
    call_edges: &[(String, Vec<String>)],
    race_traces: &[(String, Vec<(u8, String)>)],
    entry_patterns: &[String],
    defined_fns: &[String],
    addr_taken: &[String],
    indirect_callers: &[String],
) -> Option<std::collections::HashSet<String>> {
    use std::collections::{HashMap, HashSet};
    let mut edges: HashMap<&str, Vec<&str>> = HashMap::new();
    for (caller, callees) in call_edges {
        edges.entry(caller).or_default().extend(callees.iter().map(String::as_str));
    }
    // Seed: entries + spawn targets (trace event kind 7).
    let mut reach: HashSet<String> = HashSet::new();
    for (name, _) in call_edges {
        if csolver_verifier::matches_entry(name, entry_patterns) {
            reach.insert(name.clone());
        }
    }
    for (_, tr) in race_traces {
        for (k, child) in tr {
            if *k == 7 {
                reach.insert(child.clone());
            }
        }
    }
    if reach.is_empty() {
        return None; // no concurrency evidence — do not restrict (pair-all)
    }
    // Address-taken functions are the possible targets of any indirect call. Precompute the set so
    // the closure below can, on first reaching an indirect-call site, admit all of them at once.
    let defined: HashSet<&str> = defined_fns.iter().map(String::as_str).collect();
    let indirect_set: HashSet<&str> = indirect_callers.iter().map(String::as_str).collect();
    let addr_fns: Vec<&str> =
        addr_taken.iter().map(String::as_str).filter(|s| defined.contains(s)).collect();
    let mut indirect_admitted = false;
    let mut work: Vec<String> = reach.iter().cloned().collect();
    while let Some(f) = work.pop() {
        // Reaching a concurrent function that performs an indirect call means the call could
        // dispatch to any address-taken function; admit them all once (sound over-approximation).
        if !indirect_admitted && indirect_set.contains(f.as_str()) {
            indirect_admitted = true;
            for &g in &addr_fns {
                if reach.insert(g.to_string()) {
                    work.push(g.to_string());
                }
            }
        }
        if let Some(callees) = edges.get(f.as_str()) {
            for &c in callees {
                if reach.insert(c.to_string()) {
                    work.push(c.to_string());
                }
            }
        }
    }
    Some(reach)
}

/// The **genuine attacker surface**: functions directly reachable (whole-program direct-call
/// graph) from a syscall wrapper or an `*ioctl*` handler. `--attack-surface` reports only
/// findings in this set. Seeds on the syscall entry prefixes and any defined function whose
/// name contains `ioctl`, then closes over **direct** call edges only — so an internal driver
/// callback reached solely through *indirect* ops dispatch (a register accessor, a clk/drm op),
/// which has no direct edge from the entry, is excluded. That is exactly the false-positive mass
/// `--auto-entries` creates by treating every ops-struct handler as a free-parameter entry.
pub(crate) fn attack_surface_reachable(
    call_edges: &[(String, Vec<String>)],
    defined_fns: &[String],
) -> std::collections::HashSet<String> {
    use std::collections::{HashMap, HashSet};
    let mut seed_pats: Vec<String> = SYSCALL_ENTRY_PREFIXES.iter().map(|s| s.to_string()).collect();
    seed_pats.push("*ioctl*".to_string());
    let mut edges: HashMap<&str, Vec<&str>> = HashMap::new();
    for (caller, callees) in call_edges {
        edges.entry(caller).or_default().extend(callees.iter().map(String::as_str));
    }
    let mut reach: HashSet<String> = HashSet::new();
    let mut work: Vec<String> = Vec::new();
    // Seed: every genuine-entry function (defined in the tree, or a caller in the graph).
    let names = defined_fns.iter().chain(call_edges.iter().map(|(c, _)| c));
    for name in names {
        if csolver_verifier::matches_entry(name, &seed_pats) && reach.insert(name.clone()) {
            work.push(name.clone());
        }
    }
    // Close over direct callees.
    while let Some(f) = work.pop() {
        if let Some(callees) = edges.get(f.as_str()) {
            for &c in callees {
                if reach.insert(c.to_string()) {
                    work.push(c.to_string());
                }
            }
        }
    }
    reach
}

/// A finding's identity for de-duplication: the same `(function, property, witness)`
/// is the *same bug* even when it appears in many files (a `static inline` emitted
/// into every TU, a header helper, or literally copied code). The file is deliberately
/// excluded so N copies collapse to one report.
pub(crate) type FindingKey = (String, String, String);
