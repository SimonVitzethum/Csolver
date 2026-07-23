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
    // The `--facts` debug view only inspects effect summaries/preconditions; A2 hint-grounding
    // (opt-in) is not needed here, so it runs without it.
    let (facts, lowered, peak_rss) = stream_program_facts(dir, &files, closed_world, false);

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

/// Incremental, **de-duplicated** aggregate of the whole scan — folded per unit as it
/// finishes, so no per-unit `FileScan` is retained. This is what keeps a full-kernel scan
/// (37k units) within a few GB instead of tens: kernel `static inline`s are compiled into
/// *every* translation unit, so the same function name / call edge / lock edge recurs in
/// hundreds of units; the set/map dedup collapses those copies to one. The counts are
/// running totals; the program-wide graph inputs (lock, race, call) are kept only in their
/// deduplicated form, which is exactly what the end-of-scan oracles consume.
#[derive(Default)]
struct Agg {
    pass: u64,
    fail: u64,
    unknown: u64,
    dropped: u64,
    errored: u64,
    seen_find: std::collections::HashSet<FindingKey>,
    findings: Vec<Finding>,
    lock_edges: std::collections::HashSet<(String, String, String)>,
    race_accesses: std::collections::HashSet<(String, String, bool, Vec<String>)>,
    race_traces: std::collections::HashSet<(String, Vec<(u8, String)>)>,
    call_edges: std::collections::HashMap<String, std::collections::HashSet<String>>,
    defined_fns: std::collections::HashSet<String>,
    addr_taken: std::collections::HashSet<String>,
    indirect_callers: std::collections::HashSet<String>,
    /// Labels of units already folded in — the resume set. On a checkpointed scan these are
    /// written out and, on restart, reloaded so their units are skipped rather than re-scanned.
    done: std::collections::HashSet<String>,
}

impl Agg {
    /// Fold one finished unit's result in, deduplicating. Consumes `fs` (its strings move
    /// into the shared sets/maps or are dropped), so the unit's memory is released at once.
    /// `label` records the unit as done (for checkpoint/resume).
    fn fold(&mut self, label: &str, fs: FileScan) {
        self.done.insert(label.to_string());
        self.pass += fs.pass;
        self.fail += fs.fail;
        self.unknown += fs.unknown;
        self.dropped += fs.dropped;
        self.errored += fs.errored;
        for f in fs.findings {
            if self.seen_find.insert(finding_key(&f)) {
                self.findings.push(f);
            }
        }
        self.lock_edges.extend(fs.lock_edges);
        self.race_accesses.extend(fs.race_accesses);
        self.race_traces.extend(fs.race_traces);
        for (caller, callees) in fs.call_edges {
            self.call_edges.entry(caller).or_default().extend(callees);
        }
        self.defined_fns.extend(fs.defined_fns);
        self.addr_taken.extend(fs.addr_taken);
        self.indirect_callers.extend(fs.indirect_callers);
    }
}

/// Escape a field for the one-record-per-line checkpoint format: tabs and newlines (which the
/// format uses as separators) become spaces. Function names, witnesses and paths never contain
/// them in practice; this only guards against a pathological name corrupting the file.
fn ckpt_field(s: &str) -> String {
    s.replace(['\t', '\n', '\r'], " ")
}

/// **Write the scan checkpoint** atomically (temp file + rename), so a crash/reboot mid-write
/// never corrupts it. Records the coverage counts, every finished unit's label (the resume set),
/// and the de-duplicated findings — enough to reconstruct the coverage report and the full bug
/// inventory after a restart. The program-wide *concurrency* graph (lock/race/call) is NOT
/// checkpointed: those oracles re-run over whatever units the resumed pass covers, so their
/// reports may be partial after a resume — an accepted trade-off, as the memory-safety findings
/// and coverage (the payload) are fully recovered and the race report is intentionally capped.
fn write_checkpoint(path: &Path, agg: &Agg) {
    use std::fmt::Write as _;
    let mut s = String::with_capacity(agg.findings.len() * 64 + agg.done.len() * 32);
    s.push_str("CSOLVER-SCAN-CKPT 1\n");
    let _ = writeln!(s, "C\t{}\t{}\t{}\t{}\t{}", agg.pass, agg.fail, agg.unknown, agg.dropped, agg.errored);
    for label in &agg.done {
        let _ = writeln!(s, "D\t{}", ckpt_field(label));
    }
    for f in &agg.findings {
        let _ = writeln!(
            s, "F\t{}\t{}\t{}\t{}",
            ckpt_field(&f.file), ckpt_field(&f.function), ckpt_field(&f.property), ckpt_field(&f.witness),
        );
    }
    let tmp = path.with_extension("tmp");
    if std::fs::write(&tmp, s.as_bytes()).is_ok() {
        let _ = std::fs::rename(&tmp, path);
    }
}

/// **Load a scan checkpoint** written by [`write_checkpoint`], seeding an `Agg` with the counts,
/// resume set (`done`) and findings from the interrupted run. Returns `None` if the file is
/// absent or not a recognised checkpoint (a fresh scan). Unknown/short lines are skipped, so a
/// checkpoint truncated by a crash still loads every complete record before the tear-off.
fn read_checkpoint(path: &Path) -> Option<Agg> {
    let text = std::fs::read_to_string(path).ok()?;
    let mut lines = text.lines();
    if lines.next()? != "CSOLVER-SCAN-CKPT 1" {
        return None;
    }
    let mut agg = Agg::default();
    for line in lines {
        let mut it = line.split('\t');
        match it.next() {
            Some("C") => {
                let mut n = || it.next().and_then(|v| v.parse::<u64>().ok()).unwrap_or(0);
                agg.pass = n();
                agg.fail = n();
                agg.unknown = n();
                agg.dropped = n();
                agg.errored = n();
            }
            Some("D") => {
                if let Some(label) = it.next() {
                    agg.done.insert(label.to_string());
                }
            }
            Some("F") => {
                if let (Some(file), Some(function), Some(property), Some(witness)) =
                    (it.next(), it.next(), it.next(), it.next())
                {
                    let f = Finding {
                        file: file.to_string(),
                        function: function.to_string(),
                        property: property.to_string(),
                        witness: witness.to_string(),
                    };
                    if agg.seen_find.insert(finding_key(&f)) {
                        agg.findings.push(f);
                    }
                }
            }
            _ => {}
        }
    }
    Some(agg)
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
        let (facts, lowered, peak_rss) = stream_program_facts(dir, &files, config.closed_world, config.assume_valid_params);
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
    // Per-unit input size (bytes of `.ll` text) — the size-aware backpressure reserves memory
    // proportional to this, so a big cross-file directory throttles concurrent starts while many
    // small units run freely. A one-time `stat` per file; cheap next to lowering + analysis.
    let unit_sizes: Vec<u64> = units
        .iter()
        .map(|(_, ps)| ps.iter().map(|p| std::fs::metadata(p).map(|m| m.len()).unwrap_or(0)).sum())
        .collect();

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
    // Working-set memory budget for the size-aware backpressure — sampled *now*, after pass 1,
    // so the whole-program facts already resident are reflected and the budget adapts to how much
    // RAM is actually free (co-tenancy aware). The scan keeps the concurrent set of in-flight
    // units within this budget, so RSS tracks it instead of the 16-big-modules worst case.
    let budget_mb = mem_budget_mb();
    eprintln!(
        "scanning {total_files} .ll files under {} … ({total_units} units, {workers} workers × {threads_per_unit} threads{}; mem budget {} MiB{})",
        dir.display(),
        if cross_file { ", cross-file" } else { "" },
        budget_mb,
        if std::env::var_os("CSOLVER_MEM_TARGET_MB").is_some() { "" } else { ", ~70% of free — CSOLVER_MEM_TARGET_MB to set" },
    );

    let next = AtomicUsize::new(0);
    let done = AtomicUsize::new(0);
    // Reserved working-set memory (MiB) across in-flight units — the size-aware backpressure.
    let reserved = std::sync::atomic::AtomicU64::new(0);
    // Live findings counter + de-dup set: each bug is streamed to stderr the moment its
    // unit finishes (unbuffered, so a long scan surfaces bugs as they are found — visible
    // in `tail -f`), and the same bug appearing in many files is reported once.
    let found = AtomicUsize::new(0);
    let seen_find: Mutex<std::collections::HashSet<FindingKey>> = Mutex::new(std::collections::HashSet::new());
    // Byte-identical units are verified once (see `scan_one_unit`): skips re-analysis of
    // literally duplicated files and keeps the coverage counts free of those duplicates.
    let content_seen: Mutex<std::collections::HashSet<u64>> = Mutex::new(std::collections::HashSet::new());
    // **Restart safety** (opt-in `CSOLVER_SCAN_CHECKPOINT=<file>`): a long full-kernel scan that
    // is interrupted (crash, reboot, OOM, kill) resumes from where it left off instead of redoing
    // everything. The checkpoint records finished units + their counts + findings; on start it is
    // loaded, its units are skipped, and it is rewritten periodically. Absent env ⇒ no checkpoint.
    let checkpoint: Option<std::path::PathBuf> = std::env::var_os("CSOLVER_SCAN_CHECKPOINT").map(Into::into);
    let (initial_agg, resume_done) = match checkpoint.as_deref().and_then(read_checkpoint) {
        Some(a) => {
            eprintln!(
                "  resuming from checkpoint: {} of {total_units} units already done, {} findings recovered",
                a.done.len(),
                a.findings.len(),
            );
            let done_set = a.done.clone();
            (a, done_set)
        }
        None => (Agg::default(), std::collections::HashSet::new()),
    };
    done.fetch_add(resume_done.len(), Ordering::Relaxed);
    // Incremental de-duplicated aggregate (see `Agg`): folded per unit, so no per-unit
    // `FileScan` is retained — this is what bounds peak memory on a full-kernel scan.
    let agg: Mutex<Agg> = Mutex::new(initial_agg);
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
                let (label, unit) = &units[i];
                // Restart safety: a unit finished in a prior checkpointed run is already counted
                // and its findings recovered — skip it (no re-scan, no memory reserved).
                if resume_done.contains(label) {
                    continue;
                }
                // Size-aware memory backpressure: reserve this unit's estimated peak against the
                // working-set budget, blocking until it fits alongside the units already running.
                // A big cross-file directory therefore waits for room instead of piling 16 giant
                // modules into RAM at once; small units never wait. Released after the unit.
                let cost = unit_cost_mb(unit_sizes[i]);
                reserve_budget(&reserved, cost, budget_mb);
                let fs = scan_one_unit(unit, label, dir, config, cross_file, threads_per_unit, &content_seen, wp_ctx);
                reserved.fetch_sub(cost, Ordering::Relaxed);
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
                    let mut g = agg.lock().unwrap_or_else(|p| p.into_inner());
                    g.fold(label, fs);
                    // Restart safety: persist progress periodically (atomic write), so an
                    // interruption costs at most the last ~50 units, not the whole run.
                    if let Some(cp) = &checkpoint {
                        if d.is_multiple_of(50) {
                            write_checkpoint(cp, &g);
                        }
                    }
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
            agg.lock().unwrap_or_else(|p| p.into_inner()).fold(label, fs);
        }
    }
    // Final checkpoint: the run completed, so the checkpoint now reflects every unit — a
    // re-run with it present skips straight to the report instead of re-scanning.
    if let Some(cp) = &checkpoint {
        write_checkpoint(cp, &agg.lock().unwrap_or_else(|p| p.into_inner()));
    }

    // Extract the incremental aggregate. The per-unit `FileScan`s were folded in (and freed)
    // as the scan ran, deduplicated (see `Agg`), so this is already the whole-program view;
    // the graph inputs only need converting from their set/map form to the slices the oracles
    // take. Findings were deduped on the fly; sort them for deterministic report order (the
    // fold order is worker-completion order, not unit order).
    let Agg {
        pass,
        fail,
        unknown,
        dropped,
        errored,
        seen_find: _,
        mut findings,
        lock_edges,
        race_accesses,
        race_traces,
        call_edges,
        defined_fns,
        addr_taken,
        indirect_callers,
        done: _,
    } = agg.into_inner().unwrap_or_else(|p| p.into_inner());
    findings.sort_by_cached_key(finding_key);
    let lock_edges: Vec<(String, String, String)> = lock_edges.into_iter().collect();
    let race_accesses: Vec<(String, String, bool, Vec<String>)> = race_accesses.into_iter().collect();
    let race_traces: Vec<(String, Vec<(u8, String)>)> = race_traces.into_iter().collect();
    let call_edges: Vec<(String, Vec<String>)> =
        call_edges.into_iter().map(|(c, cs)| (c, cs.into_iter().collect())).collect();
    let defined_fns: Vec<String> = defined_fns.into_iter().collect();
    let addr_taken: Vec<String> = addr_taken.into_iter().collect();
    let indirect_callers: Vec<String> = indirect_callers.into_iter().collect();

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

    // Print the **payload first** — the coverage summary and the memory-safety findings (incl.
    // the `--attack-surface` subset) — then the concurrency heuristics. At whole-kernel scale the
    // concurrency reports are large and their pairwise search is expensive; running them last means
    // a slow or capped concurrency pass never delays or blocks the result the scan exists to give.
    let code = report_scan(&findings, pass, fail, unknown, dropped, errored);
    report_lock_cycles(&lock_edges);
    report_data_races(&race_accesses);
    report_atomicity(&race_traces, entry_patterns, concurrent.as_ref());
    code
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
