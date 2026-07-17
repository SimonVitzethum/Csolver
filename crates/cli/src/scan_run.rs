use super::*;

/// **Reachability-based** cross-file scan (the (a) step): rather than linking a directory,
/// link — for each attacker entry — the transitive set of translation units the entry can
/// reach through the call graph, into one whole-program module analysed closed-world. Then
/// an internal helper's callers are all present, so a caller's scalar validation soundly
/// flows into it (closed-world is justified within the reachable set), eliminating the
/// false positives a per-file or per-directory view cannot. A bug-finding mode: the link is
/// per-entry, so a helper is constrained by the callers reachable from THAT entry.
pub(crate) fn scan_reachable(dir: &Path, config: &Config, entry_patterns: &[String]) -> Result<ExitCode, String> {
    use csolver_ir::Frontend;
    use std::collections::{BTreeSet, HashMap, HashSet};

    let mut files = Vec::new();
    collect_ll(dir, &mut files);
    files.sort();
    if files.is_empty() {
        return Err(format!("no .ll files found under {}", dir.display()));
    }
    eprintln!("reachability scan: lowering {} .ll files under {} …", files.len(), dir.display());

    // Lower every file (parallel), keeping the module + its call-graph edges.
    let cores = worker_count();
    let next = std::sync::atomic::AtomicUsize::new(0);
    let lowered: std::sync::Mutex<Vec<(usize, String, csolver_ir::Module)>> =
        std::sync::Mutex::new(Vec::with_capacity(files.len()));
    std::thread::scope(|s| {
        for _ in 0..cores.min(files.len()).max(1) {
            s.spawn(|| loop {
                let i = next.fetch_add(1, std::sync::atomic::Ordering::Relaxed);
                if i >= files.len() {
                    break;
                }
                let rel = files[i].strip_prefix(dir).unwrap_or(&files[i]).display().to_string();
                if let Ok(src) = std::fs::read_to_string(&files[i]) {
                    if let Ok(m) = (csolver_llvm::LlvmFrontend).lower(csolver_llvm::LlvmInput { source: src, name: rel.clone() }) {
                        lowered.lock().unwrap_or_else(|p| p.into_inner()).push((i, rel, m));
                    }
                }
            });
        }
    });
    let mut lowered = lowered.into_inner().unwrap_or_else(|p| p.into_inner());
    lowered.sort_by_key(|(i, _, _)| *i);
    let modules: Vec<(String, csolver_ir::Module)> = lowered.into_iter().map(|(_, r, m)| (r, m)).collect();

    // Global index: which module defines each external function, and each module's callees.
    let mut def_of: HashMap<String, usize> = HashMap::new();
    let mut calls: Vec<HashSet<String>> = Vec::with_capacity(modules.len());
    let mut entry_fns: Vec<(usize, String)> = Vec::new();
    for (mi, (_, m)) in modules.iter().enumerate() {
        let (defined, called) = module_call_edges(m);
        // Reachability targets: external definitions only (a `static` name may collide).
        for name in &defined {
            def_of.entry(name.clone()).or_insert(mi);
        }
        // Entries may be `static` (a proto_ops/file_operations callback is often static),
        // so match every defined function — the entry's module is the reachability root.
        for f in &m.functions {
            if csolver_verifier::matches_entry(&f.name, entry_patterns) {
                entry_fns.push((mi, f.name.clone()));
            }
        }
        calls.push(called);
    }
    eprintln!("  {} modules, {} attacker entries", modules.len(), entry_fns.len());

    // For each entry: BFS the reachable module set, link, verify closed-world. The traversal is
    // bounded by the number of modules that exist (it can reach no more) — no artificial cap.
    let max_reach = modules.len();
    let cfg = Config { closed_world: true, entry_patterns: Some(entry_patterns.to_vec()), ..config.clone() };
    let entry_next = std::sync::atomic::AtomicUsize::new(0);
    let entry_done = std::sync::atomic::AtomicUsize::new(0);
    let entry_active = std::sync::atomic::AtomicUsize::new(0);
    let agg: std::sync::Mutex<Vec<FileScan>> = std::sync::Mutex::new(Vec::new());
    let n_entries = entry_fns.len();
    std::thread::scope(|s| {
        for _ in 0..cores.min(n_entries.max(1)) {
            s.spawn(|| loop {
                let ei = entry_next.fetch_add(1, std::sync::atomic::Ordering::Relaxed);
                if ei >= n_entries {
                    break;
                }
                await_memory(&entry_active);
                entry_active.fetch_add(1, std::sync::atomic::Ordering::Relaxed);
                let (m0, ref ename) = entry_fns[ei];
                // BFS reachable modules from the entry's module.
                let mut seen: BTreeSet<usize> = BTreeSet::new();
                let mut work = vec![m0];
                seen.insert(m0);
                while let Some(mi) = work.pop() {
                    if seen.len() >= max_reach {
                        break;
                    }
                    for callee in &calls[mi] {
                        if let Some(&tgt) = def_of.get(callee) {
                            if seen.insert(tgt) {
                                work.push(tgt);
                            }
                        }
                    }
                }
                let group: Vec<&csolver_ir::Module> = seen.iter().map(|&i| &modules[i].1).collect();
                let linked = csolver_ir::merge_modules(group.iter().map(|m| (*m).clone()).collect::<Vec<_>>(), ename.as_str());
                let fs = scan_linked_module(&linked, ename, &cfg);
                entry_active.fetch_sub(1, std::sync::atomic::Ordering::Relaxed);
                let d = entry_done.fetch_add(1, std::sync::atomic::Ordering::Relaxed) + 1;
                if d.is_multiple_of(20) {
                    eprintln!("  … {d}/{n_entries} entries");
                }
                agg.lock().unwrap_or_else(|p| p.into_inner()).push(fs);
            });
        }
    });

    // Aggregate + de-duplicate findings (a function reachable from several entries).
    let all = agg.into_inner().unwrap_or_else(|p| p.into_inner());
    let (mut pass, mut fail, mut unknown, mut dropped, mut errored) = (0u64, 0u64, 0u64, 0u64, 0u64);
    let mut findings: Vec<Finding> = Vec::new();
    let mut lock_edges: Vec<(String, String, String)> = Vec::new();
    let mut race_accesses: Vec<(String, String, bool, Vec<String>)> = Vec::new();
    let mut race_traces: Vec<(String, Vec<(u8, String)>)> = Vec::new();
    for fs in all {
        pass += fs.pass;
        fail += fs.fail;
        unknown += fs.unknown;
        dropped += fs.dropped;
        errored += fs.errored;
        findings.extend(fs.findings);
        lock_edges.extend(fs.lock_edges);
        race_accesses.extend(fs.race_accesses);
        race_traces.extend(fs.race_traces);
    }
    let mut seen_find = HashSet::new();
    findings.retain(|f| seen_find.insert(finding_key(f)));
    // Concurrency oracle: the set of functions that can run concurrently — those in a module
    // reachable (over the complete closed-world call graph) from an attacker entry or a spawned
    // thread. A function outside it is single-threaded and cannot race, so the concurrent-* detectors
    // skip it. Module-granular (a module counts if ANY part is reachable) → a sound over-
    // approximation, so no genuinely-concurrent function is dropped.
    let concurrent_fns: HashSet<String> = {
        let mut name_to_module: HashMap<&str, usize> = HashMap::new();
        for (mi, (_, m)) in modules.iter().enumerate() {
            for f in &m.functions {
                name_to_module.insert(f.name.as_str(), mi);
            }
        }
        let mut reach: HashSet<usize> = entry_fns.iter().map(|(mi, _)| *mi).collect();
        for (_, tr) in &race_traces {
            for (k, child) in tr {
                if *k == 7 {
                    if let Some(&mi) = name_to_module.get(child.as_str()) {
                        reach.insert(mi);
                    }
                }
            }
        }
        let mut work: Vec<usize> = reach.iter().copied().collect();
        while let Some(mi) = work.pop() {
            for callee in &calls[mi] {
                if let Some(&tgt) = def_of.get(callee) {
                    if reach.insert(tgt) {
                        work.push(tgt);
                    }
                }
            }
        }
        modules
            .iter()
            .enumerate()
            .filter(|(mi, _)| reach.contains(mi))
            .flat_map(|(_, (_, m))| m.functions.iter().map(|f| f.name.clone()))
            .collect()
    };

    report_lock_cycles(&lock_edges);
    report_data_races(&race_accesses);
    report_atomicity(&race_traces, entry_patterns, Some(&concurrent_fns));
    report_scan(&findings, pass, fail, unknown, dropped, errored)
}

/// Verify one already-linked whole-program module, collecting its verdicts + findings.
pub(crate) fn scan_linked_module(module: &csolver_ir::Module, label: &str, cfg: &Config) -> FileScan {
    use csolver_core::ObligationResult;
    let mut fs = FileScan { dropped: module.unanalyzed.len() as u64, ..Default::default() };
    let report = verify_module_with_threads(module, cfg, 1);
    for f in &report.functions {
        match f.verdict {
            Verdict::Pass => fs.pass += 1,
            Verdict::Unknown => fs.unknown += 1,
            Verdict::Fail => {
                fs.fail += 1;
                for o in &f.outcomes {
                    if let ObligationResult::Refuted(cx) = &o.result {
                        let witness = cx
                            .model
                            .assignments
                            .iter()
                            .filter(|a| !a.name.starts_with('?'))
                            .map(|a| format!("{}={}", a.name, a.value))
                            .collect::<Vec<_>>()
                            .join(", ");
                        fs.findings.push(Finding {
                            file: label.to_string(),
                            function: f.function.clone(),
                            property: format!("{:?}", o.obligation.property),
                            witness,
                        });
                    }
                }
            }
        }
        for (from, to) in &f.lock_edges {
            fs.lock_edges.push((f.function.clone(), from.clone(), to.clone()));
        }
        for (loc, w, ls) in &f.race_accesses {
            fs.race_accesses.push((f.function.clone(), loc.clone(), *w, ls.clone()));
        }
        if !f.race_trace.is_empty() {
            fs.race_traces.push((f.function.clone(), f.race_trace.clone()));
        }
    }
    fs
}

/// Lower every `.ll` in `unit` (relative to `dir`); in cross-file mode link them into one
/// whole-program module (so a call across a translation-unit boundary resolves to its
/// definition and the caller's context flows in) and verify closed-world; otherwise verify
/// the single module per-TU. `threads` is the per-unit function-level parallelism.
#[allow(clippy::too_many_arguments)]
pub(crate) fn scan_one_unit(
    unit: &[std::path::PathBuf],
    label: &str,
    dir: &Path,
    config: &Config,
    cross: bool,
    threads: usize,
    content_seen: &std::sync::Mutex<std::collections::HashSet<u64>>,
    wp_ctx: Option<csolver_verifier::WholeProgramContext<'_>>,
) -> FileScan {
    use csolver_core::ObligationResult;
    use csolver_ir::Frontend;
    use std::hash::{Hash, Hasher};

    let mut fs = FileScan::default();
    // Read all sources first and hash their content. If an identical unit was already
    // verified (a byte-for-byte duplicate file — literally copied code, or the same
    // generated TU), skip it: identical input ⇒ identical result, so re-running the
    // (expensive) verification would only inflate the counts and re-report the same bugs.
    // Sound and deterministic (first occurrence wins; results are unit-ordered).
    let mut sources = Vec::with_capacity(unit.len());
    let mut hasher = std::collections::hash_map::DefaultHasher::new();
    for path in unit {
        let rel = path.strip_prefix(dir).unwrap_or(path).display().to_string();
        match std::fs::read_to_string(path) {
            Err(_) => fs.errored += 1,
            Ok(source) => {
                source.hash(&mut hasher);
                sources.push((rel, source));
            }
        }
    }
    if sources.is_empty() {
        return fs;
    }
    if !content_seen.lock().unwrap_or_else(|p| p.into_inner()).insert(hasher.finish()) {
        return FileScan::default(); // an identical unit was already verified
    }

    let mut modules = Vec::with_capacity(sources.len());
    for (rel, source) in sources {
        match (csolver_llvm::LlvmFrontend).lower(csolver_llvm::LlvmInput { source, name: rel }) {
            Err(_) => fs.errored += 1,
            Ok(m) => modules.push(m),
        }
    }
    if modules.is_empty() {
        return fs;
    }
    // The finding's file label: the single TU (normal) or the linked group (cross-file).
    let file_label = if cross || unit.len() > 1 {
        label.to_string()
    } else {
        unit[0].strip_prefix(dir).unwrap_or(&unit[0]).display().to_string()
    };
    let module = if cross {
        csolver_ir::merge_modules(modules, label)
    } else {
        // Normal per-TU scan: exactly one module per unit (unchanged behaviour).
        modules.into_iter().next().unwrap_or_else(|| csolver_ir::Module::new(label))
    };
    // NOTE: cross-file does NOT enable closed-world. Linking the group only makes the call
    // graph accurate (a cross-TU `Callee::Symbol` resolves to its definition, so the caller
    // uses the callee's conservative summary instead of an opaque havoc — sound). Assuming
    // the group holds ALL callers (closed-world) would be unsound on a partial merge (a
    // caller in another subsystem could violate a synthesized contract → false PASS).
    fs.dropped = module.unanalyzed.len() as u64;
    // Collect this unit's direct-call edges for the whole-program concurrency oracle (scan_dir),
    // plus the address-taken facts that make the oracle safe against indirect calls.
    {
        use csolver_ir::{Callee, Inst};
        for f in &module.functions {
            fs.defined_fns.push(f.name.clone());
            let mut callees: Vec<String> = Vec::new();
            let mut has_indirect = false;
            for i in f.blocks.iter().flat_map(|b| &b.insts) {
                match i {
                    Inst::Call { callee: Callee::Symbol(name), .. } => callees.push(name.clone()),
                    Inst::Call { callee: Callee::Indirect(_), .. } => has_indirect = true,
                    _ => {}
                }
            }
            if has_indirect {
                fs.indirect_callers.push(f.name.clone());
            }
            if !callees.is_empty() {
                fs.call_edges.push((f.name.clone(), callees));
            }
        }
        fs.addr_taken.extend(csolver_verifier::address_taken_names(&module));
    }
    // Whole-program (2b): a cross-file `Callee::Symbol(name)` with no in-unit definition
    // resolves to the program-wide callee summary instead of an opaque havoc, and an
    // external callee's whole-program preconditions overlay its per-file ones — cross-file
    // precision without linking. Without the context (ordinary scan) behaviour is unchanged.
    let report = match wp_ctx {
        Some(ctx) => csolver_verifier::verify_module_whole_program(&module, config, threads.max(1), ctx),
        None => verify_module_with_threads(&module, config, threads.max(1)),
    };
    fs.truncated = report.any_truncated();
    for f in &report.functions {
        match f.verdict {
            Verdict::Pass => fs.pass += 1,
            Verdict::Unknown => fs.unknown += 1,
            Verdict::Fail => {
                fs.fail += 1;
                for o in &f.outcomes {
                    if let ObligationResult::Refuted(cx) = &o.result {
                        let witness = cx
                            .model
                            .assignments
                            .iter()
                            .filter(|a| !a.name.starts_with('?'))
                            .map(|a| format!("{}={}", a.name, a.value))
                            .collect::<Vec<_>>()
                            .join(", ");
                        fs.findings.push(Finding {
                            file: file_label.clone(),
                            function: f.function.clone(),
                            property: format!("{:?}", o.obligation.property),
                            witness,
                        });
                    }
                }
            }
        }
        for (from, to) in &f.lock_edges {
            fs.lock_edges.push((f.function.clone(), from.clone(), to.clone()));
        }
        for (loc, w, ls) in &f.race_accesses {
            fs.race_accesses.push((f.function.clone(), loc.clone(), *w, ls.clone()));
        }
        if !f.race_trace.is_empty() {
            fs.race_traces.push((f.function.clone(), f.race_trace.clone()));
        }
    }
    fs
}

/// This process's resident set size in MB (Linux `/proc/self/status`), 0 if
/// unavailable — used to report the streaming pass's peak memory.
pub(crate) fn rss_mb() -> u64 {
    std::fs::read_to_string("/proc/self/status")
        .ok()
        .and_then(|s| {
            s.lines()
                .find_map(|l| l.strip_prefix("VmRSS:").map(str::to_string))
        })
        .and_then(|v| v.split_whitespace().next().and_then(|kb| kb.parse::<u64>().ok()))
        .map_or(0, |kb| kb / 1024)
}

/// **Whole-program facts (streaming).** Lower every `.ll` under `dir` one at a
/// time, fold each into the four whole-program precondition builders, then drop it
/// — so peak memory is bounded by the compact facts, not the resident IR. Finalize
/// and report coverage + peak RSS. This is the memory foundation for a
/// whole-kernel scan; it extracts the facts (identical to the linked pipeline)
/// without ever holding the linked module.
/// Stream every file in `files` (relative to `dir`) through the four whole-program
/// fact builders in parallel contiguous shards, merge in file order, and finalize —
/// the memory-bounded extraction shared by `solver facts` and the whole-program
/// scan's first pass. Returns the finalized facts, the count of lowered files, and
/// the observed peak RSS (MB). Bit-identical to the linked pipeline (see
/// `WholeProgramFacts`).
pub(crate) fn stream_program_facts(
    dir: &Path,
    files: &[std::path::PathBuf],
    closed_world: bool,
) -> (csolver_verifier::ProgramFacts, usize, u64) {
    use csolver_ir::Frontend;
    use std::sync::atomic::{AtomicBool, AtomicU64, AtomicUsize, Ordering};
    use std::sync::Arc;
    let cores = worker_count();
    // Contiguous shards (file order preserved): each worker builds its own facts in
    // parallel — the expensive per-function interval analysis parallelises — then the
    // shards are merged in order, giving ids identical to a single sequential push.
    let chunk = files.len().div_ceil(cores.max(1));
    let done = Arc::new(AtomicUsize::new(0));
    let lowered = AtomicUsize::new(0);
    let peak = Arc::new(AtomicU64::new(0));
    let n = files.len();
    let shards: std::sync::Mutex<Vec<(usize, csolver_verifier::WholeProgramFacts)>> =
        std::sync::Mutex::new(Vec::new());
    // Progress + memory monitor — a **detached** thread, deliberately NOT part of the
    // worker scope. If it were scoped and looped `while done < n`, a worker that panicked
    // (leaving `done` short of `n`) would spin the monitor forever, so the scope could
    // never join and the panic would deadlock instead of surfacing. Detached, the scope
    // waits only for the workers, so a worker panic propagates (a visible abort) — the
    // correct outcome: a panic is a bug to fix, never a file to silently drop (which would
    // void the closed-world completeness the preconditions rest on).
    let stop = Arc::new(AtomicBool::new(false));
    let monitor = {
        let (done, peak, stop) = (done.clone(), peak.clone(), stop.clone());
        std::thread::spawn(move || {
            while !stop.load(Ordering::Relaxed) {
                let rss = rss_mb();
                peak.fetch_max(rss, Ordering::Relaxed);
                eprintln!("  … {}/{n} files  (RSS {rss} MB)", done.load(Ordering::Relaxed));
                std::thread::sleep(std::time::Duration::from_secs(3));
            }
        })
    };
    std::thread::scope(|s| {
        for (si, shard) in files.chunks(chunk.max(1)).enumerate() {
            let (shards, done, lowered) = (&shards, &done, &lowered);
            s.spawn(move || {
                let mut wpf = csolver_verifier::WholeProgramFacts::new();
                for path in shard {
                    // Cooperative pause at the file boundary (see `await_unpause`): no-op
                    // unless `CSOLVER_PAUSE_FILE` is set and present.
                    await_unpause();
                    let rel = path.strip_prefix(dir).unwrap_or(path).display().to_string();
                    if let Ok(src) = std::fs::read_to_string(path) {
                        if let Ok(m) = (csolver_llvm::LlvmFrontend)
                            .lower(csolver_llvm::LlvmInput { source: src, name: rel })
                        {
                            wpf.push_module(&m);
                            lowered.fetch_add(1, Ordering::Relaxed);
                        }
                    }
                    done.fetch_add(1, Ordering::Relaxed);
                }
                shards.lock().unwrap_or_else(|p| p.into_inner()).push((si, wpf));
            });
        }
    });
    // Workers joined (a panic would have propagated above); stop the monitor.
    stop.store(true, Ordering::Relaxed);
    let _ = monitor.join();
    // Merge shards in file order, then finalize.
    let mut shards = shards.into_inner().unwrap_or_else(|p| p.into_inner());
    shards.sort_by_key(|(i, _)| *i);
    peak.fetch_max(rss_mb(), Ordering::Relaxed);
    eprintln!("  merging {} shards …", shards.len());
    let mut merged = csolver_verifier::WholeProgramFacts::new();
    for (_, wpf) in shards {
        merged.merge(wpf);
    }
    peak.fetch_max(rss_mb(), Ordering::Relaxed);
    eprintln!("  finalizing …");
    let facts = merged.finalize(closed_world);
    peak.fetch_max(rss_mb(), Ordering::Relaxed);
    (facts, lowered.load(Ordering::Relaxed), peak.load(Ordering::Relaxed))
}
