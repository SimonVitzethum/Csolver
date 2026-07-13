use super::*;

pub(crate) fn finding_key(b: &Finding) -> FindingKey {
    (b.function.clone(), b.property.clone(), b.witness.clone())
}

/// Stream a finished unit's findings to stderr immediately (live feed), tagging each
/// with a running global index. De-duplicated against `seen` so the same bug found in
/// many files is streamed only once (`found` then counts distinct bugs). stderr is
/// unbuffered, so each line reaches the console / log the moment it is written.
pub(crate) fn stream_findings(
    fs: &FileScan,
    found: &std::sync::atomic::AtomicUsize,
    seen: &std::sync::Mutex<std::collections::HashSet<FindingKey>>,
) {
    for b in &fs.findings {
        if !seen.lock().unwrap_or_else(|p| p.into_inner()).insert(finding_key(b)) {
            continue; // already reported (a duplicate copy in another file)
        }
        let n = found.fetch_add(1, std::sync::atomic::Ordering::Relaxed) + 1;
        eprintln!("  [FOUND #{n}] {}::{}  [{}]  witness: {}", b.file, b.function, b.property, b.witness);
    }
}

/// Report ABBA lock-order cycles (G6) across the whole scan. Aggregates every unit's
/// lock-order edges into one program-wide graph and prints each strongly-connected cycle.
/// A bug-finding heuristic (see `csolver_verifier::lockorder`): a cycle is a *candidate*
/// deadlock (a consistent hierarchy broken by `_nested`/`trylock` is not distinguished).
pub(crate) fn report_lock_cycles(edges: &[(String, String, String)]) {
    let tagged: Vec<csolver_verifier::TaggedEdge> = edges
        .iter()
        .map(|(f, from, to)| csolver_verifier::TaggedEdge { function: f, from, to })
        .collect();
    let cycles = csolver_verifier::detect_cycles(&tagged);
    if cycles.is_empty() {
        return;
    }
    println!("\n== ABBA lock-order cycles ({}) [bug-finding] ==", cycles.len());
    for c in &cycles {
        println!("  cycle: {}", c.classes.join(" <-> "));
        println!("    in functions: {}", c.functions.join(", "));
    }
}

/// Report candidate data races (G1, lockset/Eraser) across the whole scan. Aggregates every
/// unit's shared-memory access records into one program-wide relation and flags locations with
/// an inconsistent lockset (a write, ≥2 functions, protected on some access but not all). A
/// bug-finding heuristic (see `csolver_verifier::datarace`) — reported as candidates.
pub(crate) fn report_data_races(accesses: &[(String, String, bool, Vec<String>)]) {
    let tagged: Vec<csolver_verifier::TaggedAccess> = accesses
        .iter()
        .map(|(f, loc, w, ls)| csolver_verifier::TaggedAccess {
            function: f,
            location: loc,
            write: *w,
            lockset: ls,
        })
        .collect();
    let races = csolver_verifier::detect_races(&tagged);
    if races.is_empty() {
        return;
    }
    println!("\n== data races (lockset / Eraser) ({}) [bug-finding] ==", races.len());
    for r in &races {
        let tag = if r.irq_unsafe { "  [IRQ-unsafe: plain lock on IRQ-shared data]" } else { "" };
        println!("  location: {}{tag}", r.location);
        println!("    accessed under inconsistent locking in: {}", r.functions.join(", "));
    }
}

/// Report candidate **atomicity violations** (subsystem 4, two-thread interleaving) across the
/// scan. Pairs functions whose event traces share a written location and searches for a valid
/// interleaving that interrupts a split-critical-section read-modify-write — a lost update the
/// lockset pass cannot see. Prints the interleaving witness. A bug-finding heuristic.
pub(crate) fn report_atomicity(
    traces: &[(String, Vec<(u8, String)>)],
    entry_patterns: &[String],
    concurrent: Option<&std::collections::HashSet<String>>,
) {
    // **Concurrency oracle.** A function can race only if it runs in a concurrent context. When a
    // sound concurrent-function set is supplied (computed over the complete closed-world call graph:
    // functions reachable from an attacker entry or a spawned thread), the *concurrent* detectors
    // only pair functions in it — a function that is single-threaded-reachable cannot participate in
    // a race, so excluding it removes false positives without losing a genuinely-concurrent one (the
    // set is a sound over-approximation). With no set (partial graph / no evidence), all threads are
    // paired (the heuristic default) — never dropping a real race.
    let conc_threads: Vec<csolver_verifier::Thread> = match concurrent {
        Some(set) => traces
            .iter()
            .filter(|(name, _)| set.contains(name))
            .map(|(name, tr)| csolver_verifier::trace_to_thread(name, tr))
            .collect(),
        None => traces
            .iter()
            .map(|(name, tr)| csolver_verifier::trace_to_thread(name, tr))
            .collect(),
    };
    // Cross-*syscall* composition is only valid between attacker-reachable ENTRY points (separate
    // syscall handlers). When entry patterns are configured, restrict the cross-entry detectors to
    // matching functions — a genuine sequential composition of two independent entries, not any two
    // internal helpers. With no patterns, fall back to all traces (the heuristic default).
    let entry_threads: Vec<csolver_verifier::Thread> = traces
        .iter()
        .filter(|(name, _)| entry_patterns.is_empty() || csolver_verifier::matches_entry(name, entry_patterns))
        .map(|(name, tr)| csolver_verifier::trace_to_thread(name, tr))
        .collect();
    let violations = csolver_verifier::find_atomicity_violations(&conc_threads);
    let ev = |e: &csolver_verifier::interleave::Event| -> String {
        use csolver_verifier::interleave::Event::*;
        match e {
            Acquire(l) => format!("acquire {l}"),
            Release(l) => format!("release {l}"),
            Read(x) => format!("read {x}"),
            DepRead(x) => format!("read {x} (addr-dep)"),
            Write(x) => format!("write {x}"),
            Rmw(x) => format!("read-modify-write {x}"),
            Fence => "barrier".to_string(),
            WFence => "write-barrier".to_string(),
            RFence => "read-barrier".to_string(),
            Spawn(c) => format!("spawn {c}"),
            Join => "join".to_string(),
            Free(x) => format!("free {x}"),
            Cas(x) => format!("cas {x}"),
            RefGet(x) => format!("ref-get {x}"),
            RefPut(x) => format!("ref-put {x}"),
            Typestate(_) => "typestate".to_string(),
        }
    };
    if !violations.is_empty() {
        println!("\n== atomicity violations (interleaving) ({}) [bug-finding] ==", violations.len());
        for v in &violations {
            println!("  location: {}  (non-atomic read-modify-write, lost update)", v.location);
            println!("    witness interleaving:");
            for (thread, event) in &v.schedule {
                println!("      {thread}: {}", ev(event));
            }
        }
    }
    // Cross-thread use-after-free / double-free (a free concurrent with a use/free elsewhere).
    let uaf = csolver_verifier::find_cross_thread_uaf(&conc_threads);
    if !uaf.is_empty() {
        println!("\n== cross-thread use-after-free / double-free ({}) [bug-finding] ==", uaf.len());
        for w in &uaf {
            let kind = if w.double_free { "double-free" } else { "use-after-free" };
            println!("  {kind} of {} : {} frees it, {} concurrently {}s it (disjoint locks)",
                w.location, w.threads.0, w.threads.1, if w.double_free { "free" } else { "use" });
        }
    }
    // Cross-entry (cross-syscall) use-after-free: a free of a global-rooted object in one entry and
    // a dereference/free of it in another, sequentially composable entry (no common caller). Runs
    // over every trace; the global-root restriction keeps it to persistent shared state.
    let cross_entry = csolver_verifier::find_cross_entry_uaf(&entry_threads);
    if !cross_entry.is_empty() {
        println!("\n== cross-entry (cross-syscall) use-after-free / double-free ({}) [bug-finding] ==",
            cross_entry.len());
        for w in &cross_entry {
            let kind = if w.double_free { "double-free" } else { "use-after-free" };
            println!("  {kind} of {} : entry {} frees it (root left dangling), entry {} later {}s it",
                w.location, w.entries.0, w.entries.1, if w.double_free { "free" } else { "use" });
        }
    }
    // Cross-entry (cross-syscall) typestate use-after-state: a global object set to a forbidden
    // state in one entry and used with `require-not` of it in another, independently reachable one.
    let cross_ts = csolver_verifier::find_cross_entry_typestate(&entry_threads);
    if !cross_ts.is_empty() {
        println!("\n== cross-entry (cross-syscall) typestate use-after-state ({}) [bug-finding] ==",
            cross_ts.len());
        for w in &cross_ts {
            println!("  object: {} — entry {} drives it into a forbidden state, entry {} then uses it \
                (use-after-close / use-after-free across syscalls)",
                w.location, w.entries.0, w.entries.1);
        }
    }
    // Concurrent refcount race: an unchecked get concurrent with a put of the same object.
    let rc = csolver_verifier::find_refcount_races(&conc_threads);
    if !rc.is_empty() {
        println!("\n== concurrent reference-count races ({}) [bug-finding] ==", rc.len());
        for w in &rc {
            println!("  object: {} — {} does an unchecked get while {} concurrently puts it \
                (disjoint locks); the get can resurrect a zeroed count (use `*_inc_not_zero`)",
                w.location, w.threads.0, w.threads.1);
        }
    }
    // ABA: a compare-and-swap concurrent with a modification of the same location.
    let aba = csolver_verifier::find_aba(&conc_threads);
    if !aba.is_empty() {
        println!("\n== ABA problems ({}) [bug-finding] ==", aba.len());
        for w in &aba {
            println!("  location: {} — {} CAS-es it while {} concurrently modifies it (disjoint locks)",
                w.location, w.threads.0, w.threads.1);
        }
    }
    // Weak-memory (SC-robustness) bugs via the operational PSO model (subsystem 4) — subsumes
    // the store-buffer and message-passing litmus, with a concrete non-SC schedule as witness.
    let wm = csolver_verifier::find_weak_memory_bugs(&conc_threads);
    if !wm.is_empty() {
        println!("\n== weak-memory (SC-robustness) bugs ({}) [bug-finding] ==", wm.len());
        for w in &wm {
            println!("  threads {}: {}", w.threads.join(", "), w.description);
            println!("    non-SC schedule:");
            for (thread, step) in &w.schedule {
                println!("      {thread}: {step}");
            }
        }
    }
}

/// Render a scan's findings + coverage and pick the exit code.
pub(crate) fn report_scan(
    findings: &[Finding],
    pass: u64,
    fail: u64,
    unknown: u64,
    dropped: u64,
    errored: u64,
) -> Result<ExitCode, String> {
    let total = pass + fail + unknown;
    let pct = |x: u64| if total == 0 { 0.0 } else { 100.0 * x as f64 / total as f64 };
    println!("\n== memory-safety violations found ({}) ==", findings.len());
    if findings.is_empty() {
        println!("  (none)");
    } else {
        for b in findings {
            println!("  {}::{}  [{}]  witness: {}", b.file, b.function, b.property, b.witness);
        }
    }
    println!("\n== coverage ==");
    println!("functions analyzed : {total}");
    println!("  PASS  (proven safe)  : {pass}  ({:.1}%)", pct(pass));
    println!("  FAIL  (bug found)    : {fail}  ({:.1}%)", pct(fail));
    println!("  UNKNOWN (undecided)  : {unknown}  ({:.1}%)", pct(unknown));
    println!("decided (PASS+FAIL)  : {}  ({:.1}%)", pass + fail, pct(pass + fail));
    println!("dropped (unanalyzed) : {dropped}   (functions the frontend could not lower)");
    println!("files with tool error: {errored}");
    // A scan is an inventory, not a single verdict — exit non-zero iff any bug was found.
    Ok(if fail > 0 { ExitCode::from(1) } else { ExitCode::SUCCESS })
}

/// Read an entry-point pattern file: one pattern per line (an exact function name
/// or a trailing-`*` prefix like `__x64_sys_*`). Blank lines and `#` comments are
/// ignored.
pub(crate) fn read_entry_patterns(path: &Path) -> Result<Vec<String>, String> {
    let text = std::fs::read_to_string(path).map_err(|e| format!("{}: {e}", path.display()))?;
    let pats: Vec<String> = text
        .lines()
        .map(|l| l.split('#').next().unwrap_or("").trim())
        .filter(|l| !l.is_empty())
        .map(|l| l.to_string())
        .collect();
    if pats.is_empty() {
        return Err(format!("{}: no entry patterns found", path.display()));
    }
    Ok(pats)
}

/// Recursively collect every `*.ll` file under `dir`.
pub(crate) fn collect_ll(dir: &Path, out: &mut Vec<PathBuf>) {
    let Ok(entries) = std::fs::read_dir(dir) else { return };
    for e in entries.flatten() {
        let p = e.path();
        if p.is_dir() {
            collect_ll(&p, out);
        } else if p.extension().and_then(|x| x.to_str()) == Some("ll") {
            out.push(p);
        }
    }
}
