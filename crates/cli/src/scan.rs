use super::*;

/// One found memory-safety violation, for the scan summary.
pub(crate) struct Finding {
    pub(crate) file: String,
    pub(crate) function: String,
    pub(crate) property: String,
    pub(crate) witness: String,
}

/// Scan **every** `.ll` file under `dir` (recursively), verify all of them without
/// stopping at any UNKNOWN or FAIL, and report the coverage (how much of the code is
/// actually decided) plus every memory-safety violation found, with its witness.
/// The per-unit scan result, aggregated deterministically after the parallel pass.
/// A "unit" is a single `.ll` file (normal scan) or a whole directory group merged into
/// one program (cross-file scan).
#[derive(Default)]
pub(crate) struct FileScan {
    pub(crate) pass: u64,
    pub(crate) fail: u64,
    pub(crate) unknown: u64,
    pub(crate) dropped: u64,
    pub(crate) errored: u64,
    pub(crate) findings: Vec<Finding>,
    /// Lock-order edges `(function, held-class, acquired-class)` seen in this unit —
    /// aggregated program-wide after the scan to detect ABBA lock-order cycles (G6).
    pub(crate) lock_edges: Vec<(String, String, String)>,
    /// Shared-memory accesses `(function, location-class, is_write, lock-classes)` seen in this
    /// unit — aggregated program-wide for the lockset data-race check (G1).
    pub(crate) race_accesses: Vec<(String, String, bool, Vec<String>)>,
    /// Ordered per-function interleaving traces `(function, trace)` — aggregated program-wide
    /// for the two-thread atomicity-violation check (subsystem 4).
    pub(crate) race_traces: Vec<(String, Vec<(u8, String)>)>,
    /// Per-function **direct-call edges** `(caller, callees)` — aggregated program-wide into a
    /// whole-program call graph so the concurrency oracle can compute which functions are reachable
    /// from a concurrent context (an entry or a spawned thread) in `--whole-program`/scan_dir mode.
    pub(crate) call_edges: Vec<(String, Vec<String>)>,
    /// Address-taken facts for the concurrency oracle's **indirect-call safety** (scan_dir).
    /// `defined_fns` = functions DEFINED in this unit; `addr_taken` = symbols whose ADDRESS is
    /// taken (a `Const::Symbol` operand — a candidate indirect-call target); `indirect_callers` =
    /// functions containing a `Callee::Indirect` call. If a concurrent function can reach an
    /// indirect call, every address-taken function is a potential concurrent target and must join
    /// the oracle's seed (else a handler reached only through a fn-pointer is wrongly excluded).
    pub(crate) defined_fns: Vec<String>,
    pub(crate) addr_taken: Vec<String>,
    pub(crate) indirect_callers: Vec<String>,
    /// Symbolic exploration hit its budget on ≥1 function: the unit is a
    /// candidate for a full-effort *deferred* re-run rather than accepting Unknown.
    pub(crate) truncated: bool,
}

/// The syscall-wrapper name prefixes (SYSCALL_DEFINE* expands to these) — precise entry
/// patterns covering every syscall, used by `--auto-entries`.
pub(crate) const SYSCALL_ENTRY_PREFIXES: &[&str] = &[
    "__x64_sys_*",
    "__ia32_sys_*",
    "__se_sys_*",
    "__se_compat_sys_*",
    "__do_sys_*",
    "__do_compat_sys_*",
    "__arm64_sys_*",
    "__arm64_compat_sys_*",
    "compat_sys_*",
];

/// Extract, from one `.ll`'s text, the functions it DEFINES and the function names its
/// GLOBAL CONSTANT initialisers reference — i.e. the function pointers stored in ops
/// structs (`proto_ops`, `file_operations`, …). The latter are the targets of the kernel's
/// indirect dispatch (`sock->ops->recvmsg(…)`), which no direct call graph can follow: they
/// are the real registered handlers. `@name` identifiers use the LLVM charset `[A-Za-z0-9_.$]`.
pub(crate) fn ll_defs_and_global_refs(source: &str) -> (Vec<String>, Vec<String>) {
    fn ident_at(bytes: &[u8], at: usize) -> Option<(String, usize)> {
        // `bytes[at]` is `@`; read the identifier that follows (bare form; quoted names,
        // rare for functions, are skipped).
        let start = at + 1;
        let mut end = start;
        while end < bytes.len() {
            let c = bytes[end];
            if c.is_ascii_alphanumeric() || matches!(c, b'_' | b'.' | b'$') {
                end += 1;
            } else {
                break;
            }
        }
        (end > start).then(|| (String::from_utf8_lossy(&bytes[start..end]).into_owned(), end))
    }
    fn ats(line: &str) -> Vec<String> {
        let b = line.as_bytes();
        let mut out = Vec::new();
        let mut i = 0;
        while i < b.len() {
            if b[i] == b'@' {
                if let Some((name, end)) = ident_at(b, i) {
                    out.push(name);
                    i = end;
                    continue;
                }
            }
            i += 1;
        }
        out
    }
    let mut defined = Vec::new();
    let mut refs = Vec::new();
    for line in source.lines() {
        let t = line.trim_start();
        if t.starts_with("define ") {
            // `define ... @name(` — the first `@ident` is the function name.
            if let Some(pos) = line.find('@') {
                if let Some((name, _)) = ident_at(line.as_bytes(), pos) {
                    defined.push(name);
                }
            }
        } else if t.starts_with('@') && line.contains(" = ") {
            // A global definition. Its initialiser's `@` refs (after the first, which is the
            // global's own name) are the stored pointers — the ops-struct handlers.
            let names = ats(line);
            refs.extend(names.into_iter().skip(1));
        }
    }
    (defined, refs)
}

/// Derive the attacker-entry set automatically for a directory scan: the precise syscall-wrapper
/// prefixes UNION the registered indirect handlers discovered in ops-struct initialisers
/// ([`discover_ops_handlers`]), plus any explicit `extra` patterns. This is the whole point of
/// `--auto-entries` — a complete kernel attacker surface with **no hand-written `--entries` file**.
pub(crate) fn derive_auto_entries(dir: &Path, extra: Option<&[String]>) -> Vec<String> {
    let mut pats: Vec<String> = SYSCALL_ENTRY_PREFIXES.iter().map(|s| s.to_string()).collect();
    // Userspace program entries: `main` receives attacker-controlled argv/argc; a libFuzzer
    // harness receives attacker bytes. Universally-valid entries (inert in a kernel tree that has
    // neither), so `--auto-entries`/`--reachable` also seed correctly on a userspace program — not
    // just the kernel. A userspace *library*'s exported API is covered by the all-external default.
    pats.extend(USERSPACE_ENTRY_PATTERNS.iter().map(|s| s.to_string()));
    if let Some(e) = extra {
        pats.extend(e.iter().cloned());
    }
    let handlers = discover_ops_handlers(dir);
    eprintln!("--auto-entries: {} ops-struct handlers discovered", handlers.len());
    pats.extend(handlers);
    pats
}

/// Universal userspace program entry points — the attacker-reachable roots of an executable or a
/// fuzz harness (argv/stdin/fuzzer bytes). Unioned into the auto-derived entry set so a userspace
/// scan needs no hand-written list either.
pub(crate) const USERSPACE_ENTRY_PATTERNS: &[&str] = &["main", "LLVMFuzzerTestOneInput"];

/// **Devirtualisation by ops-struct-initialiser analysis.** Scan every `.ll` under `dir` for
/// the function pointers stored in its global constant initialisers, keeping only those that
/// are actually defined functions — the complete set of the kernel's registered indirect
/// handlers (proto_ops/file_operations/… callbacks). Used as entry points, this covers the
/// attacker-reachable APIs a name-pattern list cannot, precisely and automatically (an
/// internal helper never stored in an ops struct is correctly excluded).
pub(crate) fn discover_ops_handlers(dir: &Path) -> std::collections::HashSet<String> {
    use std::sync::atomic::{AtomicUsize, Ordering};
    use std::sync::Mutex;
    let mut files = Vec::new();
    collect_ll(dir, &mut files);
    if files.is_empty() {
        return std::collections::HashSet::new();
    }
    let cores = worker_count();
    let next = AtomicUsize::new(0);
    // Per worker: local defined-set and ref-set, merged at the end (cheap, no lock churn).
    let acc: Mutex<(std::collections::HashSet<String>, std::collections::HashSet<String>)> =
        Mutex::new((std::collections::HashSet::new(), std::collections::HashSet::new()));
    std::thread::scope(|s| {
        for _ in 0..cores.min(files.len()).max(1) {
            s.spawn(|| {
                let (mut defs, mut refs) = (
                    std::collections::HashSet::new(),
                    std::collections::HashSet::new(),
                );
                loop {
                    let i = next.fetch_add(1, Ordering::Relaxed);
                    if i >= files.len() {
                        break;
                    }
                    if let Ok(src) = std::fs::read_to_string(&files[i]) {
                        let (d, r) = ll_defs_and_global_refs(&src);
                        defs.extend(d);
                        refs.extend(r);
                    }
                }
                let mut g = acc.lock().unwrap_or_else(|p| p.into_inner());
                g.0.extend(defs);
                g.1.extend(refs);
            });
        }
    });
    let (defined, refs) = acc.into_inner().unwrap_or_else(|p| p.into_inner());
    // A handler is a global-stored pointer that is a defined function in the tree.
    refs.into_iter().filter(|n| defined.contains(n)).collect()
}

/// System memory available to start new work, in MiB (Linux: `/proc/meminfo`
/// `MemAvailable`). `u64::MAX` where it cannot be read, so the throttle is a no-op.
pub(crate) fn available_mb() -> u64 {
    match std::fs::read_to_string("/proc/meminfo") {
        Ok(s) => s
            .lines()
            .find_map(|l| l.strip_prefix("MemAvailable:"))
            .and_then(|v| v.split_whitespace().next())
            .and_then(|kb| kb.parse::<u64>().ok())
            .map(|kb| kb / 1024)
            .unwrap_or(u64::MAX),
        Err(_) => u64::MAX,
    }
}

/// **Memory backpressure.** Before a worker starts a new file, wait while free memory is
/// below `MEM_FLOOR_MB` AND at least one other file is in flight (which will free memory as
/// it finishes) — so the scan never starts so many concurrent analyses that it exhausts RAM
/// and thrashes/OOMs, without aborting or skipping any analysis. Progress is guaranteed: if
/// no file is in flight (`active == 0`) the worker proceeds regardless, so at least one
/// analysis always runs even under memory pressure. `active` counts in-flight files.
///
/// The gate is RESERVATION-based: a new file may start only if free memory covers a floor
/// PLUS a per-in-flight-file reserve for every analysis already running — because an
/// in-flight analysis keeps growing after it starts, and the gate only controls STARTS.
/// So all workers run concurrently while memory is ample (a tree of small units), but when
/// several large units are in flight the reserve blocks further starts, bounding peak RSS
/// without ever capping the worker count or aborting an analysis.
pub(crate) const MEM_FLOOR_MB: u64 = 1024;
pub(crate) fn await_memory(active: &std::sync::atomic::AtomicUsize) {
    use std::sync::atomic::Ordering;
    let reserve = mem_reserve_per_inflight_mb();
    loop {
        let inflight = active.load(Ordering::Relaxed) as u64;
        // At least one analysis must always be allowed to run (progress guarantee).
        if inflight == 0 {
            return;
        }
        let need = MEM_FLOOR_MB + inflight * reserve;
        if available_mb() >= need {
            return;
        }
        std::thread::sleep(std::time::Duration::from_millis(200));
    }
}

/// **Working-set memory budget** (MiB) for the size-aware scan backpressure. `CSOLVER_MEM_TARGET_MB`
/// if set; otherwise ~70 % of the memory available *right now*, so it **adapts to co-tenancy** — a
/// machine already busy (e.g. sharing RAM with another job) yields a smaller budget, a free machine
/// a larger one. Meant to be sampled once *after* pass 1, so the whole-program facts already
/// resident are reflected in `available_mb()`. `u64::MAX` (no throttle) when meminfo is unreadable.
pub(crate) fn mem_budget_mb() -> u64 {
    if let Some(t) = std::env::var("CSOLVER_MEM_TARGET_MB")
        .ok()
        .and_then(|v| v.parse::<u64>().ok())
        .filter(|&n| n > 0)
    {
        return t;
    }
    match available_mb() {
        u64::MAX => u64::MAX,
        a => a / 10 * 7,
    }
}

/// Estimated peak resident memory (MiB) to analyse a unit holding `input_bytes` of `.ll` text:
/// a fixed base plus a multiple of the input size — LLVM IR **text** expands to the in-memory IR
/// plus the symbolic-execution / SAT state, and a cross-file unit links a whole directory into one
/// module, so a big directory (AMD-display DML, `fs`, `net`) is the memory hog. `CSOLVER_MEM_FACTOR`
/// overrides the multiple (default 12×). Deliberately an over-estimate: better to under-subscribe
/// than to OOM. This lets many small units run concurrently while throttling concurrent *large* ones.
pub(crate) fn unit_cost_mb(input_bytes: u64) -> u64 {
    const BASE_MB: u64 = 64;
    let factor = std::env::var("CSOLVER_MEM_FACTOR")
        .ok()
        .and_then(|v| v.parse::<u64>().ok())
        .filter(|&n| n > 0)
        .unwrap_or(12);
    BASE_MB + input_bytes / (1024 * 1024) * factor
}

/// Reserve `cost_mb` of the working-set `budget_mb`, blocking until it fits alongside the units
/// already in flight (`reserved`). **Progress guarantee:** if nothing is in flight (`reserved == 0`)
/// the unit proceeds even when it alone exceeds the budget, so the scan never deadlocks on a single
/// oversized unit. The caller MUST release with `reserved.fetch_sub(cost_mb, …)` when the unit
/// finishes. Soundness- and result-neutral: it changes only *when* a unit starts running (fewer
/// concurrent large modules ⇒ lower peak RSS), never *what* is analysed. Replaces the flat-reserve
/// [`await_memory`] for the main directory scan, where per-unit sizes vary by orders of magnitude.
pub(crate) fn reserve_budget(reserved: &std::sync::atomic::AtomicU64, cost_mb: u64, budget_mb: u64) {
    use std::sync::atomic::Ordering;
    loop {
        let r = reserved.load(Ordering::Acquire);
        if r == 0 || r + cost_mb <= budget_mb {
            // Reserve atomically; if another worker reserved first, retry the decision.
            if reserved
                .compare_exchange(r, r + cost_mb, Ordering::AcqRel, Ordering::Relaxed)
                .is_ok()
            {
                return;
            }
        } else {
            std::thread::sleep(std::time::Duration::from_millis(200));
        }
    }
}

/// Worker count for the parallel scan/lowering loops. `CSOLVER_JOBS`, when set,
/// caps it — a soundness-neutral RAM lever: fewer concurrent units means fewer
/// large modules resident at once (lower peak memory), while every unit is still
/// analysed identically, so no coverage and no soundness is lost, only wall-clock
/// time. Defaults to the machine's available parallelism.
pub(crate) fn worker_count() -> usize {
    std::env::var("CSOLVER_JOBS")
        .ok()
        .and_then(|v| v.parse::<usize>().ok())
        .filter(|&n| n >= 1)
        .unwrap_or_else(|| std::thread::available_parallelism().map_or(1, |n| n.get()))
}

/// **Cooperative pause.** If `CSOLVER_PAUSE_FILE` names a path that currently exists,
/// block here — polling every 500 ms — until that file is removed, then continue. This
/// is checked only at **unit/file boundaries** (never mid-analysis), so pausing withholds
/// *starting the next unit* rather than interrupting one in flight. It is
/// result- and soundness-neutral: it changes only *when* work runs, never *what* is
/// analysed or the verdict, and the deterministic post-scan aggregation is unaffected.
///
/// Usage on a long/detached run: launch with `CSOLVER_PAUSE_FILE=/path/to/pause`, then
/// `touch /path/to/pause` to pause and `rm /path/to/pause` to resume. When the env var is
/// unset (the default) this is a single cheap `getenv` and returns immediately — zero
/// overhead. One `paused`/`resumed` line is logged per transition (not per worker).
pub(crate) fn await_unpause() {
    use std::sync::atomic::{AtomicBool, Ordering};
    // Announce the pause/resume exactly once across all workers (not once per worker).
    static ANNOUNCED: AtomicBool = AtomicBool::new(false);
    let Some(path) = std::env::var_os("CSOLVER_PAUSE_FILE") else {
        return;
    };
    let path = std::path::Path::new(&path);
    if !path.exists() {
        return;
    }
    if !ANNOUNCED.swap(true, Ordering::Relaxed) {
        eprintln!("  ⏸ paused — remove {} to resume …", path.display());
    }
    while path.exists() {
        std::thread::sleep(std::time::Duration::from_millis(500));
    }
    if ANNOUNCED.swap(false, Ordering::Relaxed) {
        eprintln!("  ▶ resumed");
    }
}

/// Memory a single in-flight analysis is assumed to need, reserved by the
/// backpressure (`await_memory`). Overridable via `CSOLVER_MEM_RESERVE_MB`: raise
/// it for cross-file / whole-program runs whose linked modules dwarf a single
/// translation unit, so fewer start concurrently. Soundness-neutral (throttles
/// only — it never changes what is analysed).
pub(crate) fn mem_reserve_per_inflight_mb() -> u64 {
    std::env::var("CSOLVER_MEM_RESERVE_MB")
        .ok()
        .and_then(|v| v.parse::<u64>().ok())
        .filter(|&n| n > 0)
        .unwrap_or(2560)
}

/// The external functions a module DEFINES and the external symbols it CALLS — the edges
/// of the cross-file call graph. Internal (static) definitions are file-local, so they are
/// not exported as reachability targets; a `Callee::Symbol(name)` is a cross-file call.
pub(crate) fn module_call_edges(m: &csolver_ir::Module) -> (Vec<String>, std::collections::HashSet<String>) {
    use csolver_ir::{Callee, Inst};
    let defined: Vec<String> = m
        .functions
        .iter()
        .filter(|f| !m.internal.contains(&f.id))
        .map(|f| f.name.clone())
        .collect();
    let mut called = std::collections::HashSet::new();
    for f in &m.functions {
        for inst in f.blocks.iter().flat_map(|b| &b.insts) {
            if let Inst::Call { callee: Callee::Symbol(name), .. } = inst {
                called.insert(name.clone());
            }
        }
    }
    (defined, called)
}
