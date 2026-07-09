//! The `solver` command-line interface.
//!
//! ```text
//! solver verify <file.rs | file.mir | file.ll | file.s | binary>   [--json]
//! solver demo                                                      [--json]
//! solver report <result.json>
//! solver --help | --version
//! ```
//!
//! A `.rs` file is turnkey: the tool compiles it to MIR itself (`+nightly -Z
//! mir-include-spans` for source locations, stable fallback) and prints a coverage
//! report — how many functions were found, verified, and *not analyzed*.
//!
//! Exit codes: `0` = PASS, `1` = FAIL, `2` = UNKNOWN, `3` = tool error.

use std::path::{Path, PathBuf};
use std::process::ExitCode;

use csolver_core::{SourceLevel, Verdict};
use csolver_report::{render_json, render_text};
use csolver_verifier::{verify_module, verify_module_with_threads, Config};

mod demo;

const HELP: &str = "\
solver — CSolver memory-safety verifier

USAGE:
    solver verify <path> [--json] [--closed-world] [--bugs] [--pre <file>]
                                    verify a .rs (turnkey), .mir, .ll, .s, or ELF
                                    (--closed-world: treat the module as the whole
                                    program — synthesize contracts for exported
                                    functions from all their in-module call sites;
                                    --bugs: bug-finding mode — report OOB reachable by
                                    a genuine input even past a loop/opaque call (higher
                                    recall, small false-positive risk; verify is strict);
                                    --assume-valid-params: assume a raw pointer parameter
                                    of known pointee size is valid (framework/kernel entry
                                    ABI — opt-in, unsound in general, surfaced as an assumption);
                                    --pre <file>: apply parameter preconditions from
                                    a sidecar, e.g. `sum 0 elements 1 8`)
    solver scan <dir> [--bugs] [--assume-valid-params] [--closed-world] [--entries <file>] [--cross-file] [--reachable]
                                    verify EVERY .ll under <dir> without stopping, then
                                    report coverage (% of functions decided) and list
                                    every memory-safety violation found, with a witness
                                    (--entries <file>: treat ONLY functions whose name
                                    matches a listed pattern — an exact name or a
                                    trailing-`*` prefix, one per line — as attacker
                                    entries; every other function's parameters are taken
                                    as caller-validated. The sound kernel model: external
                                    linkage is not userspace-reachability, so this removes
                                    the internal-helper false positives.
                                    --cross-file: link each directory's .ll into ONE
                                    whole-program module before verifying (closed-world),
                                    so a call across a translation-unit boundary resolves
                                    to its definition and a caller's validation flows into
                                    the callee — finds deeper bugs and removes false
                                    positives a per-file view cannot see.
                                    --reachable <needs --entries>: link, per attacker
                                    entry, the transitive set of .ll it can reach through
                                    the call graph into ONE whole-program module analysed
                                    closed-world — so a caller's scalar validation flows
                                    soundly into its callee across files. A bug-finding
                                    mode: a helper is constrained by the callers reachable
                                    from that entry.)
    solver demo [--json]            verify a built-in MSIR sample (no frontend)
    solver report <result.json>     re-render a saved JSON report
    solver --help                   show this help
    solver --version                show the version

EXIT CODES:
    0 PASS    1 FAIL    2 UNKNOWN    3 tool error
";

fn main() -> ExitCode {
    // Bound glibc's per-thread malloc arenas. By default glibc opens up to 8×CPUs arenas and
    // retains each thread's high-water mark instead of returning freed pages to the OS, so a
    // many-threaded scan of large translation units accumulates RSS across arenas until it
    // exhausts RAM. Capping the arena count (and lowering the trim threshold) makes freed
    // memory actually return to the OS. glibc reads these at init, so re-exec once with them
    // set. Safe: a plain re-exec of ourselves with two extra env vars.
    #[cfg(target_os = "linux")]
    if std::env::var_os("MALLOC_ARENA_MAX").is_none() {
        if let Ok(exe) = std::env::current_exe() {
            if let Ok(status) = std::process::Command::new(exe)
                .args(std::env::args_os().skip(1))
                .env("MALLOC_ARENA_MAX", "2")
                .env("MALLOC_TRIM_THRESHOLD_", "67108864")
                .status()
            {
                return ExitCode::from(status.code().unwrap_or(1) as u8);
            }
        }
    }
    let args: Vec<String> = std::env::args().skip(1).collect();
    match run(&args) {
        Ok(code) => code,
        Err(message) => {
            eprintln!("error: {message}");
            ExitCode::from(3)
        }
    }
}

fn run(args: &[String]) -> Result<ExitCode, String> {
    let Some(command) = args.first() else {
        print!("{HELP}");
        return Ok(ExitCode::from(3));
    };

    let json = args.iter().any(|a| a == "--json");
    let closed_world = args.iter().any(|a| a == "--closed-world");
    let bug_finding = args.iter().any(|a| a == "--bugs");
    let assume_valid_params = args.iter().any(|a| a == "--assume-valid-params");
    let cross_file = args.iter().any(|a| a == "--cross-file");
    let reachable = args.iter().any(|a| a == "--reachable");
    let auto_entries = args.iter().any(|a| a == "--auto-entries");
    // `--pre <file>`: an opt-in parameter-precondition sidecar.
    let pre_file = args
        .iter()
        .position(|a| a == "--pre")
        .and_then(|i| args.get(i + 1))
        .map(PathBuf::from);
    // `--entries <file>`: an opt-in entry-point list (exact names or trailing-`*`
    // prefixes). Restricts adversarial (attacker-input) analysis to genuine entries —
    // the sound kernel model (external linkage != userspace-reachable).
    let entries_file = args
        .iter()
        .position(|a| a == "--entries")
        .and_then(|i| args.get(i + 1))
        .map(PathBuf::from);
    let entry_patterns = match &entries_file {
        Some(p) => Some(read_entry_patterns(p)?),
        None => None,
    };
    match command.as_str() {
        "--help" | "-h" | "help" => {
            print!("{HELP}");
            Ok(ExitCode::SUCCESS)
        }
        "--version" | "-V" => {
            println!("solver {}", env!("CARGO_PKG_VERSION"));
            Ok(ExitCode::SUCCESS)
        }
        "demo" => {
            let module = demo::build_demo_module();
            let report = verify_module(&module, &Config::default());
            emit(&report, json);
            Ok(verdict_code(report.verdict))
        }
        "verify" => {
            // The path is the first non-flag argument that is not a flag's value
            // (`--pre <file>` / `--entries <file>`).
            let flag_values: Vec<&str> = [pre_file.as_ref(), entries_file.as_ref()]
                .into_iter()
                .flatten()
                .filter_map(|p| p.to_str())
                .collect();
            let path = args
                .iter()
                .skip(1)
                .find(|a| !a.starts_with("--") && !flag_values.contains(&a.as_str()))
                .ok_or("`verify` needs a path argument")?;
            verify_path(Path::new(path), json, closed_world, bug_finding, assume_valid_params, pre_file.as_deref(), entry_patterns)
        }
        "scan" => {
            let dir = args
                .iter()
                .skip(1)
                .find(|a| !a.starts_with("--") && entries_file.as_ref().and_then(|p| p.to_str()) != Some(a.as_str()))
                .ok_or("`scan` needs a directory argument")?;
            // `--auto-entries`: derive the entry set automatically — every syscall wrapper
            // (precise prefixes) UNION the registered indirect handlers discovered in the
            // ops-struct initialisers (devirtualisation). Covers all attacker-reachable APIs
            // without a hand-written list, and merges with any `--entries` patterns given.
            let entry_patterns = if auto_entries {
                let mut pats: Vec<String> = SYSCALL_ENTRY_PREFIXES.iter().map(|s| s.to_string()).collect();
                if let Some(extra) = &entry_patterns {
                    pats.extend(extra.iter().cloned());
                }
                let handlers = discover_ops_handlers(Path::new(dir));
                eprintln!("--auto-entries: {} ops-struct handlers discovered", handlers.len());
                pats.extend(handlers);
                Some(pats)
            } else {
                entry_patterns
            };
            let config = Config { closed_world, bug_finding, assume_valid_params, entry_patterns: entry_patterns.clone(), ..Config::default() };
            if reachable {
                let pats = entry_patterns
                    .ok_or("`--reachable` requires `--entries <file>` (the entry points to link from)")?;
                scan_reachable(Path::new(dir), &config, &pats)
            } else {
                scan_dir(Path::new(dir), &config, cross_file)
            }
        }
        "report" => Err("`report` (re-rendering saved JSON) is not implemented yet (M0)".into()),
        other => Err(format!("unknown command `{other}` (try `solver --help`)")),
    }
}

/// Dispatch a path to the appropriate frontend, then verify.
#[allow(clippy::too_many_arguments)]
fn verify_path(
    path: &Path,
    json: bool,
    closed_world: bool,
    bug_finding: bool,
    assume_valid_params: bool,
    pre_file: Option<&Path>,
    entry_patterns: Option<Vec<String>>,
) -> Result<ExitCode, String> {
    // Turnkey: a `.rs` file is compiled to MIR by us, then verified with a
    // coverage report — the user does not hand-run rustc.
    if path.extension().and_then(|e| e.to_str()) == Some("rs") {
        return verify_rust_source(path, json);
    }
    let level = detect_level(path)?;
    // The frontends are M0 stubs; report their honest status rather than
    // pretending to have analyzed the input.
    let lowering = match level {
        SourceLevel::Llvm => {
            use csolver_ir::Frontend;
            let source = std::fs::read_to_string(path).map_err(|e| e.to_string())?;
            if let Some(hint) = llvm_attribute_hint(&source) {
                eprintln!("{hint}");
            }
            csolver_llvm::LlvmFrontend.lower(csolver_llvm::LlvmInput {
                source,
                name: path.display().to_string(),
            })
        }
        SourceLevel::Asm => {
            use csolver_ir::Frontend;
            let source = std::fs::read_to_string(path).map_err(|e| e.to_string())?;
            csolver_asm::AsmFrontend.lower(csolver_asm::AsmInput {
                source,
                arch: csolver_asm::Architecture::X86_64,
                syntax: csolver_asm::Syntax::Intel,
            })
        }
        SourceLevel::Elf => {
            let bytes = std::fs::read(path).map_err(|e| e.to_string())?;
            csolver_elf::load(&bytes).map(|_| unreachable!("stub always errors"))
        }
        SourceLevel::Mir => {
            use csolver_ir::Frontend;
            let source = std::fs::read_to_string(path).map_err(|e| e.to_string())?;
            csolver_mir::MirFrontend.lower(csolver_mir::MirInput {
                source,
                name: path.display().to_string(),
            })
        }
    };

    match lowering {
        Ok(mut module) => {
            // Apply an opt-in precondition sidecar before verification.
            if let Some(pf) = pre_file {
                let text = std::fs::read_to_string(pf).map_err(|e| e.to_string())?;
                let preconds = csolver_verifier::precond::parse(&text)?;
                let n = csolver_verifier::precond::apply(&mut module, &preconds)?;
                if !json {
                    eprintln!("applied {n} precondition(s) from {}", pf.display());
                }
            }
            let config = Config {
                level,
                closed_world,
                bug_finding,
                assume_valid_params,
                entry_patterns,
                ..Config::default()
            };
            let report = verify_module(&module, &config);
            emit(&report, json);
            Ok(verdict_code(report.verdict))
        }
        Err(e) => {
            // A frontend that cannot lower yields a tool error, not a verdict.
            Err(format!(
                "could not analyze {} at level {level}: {e}\n\
                 hint: try `solver demo` to exercise the verifier on built-in MSIR",
                path.display()
            ))
        }
    }
}

/// One found memory-safety violation, for the scan summary.
struct Finding {
    file: String,
    function: String,
    property: String,
    witness: String,
}

/// Scan **every** `.ll` file under `dir` (recursively), verify all of them without
/// stopping at any UNKNOWN or FAIL, and report the coverage (how much of the code is
/// actually decided) plus every memory-safety violation found, with its witness.
/// The per-unit scan result, aggregated deterministically after the parallel pass.
/// A "unit" is a single `.ll` file (normal scan) or a whole directory group merged into
/// one program (cross-file scan).
#[derive(Default)]
struct FileScan {
    pass: u64,
    fail: u64,
    unknown: u64,
    dropped: u64,
    errored: u64,
    findings: Vec<Finding>,
}

/// The syscall-wrapper name prefixes (SYSCALL_DEFINE* expands to these) — precise entry
/// patterns covering every syscall, used by `--auto-entries`.
const SYSCALL_ENTRY_PREFIXES: &[&str] = &[
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
fn ll_defs_and_global_refs(source: &str) -> (Vec<String>, Vec<String>) {
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

/// **Devirtualisation by ops-struct-initialiser analysis.** Scan every `.ll` under `dir` for
/// the function pointers stored in its global constant initialisers, keeping only those that
/// are actually defined functions — the complete set of the kernel's registered indirect
/// handlers (proto_ops/file_operations/… callbacks). Used as entry points, this covers the
/// attacker-reachable APIs a name-pattern list cannot, precisely and automatically (an
/// internal helper never stored in an ops struct is correctly excluded).
fn discover_ops_handlers(dir: &Path) -> std::collections::HashSet<String> {
    use std::sync::atomic::{AtomicUsize, Ordering};
    use std::sync::Mutex;
    let mut files = Vec::new();
    collect_ll(dir, &mut files);
    if files.is_empty() {
        return std::collections::HashSet::new();
    }
    let cores = std::thread::available_parallelism().map_or(1, |n| n.get());
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
fn available_mb() -> u64 {
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
const MEM_FLOOR_MB: u64 = 1024;
const MEM_RESERVE_PER_INFLIGHT_MB: u64 = 2560;
fn await_memory(active: &std::sync::atomic::AtomicUsize) {
    use std::sync::atomic::Ordering;
    loop {
        let inflight = active.load(Ordering::Relaxed) as u64;
        // At least one analysis must always be allowed to run (progress guarantee).
        if inflight == 0 {
            return;
        }
        let need = MEM_FLOOR_MB + inflight * MEM_RESERVE_PER_INFLIGHT_MB;
        if available_mb() >= need {
            return;
        }
        std::thread::sleep(std::time::Duration::from_millis(200));
    }
}

/// The external functions a module DEFINES and the external symbols it CALLS — the edges
/// of the cross-file call graph. Internal (static) definitions are file-local, so they are
/// not exported as reachability targets; a `Callee::Symbol(name)` is a cross-file call.
fn module_call_edges(m: &csolver_ir::Module) -> (Vec<String>, std::collections::HashSet<String>) {
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

/// **Reachability-based** cross-file scan (the (a) step): rather than linking a directory,
/// link — for each attacker entry — the transitive set of translation units the entry can
/// reach through the call graph, into one whole-program module analysed closed-world. Then
/// an internal helper's callers are all present, so a caller's scalar validation soundly
/// flows into it (closed-world is justified within the reachable set), eliminating the
/// false positives a per-file or per-directory view cannot. A bug-finding mode: the link is
/// per-entry, so a helper is constrained by the callers reachable from THAT entry.
fn scan_reachable(dir: &Path, config: &Config, entry_patterns: &[String]) -> Result<ExitCode, String> {
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
    let cores = std::thread::available_parallelism().map_or(1, |n| n.get());
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

    // For each entry: BFS the reachable module set (bounded), link, verify closed-world.
    const MAX_REACH: usize = 600;
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
                    if seen.len() >= MAX_REACH {
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
    for fs in all {
        pass += fs.pass;
        fail += fs.fail;
        unknown += fs.unknown;
        dropped += fs.dropped;
        errored += fs.errored;
        findings.extend(fs.findings);
    }
    let mut seen_find = HashSet::new();
    findings.retain(|f| seen_find.insert((f.file.clone(), f.function.clone(), f.property.clone(), f.witness.clone())));
    report_scan(&findings, pass, fail, unknown, dropped, errored)
}

/// Verify one already-linked whole-program module, collecting its verdicts + findings.
fn scan_linked_module(module: &csolver_ir::Module, label: &str, cfg: &Config) -> FileScan {
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
    }
    fs
}

/// Lower every `.ll` in `unit` (relative to `dir`); in cross-file mode link them into one
/// whole-program module (so a call across a translation-unit boundary resolves to its
/// definition and the caller's context flows in) and verify closed-world; otherwise verify
/// the single module per-TU. `threads` is the per-unit function-level parallelism.
fn scan_one_unit(
    unit: &[std::path::PathBuf],
    label: &str,
    dir: &Path,
    config: &Config,
    cross: bool,
    threads: usize,
) -> FileScan {
    use csolver_core::ObligationResult;
    use csolver_ir::Frontend;

    let mut fs = FileScan::default();
    let mut modules = Vec::with_capacity(unit.len());
    for path in unit {
        let rel = path.strip_prefix(dir).unwrap_or(path).display().to_string();
        match std::fs::read_to_string(path) {
            Err(_) => fs.errored += 1,
            Ok(source) => match (csolver_llvm::LlvmFrontend).lower(csolver_llvm::LlvmInput {
                source,
                name: rel,
            }) {
                Err(_) => fs.errored += 1,
                Ok(m) => modules.push(m),
            },
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
    let report = verify_module_with_threads(&module, config, threads.max(1));
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
    }
    fs
}

fn scan_dir(dir: &Path, config: &Config, cross_file: bool) -> Result<ExitCode, String> {
    use std::sync::atomic::{AtomicUsize, Ordering};
    use std::sync::Mutex;

    let mut files = Vec::new();
    collect_ll(dir, &mut files);
    files.sort();
    if files.is_empty() {
        return Err(format!("no .ll files found under {}", dir.display()));
    }
    let total_files = files.len();

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
    let cores = std::thread::available_parallelism().map_or(1, |n| n.get());
    // Use ALL cores as workers; the reservation-based memory backpressure (see `await_memory`)
    // bounds peak RSS by throttling STARTS when several large analyses are in flight, rather
    // than by permanently capping the worker count — so a tree of small units runs fully
    // parallel while a cluster of large units is serialised only as much as memory requires.
    // `CSOLVER_JOBS=N` overrides the worker count.
    let job_cap = std::env::var("CSOLVER_JOBS").ok().and_then(|v| v.parse::<usize>().ok());
    let workers = job_cap.unwrap_or(cores).min(cores).min(total_units).max(1);
    let threads_per_unit = (cores / workers).max(1);
    eprintln!(
        "scanning {total_files} .ll files under {} … ({total_units} units, {workers} workers × {threads_per_unit} threads{})",
        dir.display(),
        if cross_file { ", cross-file" } else { "" }
    );

    let next = AtomicUsize::new(0);
    let done = AtomicUsize::new(0);
    let active = AtomicUsize::new(0);
    let results: Mutex<Vec<(usize, FileScan)>> = Mutex::new(Vec::with_capacity(total_units));

    std::thread::scope(|s| {
        for _ in 0..workers {
            s.spawn(|| loop {
                let i = next.fetch_add(1, Ordering::Relaxed);
                if i >= total_units {
                    break;
                }
                // Memory backpressure: hold off starting this file while RAM is tight and
                // other files are still in flight (they free memory as they finish).
                await_memory(&active);
                active.fetch_add(1, Ordering::Relaxed);
                let (label, unit) = &units[i];
                let fs = scan_one_unit(unit, label, dir, config, cross_file, threads_per_unit);
                active.fetch_sub(1, Ordering::Relaxed);
                let d = done.fetch_add(1, Ordering::Relaxed) + 1;
                if d.is_multiple_of(50) {
                    eprintln!("  … {d}/{total_units} units");
                }
                results.lock().unwrap_or_else(|p| p.into_inner()).push((i, fs));
            });
        }
    });

    // Aggregate in unit order (deterministic output).
    let mut all = results.into_inner().unwrap_or_else(|p| p.into_inner());
    all.sort_by_key(|(i, _)| *i);
    let (mut pass, mut fail, mut unknown, mut dropped, mut errored) = (0u64, 0u64, 0u64, 0u64, 0u64);
    let mut findings: Vec<Finding> = Vec::new();
    for (_, fs) in all {
        pass += fs.pass;
        fail += fs.fail;
        unknown += fs.unknown;
        dropped += fs.dropped;
        errored += fs.errored;
        findings.extend(fs.findings);
    }

    report_scan(&findings, pass, fail, unknown, dropped, errored)
}

/// Render a scan's findings + coverage and pick the exit code.
fn report_scan(
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
fn read_entry_patterns(path: &Path) -> Result<Vec<String>, String> {
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
fn collect_ll(dir: &Path, out: &mut Vec<PathBuf>) {
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

/// Turnkey: compile a `.rs` file to MIR ourselves, verify it, and print a
/// coverage report. The coverage report lifts the never-silently-skip discipline
/// of the inner layers to the whole file: a function that failed to emit or lower
/// is reported, not folded into a flattering "everything checked". A turnkey user
/// looks less, so the tool must say what it did *not* verify — loudly.
fn verify_rust_source(path: &Path, json: bool) -> Result<ExitCode, String> {
    use csolver_ir::Frontend;
    let mir = emit_mir(path)?;
    let module = csolver_mir::MirFrontend
        .lower(csolver_mir::MirInput { source: mir, name: path.display().to_string() })
        .map_err(|e| format!("could not lower the emitted MIR of {}: {e}", path.display()))?;
    let config = Config { level: SourceLevel::Mir, ..Config::default() };
    let report = verify_module(&module, &config);
    if !json {
        eprint!("{}", render_coverage(path, &module, &report));
    }
    emit(&report, json);
    Ok(verdict_code(report.verdict))
}

/// Emit a `.rs` file's MIR text. Prefers `+nightly -Z mir-include-spans` so
/// obligations carry a source `FILE:LINE:COL`; falls back to stable (no spans)
/// when nightly is unavailable — the same graceful degradation the span parser
/// uses. A genuine compile error (stable also fails) is surfaced, never swallowed.
fn emit_mir(path: &Path) -> Result<String, String> {
    let base = ["--edition", "2021", "--crate-type=lib", "--emit=mir", "-o", "-"];
    let mut last_err = String::new();
    // Nightly first (with source spans), then stable.
    for nightly in [true, false] {
        let mut cmd = std::process::Command::new("rustc");
        if nightly {
            cmd.arg("+nightly");
        }
        cmd.args(base);
        if nightly {
            cmd.arg("-Zmir-include-spans");
        }
        match cmd.arg(path).output() {
            Ok(o) if o.status.success() => {
                return String::from_utf8(o.stdout)
                    .map_err(|_| "rustc emitted non-UTF-8 MIR".to_string());
            }
            Ok(o) => last_err = String::from_utf8_lossy(&o.stderr).trim().to_string(),
            Err(e) => last_err = format!("could not run rustc: {e}"),
        }
    }
    Err(format!("could not compile {} to MIR:\n{last_err}", path.display()))
}

/// A crate-/file-level coverage report: how many functions were found, how many
/// verified (and to what), and — the point — how many were **not analyzed**, named
/// individually. A `PASS` verdict on the analyzed set means nothing if a fifth of
/// the functions silently never reached the analyzer.
fn render_coverage(
    path: &Path,
    module: &csolver_ir::Module,
    report: &csolver_verifier::ModuleReport,
) -> String {
    use std::fmt::Write as _;
    let not_analyzed = &module.unanalyzed;
    let analyzed = module.functions.len();
    let found = analyzed + not_analyzed.len();
    let pass = report.count(Verdict::Pass);
    let fail = report.count(Verdict::Fail);
    // Total UNKNOWN includes the not-analyzed (they verify as UNKNOWN); split them
    // so "unknown but analyzed" is not confused with "never analyzed".
    let unknown_analyzed = report.count(Verdict::Unknown).saturating_sub(not_analyzed.len());

    let mut s = String::new();
    let _ = writeln!(s, "coverage {}: {found} function(s) found", path.display());
    if found == 0 {
        let _ = writeln!(
            s,
            "  WARNING: MIR emitted but 0 functions found — an emission or parse gap; \
             nothing was verified, so a PASS here would be meaningless."
        );
        return s;
    }
    let _ = writeln!(s, "  analyzed {analyzed}: {pass} PASS, {fail} FAIL, {unknown_analyzed} UNKNOWN");
    if not_analyzed.is_empty() {
        let _ = writeln!(s, "  not analyzed: 0 — every function found was analyzed");
    } else {
        let _ = writeln!(
            s,
            "  NOT ANALYZED {} (could not lower/parse — NOT covered by the verdict):",
            not_analyzed.len()
        );
        for (name, reason) in not_analyzed {
            let _ = writeln!(s, "    - {name}: {reason}");
        }
    }
    s
}

/// A hint when a `.ll` input carries pointer parameters but no
/// `dereferenceable` attributes — the signature of rustc's *debug* emission,
/// which omits the parameter attributes the provenance analysis feeds on.
/// Measured: oorandom verifies 14/14 PASS on attributed IR vs 25/29 on debug
/// IR; the verdicts on unattributed IR are sound but much more conservative.
/// Advisory only: it never changes a verdict, only tells the user why so many
/// obligations may come back UNKNOWN and how to emit richer input.
fn llvm_attribute_hint(source: &str) -> Option<&'static str> {
    let has_ptr_params = source.lines().any(|l| {
        l.starts_with("define") && (l.contains("(ptr") || l.contains(", ptr") || l.contains(" ptr %"))
    });
    let has_attrs = source.contains("dereferenceable");
    (has_ptr_params && !has_attrs).then_some(
        "note: this IR has pointer parameters but no `dereferenceable` attributes \
         (rustc's debug emission omits them).\n\
         note: pointer-heavy code will verify mostly UNKNOWN without them — emit with\n\
         note:   rustc --emit=llvm-ir -O -C no-prepopulate-passes\n\
         note: to keep the attributes without LLVM optimization passes.",
    )
}

/// Decide which level an input is, by extension / magic bytes.
fn detect_level(path: &Path) -> Result<SourceLevel, String> {
    if path.is_dir() || path.join("Cargo.toml").is_file() {
        return Ok(SourceLevel::Mir);
    }
    match path.extension().and_then(|e| e.to_str()) {
        Some("ll") => Ok(SourceLevel::Llvm),
        Some("mir") => Ok(SourceLevel::Mir),
        Some("s" | "asm" | "S") => Ok(SourceLevel::Asm),
        _ => {
            // Sniff the ELF magic number.
            let magic = read_magic(path)?;
            if magic == [0x7f, b'E', b'L', b'F'] {
                Ok(SourceLevel::Elf)
            } else {
                Err(format!(
                    "cannot determine input type of {} (expected .ll, .s, an ELF binary, or a crate dir)",
                    path.display()
                ))
            }
        }
    }
}

fn read_magic(path: &Path) -> Result<[u8; 4], String> {
    use std::io::Read;
    let mut file = std::fs::File::open(path).map_err(|e| e.to_string())?;
    let mut buf = [0u8; 4];
    match file.read_exact(&mut buf) {
        Ok(()) => Ok(buf),
        Err(_) => Ok([0; 4]),
    }
}

fn emit(report: &csolver_verifier::ModuleReport, json: bool) {
    if json {
        println!("{}", render_json(report));
    } else {
        print!("{}", render_text(report));
    }
}

fn verdict_code(verdict: Verdict) -> ExitCode {
    match verdict {
        Verdict::Pass => ExitCode::from(0),
        Verdict::Fail => ExitCode::from(1),
        Verdict::Unknown => ExitCode::from(2),
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    /// The coverage report must *name* functions that were not analyzed rather than
    /// fold them into a flattering count — the crate-level never-silently-skip
    /// guard. A `PASS` set means nothing if a function silently never reached the
    /// analyzer.
    #[test]
    fn coverage_names_not_analyzed_functions() {
        let mut module = csolver_ir::Module::new("m");
        module.unanalyzed.push(("uses_asm".into(), "inline asm unsupported".into()));
        let config = Config { level: SourceLevel::Mir, ..Config::default() };
        let report = verify_module(&module, &config);
        let cov = render_coverage(Path::new("x.rs"), &module, &report);
        assert!(cov.contains("NOT ANALYZED 1"), "reports the uncovered count: {cov}");
        assert!(cov.contains("uses_asm"), "names the uncovered function: {cov}");
    }

    /// The attributed-IR hint fires exactly on the debug-emission signature:
    /// pointer parameters present, `dereferenceable` absent. Attributed IR and
    /// pointer-free IR stay quiet — a hint that always fires teaches users to
    /// ignore it.
    #[test]
    fn llvm_hint_fires_only_on_unattributed_pointer_ir() {
        let debug_ir = "define i32 @f(ptr align 8 %self) {\nstart:\n  ret i32 0\n}\n";
        assert!(llvm_attribute_hint(debug_ir).is_some(), "debug-emission IR gets the hint");

        let attributed = "define i32 @f(ptr align 8 dereferenceable(8) %self) {\nstart:\n  ret i32 0\n}\n";
        assert!(llvm_attribute_hint(attributed).is_none(), "attributed IR is quiet");

        let no_ptrs = "define i64 @g(i64 %x) {\nstart:\n  ret i64 %x\n}\n";
        assert!(llvm_attribute_hint(no_ptrs).is_none(), "pointer-free IR is quiet");
    }

    /// A file whose MIR yields no functions must warn loudly, not report a vacuous
    /// clean bill of health.
    #[test]
    fn coverage_warns_on_zero_functions() {
        let module = csolver_ir::Module::new("m");
        let config = Config { level: SourceLevel::Mir, ..Config::default() };
        let report = verify_module(&module, &config);
        let cov = render_coverage(Path::new("empty.rs"), &module, &report);
        assert!(cov.contains("0 function(s) found"), "{cov}");
        assert!(cov.contains("WARNING"), "warns rather than implying coverage: {cov}");
    }
}
