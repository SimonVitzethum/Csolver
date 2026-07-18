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
                                    --assume-valid-returns: assume a pointer returned by an
                                    UNSUMMARISED call (external/unanalysed callee) is a valid
                                    non-null live pointer — proves no_null_deref / no_use_after_free
                                    through it; bounds stay UNKNOWN (no size is known). The
                                    interprocedural twin of --assume-valid-params: opt-in,
                                    UNSOUND in general (a call may return null / an ERR_PTR /
                                    a dangling pointer), surfaced as the `valid-returns`
                                    assumption. NOT a scan default — it would hide the very
                                    null/UAF bugs a bug-finding scan looks for;
                                    --assume-valid-loop-ptrs: assume a LOOP-CARRIED pointer
                                    (a moving iterator, `iter = iter->next`) still designates a
                                    valid live object each iteration — proves no_use_after_free /
                                    no_null_deref through it; bounds stay UNKNOWN. Opt-in, UNSOUND
                                    in general (a moving pointer can walk off its object; a list
                                    node can be freed), surfaced as `valid-loop-ptrs`. Models the
                                    kernel's intrusive-container discipline. NOT a scan default;
                                    --aliasing-model: opt-in Rust borrow-stack checking —
                                    flag a write through a shared &T reference
                                    (no_aliasing_violation);
                                    --pre <file>: apply parameter preconditions from
                                    a sidecar, e.g. `sum 0 elements 1 8`)
    solver scan <dir> [--no-bugs] [--no-assume-valid-params] [--no-closed-world] [--no-cross-file] [--no-whole-program] [--no-auto-entries] [--no-aliasing-model] [--attack-surface] [--entries <file>] [--reachable]
                                    verify EVERY .ll under <dir> without stopping, then
                                    report coverage (% of functions decided) and list
                                    every memory-safety violation found, with a witness.
                                    COMPLETE SCAN BY DEFAULT: --bugs, --assume-valid-params,
                                    --closed-world, --cross-file, --whole-program,
                                    --auto-entries and --aliasing-model are all ON unless
                                    their anti-flag (--no-<name>) turns them off — so a bare
                                    `solver scan <dir>` runs the full recall-first kernel
                                    scan and streams each bug live as it is found. Use the
                                    --no-* flags to narrow it (e.g. --no-assume-valid-params
                                    to drop the unsound framework-valid-parameter assumption,
                                    --no-bugs for the strict refutation gate). Runs with NO
                                    per-function wall-clock limit by default (termination is
                                    bounded by construction); --time-limit <secs> restores a
                                    per-function cap for a latency-bounded run.
                                    (--attack-surface: opt-in REPORTING lens — list only
                                    findings in functions directly reachable from a syscall
                                    or *ioctl* entry, suppressing the internal driver-callback
                                    mass (register accessors, clk/drm ops) that --auto-entries
                                    promotes to free-parameter entries and that is reachable
                                    only via indirect ops dispatch. Verdicts and coverage are
                                    unchanged (a filter, never a false PASS); trades recall for
                                    attack-surface precision.
                                    --entries <file>: treat ONLY functions whose name
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
                                    --whole-program: pass 1 streams every callee's effect
                                    summary over the WHOLE tree in bounded memory, then
                                    verifies (pass 2) with each cross-file `Symbol` call
                                    resolved to its real callee summary instead of an
                                    opaque havoc — cross-module precision at a few GB, no
                                    giant linked module. Combine with --cross-file to also
                                    link within each directory.
                                    --reachable: link, per attacker
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

/// A boolean flag with a chosen default. When `default` is `false` the flag is opt-in:
/// ON only if `--<name>` is present (the historical behaviour, kept for `verify` — the
/// strict, soundness-first path). When `default` is `true` the flag is opt-out: ON unless
/// the **anti-flag** `--no-<name>` is present. This lets the `scan` command ship the full
/// kernel-scan feature set enabled by default while a `--no-<name>` still switches any one
/// feature off. An explicit `--<name>` is always accepted too (redundant when default-on).
fn flag(args: &[String], name: &str, default: bool) -> bool {
    let anti = format!("--no-{name}");
    if args.contains(&anti) {
        return false;
    }
    let pos = format!("--{name}");
    default || args.contains(&pos)
}

fn run(args: &[String]) -> Result<ExitCode, String> {
    let Some(command) = args.first() else {
        print!("{HELP}");
        return Ok(ExitCode::from(3));
    };

    let json = args.iter().any(|a| a == "--json");
    // `verify` (strict) keeps every analysis flag OPT-IN (default off). `scan` overrides
    // these below with opt-OUT defaults (the full-scan feature set on, `--no-*` to disable).
    let closed_world = args.iter().any(|a| a == "--closed-world");
    let bug_finding = args.iter().any(|a| a == "--bugs");
    let assume_valid_params = args.iter().any(|a| a == "--assume-valid-params");
    // `--assume-valid-returns`: opt-in, unsound-in-general (see `Config`). Deliberately NOT a
    // scan default — it proves non-null/liveness for every unsummarised call result, so making
    // it default would *hide* the genuine null/UAF bugs a bug-finding scan exists to find.
    let assume_valid_returns = args.iter().any(|a| a == "--assume-valid-returns");
    // `--assume-valid-loop-ptrs`: opt-in, unsound-in-general (see `Config`). Same rationale as
    // `--assume-valid-returns` -- it proves liveness through a moving iterator, so it is not a
    // scan default (it would hide UAF-through-iterator bugs).
    let assume_valid_loop_ptrs = args.iter().any(|a| a == "--assume-valid-loop-ptrs");
    let assume_param_buffer_len = args.iter().any(|a| a == "--assume-param-buffer-len");
    let assume_struct_tail = args.iter().any(|a| a == "--assume-struct-tail");
    let assume_valid_mmio = args.iter().any(|a| a == "--assume-valid-mmio");
    let assume_field_invariants = args.iter().any(|a| a == "--assume-field-invariants");
    let aliasing_model = args.iter().any(|a| a == "--aliasing-model");
    // Scan-only flags (`--cross-file`, `--whole-program`, `--auto-entries`) are parsed inside
    // the `scan` branch with opt-out defaults; `--reachable` stays opt-in (it batches findings).
    let reachable = args.iter().any(|a| a == "--reachable");
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
            verify_path(Path::new(path), json, closed_world, bug_finding, assume_valid_params, assume_valid_returns, assume_valid_loop_ptrs, assume_param_buffer_len, assume_struct_tail, assume_valid_mmio, assume_field_invariants, aliasing_model, pre_file.as_deref(), entry_patterns)
        }
        "scan" => {
            let dir = args
                .iter()
                .skip(1)
                .find(|a| !a.starts_with("--") && entries_file.as_ref().and_then(|p| p.to_str()) != Some(a.as_str()))
                .ok_or("`scan` needs a directory argument")?;
            // A `scan` is a **complete kernel scan by default**: every feature that widens the
            // analysis is enabled unless its anti-flag turns it off. This is the recall-first
            // configuration (bug-finding, whole-program cross-module linking, auto-derived
            // attacker surface, framework-valid parameters, Rust aliasing). `verify` stays the
            // strict, opt-in, soundness-first path — only `scan` flips to opt-out here.
            let bug_finding = flag(args, "bugs", true);
            let assume_valid_params = flag(args, "assume-valid-params", true);
            let aliasing_model = flag(args, "aliasing-model", true);
            let closed_world = flag(args, "closed-world", true);
            let cross_file = flag(args, "cross-file", true);
            let whole_program = flag(args, "whole-program", true);
            let auto_entries = flag(args, "auto-entries", true);
            // `--attack-surface`: opt-in reporting lens (default OFF, so full recall by
            // default). Report only findings in functions directly reachable from a
            // syscall/ioctl entry — cuts the internal-callback false-positive mass that
            // `--auto-entries` produces. Sound (a reporting filter; verdicts unchanged).
            let attack_surface_only = args.iter().any(|a| a == "--attack-surface");
            // **No wall-clock time limit by default.** A per-function clock is a hard timeout: on
            // expiry the function truncates to UNKNOWN, dropping a slow-but-provable result for a
            // resource reason. Termination is already guaranteed *by construction* — the merged
            // exploration visits each block once (loop back-edges cut) and the SAT solver has its
            // own decision/CNF budget — so a function's cost is bounded without a clock. Give every
            // function full effort by default (`time_budget = None`); `--time-limit <secs>` restores
            // a per-function cap for a latency-bounded run. (This is what the deferred second phase
            // already did for budget-limited units; making it the default removes the two-phase
            // detour and any wall-clock-driven UNKNOWN.)
            let time_budget = args
                .iter()
                .position(|a| a == "--time-limit")
                .and_then(|i| args.get(i + 1))
                .and_then(|v| v.parse::<u64>().ok())
                .map(std::time::Duration::from_secs);
            // `--auto-entries`: derive the entry set automatically — every syscall wrapper
            // (precise prefixes) UNION the registered indirect handlers discovered in the
            // ops-struct initialisers (devirtualisation). Covers all attacker-reachable APIs
            // without a hand-written list, and merges with any `--entries` patterns given.
            let entry_patterns = if auto_entries {
                Some(derive_auto_entries(Path::new(dir), entry_patterns.as_deref()))
            } else {
                entry_patterns
            };
            if reachable {
                // `--reachable` needs a set of link-from entries. A hand-written `--entries` file is
                // NOT required: if none is given, derive the attacker surface automatically (the same
                // syscall + ops-handler set as `--auto-entries`), so `--reachable` works standalone.
                let pats = entry_patterns.unwrap_or_else(|| {
                    eprintln!("--reachable: no --entries given — deriving the attacker surface automatically");
                    derive_auto_entries(Path::new(dir), None)
                });
                let config = Config { closed_world, bug_finding, assume_valid_params, assume_valid_returns, assume_valid_loop_ptrs, assume_param_buffer_len, assume_struct_tail, assume_valid_mmio, assume_field_invariants, aliasing_model, entry_patterns: Some(pats.clone()), time_budget, attack_surface_only, ..Config::default() };
                scan_reachable(Path::new(dir), &config, &pats)
            } else {
                let config = Config { closed_world, bug_finding, assume_valid_params, assume_valid_returns, assume_valid_loop_ptrs, assume_param_buffer_len, assume_struct_tail, assume_valid_mmio, assume_field_invariants, aliasing_model, entry_patterns, time_budget, attack_surface_only, ..Config::default() };
                scan_dir(Path::new(dir), &config, cross_file, whole_program)
            }
        }
        "facts" => {
            let dir = args
                .iter()
                .skip(1)
                .find(|a| !a.starts_with("--"))
                .ok_or("`facts` needs a directory argument")?;
            facts_scan(Path::new(dir), closed_world)
        }
        "report" => Err("`report` (re-rendering saved JSON) is not implemented yet (M0)".into()),
        other => Err(format!("unknown command `{other}` (try `solver --help`)")),
    }
}


// --- module split (mechanical refactor) ---
mod findings;
mod scan;
mod scan_dir;
mod scan_run;
mod verify;
#[cfg(test)]
#[path = "cli_tests.rs"]
mod tests;
use findings::*;
use scan::*;
use scan_dir::*;
use scan_run::*;
use verify::*;
