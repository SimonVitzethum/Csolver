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
    solver scan <dir> [--bugs] [--assume-valid-params] [--closed-world] [--entries <file>] [--cross-file] [--whole-program] [--reachable]
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
    let whole_program = args.iter().any(|a| a == "--whole-program");
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
                let config = Config { closed_world, bug_finding, assume_valid_params, entry_patterns: Some(pats.clone()), ..Config::default() };
                scan_reachable(Path::new(dir), &config, &pats)
            } else {
                let config = Config { closed_world, bug_finding, assume_valid_params, entry_patterns, ..Config::default() };
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
