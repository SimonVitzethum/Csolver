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

use std::path::Path;
use std::process::ExitCode;

use csolver_core::{SourceLevel, Verdict};
use csolver_report::{render_json, render_text};
use csolver_verifier::{verify_module, Config};

mod demo;

const HELP: &str = "\
solver — CSolver memory-safety verifier

USAGE:
    solver verify <path> [--json] [--closed-world]
                                    verify a .rs (turnkey), .mir, .ll, .s, or ELF
                                    (--closed-world: treat the module as the whole
                                    program — synthesize contracts for exported
                                    functions from all their in-module call sites)
    solver demo [--json]            verify a built-in MSIR sample (no frontend)
    solver report <result.json>     re-render a saved JSON report
    solver --help                   show this help
    solver --version                show the version

EXIT CODES:
    0 PASS    1 FAIL    2 UNKNOWN    3 tool error
";

fn main() -> ExitCode {
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
            let path = args
                .get(1)
                .filter(|a| !a.starts_with("--"))
                .ok_or("`verify` needs a path argument")?;
            verify_path(Path::new(path), json, closed_world)
        }
        "report" => Err("`report` (re-rendering saved JSON) is not implemented yet (M0)".into()),
        other => Err(format!("unknown command `{other}` (try `solver --help`)")),
    }
}

/// Dispatch a path to the appropriate frontend, then verify.
fn verify_path(path: &Path, json: bool, closed_world: bool) -> Result<ExitCode, String> {
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
        Ok(module) => {
            let config = Config {
                level,
                closed_world,
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
