//! The `solver` command-line interface.
//!
//! ```text
//! solver verify <file.ll | file.s | binary | crate-dir>   [--json]
//! solver demo                                             [--json]
//! solver report <result.json>
//! solver --help | --version
//! ```
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
    solver verify <path> [--json]   verify an .ll / .s / ELF binary / crate
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
            verify_path(Path::new(path), json)
        }
        "report" => Err("`report` (re-rendering saved JSON) is not implemented yet (M0)".into()),
        other => Err(format!("unknown command `{other}` (try `solver --help`)")),
    }
}

/// Dispatch a path to the appropriate frontend, then verify.
fn verify_path(path: &Path, json: bool) -> Result<ExitCode, String> {
    let level = detect_level(path)?;
    // The frontends are M0 stubs; report their honest status rather than
    // pretending to have analyzed the input.
    let lowering = match level {
        SourceLevel::Llvm => {
            use csolver_ir::Frontend;
            let source = std::fs::read_to_string(path).map_err(|e| e.to_string())?;
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
            csolver_mir::MirFrontend.lower(csolver_mir::MirInput {
                path: path.display().to_string(),
            })
        }
    };

    match lowering {
        Ok(module) => {
            let config = Config {
                level,
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

/// Decide which level an input is, by extension / magic bytes.
fn detect_level(path: &Path) -> Result<SourceLevel, String> {
    if path.is_dir() || path.join("Cargo.toml").is_file() {
        return Ok(SourceLevel::Mir);
    }
    match path.extension().and_then(|e| e.to_str()) {
        Some("ll") => Ok(SourceLevel::Llvm),
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
