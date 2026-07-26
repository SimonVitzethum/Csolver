//! `solver gen-contracts <dir>` — **auto-generate candidate `.contract` entries** for the external
//! kernel APIs a corpus calls but does not define.
//!
//! The contract-driven checks (taint, typestate, lock-order, capability, alloc/free) fire only when
//! a `.contract` file describes the external API's effect. Hand-writing those for the whole kernel
//! is the bottleneck to out-of-the-box recall. This generator does the mechanical part: it lowers
//! every `.ll` under `dir`, collects the function names that are **called but never defined** in the
//! corpus (the true externals), and matches each against the kernel's well-established naming
//! conventions to emit a candidate effect line.
//!
//! **Soundness discipline.** A wrong effect contract can fabricate a false FAIL (a spurious `free`
//! ⇒ false double-free) or mask a bug — so the output is **not applied automatically**. It is
//! written for a human to review and then load with `--contracts <dir>`; each entry carries the
//! heuristic it came from. Names already covered by the built-in defaults are skipped. Only
//! high-confidence conventions are emitted (allocation/free/lock/unlock/user-copy/rcu); ambiguous
//! ones (`*_put`/`*_get` refcount, `*_destroy`) are deliberately omitted rather than guessed.

use crate::findings::collect_ll;
use csolver_contracts::Contracts;
use csolver_ir::{Callee, Frontend, Inst};
use std::collections::{BTreeMap, BTreeSet};
use std::path::Path;
use std::process::ExitCode;
use std::sync::OnceLock;

/// One inferred effect line (the text after the `[names]` header) plus the heuristic that produced
/// it, so entries with the same effect are grouped and the source convention is documented.
#[derive(PartialEq, Eq, PartialOrd, Ord, Clone)]
struct Effect {
    /// The heuristic tag (a comment + grouping key).
    why: &'static str,
    /// The effect line, e.g. `free ptr=arg0` or `lock arg=0 spin`.
    line: &'static str,
}

/// Match one external function name to a candidate effect via kernel naming conventions. `None`
/// when no high-confidence convention applies (left for a human to annotate).
fn infer(name: &str) -> Option<Effect> {
    // Order matters: check the more specific / overriding conventions first.
    let e = |why, line| Some(Effect { why, line });
    match name {
        // User-copy: the taint source (into the kernel, `copy_from_user(dst, src, n)`) and the
        // disclosure sink (to userspace, `copy_to_user(dst, src, n)` — dst is the USER pointer).
        "copy_from_user" | "__copy_from_user" | "_copy_from_user" | "copy_from_user_nofault" => {
            e("user-copy (taint source)", "write arg0 len=arg2 fill=user from=arg1")
        }
        "copy_to_user" | "__copy_to_user" | "_copy_to_user" | "copy_to_user_nofault" => {
            e("user-copy (disclosure sink)", "read arg1 len=arg2 sink=user")
        }
        // Element-count allocators handled by the defaults; here the long tail of plain allocators.
        _ if is_alloc(name) => e("allocator (size=arg0 — review the size arg)", "alloc size=arg0 align=16"),
        _ if is_free(name) => e("deallocator", "free arg0"),
        // NB: unlocks carry no contract effect — the executor drops a held lock's base on any call
        // that passes it, so an `unlock` line is neither needed nor a valid keyword.
        _ if is_lock(name) => {
            if name.contains("spin") {
                e("spinlock acquire", "lock-acquire arg0 spin")
            } else {
                e("mutex/semaphore acquire", "lock-acquire arg0")
            }
        }
        _ => None,
    }
}

fn is_alloc(n: &str) -> bool {
    (n.contains("alloc") || n.contains("malloc"))
        && !n.contains("free")
        && !n.contains("realloc")
        && !n.contains("alloca")
        // zeroing allocators are deliberately unmodelled (a zeroed read would false-FAIL as uninit).
        && !n.starts_with("kz")
        && !n.starts_with("kc")
        && !n.contains("zalloc")
        && !n.contains("calloc")
}

fn is_free(n: &str) -> bool {
    // A clear deallocator: contains "free", excluding false friends. `kmem_cache_free` frees arg1,
    // not arg0, so it is omitted here (the defaults cover the common freers precisely).
    (n.ends_with("free") || n.contains("_free_") || n.contains("free_"))
        && !n.contains("freeze")
        && !n.contains("freed")
        && !n.contains("kmem_cache_free")
        && !n.contains("free_percpu")
}

fn is_lock(n: &str) -> bool {
    (n.ends_with("_lock") || n == "spin_lock" || n == "mutex_lock" || n == "raw_spin_lock")
        && !n.contains("unlock")
        && !n.contains("trylock")
        && !n.contains("lockdep")
}

/// Whether the built-in defaults already describe this API (skip — the generator only adds new ones).
fn already_covered(name: &str) -> bool {
    static DEFAULTS: OnceLock<Contracts> = OnceLock::new();
    DEFAULTS.get_or_init(Contracts::defaults).lookup(name).is_some()
}

/// Generate candidate contracts for every external API a corpus calls, printing a `.contract` file
/// to stdout (redirect to a file, review, then load with `--contracts`).
pub(crate) fn gen_contracts(dir: &Path) -> Result<ExitCode, String> {
    let mut files = Vec::new();
    collect_ll(dir, &mut files);
    files.sort();
    if files.is_empty() {
        return Err(format!("no .ll files found under {}", dir.display()));
    }
    eprintln!("gen-contracts: scanning {} .ll files under {} …", files.len(), dir.display());

    let mut defined: BTreeSet<String> = BTreeSet::new();
    let mut called: BTreeSet<String> = BTreeSet::new();
    for path in &files {
        let Ok(src) = std::fs::read_to_string(path) else { continue };
        let Ok(m) = (csolver_llvm::LlvmFrontend)
            .lower(csolver_llvm::LlvmInput { source: src, name: String::new() })
        else {
            continue;
        };
        for f in &m.functions {
            defined.insert(f.name.clone());
            for inst in f.blocks.iter().flat_map(|b| &b.insts) {
                if let Inst::Call { callee: Callee::Symbol(nm), .. } = inst {
                    called.insert(nm.clone());
                }
            }
        }
    }

    // Externals = called but never defined, not already covered, with an inferable effect.
    // Group by effect so the emitted file lists many names per `[…]` header (compact + review-able).
    let mut groups: BTreeMap<Effect, BTreeSet<String>> = BTreeMap::new();
    for name in called.difference(&defined) {
        if already_covered(name) {
            continue;
        }
        if let Some(eff) = infer(name) {
            groups.entry(eff).or_default().insert(name.clone());
        }
    }

    let total: usize = groups.values().map(BTreeSet::len).sum();
    println!("# AUTO-GENERATED candidate contracts — REVIEW before use.");
    println!("# Inferred from kernel naming conventions over the corpus's external calls.");
    println!("# A wrong effect can fabricate a false FAIL (spurious free ⇒ double-free) — check each.");
    println!("# Load with: solver scan <dir> --contracts <this-dir>");
    println!("# {total} candidate APIs across {} effect classes.\n", groups.len());
    for (eff, names) in &groups {
        println!("# {} ({} APIs)", eff.why, names.len());
        let list: Vec<&str> = names.iter().map(String::as_str).collect();
        println!("[{}]", list.join(" "));
        println!("{}\n", eff.line);
    }
    eprintln!("gen-contracts: emitted {total} candidate contracts across {} classes.", groups.len());
    Ok(ExitCode::SUCCESS)
}

#[cfg(test)]
mod tests {
    use super::{infer, is_alloc, is_free};

    #[test]
    fn inference_matches_kernel_conventions() {
        // Allocators (long tail) — but NOT zeroing ones (a zeroed read would false-FAIL as uninit).
        assert_eq!(infer("my_pool_alloc").unwrap().line, "alloc size=arg0 align=16");
        assert!(!is_alloc("kzalloc") && !is_alloc("kcalloc") && !is_alloc("devm_kzalloc"));
        assert!(!is_alloc("kfree") && !is_alloc("krealloc"));
        // Deallocators.
        assert_eq!(infer("widget_free").unwrap().line, "free arg0");
        assert!(!is_free("freeze_super") && !is_free("kmem_cache_free"));
        // Locks — spin vs mutex; unlocks carry NO effect (implicit release).
        assert_eq!(infer("foo_spin_lock").unwrap().line, "lock-acquire arg0 spin");
        assert_eq!(infer("bar_lock").unwrap().line, "lock-acquire arg0");
        assert!(infer("foo_spin_unlock").is_none(), "unlocks are implicit, not a contract effect");
        assert!(infer("foo_trylock").is_none(), "trylock is not a hard acquire");
        // User-copy.
        assert_eq!(infer("copy_from_user").unwrap().line, "write arg0 len=arg2 fill=user from=arg1");
        // No convention → no guess.
        assert!(infer("some_unrelated_helper").is_none());
    }
}
