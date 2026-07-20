use super::*;

/// The whole-program concurrency oracle: from a concurrent seed (an entry, or a spawned handler
/// — `spawn` trace event kind 7) it returns the direct-call-graph closure; a function reachable
/// only from single-threaded code is excluded, and an empty seed yields `None` (pair-all).
#[test]
fn whole_program_concurrency_closure() {
    // sys_read (entry) → helper_a → helper_b ;  init_only → cold  (single-threaded).
    let edges = vec![
        ("sys_read".to_string(), vec!["helper_a".to_string()]),
        ("helper_a".to_string(), vec!["helper_b".to_string()]),
        ("init_only".to_string(), vec!["cold".to_string()]),
    ];
    let no_traces: Vec<(String, Vec<(u8, String)>)> = vec![];
    let entries = vec!["sys_*".to_string()];
    let set = whole_program_concurrent(&edges, &no_traces, &entries, &[], &[], &[])
        .expect("seed non-empty");
    assert!(set.contains("sys_read") && set.contains("helper_a") && set.contains("helper_b"),
        "the entry and its transitive callees are concurrent: {set:?}");
    assert!(!set.contains("init_only") && !set.contains("cold"),
        "single-threaded-only functions are excluded: {set:?}");
    // A spawned handler (trace kind 7) seeds concurrency without any entry pattern.
    let traces = vec![("mod_init".to_string(), vec![(7u8, "worker".to_string())])];
    let via_spawn = whole_program_concurrent(
        &[("worker".to_string(), vec!["helper_b".to_string()])],
        &traces,
        &[],
        &[],
        &[],
        &[],
    )
    .expect("spawn seed");
    assert!(via_spawn.contains("worker") && via_spawn.contains("helper_b"));
    // No entries and no spawn evidence ⇒ None (the oracle does not restrict).
    assert!(whole_program_concurrent(&edges, &no_traces, &[], &[], &[], &[]).is_none());
}

/// Indirect-call safety: a handler reachable ONLY through a stored function pointer (an
/// indirect call) must still be admitted as concurrent when a concurrent function performs
/// that indirect call. `dispatch` (concurrent, reached from the entry) does an indirect call;
/// `handler` is address-taken but has no direct edge into the concurrent closure — it must
/// nonetheless join the reach set. `unrelated` is address-taken but the indirect call would be
/// admitted regardless; a NON-address-taken cold function stays excluded.
#[test]
fn whole_program_oracle_admits_indirect_targets() {
    let edges = vec![
        ("sys_ioctl".to_string(), vec!["dispatch".to_string()]),
        ("init_only".to_string(), vec!["cold".to_string()]),
    ];
    let no_traces: Vec<(String, Vec<(u8, String)>)> = vec![];
    let entries = vec!["sys_*".to_string()];
    let defined = vec![
        "sys_ioctl".to_string(),
        "dispatch".to_string(),
        "handler".to_string(),
        "init_only".to_string(),
        "cold".to_string(),
    ];
    let addr_taken = vec!["handler".to_string()]; // fn-pointer stored somewhere
    let indirect = vec!["dispatch".to_string()]; // dispatch does an indirect call
    let set = whole_program_concurrent(
        &edges, &no_traces, &entries, &defined, &addr_taken, &indirect,
    )
    .expect("seed non-empty");
    assert!(set.contains("dispatch"), "direct closure: {set:?}");
    assert!(set.contains("handler"), "address-taken indirect target admitted: {set:?}");
    assert!(!set.contains("cold"), "non-address-taken cold fn stays excluded: {set:?}");
    // Without any indirect-call site reached, the address-taken fn is NOT admitted.
    let set2 = whole_program_concurrent(
        &edges, &no_traces, &entries, &defined, &addr_taken, &[],
    )
    .expect("seed");
    assert!(!set2.contains("handler"), "no indirect call reached ⇒ not admitted: {set2:?}");
}

/// The coverage report must *name* functions that were not analyzed rather than
/// fold them into a flattering count — the crate-level never-silently-skip
/// guard. A `PASS` set means nothing if a function silently never reached the
/// analyzer.
#[test]
fn size_aware_backpressure_reserves_and_guarantees_progress() {
    use std::sync::atomic::{AtomicU64, Ordering};
    // Cost scales with input size (12×/MiB by default, plus a 64 MiB base).
    assert_eq!(unit_cost_mb(0), 64);
    assert_eq!(unit_cost_mb(10 * 1024 * 1024), 64 + 120);

    let reserved = AtomicU64::new(0);
    // A unit that fits is admitted and reserves its cost.
    reserve_budget(&reserved, 500, 1000);
    assert_eq!(reserved.load(Ordering::Relaxed), 500);
    // A second unit that still fits (500 + 400 ≤ 1000) is admitted too.
    reserve_budget(&reserved, 400, 1000);
    assert_eq!(reserved.load(Ordering::Relaxed), 900);
    // Progress guarantee: with nothing in flight, a unit larger than the whole budget still
    // runs (never a deadlock on one oversized cross-file directory).
    reserved.store(0, Ordering::Relaxed);
    reserve_budget(&reserved, 5000, 1000);
    assert_eq!(reserved.load(Ordering::Relaxed), 5000);
}

#[test]
fn attack_surface_keeps_syscall_ioctl_reachable_only() {
    // foo_ioctl (matches *ioctl*) → helper ; __x64_sys_read (syscall) → vfs_read ;
    // drm_reg_write → reg_poke is an internal driver callback: in the real kernel it is
    // reached only through *indirect* ops dispatch, which has no direct edge here, so the
    // attack-surface closure must exclude it (that is the false-positive mass we suppress).
    let edges = vec![
        ("foo_ioctl".to_string(), vec!["helper".to_string()]),
        ("__x64_sys_read".to_string(), vec!["vfs_read".to_string()]),
        ("drm_reg_write".to_string(), vec!["reg_poke".to_string()]),
    ];
    let defined = vec![
        "foo_ioctl".to_string(),
        "helper".to_string(),
        "__x64_sys_read".to_string(),
        "vfs_read".to_string(),
        "drm_reg_write".to_string(),
        "reg_poke".to_string(),
    ];
    let set = attack_surface_reachable(&edges, &defined);
    assert!(set.contains("foo_ioctl") && set.contains("helper"), "ioctl entry + callee kept: {set:?}");
    assert!(set.contains("__x64_sys_read") && set.contains("vfs_read"), "syscall entry + callee kept: {set:?}");
    assert!(
        !set.contains("drm_reg_write") && !set.contains("reg_poke"),
        "internal callback reachable only via indirect dispatch is excluded: {set:?}"
    );
}

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
