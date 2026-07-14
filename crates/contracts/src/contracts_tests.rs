use super::*;

#[test]
fn defaults_cover_the_former_hardcoded_apis() {
    let c = Contracts::defaults();
    // Allocators (formerly `alloc_size`).
    assert_eq!(c.lookup("kmalloc").and_then(|c| c.alloc()), Some((&SizeExpr::Arg(0), 16)));
    assert_eq!(
        c.lookup("kmalloc_array").and_then(|c| c.alloc()),
        Some((&SizeExpr::Product(0, 1), 16))
    );
    assert_eq!(c.lookup("reallocarray").and_then(|c| c.alloc()), Some((&SizeExpr::Product(1, 2), 16)));
    // Deallocators (formerly `dealloc_ptr_arg`).
    assert_eq!(
        c.lookup("kfree").unwrap().effects,
        vec![
            Effect::Free { ptr: 0 },
            // RCU grace-period guard (rcu.contract): a plain free of a still-published object.
            Effect::TypestateRequire { arg: 0, protocol: "reclaim".into(), state: "deferred".into(), negate: true },
        ]
    );
    assert_eq!(c.lookup("kmem_cache_free").unwrap().effects, vec![Effect::Free { ptr: 1 }]);
    // User-copies (formerly `user_copy_kernel_arg`).
    assert_eq!(
        c.lookup("copy_from_user").unwrap().effects,
        vec![
            Effect::Write { ptr: 0, len: SizeExpr::Arg(2), fill: Fill::User, from: Some(1) },
            Effect::TaintSource { arg: 0, label: "user".into() },
        ]
    );
    assert_eq!(
        c.lookup("copy_to_user").unwrap().effects,
        vec![Effect::Read { ptr: 1, len: SizeExpr::Arg(2), sink: ReadSink::User }]
    );
    // An unknown API has no contract.
    assert!(c.lookup("definitely_not_an_api").is_none());
}

#[test]
fn parses_all_size_forms_and_reports_errors() {
    let mut c = Contracts::default();
    c.parse_str("[a b]\nalloc size=arg0*arg1 align=8\n[d]\nwrite arg0 len=64 fill=user\n", "t")
        .unwrap();
    assert_eq!(c.lookup("a").and_then(|c| c.alloc()), Some((&SizeExpr::Product(0, 1), 8)));
    assert_eq!(c.lookup("b").and_then(|c| c.alloc()), Some((&SizeExpr::Product(0, 1), 8)));
    assert_eq!(
        c.lookup("d").unwrap().effects,
        vec![Effect::Write { ptr: 0, len: SizeExpr::Const(64), fill: Fill::User, from: None }]
    );
    // An effect before any header is an error.
    assert!(Contracts::default().parse_str("free arg0\n", "t").is_err());
    // An unknown effect is an error.
    assert!(Contracts::default().parse_str("[x]\nteleport arg0\n", "t").is_err());
}

#[test]
fn provenance_lattice_labels_and_requirements() {
    let mut c = Contracts::default();
    c.parse_str(
        "prov foreign grants=read\nprov kernel grants=read,write\n\
         [mark_foreign]\nlabel arg0 foreign\n\
         [needs_writable]\nrequire arg0 write\n",
        "t",
    )
    .unwrap();
    // The lattice: `foreign` grants read but not write; `kernel` grants both.
    assert!(c.grants("foreign", "read"));
    assert!(!c.grants("foreign", "write"));
    assert!(c.grants("kernel", "write"));
    // An unlabelled region grants everything (sound default).
    assert!(c.grants("anything-unknown", "write"));
    // The effects.
    assert_eq!(
        c.lookup("mark_foreign").unwrap().effects,
        vec![Effect::Label { ptr: 0, label: "foreign".into() }]
    );
    assert_eq!(
        c.lookup("needs_writable").unwrap().effects,
        vec![Effect::Require { ptr: 0, cap: "write".into() }]
    );
}

#[test]
fn taint_effects_parse() {
    let mut c = Contracts::default();
    c.parse_str(
        "[src]\ntaint-source arg1 user\n\
         [snk]\ntaint-sink arg0 user\n\
         [san]\ntaint-sanitize ret user\n",
        "t",
    )
    .unwrap();
    assert_eq!(
        c.lookup("src").unwrap().effects,
        vec![Effect::TaintSource { arg: 1, label: "user".into() }]
    );
    assert_eq!(
        c.lookup("snk").unwrap().effects,
        vec![Effect::TaintSink { arg: 0, label: "user".into() }]
    );
    // `ret` maps to the return-value sentinel.
    assert_eq!(
        c.lookup("san").unwrap().effects,
        vec![Effect::TaintSanitize { arg: RET_ARG, label: "user".into() }]
    );
}

#[test]
fn typestate_effects_parse() {
    let mut c = Contracts::default();
    c.parse_str(
        "[open_h]\ntypestate-set ret file open\n\
         [close_h]\ntypestate-require-not arg0 file closed\ntypestate-set arg0 file closed\n\
         [use_h]\ntypestate-require arg0 perm checked\n",
        "t",
    )
    .unwrap();
    assert_eq!(
        c.lookup("open_h").unwrap().effects,
        vec![Effect::TypestateSet { arg: RET_ARG, protocol: "file".into(), state: "open".into() }]
    );
    assert_eq!(
        c.lookup("close_h").unwrap().effects,
        vec![
            Effect::TypestateRequire { arg: 0, protocol: "file".into(), state: "closed".into(), negate: true },
            Effect::TypestateSet { arg: 0, protocol: "file".into(), state: "closed".into() },
        ]
    );
    assert_eq!(
        c.lookup("use_h").unwrap().effects,
        vec![Effect::TypestateRequire { arg: 0, protocol: "perm".into(), state: "checked".into(), negate: false }]
    );
}

#[test]
fn yield_refcount_and_leak_effects_parse() {
    let mut c = Contracts::default();
    c.parse_str(
        "[yld]\ntypestate-yield toctou checked stale\n\
         [get]\nrefcount-inc arg0 kref\n\
         [put]\nrefcount-dec arg0 kref\n\
         [own]\ntypestate-leak file open\n",
        "t",
    )
    .unwrap();
    assert_eq!(
        c.lookup("yld").unwrap().effects,
        vec![Effect::TypestateYield { protocol: "toctou".into(), from: "checked".into(), to: "stale".into() }]
    );
    assert_eq!(
        c.lookup("get").unwrap().effects,
        vec![Effect::Refcount { arg: 0, protocol: "kref".into(), dec: false, checked: false }]
    );
    assert_eq!(
        c.lookup("put").unwrap().effects,
        vec![Effect::Refcount { arg: 0, protocol: "kref".into(), dec: true, checked: false }]
    );
    assert_eq!(
        c.lookup("own").unwrap().effects,
        vec![Effect::TypestateLeak { protocol: "file".into(), state: "open".into() }]
    );
    // Spawn/join effects.
    let mut c3 = Contracts::default();
    c3.parse_str("[pthread_create]\nspawn arg2\n[pthread_join]\njoin\n", "t").unwrap();
    assert_eq!(c3.lookup("pthread_create").unwrap().effects, vec![Effect::Spawn { arg: 2 }]);
    assert_eq!(c3.lookup("pthread_join").unwrap().effects, vec![Effect::Join]);
    // Barrier effects: full (default), write, read — bare fences (no location access).
    let mut c2 = Contracts::default();
    c2.parse_str("[smp_mb]\nbarrier\n[smp_wmb]\nbarrier write\n[smp_rmb]\nbarrier read\n", "t").unwrap();
    assert_eq!(c2.lookup("smp_mb").unwrap().effects, vec![Effect::Barrier { kind: 0, access: None }]);
    assert_eq!(c2.lookup("smp_wmb").unwrap().effects, vec![Effect::Barrier { kind: 1, access: None }]);
    assert_eq!(c2.lookup("smp_rmb").unwrap().effects, vec![Effect::Barrier { kind: 2, access: None }]);
    // A release/acquire store/load ALSO accesses the flag at the given arg.
    let mut c4 = Contracts::default();
    c4.parse_str("[sr]\nbarrier write arg0\n[la]\nbarrier read arg1\n", "t").unwrap();
    assert_eq!(c4.lookup("sr").unwrap().effects, vec![Effect::Barrier { kind: 1, access: Some(0) }]);
    assert_eq!(c4.lookup("la").unwrap().effects, vec![Effect::Barrier { kind: 2, access: Some(1) }]);
    // The shipped defaults wire smp_store_release/smp_load_acquire to the flag access.
    let d = Contracts::defaults();
    assert_eq!(d.lookup("smp_store_release").unwrap().effects, vec![Effect::Barrier { kind: 1, access: Some(0) }]);
    assert_eq!(d.lookup("smp_load_acquire").unwrap().effects, vec![Effect::Barrier { kind: 2, access: Some(0) }]);
}

#[test]
fn propagate_effect_parses() {
    let mut c = Contracts::default();
    c.parse_str("[sg_set_page]\npropagate arg0 from arg1\n", "t").unwrap();
    assert_eq!(
        c.lookup("sg_set_page").unwrap().effects,
        vec![Effect::Propagate { dst: 0, src: 1 }]
    );
    // Bad syntax (missing `from`) is an error.
    assert!(Contracts::default().parse_str("[x]\npropagate arg0 arg1\n", "t").is_err());
}

#[test]
fn require_if_alias_parses() {
    let mut c = Contracts::default();
    c.parse_str("[aead_request_set_crypt]\nrequire-if-alias arg1 arg2 write\n", "t").unwrap();
    assert_eq!(
        c.lookup("aead_request_set_crypt").unwrap().effects,
        vec![Effect::RequireIfAlias { a: 1, b: 2, cap: "write".into() }]
    );
}

#[test]
fn comments_and_blank_lines_are_ignored() {
    let mut c = Contracts::default();
    c.parse_str("# header\n\n[m]   # the allocator\nalloc size=arg0 align=16 # 16-byte\n", "t")
        .unwrap();
    assert_eq!(c.lookup("m").and_then(|c| c.alloc()), Some((&SizeExpr::Arg(0), 16)));
}

#[test]
fn sync_effects_parse() {
    let mut c = Contracts::default();
    c.parse_str(
        "[spin_lock]\nlock-acquire arg0 spin\n[mutex_lock]\nlock-acquire arg0\nblocking\n\
         [local_irq_save]\nirq-disable\n[local_irq_restore]\nirq-enable\n\
         [rcu_read_lock]\nrcu-read-lock\n[rcu_read_unlock]\nrcu-read-unlock\n\
         [this_cpu_ptr]\npercpu-ptr\n[idr_find]\ncontainer-lookup arg0\n\
         [fget]\nglobal-lookup @files\n",
        "t",
    )
    .unwrap();
    assert_eq!(
        c.lookup("spin_lock").unwrap().effects,
        vec![Effect::LockAcquire { arg: 0, spin: true }]
    );
    assert_eq!(
        c.lookup("mutex_lock").unwrap().effects,
        vec![Effect::LockAcquire { arg: 0, spin: false }, Effect::Blocking]
    );
    assert_eq!(c.lookup("local_irq_save").unwrap().effects, vec![Effect::IrqDisable]);
    assert_eq!(c.lookup("local_irq_restore").unwrap().effects, vec![Effect::IrqEnable]);
    assert_eq!(c.lookup("rcu_read_lock").unwrap().effects, vec![Effect::RcuReadLock]);
    assert_eq!(c.lookup("rcu_read_unlock").unwrap().effects, vec![Effect::RcuReadUnlock]);
    assert_eq!(c.lookup("this_cpu_ptr").unwrap().effects, vec![Effect::PercpuPtr]);
    assert_eq!(c.lookup("idr_find").unwrap().effects, vec![Effect::ContainerLookup { arg: 0 }]);
    assert_eq!(
        c.lookup("fget").unwrap().effects,
        vec![Effect::GlobalLookup { root: "@files".into() }]
    );
    // An unknown lock-acquire flag is an error.
    assert!(Contracts::default().parse_str("[x]\nlock-acquire arg0 fast\n", "t").is_err());
}

#[test]
fn default_kernel_sync_contract_loads() {
    // The built-in kernel_sync.contract must classify the migrated primitives.
    let c = Contracts::defaults();
    assert_eq!(
        c.lookup("spin_lock").unwrap().effects,
        vec![Effect::LockAcquire { arg: 0, spin: true }]
    );
    assert!(c
        .lookup("spin_lock_irqsave")
        .unwrap()
        .effects
        .contains(&Effect::IrqDisable));
    assert!(c.lookup("schedule").unwrap().effects.contains(&Effect::Blocking));
    // `mutex_lock` keeps its TOCTOU yield alongside the sync classification.
    assert!(c.lookup("mutex_lock").unwrap().effects.iter().any(|e| matches!(
        e,
        Effect::TypestateYield { protocol, .. } if protocol == "toctou"
    )));
    // `synchronize_rcu` keeps the reclaim safe-point yield and gains `blocking`.
    let sr = &c.lookup("synchronize_rcu").unwrap().effects;
    assert!(sr.contains(&Effect::Blocking));
    assert!(sr.iter().any(|e| matches!(
        e,
        Effect::TypestateYield { protocol, .. } if protocol == "reclaim"
    )));
}

#[test]
fn ordered_cmpxchg_carries_both_cas_and_ordering_barrier() {
    let c = Contracts::defaults();
    // A **release** CAS publishes: ABA (`cas`) plus a write barrier ordering prior stores
    // before it, so a lock-free publish/consume is seen as ordered (no false weak-memory bug).
    let rel = &c.lookup("cmpxchg_release").unwrap().effects;
    assert!(rel.contains(&Effect::Cas { arg: 0 }), "release CAS keeps ABA detection");
    assert!(rel.contains(&Effect::Barrier { kind: 1, access: None }), "release CAS orders prior stores (W→W)");
    // An **acquire** CAS consumes: `cas` plus a read barrier ordering later loads after it.
    let acq = &c.lookup("cmpxchg_acquire").unwrap().effects;
    assert!(acq.contains(&Effect::Cas { arg: 0 }));
    assert!(acq.contains(&Effect::Barrier { kind: 2, access: None }), "acquire CAS orders later loads (R→R)");
    // The relaxed / plain forms stay `cas`-only (no ordering claimed — the conservative
    // direction: at worst a false positive, never a hidden barrier bug).
    let relaxed = &c.lookup("cmpxchg_relaxed").unwrap().effects;
    assert_eq!(relaxed, &vec![Effect::Cas { arg: 0 }]);
    assert!(!c.lookup("cmpxchg").unwrap().effects.iter().any(|e| matches!(e, Effect::Barrier { .. })));
}
