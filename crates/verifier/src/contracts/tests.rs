use super::*;
use csolver_ir::{merge_modules, BasicBlock, Function, RValue};

pub(crate) fn func(id: u32, name: &str, params: Vec<(RegId, Type)>, insts: Vec<Inst>) -> Function {
    let mut bb = BasicBlock::new(BlockId(0), Terminator::Return(None));
    bb.insts = insts;
    Function {
        id: FuncId(id),
        name: name.into(),
        params,
        ret_ty: Type::Unit,
        blocks: vec![bb],
        entry: BlockId(0),
    }
}
pub(crate) fn call(callee: Callee, arg: i128) -> Inst {
    Inst::Call {
        dst: None,
        callee,
        args: vec![Operand::int(32, arg as u128)],
        ret_ty: Type::Unit,
        ret_ref: None,
    }
}

/// End-to-end 2b whole-program equivalence: verifying a callee's file **alone**
/// with the streaming-facts overlay (name-keyed preconditions from the whole tree)
/// reaches the same verdict as verifying the fully-**linked** closed-world module —
/// and strictly more than verifying the file open-world with no overlay. This is the
/// proof that the on-demand path (2b) replaces `--cross-file` linking soundly.
#[test]
fn whole_program_overlay_matches_linked_closed_world() {
    use csolver_core::SafetyProperty;
    use csolver_ir::{Condition, CmpOp};
    let verdict_of = |r: &crate::ModuleReport, name: &str| {
        r.functions.iter().find(|f| f.function == name).map(|f| f.verdict)
    };
    // Module A: a caller passing the constant 2 across a file boundary to `target`.
    let mut a = Module::new("a");
    a.functions.push(func(0, "caller_a", vec![], vec![call(Callee::Symbol("target".into()), 2)]));
    // Module B: `target(i)` does a bounds check `i < 4`. Provable only if the caller's
    // argument range (i = 2) flows in as a precondition; unconstrained, i could be >= 4.
    let mut b = Module::new("b");
    b.functions.push(func(
        0,
        "target",
        vec![(RegId(0), Type::int(32))],
        vec![Inst::SafetyCheck {
            property: SafetyProperty::InBounds,
            condition: Condition::Cmp {
                op: CmpOp::Ult,
                lhs: Operand::Reg(RegId(0)),
                rhs: Operand::int(32, 4),
            },
            note: "i < 4".into(),
        }],
    ));

    // An empty entry policy: nothing is an attacker entry, so every function's
    // parameters are taken as caller-validated (the sound kernel model — external
    // linkage is not userspace-reachability). This is the regime in which a
    // caller-derived precondition applies to an external, non-entry callee.
    let cfg = crate::Config {
        closed_world: true,
        entry_patterns: Some(vec![]),
        ..crate::Config::default()
    };

    // (1) Linked closed-world: the reference verdict for `target`.
    let linked = merge_modules(vec![a.clone(), b.clone()], "linked");
    let linked_report = crate::verify_module(&linked, &cfg);

    // (2) 2b: stream the whole-program facts closed-world, then verify B's file ALONE
    //     with the name-keyed overlay.
    let mut wpf = crate::WholeProgramFacts::new();
    wpf.push_module(&a);
    wpf.push_module(&b);
    let facts = wpf.finalize(true, false);
    let wp_report = crate::verify_module_whole_program(&b, &cfg, 1, facts.context());

    // (3) Control: B's file alone, same entry policy but open-world and no overlay —
    //     the precondition is absent, so the only difference from (2) is the overlay.
    let open_cfg = crate::Config { entry_patterns: Some(vec![]), ..crate::Config::default() };
    let open_report = crate::verify_module(&b, &open_cfg);

    assert_eq!(
        verdict_of(&wp_report, "target"),
        verdict_of(&linked_report, "target"),
        "2b overlay must reach the linked closed-world verdict"
    );
    assert_eq!(
        verdict_of(&wp_report, "target"),
        Some(csolver_core::Verdict::Pass),
        "the overlaid precondition (i=2) must prove i<4"
    );
    assert_ne!(
        verdict_of(&open_report, "target"),
        Some(csolver_core::Verdict::Pass),
        "without the overlay, i is unconstrained and the check is not proven"
    );
}

/// `synthesize_scalars_program` must equal `synthesize_scalars(&merge(...))`
/// key-for-key: cross-module `Symbol` folds into the callee's precondition like
/// the linked `Direct` call, an in-module `Direct` folds too, and an
/// address-taken (escaped) callee is excluded everywhere.
#[test]
fn scalar_preconditions_match_the_linked_module() {
    let ip = |r: u32| vec![(RegId(r), Type::int(32))];
    // Module A: a caller that calls the cross-module `target` (5 and 10), an
    // in-module `atgt` (7), and an escaped `esc` (3) whose address it also takes.
    let mut a = Module::new("a");
    a.functions.push(func(
        0,
        "caller_a",
        vec![],
        vec![
            call(Callee::Symbol("target".into()), 5),
            call(Callee::Symbol("target".into()), 10),
            call(Callee::Direct(FuncId(1)), 7),
            Inst::Assign {
                dst: RegId(9),
                ty: Type::ptr(Type::int(32)),
                value: RValue::Use(Operand::Const(Const::Symbol("esc".into()))),
            },
            call(Callee::Direct(FuncId(2)), 3),
        ],
    ));
    a.functions.push(func(1, "atgt", ip(0), vec![]));
    a.functions.push(func(2, "esc", ip(0), vec![]));
    // Module B: the cross-module target.
    let mut b = Module::new("b");
    b.functions.push(func(0, "target", ip(0), vec![]));

    for cw in [true, false] {
        let linked = merge_modules(vec![a.clone(), b.clone()], "linked");
        let want = synthesize_scalars(&linked, cw);
        let got = synthesize_scalars_program(&[&a, &b], cw);
        assert_eq!(got, want, "link-free scalar preconditions must equal linked (cw={cw})");
    }

    // Spot-check the intent under closed-world: target=[5,10], atgt=[7,7], esc absent.
    let got = synthesize_scalars_program(&[&a, &b], true);
    assert_eq!(got.get(&(FuncId(3), 0)), Some(&(5, 10)), "target folds 5∪10");
    assert_eq!(got.get(&(FuncId(1), 0)), Some(&(7, 7)), "atgt folds 7");
    assert!(!got.contains_key(&(FuncId(2), 0)), "escaped esc is excluded");
}

/// `synthesize_program` (pointer contracts, link-free) must equal
/// `synthesize(&merge(...))` key-for-key: a cross-module `Symbol` call passing a
/// const-sized alloca gives the callee's parameter the same contract the linked
/// `Direct` call would, and an address-taken callee is excluded.
#[test]
fn pointer_contracts_match_the_linked_module() {
    let pp = || vec![(RegId(0), Type::ptr(Type::int(32)))];
    let alloc16 = Inst::Alloc {
        dst: RegId(1),
        region: csolver_core::RegionKind::Stack,
        elem: Type::int(32),
        count: Operand::int(64, 4), // 4 × i32 = 16 bytes
        align: 4,
    };
    let pcall = |callee: Callee, arg: Operand| Inst::Call {
        dst: None,
        callee,
        args: vec![arg],
        ret_ty: Type::Unit,
        ret_ref: None,
    };
    // A: caller allocs 16 bytes and passes it cross-module to `sink`.
    let mut a = Module::new("a");
    a.functions.push(func(
        0,
        "caller",
        vec![],
        vec![alloc16, pcall(Callee::Symbol("sink".into()), Operand::Reg(RegId(1)))],
    ));
    // B: the sink (uncontracted ptr param) and an escaped ptr-param function.
    let mut b = Module::new("b");
    b.functions.push(func(0, "sink", pp(), vec![]));

    for cw in [true, false] {
        let want = synthesize(&merge_modules(vec![a.clone(), b.clone()], "l"), cw, false);
        let got = synthesize_program(&[&a, &b], cw, false);
        assert_eq!(got, want, "link-free pointer contracts must equal linked (cw={cw})");
    }
    // Under closed-world, sink (FuncId 1 after merge) gets a 16-byte contract.
    let got = synthesize_program(&[&a, &b], true, false);
    assert_eq!(got.get(&(FuncId(1), 0)).map(|c| c.size), Some(SizeSpec::Bytes(16)));
}

/// Randomised guard for pointer contracts over random multi-module programs:
/// const-sized allocas, cross-module and in-module calls that pass an alloca, a
/// forwarded parameter (exercising the synthesis fixpoint), or a constant, plus
/// random address-taking and closed-world flag.
#[test]
fn pointer_contracts_match_linked_on_random_programs() {
    let mut state: u64 = 0x00A5_5A5A_1357_9BDF;
    let mut rng = || {
        state ^= state << 13;
        state ^= state >> 7;
        state ^= state << 17;
        state
    };
    let pcall = |callee: Callee, arg: Operand| Inst::Call {
        dst: None,
        callee,
        args: vec![arg],
        ret_ty: Type::Unit,
        ret_ref: None,
    };
    for _ in 0..300 {
        let n_mods = 2 + (rng() % 2) as usize;
        let per = 2 + (rng() % 3) as usize;
        let total = n_mods * per;
        let name = |gi: usize| format!("h{gi}");
        let mut modules = Vec::new();
        let mut gi = 0usize;
        for _ in 0..n_mods {
            let mut m = Module::new("m");
            for local in 0..per {
                let mut insts = Vec::new();
                let has_alloc = rng() % 2 == 0;
                if has_alloc {
                    insts.push(Inst::Alloc {
                        dst: RegId(1),
                        region: csolver_core::RegionKind::Stack,
                        elem: Type::int(32),
                        count: Operand::int(64, (1 + rng() % 4) as u128),
                        align: [1u32, 2, 4, 8][(rng() % 4) as usize],
                    });
                }
                for _ in 0..(rng() % 3) {
                    let tgt = (rng() as usize) % total;
                    let arg = match rng() % 3 {
                        0 => Operand::Reg(RegId(0)), // forward own param (fixpoint)
                        1 => Operand::Reg(RegId(1)), // the alloca (or an undefined reg)
                        _ => Operand::int(64, 0),    // a non-derivable constant
                    };
                    insts.push(pcall(Callee::Symbol(name(tgt)), arg));
                }
                if rng() % 4 == 0 {
                    let e = (rng() as usize) % total;
                    insts.push(Inst::Assign {
                        dst: RegId(9),
                        ty: Type::ptr(Type::int(32)),
                        value: RValue::Use(Operand::Const(Const::Symbol(name(e)))),
                    });
                }
                m.functions.push(func(
                    local as u32,
                    &name(gi),
                    vec![(RegId(0), Type::ptr(Type::int(32)))],
                    insts,
                ));
                gi += 1;
            }
            modules.push(m);
        }
        let cw = rng() & 1 == 0;
        let refs: Vec<&Module> = modules.iter().collect();
        let got = synthesize_program(&refs, cw, false);
        let want = synthesize(&merge_modules(modules.clone(), "linked"), cw, false);
        assert_eq!(got, want, "link-free != linked pointer contracts (cw={cw})");
    }
}

/// Streaming pointer contracts: `ContractFacts` (push each module, then
/// `finalize`) must equal `synthesize_program` (and hence `synthesize∘merge`)
/// over random multi-module programs — the fixpoint recomputed from body-free
/// facts, not the bodies.
#[test]
fn contract_facts_match_synthesize_program_on_random() {
    let mut state: u64 = 0x0C0F_FEE0_1234_ABCD;
    let mut rng = || {
        state ^= state << 13;
        state ^= state >> 7;
        state ^= state << 17;
        state
    };
    let pcall = |callee: Callee, arg: Operand| Inst::Call {
        dst: None,
        callee,
        args: vec![arg],
        ret_ty: Type::Unit,
        ret_ref: None,
    };
    let mut total_with_contracts = 0;
    for _ in 0..300 {
        let n_mods = 2 + (rng() % 2) as usize;
        let per = 2 + (rng() % 3) as usize;
        let total = n_mods * per;
        let name = |gi: usize| format!("c{gi}");
        let mut modules = Vec::new();
        let mut gi = 0usize;
        for _ in 0..n_mods {
            let mut m = Module::new("m");
            for local in 0..per {
                let mut insts = Vec::new();
                if rng() % 2 == 0 {
                    insts.push(Inst::Alloc {
                        dst: RegId(1),
                        region: csolver_core::RegionKind::Stack,
                        elem: Type::int(32),
                        count: Operand::int(64, (1 + rng() % 4) as u128),
                        align: [1u32, 2, 4, 8][(rng() % 4) as usize],
                    });
                }
                // A constant PtrOffset off the alloca (a field/subarray pointer).
                if rng() % 2 == 0 {
                    insts.push(Inst::PtrOffset {
                        dst: RegId(3),
                        base: Operand::Reg(RegId(1)),
                        index: Operand::int(64, (rng() % 3) as u128),
                        elem: Type::int(32),
                    });
                }
                for _ in 0..(rng() % 3) {
                    let tgt = (rng() as usize) % total;
                    let arg = match rng() % 4 {
                        0 => Operand::Reg(RegId(0)), // forwarded param (fixpoint)
                        1 => Operand::Reg(RegId(1)), // alloca
                        2 => Operand::Reg(RegId(3)), // offset pointer
                        _ => Operand::int(64, 0),
                    };
                    insts.push(pcall(Callee::Symbol(name(tgt)), arg));
                }
                if rng() % 5 == 0 {
                    let e = (rng() as usize) % total;
                    insts.push(Inst::Assign {
                        dst: RegId(9),
                        ty: Type::ptr(Type::int(32)),
                        value: RValue::Use(Operand::Const(Const::Symbol(name(e)))),
                    });
                }
                m.functions.push(func(
                    local as u32,
                    &name(gi),
                    vec![(RegId(0), Type::ptr(Type::int(32)))],
                    insts,
                ));
                gi += 1;
            }
            modules.push(m);
        }
        let cw = rng() & 1 == 0;
        let refs: Vec<&Module> = modules.iter().collect();
        let mut facts = ContractFacts::default();
        for m in &refs {
            facts.push_module(m);
        }
        let got = facts.finalize(cw, false);
        let want = synthesize_program(&refs, cw, false);
        assert_eq!(got, want, "streamed pointer contracts != synthesize_program (cw={cw})");
        total_with_contracts += usize::from(!got.is_empty());
    }
    assert!(total_with_contracts > 0, "no program produced a contract — test is vacuous");
}

/// Streaming property: push each module then **drop it**, then `finalize`, equals
/// the linked pointer contracts (caller pushed before its callee's module).
#[test]
fn contract_facts_stream_and_drop_equals_linked() {
    let caller = {
        let mut m = Module::new("a");
        m.functions.push(func(
            0,
            "caller",
            vec![],
            vec![
                Inst::Alloc {
                    dst: RegId(1),
                    region: csolver_core::RegionKind::Stack,
                    elem: Type::int(32),
                    count: Operand::int(64, 4),
                    align: 4,
                },
                Inst::Call {
                    dst: None,
                    callee: Callee::Symbol("sink".into()),
                    args: vec![Operand::Reg(RegId(1))],
                    ret_ty: Type::Unit,
                    ret_ref: None,
                },
            ],
        ));
        m
    };
    let callee = {
        let mut m = Module::new("b");
        m.functions.push(func(0, "sink", vec![(RegId(0), Type::ptr(Type::int(32)))], vec![]));
        m
    };
    let want = synthesize(&merge_modules(vec![caller.clone(), callee.clone()], "l"), true, false);
    let mut facts = ContractFacts::default();
    {
        let m0 = caller;
        facts.push_module(&m0);
    }
    {
        let m1 = callee;
        facts.push_module(&m1);
    }
    assert_eq!(facts.finalize(true, false), want, "streamed+dropped == linked pointer contracts");
}
