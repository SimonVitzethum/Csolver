use super::*;
use super::tests::*;
use csolver_ir::{merge_modules, RValue};

/// Streaming member-provenance: `FieldFacts` (push each module, then `finalize`
/// with the pointer contracts) must equal `synthesize_fields_program` (and hence
/// `synthesize_fields∘merge`) over random field-building programs — the per-block
/// analysis replayed from body-free facts.
#[test]
fn field_facts_match_synthesize_fields_program_on_random() {
    let mut state: u64 = 0x0FAC_E0FF_1234_5678;
    let mut rng = || {
        state ^= state << 13;
        state ^= state >> 7;
        state ^= state << 17;
        state
    };
    let mut total_with_fields = 0;
    for _ in 0..300 {
        let n_mods = 2 + (rng() % 2) as usize;
        let per = 2 + (rng() % 3) as usize;
        let total = n_mods * per;
        let name = |gi: usize| format!("d{gi}");
        let mut modules = Vec::new();
        let mut gi = 0usize;
        for _ in 0..n_mods {
            let mut m = Module::new("m");
            for local in 0..per {
                let mut insts = vec![
                    Inst::Alloc {
                        dst: RegId(1),
                        region: csolver_core::RegionKind::Stack,
                        elem: Type::int(64),
                        count: Operand::int(64, 2),
                        align: 8,
                    },
                    Inst::Alloc {
                        dst: RegId(2),
                        region: csolver_core::RegionKind::Stack,
                        elem: Type::int(64),
                        count: Operand::int(64, 1),
                        align: 8,
                    },
                ];
                if rng() % 2 == 0 {
                    insts.push(Inst::PtrOffset {
                        dst: RegId(3),
                        base: Operand::Reg(RegId(1)),
                        index: Operand::int(64, (rng() % 2) as u128),
                        elem: Type::int(64),
                    });
                }
                if rng() % 3 != 0 {
                    let target = if rng() % 2 == 0 { RegId(1) } else { RegId(3) };
                    let value = if rng() % 3 == 0 { Operand::int(64, 0) } else { Operand::Reg(RegId(2)) };
                    insts.push(Inst::Store {
                        ty: Type::ptr(Type::int(64)),
                        ptr: Operand::Reg(target),
                        value,
                        align: 8, volatile: false
                    });
                }
                for _ in 0..(1 + rng() % 2) {
                    let tgt = (rng() as usize) % total;
                    insts.push(Inst::Call {
                        dst: None,
                        callee: Callee::Symbol(name(tgt)),
                        args: vec![Operand::Reg(RegId(1))],
                        ret_ty: Type::Unit,
                        ret_ref: None,
                    });
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
                    vec![(RegId(0), Type::ptr(Type::int(64)))],
                    insts,
                ));
                gi += 1;
            }
            modules.push(m);
        }
        let cw = rng() & 1 == 0;
        let refs: Vec<&Module> = modules.iter().collect();
        let params = synthesize_program(&refs, cw);
        let want = synthesize_fields_program(&refs, &params, cw);
        let mut facts = FieldFacts::default();
        for m in &refs {
            facts.push_module(m);
        }
        let got = facts.finalize(&params, cw);
        assert_eq!(got, want, "streamed field contracts != synthesize_fields_program (cw={cw})");
        total_with_fields += usize::from(!got.is_empty());
    }
    assert!(total_with_fields > 0, "no program produced a field contract — test is vacuous");
}

/// Streaming property for member-provenance: push each module then **drop it**,
/// then `finalize`, equals the linked field contracts.
#[test]
fn field_facts_stream_and_drop_equals_linked() {
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
                    elem: Type::int(64),
                    count: Operand::int(64, 2),
                    align: 8,
                },
                Inst::Alloc {
                    dst: RegId(2),
                    region: csolver_core::RegionKind::Stack,
                    elem: Type::int(64),
                    count: Operand::int(64, 1),
                    align: 8,
                },
                Inst::Store {
                    ty: Type::ptr(Type::int(64)),
                    ptr: Operand::Reg(RegId(1)),
                    value: Operand::Reg(RegId(2)),
                    align: 8, volatile: false
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
        m.functions.push(func(0, "sink", vec![(RegId(0), Type::ptr(Type::int(64)))], vec![]));
        m
    };
    let merged = merge_modules(vec![caller.clone(), callee.clone()], "l");
    let params = synthesize(&merged, true);
    let want = synthesize_fields(&merged, &params, true);
    let mut facts = FieldFacts::default();
    {
        let m0 = caller;
        facts.push_module(&m0);
    }
    {
        let m1 = callee;
        facts.push_module(&m1);
    }
    assert_eq!(facts.finalize(&params, true), want, "streamed+dropped == linked field contracts");
}

/// The streaming property: pushing modules one at a time and **dropping each**
/// right after `push_module` yields the same scalar preconditions as the linked
/// module — the caller is pushed and dropped before its callee's module is even
/// seen, so a whole-program pass needs no IR resident.
#[test]
fn scalar_facts_stream_and_drop_equals_linked() {
    let ip = |r: u32| vec![(RegId(r), Type::int(32))];
    let caller = {
        let mut m = Module::new("a");
        m.functions.push(func(0, "caller", vec![], vec![call(Callee::Symbol("t".into()), 9)]));
        m
    };
    let callee = {
        let mut m = Module::new("b");
        m.functions.push(func(0, "t", ip(0), vec![]));
        m
    };
    let want = synthesize_scalars(&merge_modules(vec![caller.clone(), callee.clone()], "l"), true);
    let mut facts = ScalarFacts::default();
    {
        let m0 = caller;
        facts.push_module(&m0);
    }
    {
        let m1 = callee;
        facts.push_module(&m1);
    }
    assert_eq!(facts.finalize(true), want, "streamed+dropped == linked");
}

/// Randomised guard: over many random multi-module programs (cross-module and
/// in-module constant-argument calls, random address-taking, random closed-world
/// flag), the link-free scalar preconditions must always equal the linked ones.
#[test]
fn scalar_preconditions_match_linked_on_random_programs() {
    let mut state: u64 = 0x0BEE_F123_4567_89AB;
    let mut rng = || {
        state ^= state << 13;
        state ^= state >> 7;
        state ^= state << 17;
        state
    };
    for _ in 0..300 {
        let n_mods = 2 + (rng() % 2) as usize; // 2..=3
        let per = 2 + (rng() % 3) as usize; // 2..=4
        let total = n_mods * per;
        let name = |gi: usize| format!("g{gi}");
        let mut modules = Vec::new();
        let mut gi = 0usize;
        for _ in 0..n_mods {
            let mut m = Module::new("m");
            for local in 0..per {
                let mut insts = Vec::new();
                for _ in 0..(rng() % 3) {
                    let tgt = (rng() as usize) % total;
                    let v = (rng() % 20) as i128;
                    insts.push(call(Callee::Symbol(name(tgt)), v));
                }
                if rng() % 4 == 0 {
                    let e = (rng() as usize) % total;
                    insts.push(Inst::Assign {
                        dst: RegId(50),
                        ty: Type::ptr(Type::int(32)),
                        value: RValue::Use(Operand::Const(Const::Symbol(name(e)))),
                    });
                }
                m.functions.push(func(
                    local as u32,
                    &name(gi),
                    vec![(RegId(0), Type::int(32))],
                    insts,
                ));
                gi += 1;
            }
            modules.push(m);
        }
        let cw = rng() & 1 == 0;
        let refs: Vec<&Module> = modules.iter().collect();
        let got = synthesize_scalars_program(&refs, cw);
        let want = synthesize_scalars(&merge_modules(modules.clone(), "linked"), cw);
        assert_eq!(got, want, "link-free != linked scalar preconditions (cw={cw})");
    }
}
