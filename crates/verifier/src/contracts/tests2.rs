use super::*;
use super::tests::*;
use csolver_ir::{merge_modules, RValue};

/// `synthesize_fields_program` (member-provenance, link-free) must equal
/// `synthesize_fields(&merge(...), params, …)`: a valid pointer stored into a
/// field of a region that is then passed cross-module to a contracted-parameter
/// callee gives that parameter's field the same contract as when linked.
#[test]
fn field_contracts_match_the_linked_module() {
    // caller: R = alloc 16B; B = alloc 8B; store B into R@0; sink(R).
    let mut a = Module::new("a");
    a.functions.push(func(
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
    let mut b = Module::new("b");
    b.functions.push(func(0, "sink", vec![(RegId(0), Type::ptr(Type::int(64)))], vec![]));

    for cw in [true, false] {
        let merged = merge_modules(vec![a.clone(), b.clone()], "l");
        let params = synthesize(&merged, cw);
        let want = synthesize_fields(&merged, &params, cw);
        let got = synthesize_fields_program(&[&a, &b], &params, cw);
        assert_eq!(got, want, "link-free field contracts must equal linked (cw={cw})");
    }
    // Under closed-world, sink (FuncId 1) gets a field at offset 0.
    let merged = merge_modules(vec![a.clone(), b.clone()], "l");
    let params = synthesize(&merged, true);
    let got = synthesize_fields_program(&[&a, &b], &params, true);
    assert_eq!(got.get(&(FuncId(1), 0)).map(|v| v.len()), Some(1), "sink gets one field");
}

/// Randomised guard for member-provenance over random multi-module programs
/// that build regions, store valid pointers into fields (at offset 0 and via a
/// constant `PtrOffset`), pass the region cross-module and in-module, and clobber
/// via extra calls / stores — with `params` taken from `synthesize` so callees
/// carry the contracts fields attach to.
#[test]
fn field_contracts_match_linked_on_random_programs() {
    let mut state: u64 = 0x0F1E_2D3C_4B5A_6978;
    let mut rng = || {
        state ^= state << 13;
        state ^= state >> 7;
        state ^= state << 17;
        state
    };
    for _ in 0..300 {
        let n_mods = 2 + (rng() % 2) as usize;
        let per = 2 + (rng() % 3) as usize;
        let total = n_mods * per;
        let name = |gi: usize| format!("k{gi}");
        let mut modules = Vec::new();
        let mut gi = 0usize;
        for _ in 0..n_mods {
            let mut m = Module::new("m");
            for local in 0..per {
                let mut insts = vec![
                    // R = region (16B, holds two 8B slots), B = a valid 8B buffer.
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
                // Maybe a field pointer R + k*8.
                if rng() % 2 == 0 {
                    insts.push(Inst::PtrOffset {
                        dst: RegId(3),
                        base: Operand::Reg(RegId(1)),
                        index: Operand::int(64, (rng() % 2) as u128),
                        elem: Type::int(64),
                    });
                }
                // Maybe store B (a valid ptr) or an unknown value into R@0 or the field.
                if rng() % 3 != 0 {
                    let target = if rng() % 2 == 0 { RegId(1) } else { RegId(3) };
                    let value = if rng() % 3 == 0 {
                        Operand::int(64, 0) // unknown value clears the slot
                    } else {
                        Operand::Reg(RegId(2))
                    };
                    insts.push(Inst::Store {
                        ty: Type::ptr(Type::int(64)),
                        ptr: Operand::Reg(target),
                        value,
                        align: 8, volatile: false
                    });
                }
                // Pass R to some targets (and maybe escape it via an extra call).
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
        let merged = merge_modules(modules.clone(), "linked");
        let params = synthesize(&merged, cw);
        let want = synthesize_fields(&merged, &params, cw);
        let got = synthesize_fields_program(&refs, &params, cw);
        assert_eq!(got, want, "link-free != linked field contracts (cw={cw})");
    }
}

/// The parallel-merge property: building the whole-program facts in two shards
/// and merging them in order must give the same four result maps as pushing all
/// modules sequentially — so shards can be extracted in parallel. Covers all
/// four builders' `merge` at once via `WholeProgramFacts`.
#[test]
fn wholeprog_facts_shard_and_merge_equals_sequential() {
    let mut state: u64 = 0x00DE_AD57_A11E_D000;
    let mut rng = || {
        state ^= state << 13;
        state ^= state >> 7;
        state ^= state << 17;
        state
    };
    for _ in 0..200 {
        let n_mods = 3 + (rng() % 3) as usize; // 3..=5 modules (so a split is meaningful)
        let per = 2 + (rng() % 3) as usize;
        let total = n_mods * per;
        let name = |gi: usize| format!("w{gi}");
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
                    insts.push(Inst::Store {
                        ty: Type::ptr(Type::int(64)),
                        ptr: Operand::Reg(RegId(1)),
                        value: Operand::Reg(RegId(2)),
                        align: 8, volatile: false
                    });
                }
                for _ in 0..(1 + rng() % 2) {
                    let tgt = (rng() as usize) % total;
                    let arg = if rng() % 2 == 0 { Operand::Reg(RegId(1)) } else { Operand::Reg(RegId(0)) };
                    insts.push(Inst::Call {
                        dst: None,
                        callee: Callee::Symbol(name(tgt)),
                        args: vec![arg],
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

        let seq = {
            let mut w = crate::WholeProgramFacts::new();
            for m in &modules {
                w.push_module(m);
            }
            w.finalize(cw)
        };
        let k = 1 + (rng() as usize % (n_mods - 1)); // split point in 1..n_mods
        let sharded = {
            let mut w1 = crate::WholeProgramFacts::new();
            for m in &modules[..k] {
                w1.push_module(m);
            }
            let mut w2 = crate::WholeProgramFacts::new();
            for m in &modules[k..] {
                w2.push_module(m);
            }
            w1.merge(w2);
            w1.finalize(cw)
        };
        assert_eq!(seq.summaries, sharded.summaries, "summaries differ");
        assert_eq!(seq.scalars, sharded.scalars, "scalars differ");
        assert_eq!(seq.ptr_contracts, sharded.ptr_contracts, "pointer contracts differ");
        assert_eq!(seq.field_contracts, sharded.field_contracts, "field contracts differ");
    }
}
