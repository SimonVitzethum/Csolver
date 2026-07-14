use super::*;

/// Summarize every function in a module (with the call-graph effect fixpoint).
pub fn summarize_module(module: &Module) -> HashMap<FuncId, Summary> {
    let mut map: HashMap<FuncId, Summary> = HashMap::new();
    for f in &module.functions {
        map.insert(f.id, summarize_fn(f));
    }

    // A call in a block that ends `Unreachable` is *diverging* (rustc's panic
    // shape: `call @panic…; unreachable`): control never returns past it, so no
    // caller-side code can observe its effects — the block's own path dies at
    // the terminator, and an unwinding path re-enters only through an `invoke`
    // cleanup edge, whose block does *not* end `Unreachable` and therefore still
    // contaminates. Exempting these calls keeps one panic check from poisoning
    // the effect summary of everything above it.
    let observable = |b: &csolver_ir::BasicBlock| {
        !matches!(b.term, csolver_ir::Terminator::Unreachable)
    };

    // Any non-direct call (external symbol / indirect) may do anything — EXCEPT
    // register-only inline asm (`<inline asm nomem>`), which writes/frees no tracked
    // memory (decided from its constraint string), so it must not poison the summary.
    let opaque = |callee: &Callee| {
        !matches!(callee, Callee::Direct(_))
            && !matches!(callee, Callee::Symbol(n) if n == "<inline asm nomem>")
    };
    for f in &module.functions {
        let opaque_call = f.blocks.iter().filter(|b| observable(b)).flat_map(|b| &b.insts).any(
            |i| matches!(i, Inst::Call { callee, .. } if opaque(callee)),
        );
        if opaque_call {
            if let Some(s) = map.get_mut(&f.id) {
                s.writes = true;
                s.frees = true;
            }
        }
    }

    // Propagate effects through direct calls to a fixpoint.
    loop {
        let mut changed = false;
        for f in &module.functions {
            let mut writes = map.get(&f.id).is_some_and(|s| s.writes);
            let mut frees = map.get(&f.id).is_some_and(|s| s.frees);
            for inst in f.blocks.iter().filter(|b| observable(b)).flat_map(|b| &b.insts) {
                if let Inst::Call { callee: Callee::Direct(g), .. } = inst {
                    if let Some(sg) = map.get(g) {
                        writes |= sg.writes;
                        frees |= sg.frees;
                    }
                }
            }
            if let Some(s) = map.get_mut(&f.id) {
                if writes != s.writes || frees != s.frees {
                    s.writes = writes;
                    s.frees = frees;
                    changed = true;
                }
            }
        }
        if !changed {
            break;
        }
    }

    // Propagate provenance transfers through direct calls to a fixpoint: if `f` calls `g`
    // and `g` transfers/labels one of its parameters, `f` does so on whichever of *its*
    // parameters the corresponding argument aliases. Only definite parameter aliasing
    // (`ptr_param_of`) is used, so a composed transfer is never spurious.
    let param_of: HashMap<FuncId, HashMap<RegId, usize>> =
        module.functions.iter().map(|f| (f.id, ptr_param_of(f))).collect();
    loop {
        let mut changed = false;
        for f in &module.functions {
            let pof = &param_of[&f.id];
            let arg = |op: &Operand| match op {
                Operand::Reg(r) => pof.get(r).copied(),
                _ => None,
            };
            let mut add: ProvTransfer = ProvTransfer::default();
            for inst in f.blocks.iter().filter(|b| observable(b)).flat_map(|b| &b.insts) {
                let Inst::Call { callee: Callee::Direct(g), args, .. } = inst else { continue };
                let Some(sg) = map.get(g) else { continue };
                for &(d, s) in &sg.prov.transfers {
                    if let (Some(pd), Some(ps)) = (args.get(d).and_then(&arg), args.get(s).and_then(&arg)) {
                        add.transfers.push((pd, ps));
                    }
                }
                for &(a, label) in &sg.prov.labels {
                    if let Some(pa) = args.get(a).and_then(&arg) {
                        add.labels.push((pa, label));
                    }
                }
            }
            if let Some(s) = map.get_mut(&f.id) {
                let before = (s.prov.transfers.len(), s.prov.labels.len());
                s.prov.transfers.extend(add.transfers);
                s.prov.labels.extend(add.labels);
                dedup(&mut s.prov);
                if (s.prov.transfers.len(), s.prov.labels.len()) != before {
                    changed = true;
                }
            }
        }
        if !changed {
            break;
        }
    }

    // Propagate the reference-count effect through direct calls: `f`'s total effect is its own
    // (base) plus, for each call `g(args)`, `g`'s effect mapped from `g`'s parameters onto `f`'s
    // (via argument aliasing). Recomputed from the base each round (the effect is additive, so it
    // must not accumulate across iterations) and capped, so a recursive refcount terminates.
    let base: HashMap<FuncId, Vec<(usize, u32, i64)>> =
        module.functions.iter().map(|f| (f.id, refcount_effect_of_fn(f))).collect();
    for _ in 0..8 {
        let mut changed = false;
        let snapshot: HashMap<FuncId, Vec<(usize, u32, i64)>> =
            map.iter().map(|(k, s)| (*k, s.refcount_effect.clone())).collect();
        for f in &module.functions {
            let pof = &param_of[&f.id];
            let arg = |op: &Operand| match op {
                Operand::Reg(r) => pof.get(r).copied(),
                _ => None,
            };
            let mut acc: std::collections::BTreeMap<(usize, u32), i64> =
                base[&f.id].iter().map(|&(p, pr, d)| ((p, pr), d)).collect();
            for inst in f.blocks.iter().filter(|b| observable(b)).flat_map(|b| &b.insts) {
                let Inst::Call { callee: Callee::Direct(g), args, .. } = inst else { continue };
                let Some(eff) = snapshot.get(g) else { continue };
                for &(k, proto, d) in eff {
                    if let Some(pj) = args.get(k).and_then(&arg) {
                        *acc.entry((pj, proto)).or_insert(0) += d;
                    }
                }
            }
            let new_eff: Vec<(usize, u32, i64)> =
                acc.into_iter().filter(|(_, d)| *d != 0).map(|((p, pr), d)| (p, pr, d)).collect();
            if let Some(s) = map.get_mut(&f.id) {
                if s.refcount_effect != new_eff {
                    s.refcount_effect = new_eff;
                    changed = true;
                }
            }
        }
        if !changed {
            break;
        }
    }

    // Propagate a dangling-stack return through wrappers (mirrors `SummaryFacts::finalize`
    // step 4, so the link-free and linked summaries stay equal): a function that returns a
    // Direct callee's result inherits `DanglingStack` when that callee does. Only the dangling
    // case composes without argument remapping; `PtrFromArg` stays Unknown (sound).
    let ret_callee: HashMap<FuncId, Option<FuncId>> = module
        .functions
        .iter()
        .map(|f| {
            let g = returned_call_index(f).and_then(|ci| {
                f.blocks
                    .iter()
                    .filter(|b| observable(b))
                    .flat_map(|b| &b.insts)
                    .filter_map(|i| match i {
                        Inst::Call { callee, .. } => Some(callee),
                        _ => None,
                    })
                    .nth(ci)
                    .and_then(|c| match c {
                        Callee::Direct(g) => Some(*g),
                        _ => None,
                    })
            });
            (f.id, g)
        })
        .collect();
    loop {
        let mut changed = false;
        for f in &module.functions {
            let inherits = map.get(&f.id).is_some_and(|s| s.ret == RetSummary::Unknown)
                && ret_callee[&f.id]
                    .is_some_and(|g| map.get(&g).is_some_and(|s| s.ret == RetSummary::DanglingStack));
            if inherits {
                if let Some(s) = map.get_mut(&f.id) {
                    s.ret = RetSummary::DanglingStack;
                    changed = true;
                }
            }
        }
        if !changed {
            break;
        }
    }

    map
}
