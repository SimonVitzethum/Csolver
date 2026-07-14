use super::*;
use csolver_ir::{BasicBlock, BlockId, Terminator, Type};

/// A callee that memcpys into a *parameter* writes caller-visible memory —
/// before, only `Inst::Store` counted and such a callee looked pure, letting
/// the caller keep stale heap knowledge across the call (false-PASS
/// material). A callee that only writes its *own* alloca stays pure: rustc's
/// debug IR round-trips every local through one, and treating that as a
/// visible write would havoc the caller on every helper call.
#[test]
fn memcpy_to_a_parameter_is_a_visible_write_but_own_allocas_are_not() {
    let p = RegId(0);
    let buf = RegId(1);
    let make = |dst_reg: RegId| {
        let mut bb0 = BasicBlock::new(BlockId(0), Terminator::Return(None));
        bb0.insts.push(Inst::Alloc {
            dst: buf,
            region: csolver_core::RegionKind::Stack,
            elem: Type::int(32),
            count: Operand::int(64, 1),
            align: 4,
        });
        bb0.insts.push(Inst::MemIntrinsic {
            kind: csolver_ir::MemKind::Set,
            dst: Operand::Reg(dst_reg),
            src: None,
            len: Operand::int(64, 4),
        });
        Function {
            id: FuncId(0),
            name: "m".into(),
            params: vec![(p, Type::ptr(Type::int(32)))],
            ret_ty: Type::Unit,
            blocks: vec![bb0],
            entry: BlockId(0),
        }
    };
    assert!(summarize_fn(&make(p)).writes, "memset to a parameter is a visible write");
    assert!(!summarize_fn(&make(buf)).writes, "memset to an own alloca is not");
}

/// The load-bearing losslessness oracle for whole-program-without-linking:
/// `summarize_program(&[&a, &b])` must equal `summarize_module(&merge(a, b))`
/// key-for-key — proving that resolving call edges by name across separate
/// modules and running the fixpoints on facts reproduces the linked result
/// exactly (cross-module `Symbol` resolve, in-module `Direct` remap, and an
/// unresolved external staying opaque).
#[test]
fn summarize_program_equals_summarize_of_the_linked_module() {
    use csolver_ir::merge_modules;
    let p = RegId(0);
    let one_block = |insts: Vec<Inst>| {
        let mut bb = BasicBlock::new(BlockId(0), Terminator::Return(None));
        bb.insts = insts;
        vec![bb]
    };
    let func = |id: u32, name: &str, params: Vec<(RegId, Type)>, insts: Vec<Inst>| Function {
        id: FuncId(id),
        name: name.into(),
        params,
        ret_ty: Type::Unit,
        blocks: one_block(insts),
        entry: BlockId(0),
    };
    let store_p = || Inst::Store {
        ty: Type::int(32),
        ptr: Operand::Reg(p),
        value: Operand::int(32, 0),
        align: 4, volatile: false
    };
    let call = |callee: Callee, args: Vec<Operand>| Inst::Call {
        dst: None,
        callee,
        args,
        ret_ty: Type::Unit,
        ret_ref: None,
    };
    let pp = || vec![(p, Type::ptr(Type::int(32)))];

    // Module B: a real writer, and an in-module Direct wrapper around it.
    let mut b = Module::new("b");
    b.functions.push(func(0, "writer", pp(), vec![store_p()]));
    b.functions.push(func(
        1,
        "b_wrapper",
        pp(),
        vec![call(Callee::Direct(FuncId(0)), vec![Operand::Reg(p)])],
    ));
    // Module A: a cross-module Symbol wrapper (resolves to B::writer → writes),
    // and a call to an unresolved external (stays opaque → writes+frees).
    let mut a = Module::new("a");
    a.functions.push(func(
        0,
        "a_wrapper",
        pp(),
        vec![call(Callee::Symbol("writer".into()), vec![Operand::Reg(p)])],
    ));
    a.functions.push(func(
        1,
        "a_opaque",
        vec![],
        vec![call(Callee::Symbol("some_undefined_ext".into()), vec![])],
    ));

    let linked = merge_modules(vec![a.clone(), b.clone()], "linked");
    let want = summarize_module(&linked);
    let got = summarize_program(&[&a, &b]);
    assert_eq!(got, want, "link-free summaries must equal the linked summaries");

    // Spot-check the intended effects survived (guards against both being wrong).
    assert!(want[&FuncId(0)].writes, "a_wrapper inherits B::writer's write");
    assert!(want[&FuncId(1)].writes && want[&FuncId(1)].frees, "a_opaque is fully havoc'd");
    assert!(want[&FuncId(2)].writes, "writer writes");
    assert!(want[&FuncId(3)].writes, "b_wrapper inherits via Direct");
}

/// The out-parameter stack-escape detector records a parameter through which the entry block
/// **unconditionally** stores the address of a local (`*out = &x`), but NOT a store of a
/// parameter pointer (the caller owns it), so the caller-side dangling mark is never a false FAIL.
#[test]
fn out_param_stack_escape_detection() {
    let out = RegId(0);
    let x = RegId(1);
    // fn bad(out) { let x; *out = &x }
    let mut bb = BasicBlock::new(BlockId(0), Terminator::Return(None));
    bb.insts.push(Inst::Alloc {
        dst: x,
        region: csolver_core::RegionKind::Stack,
        elem: Type::int(32),
        count: Operand::int(64, 1),
        align: 4,
    });
    bb.insts.push(Inst::Store {
        ty: Type::ptr(Type::int(32)),
        ptr: Operand::Reg(out),
        value: Operand::Reg(x),
        align: 8,
        volatile: false,
    });
    let bad = Function {
        id: FuncId(0),
        name: "bad".into(),
        params: vec![(out, Type::ptr(Type::ptr(Type::int(32))))],
        ret_ty: Type::Unit,
        blocks: vec![bb],
        entry: BlockId(0),
    };
    assert_eq!(summarize_fn(&bad).escapes_stack, vec![0]);

    // fn passthrough(out, p) { *out = p } — stores a *parameter* pointer, not a local → no escape.
    let p = RegId(2);
    let mut bb = BasicBlock::new(BlockId(0), Terminator::Return(None));
    bb.insts.push(Inst::Store {
        ty: Type::ptr(Type::int(32)),
        ptr: Operand::Reg(out),
        value: Operand::Reg(p),
        align: 8,
        volatile: false,
    });
    let passthrough = Function {
        id: FuncId(0),
        name: "passthrough".into(),
        params: vec![
            (out, Type::ptr(Type::ptr(Type::int(32)))),
            (p, Type::ptr(Type::int(32))),
        ],
        ret_ty: Type::Unit,
        blocks: vec![bb],
        entry: BlockId(0),
    };
    assert!(summarize_fn(&passthrough).escapes_stack.is_empty(), "a parameter pointer does not escape");
}

/// A wrapper that returns a callee's dangling-stack result inherits `DanglingStack`
/// through the cross-function fixpoint, so the wrapper's callers are caught too — for
/// both an in-module `Direct` and a cross-module `Symbol` edge. A wrapper around a
/// benign callee (returns a parameter pointer) must NOT be flagged.
#[test]
fn wrapper_inherits_callee_dangling_stack_return() {
    use csolver_ir::merge_modules;
    let a = RegId(0);
    let q = RegId(1);
    // leak(): { %a = alloca i32; ret %a }
    let mut leak_bb = BasicBlock::new(BlockId(0), Terminator::Return(Some(Operand::Reg(a))));
    leak_bb.insts.push(Inst::Alloc {
        dst: a,
        region: csolver_core::RegionKind::Stack,
        elem: Type::int(32),
        count: Operand::int(64, 1),
        align: 4,
    });
    // id(p): { ret p } — benign (returns its parameter).
    let p = RegId(0);
    let id_bb = BasicBlock::new(BlockId(0), Terminator::Return(Some(Operand::Reg(p))));
    // wrap(): { %q = call <callee>(); ret %q }
    let wrap = |callee: Callee| {
        let mut bb = BasicBlock::new(BlockId(0), Terminator::Return(Some(Operand::Reg(q))));
        bb.insts.push(Inst::Call {
            dst: Some(q),
            callee,
            args: vec![],
            ret_ty: Type::ptr(Type::int(32)),
            ret_ref: None,
        });
        bb
    };
    let func = |id: u32, name: &str, params: Vec<(RegId, Type)>, bb: BasicBlock| Function {
        id: FuncId(id),
        name: name.into(),
        params,
        ret_ty: Type::ptr(Type::int(32)),
        blocks: vec![bb],
        entry: BlockId(0),
    };
    let pp = || vec![(p, Type::ptr(Type::int(32)))];

    // Module B holds leak + an in-module Direct wrapper around it; module A a cross-module
    // Symbol wrapper around leak, and a benign wrapper around `id`.
    let mut b = Module::new("b");
    b.functions.push(func(0, "leak", vec![], leak_bb));
    b.functions.push(func(1, "b_wrap", vec![], wrap(Callee::Direct(FuncId(0)))));
    let mut aa = Module::new("a");
    aa.functions.push(func(0, "a_wrap", vec![], wrap(Callee::Symbol("leak".into()))));
    aa.functions.push(func(1, "id", pp(), id_bb));
    aa.functions.push(func(2, "benign_wrap", vec![], wrap(Callee::Symbol("id".into()))));

    let linked = merge_modules(vec![aa.clone(), b.clone()], "linked");
    let want = summarize_module(&linked);
    // Streaming/link-free must agree with the linked result (the losslessness oracle).
    assert_eq!(summarize_program(&[&aa, &b]), want);

    // Ids in the linked module: a_wrap=0, id=1, benign_wrap=2, leak=3, b_wrap=4.
    assert_eq!(want[&FuncId(3)].ret, RetSummary::DanglingStack, "leak returns a local");
    assert_eq!(want[&FuncId(4)].ret, RetSummary::DanglingStack, "Direct wrapper inherits it");
    assert_eq!(want[&FuncId(0)].ret, RetSummary::DanglingStack, "Symbol wrapper inherits it");
    assert_eq!(
        want[&FuncId(1)].ret,
        RetSummary::PtrFromArg { arg: 0, offset: Affine::constant(0) },
        "id returns its parameter"
    );
    // The benign wrapper must NOT be claimed dangling — only `DanglingStack` composes through
    // a wrapper; a `PtrFromArg` callee result stays Unknown (sound: the caller havocs).
    assert_ne!(want[&FuncId(2)].ret, RetSummary::DanglingStack, "benign wrapper is not dangling");
}

/// The streaming property: feeding modules one at a time and **dropping each**
/// right after `push_module` yields the same summaries as the linked module —
/// so a whole-program pass never needs the IR resident. Uses `atgt`/`writer`
/// cross-module resolution to make the drop meaningful (a later module's
/// definition still resolves a caller pushed earlier).
#[test]
fn summary_facts_stream_and_drop_equals_linked() {
    use csolver_ir::merge_modules;
    let p = RegId(0);
    let mk = |name: &str, insts: Vec<Inst>| {
        let mut m = Module::new("m");
        let mut bb = BasicBlock::new(BlockId(0), Terminator::Return(None));
        bb.insts = insts;
        m.functions.push(Function {
            id: FuncId(0),
            name: name.into(),
            params: vec![(p, Type::ptr(Type::int(32)))],
            ret_ty: Type::Unit,
            blocks: vec![bb],
            entry: BlockId(0),
        });
        m
    };
    let store = Inst::Store {
        ty: Type::int(32),
        ptr: Operand::Reg(p),
        value: Operand::int(32, 0),
        align: 4, volatile: false
    };
    let call_writer = Inst::Call {
        dst: None,
        callee: Callee::Symbol("writer".into()),
        args: vec![Operand::Reg(p)],
        ret_ty: Type::Unit,
        ret_ref: None,
    };
    // Caller pushed FIRST, its callee's definition SECOND — so resolution must
    // survive dropping the caller's module before the callee is even seen.
    let caller = mk("caller", vec![call_writer]);
    let writer = mk("writer", vec![store]);

    let want = summarize_module(&merge_modules(vec![caller.clone(), writer.clone()], "l"));
    let mut facts = SummaryFacts::new();
    {
        let m0 = caller; // moved in, pushed, then dropped at end of scope
        facts.push_module(&m0);
    }
    {
        let m1 = writer;
        facts.push_module(&m1);
    }
    assert_eq!(facts.finalize(), want, "streamed+dropped == linked");
}

/// Randomised losslessness guard: over many random multi-module call graphs
/// (stores, frees, and cross-module `Symbol` calls — some to defined names,
/// some unresolved/opaque), the link-free summaries must always equal the
/// linked ones. Exercises the transitive write/free fixpoint on arbitrary
/// graphs, which hand-built cases cannot cover exhaustively.
#[test]
fn summarize_program_matches_linked_on_random_programs() {
    use csolver_ir::merge_modules;
    let p = RegId(0);
    let mut state: u64 = 0x00C0_FFEE_1234_5678;
    let mut rng = || {
        state ^= state << 13;
        state ^= state >> 7;
        state ^= state << 17;
        state
    };
    let call = |callee: Callee| Inst::Call {
        dst: None,
        callee,
        args: vec![Operand::Reg(p)],
        ret_ty: Type::Unit,
        ret_ref: None,
    };
    for _ in 0..400 {
        let n_mods = 2 + (rng() % 3) as usize; // 2..=4 modules
        let per = 2 + (rng() % 4) as usize; // 2..=5 functions each
        let total = n_mods * per;
        let name = |gi: usize| format!("f{gi}");
        let mut modules = Vec::new();
        let mut gi = 0usize;
        for _ in 0..n_mods {
            let mut m = Module::new("m");
            for local in 0..per {
                let mut insts = Vec::new();
                if rng() & 1 == 0 {
                    insts.push(Inst::Store {
                        ty: Type::int(32),
                        ptr: Operand::Reg(p),
                        value: Operand::int(32, 0),
                        align: 4, volatile: false
                    });
                }
                if rng() % 4 == 0 {
                    insts.push(Inst::Dealloc {
                        region: csolver_core::RegionKind::Heap,
                        ptr: Operand::Reg(p),
                    });
                }
                for _ in 0..(rng() % 3) {
                    let callee = if rng() % 5 == 0 {
                        Callee::Symbol("undefined_ext".into()) // opaque
                    } else {
                        Callee::Symbol(name((rng() as usize) % total))
                    };
                    insts.push(call(callee));
                }
                m.functions.push(Function {
                    id: FuncId(local as u32),
                    name: name(gi),
                    params: vec![(p, Type::ptr(Type::int(32)))],
                    ret_ty: Type::Unit,
                    blocks: {
                        let mut bb = BasicBlock::new(BlockId(0), Terminator::Return(None));
                        bb.insts = insts;
                        vec![bb]
                    },
                    entry: BlockId(0),
                });
                gi += 1;
            }
            modules.push(m);
        }
        let refs: Vec<&Module> = modules.iter().collect();
        let got = summarize_program(&refs);
        let want = summarize_module(&merge_modules(modules.clone(), "linked"));
        assert_eq!(got, want, "link-free != linked on a random program");
    }
}

/// A call in an `Unreachable`-terminated block (rustc's `call @panic…;
/// unreachable` shape) never returns control, so its effects are
/// unobservable by any caller — it must not contaminate the effect summary.
/// The same call in a *returning* block must.
#[test]
fn diverging_calls_do_not_contaminate_the_effect_summary() {
    let make = |term: Terminator| {
        let mut bb0 = BasicBlock::new(BlockId(0), term);
        bb0.insts.push(Inst::Call {
            dst: None,
            callee: Callee::Symbol("core::panicking::panic".into()),
            args: vec![],
            ret_ty: Type::Unit,
            ret_ref: None,
        });
        let f = Function {
            id: FuncId(0),
            name: "p".into(),
            params: vec![],
            ret_ty: Type::Unit,
            blocks: vec![bb0],
            entry: BlockId(0),
        };
        let mut m = Module::new("m");
        m.functions.push(f);
        m
    };
    let diverging = summarize_module(&make(Terminator::Unreachable));
    assert!(diverging[&FuncId(0)].is_pure(), "a diverging call's effects are unobservable");
    let returning = summarize_module(&make(Terminator::Return(None)));
    assert!(!returning[&FuncId(0)].is_pure(), "a returning opaque call must contaminate");
}

#[test]
fn pointer_wrapper_summary() {
    // fn first(b: *i32) -> *i32 { b + 0 }
    let b = RegId(0);
    let q = RegId(1);
    let mut bb0 = BasicBlock::new(BlockId(0), Terminator::Return(Some(Operand::Reg(q))));
    bb0.insts.push(Inst::PtrOffset {
        dst: q,
        base: Operand::Reg(b),
        index: Operand::int(64, 0),
        elem: Type::int(32),
    });
    let f = Function {
        id: FuncId(0),
        name: "first".into(),
        params: vec![(b, Type::ptr(Type::int(32)))],
        ret_ty: Type::ptr(Type::int(32)),
        blocks: vec![bb0],
        entry: BlockId(0),
    };
    let s = summarize_fn(&f);
    assert!(s.is_pure());
    assert_eq!(
        s.ret,
        RetSummary::PtrFromArg { arg: 0, offset: Affine::constant(0) }
    );
}

/// rustc's guard shape: `entry: cond ? panic : ok; ok: ret p+4`. The panic
/// block never returns, so the summary must come from the agreeing return
/// site — multi-block functions were previously always `Unknown`.
#[test]
fn guarded_pointer_wrapper_summary() {
    let p = RegId(0);
    let c = RegId(1);
    let q = RegId(2);
    let mut entry = BasicBlock::new(
        BlockId(0),
        Terminator::CondBr {
            cond: Operand::Reg(c),
            then_blk: BlockId(1),
            then_args: vec![],
            else_blk: BlockId(2),
            else_args: vec![],
        },
    );
    entry.insts.push(Inst::Call {
        dst: Some(c),
        callee: Callee::Symbol("check".into()),
        args: vec![],
        ret_ty: Type::Bool,
        ret_ref: None,
    });
    let panic_blk = BasicBlock::new(BlockId(1), Terminator::Unreachable);
    let mut ok = BasicBlock::new(BlockId(2), Terminator::Return(Some(Operand::Reg(q))));
    ok.insts.push(Inst::PtrOffset {
        dst: q,
        base: Operand::Reg(p),
        index: Operand::int(64, 1),
        elem: Type::int(32),
    });
    let f = Function {
        id: FuncId(0),
        name: "guarded".into(),
        params: vec![(p, Type::ptr(Type::int(32)))],
        ret_ty: Type::ptr(Type::int(32)),
        blocks: vec![entry, panic_blk, ok],
        entry: BlockId(0),
    };
    assert_eq!(
        summarize_fn(&f).ret,
        RetSummary::PtrFromArg { arg: 0, offset: Affine::constant(4) },
        "the non-returning panic block must not defeat the summary"
    );
}

/// A function that returns the address of its own stack allocation (`return &local`,
/// optionally offset into it) escapes a pointer to a frame popped at the return — the
/// summary must report `DanglingStack` so a caller that derefs the result trips the
/// use-after-free machinery. A returned *parameter* pointer stays `PtrFromArg` (the
/// caller owns it), and a mixed path (local on one arm, parameter on the other) must
/// degrade to `Unknown` — never a false dangling claim.
#[test]
fn returning_a_local_stack_pointer_is_dangling() {
    let a = RegId(0);
    let q = RegId(1);
    let alloc = |dst| Inst::Alloc {
        dst,
        region: csolver_core::RegionKind::Stack,
        elem: Type::int(32),
        count: Operand::int(64, 1),
        align: 4,
    };
    // fn leak() { let a; return &a }
    let mut bb = BasicBlock::new(BlockId(0), Terminator::Return(Some(Operand::Reg(a))));
    bb.insts.push(alloc(a));
    let leak = Function {
        id: FuncId(0),
        name: "leak".into(),
        params: vec![],
        ret_ty: Type::ptr(Type::int(32)),
        blocks: vec![bb],
        entry: BlockId(0),
    };
    assert_eq!(summarize_fn(&leak).ret, RetSummary::DanglingStack);

    // fn leak_off() { let a; return &a[1] } — an offset into the local is still the local.
    let mut bb = BasicBlock::new(BlockId(0), Terminator::Return(Some(Operand::Reg(q))));
    bb.insts.push(alloc(a));
    bb.insts.push(Inst::PtrOffset {
        dst: q,
        base: Operand::Reg(a),
        index: Operand::int(64, 1),
        elem: Type::int(32),
    });
    let leak_off = Function {
        id: FuncId(0),
        name: "leak_off".into(),
        params: vec![],
        ret_ty: Type::ptr(Type::int(32)),
        blocks: vec![bb],
        entry: BlockId(0),
    };
    assert_eq!(summarize_fn(&leak_off).ret, RetSummary::DanglingStack);

    // fn maybe(p, c) { if c { return p } else { let a; return &a } } — mixed → Unknown.
    let p = RegId(2);
    let c = RegId(3);
    let entry = BasicBlock::new(
        BlockId(0),
        Terminator::CondBr {
            cond: Operand::Reg(c),
            then_blk: BlockId(1),
            then_args: vec![],
            else_blk: BlockId(2),
            else_args: vec![],
        },
    );
    let ret_param = BasicBlock::new(BlockId(1), Terminator::Return(Some(Operand::Reg(p))));
    let mut ret_local = BasicBlock::new(BlockId(2), Terminator::Return(Some(Operand::Reg(a))));
    ret_local.insts.push(alloc(a));
    let maybe = Function {
        id: FuncId(0),
        name: "maybe".into(),
        params: vec![(p, Type::ptr(Type::int(32))), (c, Type::Bool)],
        ret_ty: Type::ptr(Type::int(32)),
        blocks: vec![entry, ret_param, ret_local],
        entry: BlockId(0),
    };
    assert_eq!(
        summarize_fn(&maybe).ret,
        RetSummary::Unknown,
        "a local on only one path must not be claimed dangling"
    );
}

/// Disagreeing return sites (`ret p` vs `ret p+4`) must yield `Unknown` —
/// the caller trusts a summary to rebuild the result *exactly*, so a "may"
/// summary would be unsound. Likewise a loop-varying pointer: the back-edge
/// join makes the block parameter `Opaque`.
#[test]
fn disagreeing_and_loop_varying_returns_are_unknown() {
    let p = RegId(0);
    let c = RegId(1);
    let q = RegId(2);
    // fn f(p, c) { if c { return p } else { return p+4 } }
    let mut entry = BasicBlock::new(
        BlockId(0),
        Terminator::CondBr {
            cond: Operand::Reg(c),
            then_blk: BlockId(1),
            then_args: vec![],
            else_blk: BlockId(2),
            else_args: vec![],
        },
    );
    entry.insts.push(Inst::PtrOffset {
        dst: q,
        base: Operand::Reg(p),
        index: Operand::int(64, 1),
        elem: Type::int(32),
    });
    let a = BasicBlock::new(BlockId(1), Terminator::Return(Some(Operand::Reg(p))));
    let b = BasicBlock::new(BlockId(2), Terminator::Return(Some(Operand::Reg(q))));
    let f = Function {
        id: FuncId(0),
        name: "diverging_returns".into(),
        params: vec![(p, Type::ptr(Type::int(32))), (c, Type::Bool)],
        ret_ty: Type::ptr(Type::int(32)),
        blocks: vec![entry, a, b],
        entry: BlockId(0),
    };
    assert_eq!(summarize_fn(&f).ret, RetSummary::Unknown);

    // fn g(p) { loop { p = p+4; if done { return p } } } — the block param
    // joins p (entry) with p+4k (back-edge) → Opaque → Unknown.
    let cur = RegId(3);
    let next = RegId(4);
    let done = RegId(5);
    let entry = BasicBlock::new(
        BlockId(0),
        Terminator::Br { target: BlockId(1), args: vec![Operand::Reg(p)] },
    );
    let mut head = BasicBlock::new(
        BlockId(1),
        Terminator::CondBr {
            cond: Operand::Reg(done),
            then_blk: BlockId(2),
            then_args: vec![],
            else_blk: BlockId(1),
            else_args: vec![Operand::Reg(next)],
        },
    );
    head.params.push((cur, Type::ptr(Type::int(32))));
    head.insts.push(Inst::PtrOffset {
        dst: next,
        base: Operand::Reg(cur),
        index: Operand::int(64, 1),
        elem: Type::int(32),
    });
    head.insts.push(Inst::Call {
        dst: Some(done),
        callee: Callee::Symbol("check".into()),
        args: vec![],
        ret_ty: Type::Bool,
        ret_ref: None,
    });
    let exit = BasicBlock::new(BlockId(2), Terminator::Return(Some(Operand::Reg(next))));
    let g = Function {
        id: FuncId(1),
        name: "loop_advance".into(),
        params: vec![(p, Type::ptr(Type::int(32)))],
        ret_ty: Type::ptr(Type::int(32)),
        blocks: vec![entry, head, exit],
        entry: BlockId(0),
    };
    assert_eq!(summarize_fn(&g).ret, RetSummary::Unknown);
}

#[test]
fn index_wrapper_summary() {
    // fn at(b: *i32, i: i64) -> *i32 { b + i }   => ret = arg0 + 4*param1
    let b = RegId(0);
    let i = RegId(1);
    let q = RegId(2);
    let mut bb0 = BasicBlock::new(BlockId(0), Terminator::Return(Some(Operand::Reg(q))));
    bb0.insts.push(Inst::PtrOffset {
        dst: q,
        base: Operand::Reg(b),
        index: Operand::Reg(i),
        elem: Type::int(32),
    });
    let f = Function {
        id: FuncId(0),
        name: "at".into(),
        params: vec![(b, Type::ptr(Type::int(32))), (i, Type::int(64))],
        ret_ty: Type::ptr(Type::int(32)),
        blocks: vec![bb0],
        entry: BlockId(0),
    };
    let s = summarize_fn(&f);
    match s.ret {
        RetSummary::PtrFromArg { arg: 0, offset } => {
            assert_eq!(offset.constant, 0);
            assert_eq!(offset.terms.get(&1), Some(&4)); // i * sizeof(i32)
        }
        other => panic!("expected PtrFromArg, got {other:?}"),
    }
}
