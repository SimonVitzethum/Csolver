use super::*;

/// Build a caller that stores `buf` into `slot`, loads a function pointer
/// from constant global `G` at offset 0, calls it indirectly, reloads `slot`
/// and writes through it. The final write proves temporal safety **iff** the
/// indirect call was devirtualised to a pure summary (no havoc/free).
fn devirt_caller() -> Function {
    let slot = RegId(0);
    let buf = RegId(1);
    let fp = RegId(2);
    let p = RegId(3);
    let mut bb0 = BasicBlock::new(BlockId(0), Terminator::Return(None));
    bb0.insts.push(Inst::Alloc {
        dst: slot,
        region: RegionKind::Heap,
        elem: Type::ptr(Type::int(8)),
        count: Operand::int(64, 1),
        align: 8,
    });
    bb0.insts.push(Inst::Alloc {
        dst: buf,
        region: RegionKind::Heap,
        elem: Type::int(8),
        count: Operand::int(64, 8),
        align: 1,
    });
    bb0.insts.push(Inst::Store {
        ty: Type::ptr(Type::int(8)),
        ptr: Operand::Reg(slot),
        value: Operand::Reg(buf),
        align: 8, volatile: false
    });
    bb0.insts.push(Inst::Load {
        dst: fp,
        ty: Type::ptr(Type::int(8)),
        ptr: Operand::Const(Const::Symbol("G".into())),
        align: 8, volatile: false
    });
    bb0.insts.push(Inst::Call {
        dst: None,
        callee: csolver_ir::Callee::Indirect(Operand::Reg(fp)),
        args: vec![],
        ret_ty: Type::Unit,
        ret_ref: None,
    });
    bb0.insts.push(Inst::Load {
        dst: p,
        ty: Type::ptr(Type::int(8)),
        ptr: Operand::Reg(slot),
        align: 8, volatile: false
    });
    bb0.insts.push(Inst::Store {
        ty: Type::int(8),
        ptr: Operand::Reg(p),
        value: Operand::int(8, 0),
        align: 1, volatile: false
    });
    Function {
        id: FuncId(0),
        name: "devirt_caller".into(),
        params: vec![],
        ret_ty: Type::Unit,
        blocks: vec![bb0],
        entry: BlockId(0),
    }
}

#[test]
fn indirect_call_devirtualised_to_a_pure_summary_preserves_state() {
    use std::collections::HashMap;
    let f = devirt_caller();
    let mut summaries = HashMap::new();
    // A pure callee: no writes, no frees.
    summaries.insert(
        FuncId(1),
        Summary { ret: RetSummary::Unknown, writes: false, frees: false, frees_arg: None, prov: ProvTransfer::default(), refcount_effect: vec![], escapes_stack: vec![] },
    );
    let mut globals = HashMap::new();
    globals.insert("G".to_string(), csolver_ir::GlobalDef { size: 8, align: 8, writable: false });
    let empty_grants = HashMap::new();

    // With the devirt table, the indirect call resolves to the pure summary,
    // so the store into `slot` survives and `buf`'s liveness/provenance too.
    let mut table = HashMap::new();
    table.insert("G".to_string(), vec![(0u64, FuncId(1))]);
    let r = discharge_inner(
        &f, ExecLimits::default(), &summaries, &HashMap::new(), &[], &[], &[], &globals,
        &empty_grants, &table, &HashMap::new(), None, &HashMap::new(), None, &HashMap::new(),
    );
    assert!(
        r.assumptions.iter().any(|a| a == "devirtualized-indirect-call"),
        "the indirect call should have been devirtualised: {:?}", r.assumptions,
    );
    let uaf = r.mem_decision(BlockId(0), 6, SafetyProperty::NoUseAfterFree).expect("uaf");
    assert!(uaf.proven, "pure devirtualised call must preserve liveness: {}", uaf.residual);

    // Control: no table ⇒ opaque indirect call ⇒ default (may write & free)
    // havoc ⇒ the final write is not proven safe.
    let r2 = discharge_inner(
        &f, ExecLimits::default(), &summaries, &HashMap::new(), &[], &[], &[], &globals,
        &empty_grants, &HashMap::new(), &HashMap::new(), None, &HashMap::new(), None, &HashMap::new(),
    );
    assert!(
        !r2.assumptions.iter().any(|a| a == "devirtualized-indirect-call"),
        "no table ⇒ no devirtualisation",
    );
    let uaf2 = r2.mem_decision(BlockId(0), 6, SafetyProperty::NoUseAfterFree).expect("uaf2");
    assert!(!uaf2.proven, "an opaque indirect call must havoc, leaving the write unproven");
}

/// A CFI slice: an indirect call through a **null** function pointer is a
/// definite control-flow-integrity violation (`ValidIndirectTarget` refuted),
/// while a devirtualised (known-target) call is proven valid.
#[test]
fn indirect_call_through_null_fn_ptr_is_refuted() {
    use std::collections::HashMap;
    let mut bb0 = BasicBlock::new(BlockId(0), Terminator::Return(None));
    bb0.insts.push(Inst::Call {
        dst: None,
        callee: csolver_ir::Callee::Indirect(Operand::Const(Const::Null)),
        args: vec![],
        ret_ty: Type::Unit,
        ret_ref: None,
    });
    let f = Function {
        id: FuncId(0),
        name: "callnull".into(),
        params: vec![],
        ret_ty: Type::Unit,
        blocks: vec![bb0],
        entry: BlockId(0),
    };
    let empty_grants = HashMap::new();
    let r = discharge_inner(
        &f, ExecLimits::default(), &HashMap::new(), &HashMap::new(), &[], &[], &[],
        &HashMap::new(), &empty_grants, &HashMap::new(), &HashMap::new(), None, &HashMap::new(), None, &HashMap::new(),
    );
    let d = r
        .mem_decision(BlockId(0), 0, SafetyProperty::ValidIndirectTarget)
        .expect("valid-target obligation recorded");
    assert!(!d.proven, "a null function-pointer call must not be proven valid");
    assert!(d.refutation.is_some(), "the null call is refuted with a witness");
}

/// A CFI slice: an indirect call **into a stack region** (executing data as code — the
/// classic jump-to-injected-shellcode) is a definite `ValidIndirectTarget` violation, while
/// an indirect call through an opaque parameter pointer (unknown but assumed valid) is not.
#[test]
fn indirect_call_into_stack_data_is_refuted() {
    use std::collections::HashMap;
    let empty_grants = HashMap::new();
    let run = |f: &Function| {
        discharge_inner(
            f, ExecLimits::default(), &HashMap::new(), &HashMap::new(), &[], &[], &[],
            &HashMap::new(), &empty_grants, &HashMap::new(), &HashMap::new(), None, &HashMap::new(), None, &HashMap::new(),
        )
    };
    // `%p = alloca i32; call %p()` — calling the address of a stack local as code.
    let p = RegId(0);
    let mut bb0 = BasicBlock::new(BlockId(0), Terminator::Return(None));
    bb0.insts.push(Inst::Alloc {
        dst: p,
        region: csolver_core::RegionKind::Stack,
        elem: Type::int(32),
        count: Operand::int(64, 1),
        align: 4,
    });
    bb0.insts.push(Inst::Call {
        dst: None,
        callee: csolver_ir::Callee::Indirect(Operand::Reg(p)),
        args: vec![],
        ret_ty: Type::Unit,
        ret_ref: None,
    });
    let f = Function {
        id: FuncId(0), name: "callstack".into(), params: vec![],
        ret_ty: Type::Unit, blocks: vec![bb0], entry: BlockId(0),
    };
    let rf = run(&f);
    let d = rf
        .mem_decision(BlockId(0), 1, SafetyProperty::ValidIndirectTarget)
        .expect("valid-target obligation recorded");
    assert!(!d.proven, "calling a stack address as code must not be proven valid");
    assert!(d.refutation.is_some(), "the stack-data call is refuted with a witness");

    // Negative control: an indirect call through an opaque parameter pointer is assumed valid
    // (an ordinary callback) — it must NOT be flagged.
    let fp = RegId(0);
    let mut bb = BasicBlock::new(BlockId(0), Terminator::Return(None));
    bb.insts.push(Inst::Call {
        dst: None,
        callee: csolver_ir::Callee::Indirect(Operand::Reg(fp)),
        args: vec![],
        ret_ty: Type::Unit,
        ret_ref: None,
    });
    let g = Function {
        id: FuncId(0), name: "callparam".into(),
        params: vec![(fp, Type::ptr(Type::Unit))],
        ret_ty: Type::Unit, blocks: vec![bb], entry: BlockId(0),
    };
    let rg = run(&g);
    let d2 = rg.mem_decision(BlockId(0), 0, SafetyProperty::ValidIndirectTarget);
    // Either proven valid or left open — but never refuted (no false CFI FAIL on a callback).
    assert!(d2.is_none_or(|d| d.refutation.is_none()), "an opaque callback pointer must not be refuted");
}

/// A1 (IR-intrinsic read-only): a store into a `constant` global — a `.rodata`
/// write that faults at runtime — is a refutable violation (FAIL), while a store
/// into a writable global proves. General and sound: it rests only on the module's
/// own `constant` vs `global` linkage, and a runtime `.rodata` write is always a bug.
#[test]
fn write_to_constant_global_is_refuted() {
    use std::collections::HashMap;
    let mk = |name: &str| {
        let mut bb0 = BasicBlock::new(BlockId(0), Terminator::Return(None));
        bb0.insts.push(Inst::Store {
            ty: Type::int(32),
            ptr: Operand::Const(Const::Symbol(name.into())),
            value: Operand::int(32, 7),
            align: 4, volatile: false
        });
        Function {
            id: FuncId(0),
            name: "w".into(),
            params: vec![],
            ret_ty: Type::Unit,
            blocks: vec![bb0],
            entry: BlockId(0),
        }
    };
    let mut globals = HashMap::new();
    globals.insert("ro".to_string(), csolver_ir::GlobalDef { size: 4, align: 4, writable: false });
    globals.insert("rw".to_string(), csolver_ir::GlobalDef { size: 4, align: 4, writable: true });
    let empty = HashMap::new();
    let run = |f: &Function| {
        discharge_inner(
            f, ExecLimits { bug_finding: true, ..ExecLimits::default() }, &HashMap::new(),
            &HashMap::new(), &[], &[], &[], &globals, &empty, &HashMap::new(), &HashMap::new(), None, &HashMap::new(), None, &HashMap::new(),
        )
    };
    let ro = run(&mk("ro"));
    let vw = ro.mem_decision(BlockId(0), 0, SafetyProperty::ValidWrite).expect("valid_write");
    assert!(!vw.proven && vw.refutation.is_some(), "a write into a constant global must be refuted: {}", vw.residual);
    let rw = run(&mk("rw"));
    let vw2 = rw.mem_decision(BlockId(0), 0, SafetyProperty::ValidWrite).expect("valid_write");
    assert!(vw2.proven, "a write into a writable global must prove: {}", vw2.residual);
}

/// 2b (whole-program on-demand): a cross-file `Callee::Symbol(name)` with no
/// in-module id resolves to the program-wide callee summary passed in
/// `name_summaries` — so the call is analysed with the callee's real effect
/// instead of an opaque havoc. Sound *and* precise: a pure remote callee lets
/// the following use prove; a remote callee that frees the argument turns it
/// into a caught use-after-free.
#[test]
fn cross_file_symbol_call_resolves_via_name_summaries() {
    use std::collections::HashMap;
    // bb0: buf = alloc[8]; remote(buf); *buf = 0
    let buf = RegId(0);
    let mut bb0 = BasicBlock::new(BlockId(0), Terminator::Return(None));
    bb0.insts.push(Inst::Alloc {
        dst: buf,
        region: RegionKind::Heap,
        elem: Type::int(8),
        count: Operand::int(64, 8),
        align: 1,
    });
    bb0.insts.push(Inst::Call {
        dst: None,
        callee: Callee::Symbol("remote".into()),
        args: vec![Operand::Reg(buf)],
        ret_ty: Type::Unit,
        ret_ref: None,
    });
    bb0.insts.push(Inst::Store {
        ty: Type::int(8),
        ptr: Operand::Reg(buf),
        value: Operand::int(8, 0),
        align: 1, volatile: false
    });
    let f = Function {
        id: FuncId(0),
        name: "cross_caller".into(),
        params: vec![],
        ret_ty: Type::Unit,
        blocks: vec![bb0],
        entry: BlockId(0),
    };
    let empty_grants = HashMap::new();

    // Control: no name map ⇒ opaque `Symbol` havoc ⇒ the call may free `buf`,
    // so the following store is NOT proven free of use-after-free.
    let opaque = discharge_inner(
        &f, ExecLimits::default(), &HashMap::new(), &HashMap::new(), &[], &[], &[],
        &HashMap::new(), &empty_grants, &HashMap::new(), &HashMap::new(), None, &HashMap::new(), None, &HashMap::new(),
    );
    let uaf = opaque.mem_decision(BlockId(0), 2, SafetyProperty::NoUseAfterFree).expect("uaf");
    assert!(!uaf.proven, "an unresolved cross-file symbol must havoc (may free)");

    // Resolve `remote` to a PURE summary ⇒ the store is proven live.
    let mut pure = HashMap::new();
    pure.insert(
        "remote".to_string(),
        Summary { ret: RetSummary::Unknown, writes: false, frees: false, frees_arg: None, prov: ProvTransfer::default(), refcount_effect: vec![], escapes_stack: vec![] },
    );
    let r_pure = discharge_inner(
        &f, ExecLimits::default(), &HashMap::new(), &pure, &[], &[], &[], &HashMap::new(),
        &empty_grants, &HashMap::new(), &HashMap::new(), None, &HashMap::new(), None, &HashMap::new(),
    );
    let uaf_pure = r_pure.mem_decision(BlockId(0), 2, SafetyProperty::NoUseAfterFree).expect("uaf");
    assert!(uaf_pure.proven, "a pure remote callee must preserve liveness: {}", uaf_pure.residual);

    // Resolve `remote` to a summary that frees argument 0 ⇒ the store is a
    // use-after-free and must be refuted (sound: the real effect flows in).
    let mut frees = HashMap::new();
    frees.insert(
        "remote".to_string(),
        Summary { ret: RetSummary::Unknown, writes: false, frees: true, frees_arg: Some(0), prov: ProvTransfer::default(), refcount_effect: vec![], escapes_stack: vec![] },
    );
    let r_free = discharge_inner(
        &f, ExecLimits::default(), &HashMap::new(), &frees, &[], &[], &[], &HashMap::new(),
        &empty_grants, &HashMap::new(), &HashMap::new(), None, &HashMap::new(), None, &HashMap::new(),
    );
    let uaf_free = r_free.mem_decision(BlockId(0), 2, SafetyProperty::NoUseAfterFree).expect("uaf");
    assert!(!uaf_free.proven, "a remote callee that frees the arg makes the store a UAF");
}

#[test]
fn loop_body_access_is_proven_via_invariant() {
    let f = loop_store();
    let r = discharge_function(&f);
    assert!(!r.truncated, "loop exploration must terminate");
    // The store at bb2 index 1: in-bounds proved from the interval
    // invariant (i >= 0) plus the loop guard (i < n).
    let inb = r
        .mem_decision(BlockId(2), 1, SafetyProperty::InBounds)
        .expect("in-bounds decided");
    assert!(inb.proven, "loop body access should be in bounds: {}", inb.residual);
    // Pointer arithmetic too.
    let arith = r
        .mem_decision(BlockId(2), 0, SafetyProperty::ValidPointerArith)
        .expect("ptr arith decided");
    assert!(arith.proven, "pointer arithmetic: {}", arith.residual);
}
