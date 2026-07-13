use super::*;

/// A straight-line function: allocate a 16-byte region, optionally label it with
/// provenance id 0, then `CapRequire` capability id 1 on it. The `CapRequire` is the
/// last instruction (index 1 unlabelled, 2 labelled).
fn cap_func(with_label: bool) -> (Function, usize) {
    let buf = RegId(0);
    let mut bb0 = BasicBlock::new(BlockId(0), Terminator::Return(None));
    bb0.insts.push(Inst::Alloc {
        dst: buf,
        region: RegionKind::Heap,
        elem: Type::int(8),
        count: Operand::int(64, 16),
        align: 16,
    });
    if with_label {
        bb0.insts.push(Inst::ProvLabel { ptr: Operand::Reg(buf), label: 0 });
    }
    bb0.insts.push(Inst::CapRequire { ptr: Operand::Reg(buf), cap: 1 });
    let idx = bb0.insts.len() - 1;
    let f = Function {
        id: FuncId(0),
        name: "cap".into(),
        params: vec![],
        ret_ty: Type::Unit,
        blocks: vec![bb0],
        entry: BlockId(0),
    };
    (f, idx)
}

fn discharge_with_grants(f: &Function, grants: HashMap<u32, HashSet<u32>>) -> SymbolicReport {
    discharge_with_fields(
        f,
        &HashMap::new(),
        &[],
        &[],
        &HashMap::new(),
        &grants,
        false,
        false,
        false,
    )
}

#[test]
fn capability_violation_on_labelled_region_is_refuted() {
    // Region labelled `foreign` (id 0), which grants nothing; a `CapRequire` for
    // capability `write` (id 1) is therefore a definite violation → FAIL with witness.
    let (f, idx) = cap_func(true);
    let grants = HashMap::from([(0u32, HashSet::new())]);
    let d = discharge_with_grants(&f, grants)
        .mem_decision(BlockId(0), idx, SafetyProperty::WriteCapability)
        .expect("a WriteCapability obligation for the CapRequire")
        .clone();
    assert!(!d.proven, "a label lacking the capability must not be proven");
    assert!(d.refutation.is_some(), "it is refuted with a witness: {d:?}");
}

#[test]
fn capability_granted_by_label_proves() {
    // The same label now grants `write` (id 1) → the requirement holds.
    let (f, idx) = cap_func(true);
    let grants = HashMap::from([(0u32, HashSet::from([1u32]))]);
    let d = discharge_with_grants(&f, grants)
        .mem_decision(BlockId(0), idx, SafetyProperty::WriteCapability)
        .expect("a WriteCapability obligation")
        .clone();
    assert!(d.proven, "a granting label proves the requirement: {d:?}");
}

#[test]
fn capability_on_unlabelled_region_proves() {
    // No label ⇒ the region grants EVERYTHING (the sound default): no false FAIL,
    // even though the grant map withholds the capability from label 0.
    let (f, idx) = cap_func(false);
    let grants = HashMap::from([(0u32, HashSet::new())]);
    let d = discharge_with_grants(&f, grants)
        .mem_decision(BlockId(0), idx, SafetyProperty::WriteCapability)
        .expect("a WriteCapability obligation")
        .clone();
    assert!(d.proven, "an unlabelled region grants all capabilities: {d:?}");
}

/// The Copy-Fail flow in miniature: a `foreign` element propagates its provenance into
/// a container, and a later `require write` on the container is refuted — the container
/// is only as capable as its least-capable member.
#[test]
fn capability_propagates_from_element_into_container() {
    let page = RegId(0);
    let container = RegId(1);
    let mut bb0 = BasicBlock::new(BlockId(0), Terminator::Return(None));
    for dst in [page, container] {
        bb0.insts.push(Inst::Alloc {
            dst,
            region: RegionKind::Heap,
            elem: Type::int(8),
            count: Operand::int(64, 16),
            align: 16,
        });
    }
    // page is `foreign` (label 0); container absorbs page's labels; then require `write`.
    bb0.insts.push(Inst::ProvLabel { ptr: Operand::Reg(page), label: 0 });
    bb0.insts.push(Inst::ProvPropagate { dst: Operand::Reg(container), src: Operand::Reg(page) });
    bb0.insts.push(Inst::CapRequire { ptr: Operand::Reg(container), cap: 1 });
    let idx = bb0.insts.len() - 1;
    let f = Function {
        id: FuncId(0),
        name: "prop".into(),
        params: vec![],
        ret_ty: Type::Unit,
        blocks: vec![bb0],
        entry: BlockId(0),
    };
    // `foreign` (0) grants read only, not write (1).
    let grants = HashMap::from([(0u32, HashSet::from([2u32]))]);
    let d = discharge_with_grants(&f, grants)
        .mem_decision(BlockId(0), idx, SafetyProperty::WriteCapability)
        .expect("a WriteCapability obligation")
        .clone();
    assert!(!d.proven, "the container inherits the element's foreign provenance");
    assert!(d.refutation.is_some(), "a write to the foreign-tainted container is refuted: {d:?}");
}

/// The real algif_aead shape in miniature: the request object is an **opaque** pointer
/// (an allocator's result, not a tracked region), it is labelled `foreign`, and the same
/// foreign pointer is stored into two of its fields (`req->src` at +64 and `req->dst` at
/// +72 — an in-place op). The `require-if-alias-fields` sink reads those fields back and
/// must refute the write. This exercises read-your-writes over an *opaque base* (the
/// `alias_check` same-opaque-identity case): without it the field loads return fresh
/// values, the alias is lost, and the bug is missed.
#[test]
fn in_place_write_of_a_foreign_opaque_object_is_refused() {
    let obj = RegId(0); // an opaque pointer parameter (Prov::Unknown)
    let fsrc = RegId(1);
    let fdst = RegId(2);
    let mut bb0 = BasicBlock::new(BlockId(0), Terminator::Return(None));
    // Label the opaque object `foreign` (id 0).
    bb0.insts.push(Inst::ProvLabel { ptr: Operand::Reg(obj), label: 0 });
    // req->src = obj  (field at +64)
    bb0.insts.push(Inst::PtrOffset {
        dst: fsrc,
        base: Operand::Reg(obj),
        index: Operand::int(64, 64),
        elem: Type::int(8),
    });
    bb0.insts.push(Inst::Store {
        ty: Type::ptr(Type::int(8)),
        ptr: Operand::Reg(fsrc),
        value: Operand::Reg(obj),
        align: 8, volatile: false
    });
    // req->dst = obj  (field at +72) — same pointer ⇒ in-place
    bb0.insts.push(Inst::PtrOffset {
        dst: fdst,
        base: Operand::Reg(obj),
        index: Operand::int(64, 72),
        elem: Type::int(8),
    });
    bb0.insts.push(Inst::Store {
        ty: Type::ptr(Type::int(8)),
        ptr: Operand::Reg(fdst),
        value: Operand::Reg(obj),
        align: 8, volatile: false
    });
    // Sink: read req->src (+64) and req->dst (+72) back; iff they alias, require `write` (1).
    bb0.insts.push(Inst::CapRequireIfAliasFields {
        obj: Operand::Reg(obj),
        off_a: 64,
        off_b: 72,
        cap: 1,
    });
    let idx = bb0.insts.len() - 1;
    let f = Function {
        id: FuncId(0),
        name: "inplace_opaque".into(),
        params: vec![(obj, Type::ptr(Type::int(8)))],
        ret_ty: Type::Unit,
        blocks: vec![bb0],
        entry: BlockId(0),
    };
    // `foreign` (0) grants read (2) only, not write (1).
    let grants = HashMap::from([(0u32, HashSet::from([2u32]))]);
    let d = discharge_with_grants(&f, grants)
        .mem_decision(BlockId(0), idx, SafetyProperty::WriteCapability)
        .expect("a WriteCapability obligation")
        .clone();
    assert!(!d.proven, "the in-place write of a foreign opaque object is refuted: {d:?}");
    assert!(d.refutation.is_some(), "read-your-writes over the opaque base found the alias: {d:?}");
}

/// COPY-FAIL DIAGNOSIS, suspect 3 — a DERIVED pointer. The real IR stores
/// `%143 = gep %87+K` (a field pointer derived from the opaque object), not the
/// object itself, into req->src and req->dst. Does the derived pointer still carry
/// `foreign` and alias itself when read back? Expect: still refuted (fires).
#[test]
fn diag_copyfail_3_derived_pointer_in_place() {
    let obj = RegId(0);
    let p = RegId(1);
    let fsrc = RegId(2);
    let fdst = RegId(3);
    let mut bb0 = BasicBlock::new(BlockId(0), Terminator::Return(None));
    bb0.insts.push(Inst::ProvLabel { ptr: Operand::Reg(obj), label: 0 });
    bb0.insts.push(Inst::PtrOffset { dst: p, base: Operand::Reg(obj), index: Operand::int(64, 16), elem: Type::int(8) });
    bb0.insts.push(Inst::PtrOffset { dst: fsrc, base: Operand::Reg(obj), index: Operand::int(64, 64), elem: Type::int(8) });
    bb0.insts.push(Inst::Store { ty: Type::ptr(Type::int(8)), ptr: Operand::Reg(fsrc), value: Operand::Reg(p), align: 8 , volatile: false});
    bb0.insts.push(Inst::PtrOffset { dst: fdst, base: Operand::Reg(obj), index: Operand::int(64, 72), elem: Type::int(8) });
    bb0.insts.push(Inst::Store { ty: Type::ptr(Type::int(8)), ptr: Operand::Reg(fdst), value: Operand::Reg(p), align: 8 , volatile: false});
    bb0.insts.push(Inst::CapRequireIfAliasFields { obj: Operand::Reg(obj), off_a: 64, off_b: 72, cap: 1 });
    let idx = bb0.insts.len() - 1;
    let f = Function {
        id: FuncId(0),
        name: "diag3".into(),
        params: vec![(obj, Type::ptr(Type::int(8)))],
        ret_ty: Type::Unit,
        blocks: vec![bb0],
        entry: BlockId(0),
    };
    let grants = HashMap::from([(0u32, HashSet::from([2u32]))]);
    let d = discharge_with_grants(&f, grants)
        .mem_decision(BlockId(0), idx, SafetyProperty::WriteCapability)
        .expect("a WriteCapability obligation")
        .clone();
    assert!(!d.proven && d.refutation.is_some(), "a derived foreign pointer stored in-place is refuted: {d:?}");
}

/// SOUNDNESS GUARD for the satisfiability-based offset alias (Fix 2): the OUT-OF-PLACE
/// (patched) shape — req->src and req->dst hold DIFFERENT, provably-distinct field
/// offsets of the same foreign object — must NOT fire. If the possible-alias check over-
/// fired, this would be a false FAIL on patched code.
#[test]
fn out_of_place_distinct_fields_do_not_fire() {
    let obj = RegId(0);
    let p1 = RegId(1); // gep obj+16
    let p2 = RegId(2); // gep obj+32  (distinct from p1)
    let fsrc = RegId(3);
    let fdst = RegId(4);
    let mut bb0 = BasicBlock::new(BlockId(0), Terminator::Return(None));
    bb0.insts.push(Inst::ProvLabel { ptr: Operand::Reg(obj), label: 0 });
    bb0.insts.push(Inst::PtrOffset { dst: p1, base: Operand::Reg(obj), index: Operand::int(64, 16), elem: Type::int(8) });
    bb0.insts.push(Inst::PtrOffset { dst: p2, base: Operand::Reg(obj), index: Operand::int(64, 32), elem: Type::int(8) });
    bb0.insts.push(Inst::PtrOffset { dst: fsrc, base: Operand::Reg(obj), index: Operand::int(64, 64), elem: Type::int(8) });
    bb0.insts.push(Inst::Store { ty: Type::ptr(Type::int(8)), ptr: Operand::Reg(fsrc), value: Operand::Reg(p1), align: 8 , volatile: false});
    bb0.insts.push(Inst::PtrOffset { dst: fdst, base: Operand::Reg(obj), index: Operand::int(64, 72), elem: Type::int(8) });
    bb0.insts.push(Inst::Store { ty: Type::ptr(Type::int(8)), ptr: Operand::Reg(fdst), value: Operand::Reg(p2), align: 8 , volatile: false});
    bb0.insts.push(Inst::CapRequireIfAliasFields { obj: Operand::Reg(obj), off_a: 64, off_b: 72, cap: 1 });
    let idx = bb0.insts.len() - 1;
    let f = Function {
        id: FuncId(0),
        name: "outofplace".into(),
        params: vec![(obj, Type::ptr(Type::int(8)))],
        ret_ty: Type::Unit,
        blocks: vec![bb0],
        entry: BlockId(0),
    };
    let grants = HashMap::from([(0u32, HashSet::from([2u32]))]);
    for bugf in [false, true] {
        let d = discharge_with_fields(
            &f, &HashMap::new(), &[], &[], &HashMap::new(), &grants, bugf, false, false,
        )
        .mem_decision(BlockId(0), idx, SafetyProperty::WriteCapability)
        .expect("a WriteCapability obligation")
        .clone();
        assert!(d.refutation.is_none(), "distinct (out-of-place) fields must NOT be refuted (bug_finding={bugf}): {d:?}");
    }
}

/// COPY-FAIL DIAGNOSIS, suspect 1 — a PHI on the src value. The real IR sets
/// `req->src = phi [%143 (in-place), %190 (out-of-place)]` and `req->dst = %143`. On
/// the in-place path src == dst == foreign ⇒ must refute. Tests whether the block-arg
/// merge (a `Prov::Select` at the join) preserves the in-place aliasing/foreign label.
#[test]
fn diag_copyfail_1_phi_on_src() {
    let obj = RegId(0);
    let c = RegId(1); // nondeterministic condition
    let p143 = RegId(2); // in-place value: derived from obj
    let other = RegId(3); // out-of-place value: a distinct tracked region
    let src = RegId(4); // the phi (merge block param)
    let fsrc = RegId(5);
    let fdst = RegId(6);
    let mut bb0 = BasicBlock::new(
        BlockId(0),
        Terminator::CondBr {
            cond: Operand::Reg(c),
            then_blk: BlockId(1),
            then_args: vec![Operand::Reg(p143)],
            else_blk: BlockId(1),
            else_args: vec![Operand::Reg(other)],
        },
    );
    bb0.insts.push(Inst::ProvLabel { ptr: Operand::Reg(obj), label: 0 });
    bb0.insts.push(Inst::PtrOffset { dst: p143, base: Operand::Reg(obj), index: Operand::int(64, 16), elem: Type::int(8) });
    bb0.insts.push(Inst::Alloc { dst: other, region: RegionKind::Heap, elem: Type::int(8), count: Operand::int(64, 16), align: 16 });
    let mut bb1 = BasicBlock::new(BlockId(1), Terminator::Return(None));
    bb1.params = vec![(src, Type::ptr(Type::int(8)))];
    bb1.insts.push(Inst::PtrOffset { dst: fsrc, base: Operand::Reg(obj), index: Operand::int(64, 64), elem: Type::int(8) });
    bb1.insts.push(Inst::Store { ty: Type::ptr(Type::int(8)), ptr: Operand::Reg(fsrc), value: Operand::Reg(src), align: 8 , volatile: false});
    bb1.insts.push(Inst::PtrOffset { dst: fdst, base: Operand::Reg(obj), index: Operand::int(64, 72), elem: Type::int(8) });
    bb1.insts.push(Inst::Store { ty: Type::ptr(Type::int(8)), ptr: Operand::Reg(fdst), value: Operand::Reg(p143), align: 8 , volatile: false});
    bb1.insts.push(Inst::CapRequireIfAliasFields { obj: Operand::Reg(obj), off_a: 64, off_b: 72, cap: 1 });
    let idx = bb1.insts.len() - 1;
    let f = Function {
        id: FuncId(0),
        name: "diag1".into(),
        params: vec![(obj, Type::ptr(Type::int(8))), (c, Type::int(1))],
        ret_ty: Type::Unit,
        blocks: vec![bb0, bb1],
        entry: BlockId(0),
    };
    let grants = HashMap::from([(0u32, HashSet::from([2u32]))]);
    let d = discharge_with_grants(&f, grants)
        .mem_decision(BlockId(1), idx, SafetyProperty::WriteCapability)
        .expect("a WriteCapability obligation")
        .clone();
    // Strict mode: the two-way merge marks the path inexact, so the (correctly found)
    // refutation is soundly downgraded to UNKNOWN — never proven (no false PASS).
    assert!(!d.proven, "the phi merge never proves the in-place write safe: {d:?}");
    assert!(d.refutation.is_none(), "strict mode downgrades the merged-path refutation to UNKNOWN: {d:?}");

    // Bug-finding mode (the real kernel scan mode): the refutation stands — the merge's
    // `Prov::Select` is decomposed and the in-place foreign alternative refutes. So the
    // PHI is NOT what blocks the real algif_aead (which PASSes, a mode no synthetic hits).
    let grants2 = HashMap::from([(0u32, HashSet::from([2u32]))]);
    let d2 = discharge_with_fields(
        &f, &HashMap::new(), &[], &[], &HashMap::new(), &grants2, true, false, false,
    )
    .mem_decision(BlockId(1), idx, SafetyProperty::WriteCapability)
    .expect("a WriteCapability obligation")
    .clone();
    assert!(!d2.proven && d2.refutation.is_some(), "bug-finding mode refutes the phi in-place write: {d2:?}");
}

/// COPY-FAIL DIAGNOSIS, suspect 1b — a pointer passed through a SINGLE-EDGE block
/// parameter (no two-way merge). Distinguishes "block-arg pointer passing loses
/// identity" from "only the two-predecessor merge loses it". Expect: still refuted.
#[test]
fn diag_copyfail_1b_single_edge_blockparam() {
    let obj = RegId(0);
    let p143 = RegId(1);
    let src = RegId(2); // block param, bound to p143 by the single incoming edge
    let fsrc = RegId(3);
    let fdst = RegId(4);
    let mut bb0 = BasicBlock::new(
        BlockId(0),
        Terminator::Br { target: BlockId(1), args: vec![Operand::Reg(p143)] },
    );
    bb0.insts.push(Inst::ProvLabel { ptr: Operand::Reg(obj), label: 0 });
    bb0.insts.push(Inst::PtrOffset { dst: p143, base: Operand::Reg(obj), index: Operand::int(64, 16), elem: Type::int(8) });
    let mut bb1 = BasicBlock::new(BlockId(1), Terminator::Return(None));
    bb1.params = vec![(src, Type::ptr(Type::int(8)))];
    bb1.insts.push(Inst::PtrOffset { dst: fsrc, base: Operand::Reg(obj), index: Operand::int(64, 64), elem: Type::int(8) });
    bb1.insts.push(Inst::Store { ty: Type::ptr(Type::int(8)), ptr: Operand::Reg(fsrc), value: Operand::Reg(src), align: 8 , volatile: false});
    bb1.insts.push(Inst::PtrOffset { dst: fdst, base: Operand::Reg(obj), index: Operand::int(64, 72), elem: Type::int(8) });
    bb1.insts.push(Inst::Store { ty: Type::ptr(Type::int(8)), ptr: Operand::Reg(fdst), value: Operand::Reg(p143), align: 8 , volatile: false});
    bb1.insts.push(Inst::CapRequireIfAliasFields { obj: Operand::Reg(obj), off_a: 64, off_b: 72, cap: 1 });
    let idx = bb1.insts.len() - 1;
    let f = Function {
        id: FuncId(0),
        name: "diag1b".into(),
        params: vec![(obj, Type::ptr(Type::int(8)))],
        ret_ty: Type::Unit,
        blocks: vec![bb0, bb1],
        entry: BlockId(0),
    };
    let grants = HashMap::from([(0u32, HashSet::from([2u32]))]);
    let d = discharge_with_grants(&f, grants)
        .mem_decision(BlockId(1), idx, SafetyProperty::WriteCapability)
        .expect("a WriteCapability obligation")
        .clone();
    assert!(!d.proven && d.refutation.is_some(), "a pointer through a single-edge block param still refutes: {d:?}");
}

/// COPY-FAIL DIAGNOSIS, suspect 2 — the sink object is a NESTED field of the opaque
/// base. The real IR's `crypto_aead_encrypt(%193)` has `%193 = gep %87 field9` (the
/// embedded request), and the src/dst stores + the sink's +64/+72 are all relative to
/// `%193`, i.e. `%87 + off(field9) + {64,72}`. This mirrors the real shape exactly:
/// obj is opaque+foreign, reqbase = gep obj+128, and everything hangs off reqbase.
/// Expect: still refuted (the real case PASSes, so if THIS one PASSes, the nested base
/// is the blocker).
#[test]
fn diag_copyfail_2_nested_request_base() {
    let obj = RegId(0);
    let reqbase = RegId(1); // = gep obj + 128  (the embedded request, like %193)
    let p = RegId(2); // the foreign scatterlist pointer, derived from obj (like %143)
    let fsrc = RegId(3);
    let fdst = RegId(4);
    let mut bb0 = BasicBlock::new(BlockId(0), Terminator::Return(None));
    bb0.insts.push(Inst::ProvLabel { ptr: Operand::Reg(obj), label: 0 });
    bb0.insts.push(Inst::PtrOffset { dst: reqbase, base: Operand::Reg(obj), index: Operand::int(64, 128), elem: Type::int(8) });
    bb0.insts.push(Inst::PtrOffset { dst: p, base: Operand::Reg(obj), index: Operand::int(64, 16), elem: Type::int(8) });
    // req->src = p  (reqbase + 64)
    bb0.insts.push(Inst::PtrOffset { dst: fsrc, base: Operand::Reg(reqbase), index: Operand::int(64, 64), elem: Type::int(8) });
    bb0.insts.push(Inst::Store { ty: Type::ptr(Type::int(8)), ptr: Operand::Reg(fsrc), value: Operand::Reg(p), align: 8 , volatile: false});
    // req->dst = p  (reqbase + 72)
    bb0.insts.push(Inst::PtrOffset { dst: fdst, base: Operand::Reg(reqbase), index: Operand::int(64, 72), elem: Type::int(8) });
    bb0.insts.push(Inst::Store { ty: Type::ptr(Type::int(8)), ptr: Operand::Reg(fdst), value: Operand::Reg(p), align: 8 , volatile: false});
    // sink on the NESTED base reqbase, offsets 64/72
    bb0.insts.push(Inst::CapRequireIfAliasFields { obj: Operand::Reg(reqbase), off_a: 64, off_b: 72, cap: 1 });
    let idx = bb0.insts.len() - 1;
    let f = Function {
        id: FuncId(0),
        name: "diag2".into(),
        params: vec![(obj, Type::ptr(Type::int(8)))],
        ret_ty: Type::Unit,
        blocks: vec![bb0],
        entry: BlockId(0),
    };
    let grants = HashMap::from([(0u32, HashSet::from([2u32]))]);
    // Fires in both modes — a nested request base (sink object = gep of the opaque base)
    // read-your-writes and aliases correctly. So the nested base is NOT the blocker.
    for bugf in [false, true] {
        let d = discharge_with_fields(
            &f, &HashMap::new(), &[], &[], &HashMap::new(), &grants, bugf, false, false,
        )
        .mem_decision(BlockId(0), idx, SafetyProperty::WriteCapability)
        .expect("a WriteCapability obligation")
        .clone();
        assert!(!d.proven && d.refutation.is_some(), "nested-base in-place write refuted (bug_finding={bugf}): {d:?}");
    }
}
