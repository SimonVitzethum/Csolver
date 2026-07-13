use super::*;

/// `loop_array_store(n)`: the canonical counting loop `for i in 0..n { buf[i] = 0 }`
/// over a freshly allocated `[i32; n]`. Proving the in-loop access in bounds
/// needs a *relational* loop invariant (`i < n`) that intervals cannot express;
/// the symbolic engine gets it from the loop guard (path condition) plus the
/// interval invariant `i >= 0` at the header.
///
/// ```text
///   bb0: buf = alloc i32 * n ; br bb1(0)
///   bb1(i): c = i < n ; condbr c -> bb2(i) / bb3
///   bb2(j): p = buf + j*4 ; store 0 -> p ; nj = j+1 ; br bb1(nj)
///   bb3: return
/// ```
pub fn loop_array_store() -> Function {
    let n = RegId(0);
    let buf = RegId(1);
    let i = RegId(2);
    let c = RegId(3);
    let j = RegId(4);
    let p = RegId(5);
    let nj = RegId(6);

    let mut bb0 = BasicBlock::new(
        BlockId(0),
        Terminator::Br {
            target: BlockId(1),
            args: vec![Operand::int(64, 0)],
        },
    );
    bb0.insts.push(Inst::Alloc {
        dst: buf,
        region: RegionKind::Heap,
        elem: Type::int(32),
        count: Operand::Reg(n),
        align: 4,
    });

    let mut bb1 = BasicBlock::new(
        BlockId(1),
        Terminator::CondBr {
            cond: Operand::Reg(c),
            then_blk: BlockId(2),
            then_args: vec![Operand::Reg(i)],
            else_blk: BlockId(3),
            else_args: vec![],
        },
    );
    bb1.params = vec![(i, Type::int(64))];
    bb1.insts.push(Inst::Assign {
        dst: c,
        ty: Type::Bool,
        value: csolver_ir::RValue::Cmp {
            op: CmpOp::Slt,
            lhs: Operand::Reg(i),
            rhs: Operand::Reg(n),
        },
    });

    let mut bb2 = BasicBlock::new(
        BlockId(2),
        Terminator::Br {
            target: BlockId(1),
            args: vec![Operand::Reg(nj)],
        },
    );
    bb2.params = vec![(j, Type::int(64))];
    bb2.insts.push(Inst::PtrOffset {
        dst: p,
        base: Operand::Reg(buf),
        index: Operand::Reg(j),
        elem: Type::int(32),
    });
    bb2.insts.push(Inst::Store {
        ty: Type::int(32),
        ptr: Operand::Reg(p),
        value: Operand::int(32, 0),
        align: 4, volatile: false
    });
    bb2.insts.push(Inst::Assign {
        dst: nj,
        ty: Type::int(64),
        value: csolver_ir::RValue::Bin {
            op: csolver_ir::BinOp::Add,
            lhs: Operand::Reg(j),
            rhs: Operand::int(64, 1),
        flags: Default::default(),
        },
    });

    let bb3 = BasicBlock::new(BlockId(3), Terminator::Return(None));

    Function {
        id: FuncId(0),
        name: "loop_array_store".into(),
        params: vec![(n, Type::int(64))],
        ret_ty: Type::Unit,
        blocks: vec![bb0, bb1, bb2, bb3],
        entry: BlockId(0),
    }
}

/// `relational_loop(n)`: `for (i, j) = (0, 0); i < n; i++, j++ { buf[j] = 0 }`
/// over a `[i32; n]`. Proving `buf[j]` in bounds needs the **relation** `j <= i`
/// (so `j <= i < n`), which the per-register interval domain and the loop guard
/// (`i < n`, on `i` not `j`) cannot supply — only the relational *zone* domain
/// can. So this verifies PASS solely because of the zone invariant.
///
/// ```text
///   bb0: buf = alloc i32 * n ; br bb1(0, 0)
///   bb1(i, j): c = i < n ; condbr c -> bb2 / bb3
///   bb2: p = buf + j*4 ; store 0 -> p ; ni = i+1 ; nj = j+1 ; br bb1(ni, nj)
///   bb3: return
/// ```
pub fn relational_loop() -> Function {
    let n = RegId(0);
    let buf = RegId(1);
    let i = RegId(2);
    let j = RegId(3);
    let c = RegId(4);
    let p = RegId(5);
    let ni = RegId(6);
    let nj = RegId(7);

    let mut bb0 = BasicBlock::new(
        BlockId(0),
        Terminator::Br { target: BlockId(1), args: vec![Operand::int(64, 0), Operand::int(64, 0)] },
    );
    bb0.insts.push(Inst::Alloc {
        dst: buf,
        region: RegionKind::Heap,
        elem: Type::int(32),
        count: Operand::Reg(n),
        align: 4,
    });

    let mut bb1 = BasicBlock::new(
        BlockId(1),
        Terminator::CondBr {
            cond: Operand::Reg(c),
            then_blk: BlockId(2),
            then_args: vec![],
            else_blk: BlockId(3),
            else_args: vec![],
        },
    );
    bb1.params = vec![(i, Type::int(64)), (j, Type::int(64))];
    bb1.insts.push(Inst::Assign {
        dst: c,
        ty: Type::Bool,
        value: RValue::Cmp { op: CmpOp::Slt, lhs: Operand::Reg(i), rhs: Operand::Reg(n) },
    });

    // The body uses the header's i/j directly (it is dominated by bb1).
    let mut bb2 = BasicBlock::new(
        BlockId(2),
        Terminator::Br { target: BlockId(1), args: vec![Operand::Reg(ni), Operand::Reg(nj)] },
    );
    bb2.insts.push(Inst::PtrOffset {
        dst: p,
        base: Operand::Reg(buf),
        index: Operand::Reg(j),
        elem: Type::int(32),
    });
    bb2.insts.push(Inst::Store { ty: Type::int(32), ptr: Operand::Reg(p), value: Operand::int(32, 0), align: 4 , volatile: false});
    bb2.insts.push(Inst::Assign {
        dst: ni,
        ty: Type::int(64),
        value: RValue::Bin { op: BinOp::Add, lhs: Operand::Reg(i), rhs: Operand::int(64, 1) , flags: Default::default() },
    });
    bb2.insts.push(Inst::Assign {
        dst: nj,
        ty: Type::int(64),
        value: RValue::Bin { op: BinOp::Add, lhs: Operand::Reg(j), rhs: Operand::int(64, 1) , flags: Default::default() },
    });

    let bb3 = BasicBlock::new(BlockId(3), Terminator::Return(None));
    Function {
        id: FuncId(0),
        name: "relational_loop".into(),
        params: vec![(n, Type::int(64))],
        ret_ty: Type::Unit,
        blocks: vec![bb0, bb1, bb2, bb3],
        entry: BlockId(0),
    }
}

/// `indirect_store()`: store a pointer into a slot, load it back, and write
/// through it — a raw-pointer round-trip through memory. The alias-aware
/// symbolic heap preserves the pointer's provenance across the store/load, so
/// the final dereference is proved safe.
///
/// ```text
///   buf  = alloc i8 * 16
///   slot = alloc *i8 * 1
///   store buf -> slot
///   p = load slot           // must-alias slot => p has buf's provenance
///   store 0 -> p            // deref proved in-bounds / non-null / live / writable
/// ```
pub fn indirect_store() -> Function {
    let buf = RegId(0);
    let slot = RegId(1);
    let p = RegId(2);
    let mut bb0 = BasicBlock::new(BlockId(0), Terminator::Return(None));
    bb0.insts.push(Inst::Alloc {
        dst: buf,
        region: RegionKind::Heap,
        elem: Type::int(8),
        count: Operand::int(64, 16),
        align: 1,
    });
    bb0.insts.push(Inst::Alloc {
        dst: slot,
        region: RegionKind::Heap,
        elem: Type::ptr(Type::int(8)),
        count: Operand::int(64, 1),
        align: 8,
    });
    bb0.insts.push(Inst::Store {
        ty: Type::ptr(Type::int(8)),
        ptr: Operand::Reg(slot),
        value: Operand::Reg(buf),
        align: 8, volatile: false
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
        name: "indirect_store".into(),
        params: vec![],
        ret_ty: Type::Unit,
        blocks: vec![bb0],
        entry: BlockId(0),
    }
}

/// `uninit_read()`: allocate a buffer and *read* it before any write. A fresh
/// allocation holds uninitialized bytes, so the load is a read of uninitialized
/// memory (undefined behaviour in Rust). On this exact, straight-line path the
/// violation is definite and is refuted (`ValidRead` FAIL) with a witness.
///
/// ```text
///   buf = alloc i32 * 4    // uninitialized
///   v   = load buf         // UB: reads never-written memory
/// ```
pub fn uninit_read() -> Function {
    let buf = RegId(0);
    let v = RegId(1);
    let mut bb0 = BasicBlock::new(BlockId(0), Terminator::Return(None));
    bb0.insts.push(Inst::Alloc {
        dst: buf,
        region: RegionKind::Heap,
        elem: Type::int(32),
        count: Operand::int(64, 4),
        align: 4,
    });
    bb0.insts.push(Inst::Load {
        dst: v,
        ty: Type::int(32),
        ptr: Operand::Reg(buf),
        align: 4, volatile: false
    });
    Function {
        id: FuncId(0),
        name: "uninit_read".into(),
        params: vec![],
        ret_ty: Type::Unit,
        blocks: vec![bb0],
        entry: BlockId(0),
    }
}

/// `init_read()`: the safe counterpart — the same buffer is *written* before it
/// is read, so the load reads an initialized value (the store `Must`-aliases it)
/// and the function verifies PASS.
///
/// ```text
///   buf = alloc i32 * 4
///   store 7 -> buf         // initializes [0, 4)
///   v   = load buf         // reads the stored value
/// ```
pub fn init_read() -> Function {
    let buf = RegId(0);
    let v = RegId(1);
    let mut bb0 = BasicBlock::new(BlockId(0), Terminator::Return(None));
    bb0.insts.push(Inst::Alloc {
        dst: buf,
        region: RegionKind::Heap,
        elem: Type::int(32),
        count: Operand::int(64, 4),
        align: 4,
    });
    bb0.insts.push(Inst::Store {
        ty: Type::int(32),
        ptr: Operand::Reg(buf),
        value: Operand::int(32, 7),
        align: 4, volatile: false
    });
    bb0.insts.push(Inst::Load {
        dst: v,
        ty: Type::int(32),
        ptr: Operand::Reg(buf),
        align: 4, volatile: false
    });
    Function {
        id: FuncId(0),
        name: "init_read".into(),
        params: vec![],
        ret_ty: Type::Unit,
        blocks: vec![bb0],
        entry: BlockId(0),
    }
}

/// `eq_exit_loop()`: `buf = [i32; 8]; i = 0; while i != 8 { buf[i] = 0; i += 1 }`.
/// The loop exits on an **equality** test (`i == 8`), not `i < 8`, so the
/// interval domain widens `i` to `[0, +∞]` and cannot bound it. The equality-exit
/// induction analysis recognizes `i` (start 0, stride 1, bound 8) and the engine
/// asserts the sound invariant `0 ≤ i ≤ 8`; with the loop guard `i != 8` this
/// gives `i < 8`, so every `buf[i]` is in bounds → PASS. This is the integer
/// precursor of the pointer-walk (`iter != end`) loop.
///
/// ```text
///   bb0: buf = alloc i32 * 8 ; br bb1(0)
///   bb1(i): c = (i == 8) ; condbr c -> bb3 / bb2
///   bb2: p = buf + i ; store 0 -> p ; ni = i + 1 ; br bb1(ni)
///   bb3: return
/// ```
pub fn eq_exit_loop() -> Function {
    eq_exit_loop_to(8)
}

/// As [`eq_exit_loop`] but the exit bound exceeds the buffer: `while i != 16`
/// over a `[i32; 8]`. The asserted invariant `0 ≤ i ≤ 16` does not bound the
/// access below 8, so `buf[i]` is out of bounds for `i ∈ [8, 16)` and must NOT
/// be proved PASS (soundness: the equality-exit bound never fakes safety).
pub fn eq_exit_loop_oob() -> Function {
    eq_exit_loop_to(16)
}

fn eq_exit_loop_to(exit: u128) -> Function {
    let buf = RegId(0);
    let i = RegId(1);
    let c = RegId(2);
    let ni = RegId(3);
    let p = RegId(4);

    let mut bb0 = BasicBlock::new(
        BlockId(0),
        Terminator::Br { target: BlockId(1), args: vec![Operand::int(64, 0)] },
    );
    bb0.insts.push(Inst::Alloc {
        dst: buf,
        region: RegionKind::Heap,
        elem: Type::int(32),
        count: Operand::int(64, 8),
        align: 4,
    });

    let mut bb1 = BasicBlock::new(
        BlockId(1),
        Terminator::CondBr {
            cond: Operand::Reg(c),
            then_blk: BlockId(3),
            then_args: vec![],
            else_blk: BlockId(2),
            else_args: vec![],
        },
    );
    bb1.params = vec![(i, Type::int(64))];
    bb1.insts.push(Inst::Assign {
        dst: c,
        ty: Type::Bool,
        value: csolver_ir::RValue::Cmp {
            op: CmpOp::Eq,
            lhs: Operand::Reg(i),
            rhs: Operand::int(64, exit),
        },
    });

    let mut bb2 = BasicBlock::new(
        BlockId(2),
        Terminator::Br { target: BlockId(1), args: vec![Operand::Reg(ni)] },
    );
    bb2.insts.push(Inst::PtrOffset {
        dst: p,
        base: Operand::Reg(buf),
        index: Operand::Reg(i),
        elem: Type::int(32),
    });
    bb2.insts.push(Inst::Store {
        ty: Type::int(32),
        ptr: Operand::Reg(p),
        value: Operand::int(32, 0),
        align: 4, volatile: false
    });
    bb2.insts.push(Inst::Assign {
        dst: ni,
        ty: Type::int(64),
        value: csolver_ir::RValue::Bin {
            op: csolver_ir::BinOp::Add,
            lhs: Operand::Reg(i),
            rhs: Operand::int(64, 1),
        flags: Default::default(),
        },
    });

    let bb3 = BasicBlock::new(BlockId(3), Terminator::Return(None));

    Function {
        id: FuncId(0),
        name: "eq_exit_loop".into(),
        params: vec![],
        ret_ty: Type::Unit,
        blocks: vec![bb0, bb1, bb2, bb3],
        entry: BlockId(0),
    }
}
