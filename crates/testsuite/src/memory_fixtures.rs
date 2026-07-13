use super::*;

/// `masked_index_store(x)`: write `buf[x & 7]` into a `[i8; 8]`. The masked
/// index is provably in `[0, 7]`, so every access is in bounds — but *only*
/// bit-precisely: the linear decision procedure abstracts the bitwise `&` as an
/// opaque value and cannot bound it, so it leaves the access UNKNOWN. The
/// bit-precise SAT backend decides the mask exactly and proves it PASS, with no
/// `linear-no-overflow` assumption. This is the canonical case the pure-Rust
/// bit-blasting backend unlocks.
///
/// ```text
///   buf = alloc i8 * 8
///   j   = x & 7            // j in [0, 7]
///   p   = buf + j          // (elem size 1)
///   store 0 -> p           // in bounds, by bit-precise reasoning about `& 7`
/// ```
pub fn masked_index_store() -> Function {
    let x = RegId(0);
    let buf = RegId(1);
    let j = RegId(2);
    let p = RegId(3);
    let mut bb0 = BasicBlock::new(BlockId(0), Terminator::Return(None));
    bb0.insts.push(Inst::Alloc {
        dst: buf,
        region: RegionKind::Heap,
        elem: Type::int(8),
        count: Operand::int(64, 8),
        align: 1,
    });
    bb0.insts.push(Inst::Assign {
        dst: j,
        ty: Type::int(64),
        value: RValue::Bin {
            op: BinOp::And,
            lhs: Operand::Reg(x),
            rhs: Operand::int(64, 7),
        flags: Default::default(),
        },
    });
    bb0.insts.push(Inst::PtrOffset {
        dst: p,
        base: Operand::Reg(buf),
        index: Operand::Reg(j),
        elem: Type::int(8),
    });
    bb0.insts.push(Inst::Store {
        ty: Type::int(8),
        ptr: Operand::Reg(p),
        value: Operand::int(8, 0),
        align: 1, volatile: false
    });
    Function {
        id: FuncId(0),
        name: "masked_index_store".into(),
        params: vec![(x, Type::int(64))],
        ret_ty: Type::Unit,
        blocks: vec![bb0],
        entry: BlockId(0),
    }
}

/// `oob_mask_check(x)`: the bounds check `(x | 8) < 8` over a length-8 buffer.
/// Setting bit 3 forces `x | 8 >= 8`, so the index is **never** in bounds — the
/// check is false for *every* input, a definite violation. Intervals cannot see
/// it (`|` is opaque to them), but the bit-precise symbolic engine proves the
/// check is always violated on this exact path and produces a concrete
/// counterexample (e.g. `x = 0`, giving index 8). The verdict is FAIL with a
/// witness — the symbolic analogue of [`provably_buggy`], reachable only because
/// the index is computed by a bitwise op.
///
/// ```text
///   j = x | 8                       // j >= 8 always
///   safety_check InBounds: j < 8    // never holds
/// ```
pub fn oob_mask_check() -> Function {
    let x = RegId(0);
    let j = RegId(1);
    let mut bb0 = BasicBlock::new(BlockId(0), Terminator::Return(None));
    bb0.insts.push(Inst::Assign {
        dst: j,
        ty: Type::int(64),
        value: RValue::Bin {
            op: BinOp::Or,
            lhs: Operand::Reg(x),
            rhs: Operand::int(64, 8),
        flags: Default::default(),
        },
    });
    bb0.insts.push(Inst::SafetyCheck {
        property: SafetyProperty::InBounds,
        condition: Condition::Cmp {
            op: CmpOp::Ult,
            lhs: Operand::Reg(j),
            rhs: Operand::int(64, 8),
        },
        note: "index x|8 into a length-8 buffer".into(),
    });
    Function {
        id: FuncId(0),
        name: "oob_mask_check".into(),
        params: vec![(x, Type::int(64))],
        ret_ty: Type::Unit,
        blocks: vec![bb0],
        entry: BlockId(0),
    }
}

/// `oob_index_store(i)`: the unguarded write `buf[i] = 0` into a `[i32; 8]`,
/// with `i` an unconstrained parameter. The access executes for every input, so
/// any `i >= 8` is a genuine out-of-bounds write. The symbolic engine cannot
/// prove the access in bounds and, on this exact path with a concrete-size
/// region, refutes it with a concrete counterexample (e.g. `i = 8`). The verdict
/// is FAIL with a witness — the memory-access analogue of [`provably_buggy`].
///
/// ```text
///   buf = alloc i32 * 8        // size 32 bytes
///   p   = buf + i*4            // out of bounds when i >= 8
///   store 0 -> p
/// ```
pub fn oob_index_store() -> Function {
    let i = RegId(0);
    let buf = RegId(1);
    let p = RegId(2);
    let mut bb0 = BasicBlock::new(BlockId(0), Terminator::Return(None));
    bb0.insts.push(Inst::Alloc {
        dst: buf,
        region: RegionKind::Heap,
        elem: Type::int(32),
        count: Operand::int(64, 8),
        align: 4,
    });
    bb0.insts.push(Inst::PtrOffset {
        dst: p,
        base: Operand::Reg(buf),
        index: Operand::Reg(i),
        elem: Type::int(32),
    });
    bb0.insts.push(Inst::Store {
        ty: Type::int(32),
        ptr: Operand::Reg(p),
        value: Operand::int(32, 0),
        align: 4, volatile: false
    });
    Function {
        id: FuncId(0),
        name: "oob_index_store".into(),
        params: vec![(i, Type::int(64))],
        ret_ty: Type::Unit,
        blocks: vec![bb0],
        entry: BlockId(0),
    }
}

/// `oob_dynamic_store(n, i)`: the unguarded write `buf[i] = 0` into a freshly
/// allocated `[i32; n]` of **dynamic** length `n`. Out of bounds whenever
/// `i >= n`. The region's byte size `n * 4` is symbolic, but a successful
/// allocation guarantees `n * 4 <= isize::MAX` (so it does not wrap); with that
/// premise the symbolic engine refutes the access with a concrete witness for
/// both `n` and `i` (e.g. `n = 0, i = 0`). The verdict is FAIL — OOB
/// counterexamples now reach dynamically-sized buffers, not just fixed arrays.
///
/// ```text
///   buf = alloc i32 * n        // symbolic size n*4 (<= isize::MAX)
///   p   = buf + i*4            // out of bounds when i >= n
///   store 0 -> p
/// ```
pub fn oob_dynamic_store() -> Function {
    let n = RegId(0);
    let i = RegId(1);
    let buf = RegId(2);
    let p = RegId(3);
    let mut bb0 = BasicBlock::new(BlockId(0), Terminator::Return(None));
    bb0.insts.push(Inst::Alloc {
        dst: buf,
        region: RegionKind::Heap,
        elem: Type::int(32),
        count: Operand::Reg(n),
        align: 4,
    });
    bb0.insts.push(Inst::PtrOffset {
        dst: p,
        base: Operand::Reg(buf),
        index: Operand::Reg(i),
        elem: Type::int(32),
    });
    bb0.insts.push(Inst::Store {
        ty: Type::int(32),
        ptr: Operand::Reg(p),
        value: Operand::int(32, 0),
        align: 4, volatile: false
    });
    Function {
        id: FuncId(0),
        name: "oob_dynamic_store".into(),
        params: vec![(n, Type::int(64)), (i, Type::int(64))],
        ret_ty: Type::Unit,
        blocks: vec![bb0],
        entry: BlockId(0),
    }
}

/// `dangling_store()`: allocate, free, then write through the freed pointer —
/// a use-after-free. The free itself is fine; the later store cannot be proved
/// temporally safe, so it stays UNKNOWN (this increment never refutes).
pub fn dangling_store() -> Function {
    let buf = RegId(0);
    let mut bb0 = BasicBlock::new(BlockId(0), Terminator::Return(None));
    bb0.insts.push(Inst::Alloc {
        dst: buf,
        region: RegionKind::Heap,
        elem: Type::int(8),
        count: Operand::int(64, 8),
        align: 1,
    });
    bb0.insts.push(Inst::Dealloc {
        region: RegionKind::Heap,
        ptr: Operand::Reg(buf),
    });
    bb0.insts.push(Inst::Store {
        ty: Type::int(8),
        ptr: Operand::Reg(buf),
        value: Operand::int(8, 0),
        align: 1, volatile: false
    });
    Function {
        id: FuncId(0),
        name: "dangling_store".into(),
        params: vec![],
        ret_ty: Type::Unit,
        blocks: vec![bb0],
        entry: BlockId(0),
    }
}
