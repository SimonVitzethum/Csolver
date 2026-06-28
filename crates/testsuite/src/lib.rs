//! # csolver-testsuite
//!
//! Shared MSIR fixtures that model real (often `unsafe`) Rust patterns at the
//! IR level, plus the integration tests in `tests/`. Keeping the fixtures in a
//! library lets multiple integration tests reuse them.
//!
//! As real frontends land (LLVM-IR, MIR), these hand-built fixtures are
//! progressively replaced by lowering actual Rust/`unsafe` programs.

use csolver_core::{RegionKind, SafetyProperty};
use csolver_ir::{
    BasicBlock, BinOp, BlockId, CmpOp, Condition, FuncId, Function, Inst, Module, Operand, RegId,
    RValue, Terminator, Type,
};

/// A single-block function with one `InBounds` safety check over `condition`.
pub fn single_check(name: &str, condition: Condition, note: &str) -> Function {
    let mut bb = BasicBlock::new(BlockId(0), Terminator::Return(None));
    bb.insts.push(Inst::SafetyCheck {
        property: SafetyProperty::InBounds,
        condition,
        note: note.into(),
    });
    Function {
        id: FuncId(0),
        name: name.into(),
        params: vec![(RegId(0), Type::int(64))],
        ret_ty: Type::Unit,
        blocks: vec![bb],
        entry: BlockId(0),
    }
}

/// `slice[3]` on a length-8 slice: provably in bounds.
pub fn provably_safe() -> Function {
    single_check(
        "provably_safe",
        Condition::Cmp {
            op: CmpOp::Ult,
            lhs: Operand::int(64, 3),
            rhs: Operand::int(64, 8),
        },
        "a[3], len 8",
    )
}

/// `slice[10]` on a length-8 slice: provably out of bounds.
pub fn provably_buggy() -> Function {
    single_check(
        "provably_buggy",
        Condition::Cmp {
            op: CmpOp::Ult,
            lhs: Operand::int(64, 10),
            rhs: Operand::int(64, 8),
        },
        "a[10], len 8",
    )
}

/// `slice[i]` with an unconstrained `i`: not decidable by intervals alone.
pub fn needs_solver() -> Function {
    single_check(
        "needs_solver",
        Condition::Cmp {
            op: CmpOp::Ult,
            lhs: Operand::Reg(RegId(0)),
            rhs: Operand::int(64, 8),
        },
        "a[i], len 8",
    )
}

/// A module bundling all three fixtures.
pub fn mixed_module() -> Module {
    let mut m = Module::new("mixed");
    m.functions.push(provably_safe());
    m.functions.push(provably_buggy());
    m.functions.push(needs_solver());
    m
}

/// An interprocedural module: `entry` allocates a buffer, obtains a pointer
/// into it from the wrapper `first`, and dereferences it. The function summary
/// for `first` lets `entry` keep the pointer's provenance across the call, so
/// `entry`'s dereference is proved memory-safe.
///
/// ```text
///   fn first(b: *i32) -> *i32 { b + 0 }
///   fn entry() { let buf = alloc [i32; 8]; let p = first(buf); *p = 0; }
/// ```
pub fn interproc_module() -> Module {
    // first(b: *i32) -> *i32 { q = b + 0 ; return q }
    let b = RegId(0);
    let q = RegId(1);
    let mut fb = BasicBlock::new(BlockId(0), Terminator::Return(Some(Operand::Reg(q))));
    fb.insts.push(Inst::PtrOffset {
        dst: q,
        base: Operand::Reg(b),
        index: Operand::int(64, 0),
        elem: Type::int(32),
    });
    let first = Function {
        id: FuncId(0),
        name: "first".into(),
        params: vec![(b, Type::ptr(Type::int(32)))],
        ret_ty: Type::ptr(Type::int(32)),
        blocks: vec![fb],
        entry: BlockId(0),
    };

    // entry() { buf = alloc i32*8 ; p = call first(buf) ; store 0 -> p ; return }
    let buf = RegId(0);
    let p = RegId(1);
    let mut eb = BasicBlock::new(BlockId(0), Terminator::Return(None));
    eb.insts.push(Inst::Alloc {
        dst: buf,
        region: RegionKind::Heap,
        elem: Type::int(32),
        count: Operand::int(64, 8),
        align: 4,
    });
    eb.insts.push(Inst::Call {
        dst: Some(p),
        callee: csolver_ir::Callee::Direct(FuncId(0)),
        args: vec![Operand::Reg(buf)],
        ret_ty: Type::ptr(Type::int(32)),
    });
    eb.insts.push(Inst::Store {
        ty: Type::int(32),
        ptr: Operand::Reg(p),
        value: Operand::int(32, 0),
        align: 4,
    });
    let entry = Function {
        id: FuncId(1),
        name: "entry".into(),
        params: vec![],
        ret_ty: Type::Unit,
        blocks: vec![eb],
        entry: BlockId(0),
    };

    let mut m = Module::new("interproc");
    m.functions.push(first);
    m.functions.push(entry);
    m
}

/// `guarded_get(i, len)`: the slice access `a[i]` is performed only on the
/// branch where the guard `i < len` holds — the classic pattern that intervals
/// cannot prove (i, len are unconstrained inputs) but symbolic execution can.
///
/// ```text
///   bb0: c = i <u len ; condbr c -> bb1 / bb2
///   bb1: safetycheck InBounds (i <u len) ; return   // a[i], reached under guard
///   bb2: return
/// ```
pub fn guarded_get() -> Function {
    let i = RegId(0);
    let len = RegId(1);
    let c = RegId(2);

    let mut bb0 = BasicBlock::new(
        BlockId(0),
        Terminator::CondBr {
            cond: Operand::Reg(c),
            then_blk: BlockId(1),
            then_args: vec![],
            else_blk: BlockId(2),
            else_args: vec![],
        },
    );
    bb0.insts.push(Inst::Assign {
        dst: c,
        ty: Type::Bool,
        value: csolver_ir::RValue::Cmp {
            op: CmpOp::Ult,
            lhs: Operand::Reg(i),
            rhs: Operand::Reg(len),
        },
    });

    let mut bb1 = BasicBlock::new(BlockId(1), Terminator::Return(None));
    bb1.insts.push(Inst::SafetyCheck {
        property: SafetyProperty::InBounds,
        condition: Condition::Cmp {
            op: CmpOp::Ult,
            lhs: Operand::Reg(i),
            rhs: Operand::Reg(len),
        },
        note: "a[i] under guard i < len".into(),
    });

    let bb2 = BasicBlock::new(BlockId(2), Terminator::Return(None));

    Function {
        id: FuncId(0),
        name: "guarded_get".into(),
        params: vec![(i, Type::int(64)), (len, Type::int(64))],
        ret_ty: Type::Unit,
        blocks: vec![bb0, bb1, bb2],
        entry: BlockId(0),
    }
}

/// `safe_buffer_store(i, n)`: allocate `n` `i32`s, then store `0` into
/// `buf[i]` only on the path guarded by `0 <= i` *and* `i < n`. Every implied
/// memory obligation (non-null, live, in-bounds, aligned, writable) plus the
/// pointer arithmetic is provable by the symbolic memory model.
///
/// ```text
///   bb0: buf = alloc i32 * n ; c0 = 0 <= i ; condbr c0 -> bb1 / bb3
///   bb1: c1 = i < n          ; condbr c1 -> bb2 / bb3
///   bb2: p = buf + i*4       ; store i32 0 -> p ; return
///   bb3: return
/// ```
pub fn safe_buffer_store() -> Function {
    let i = RegId(0);
    let n = RegId(1);
    let buf = RegId(2);
    let c0 = RegId(3);
    let c1 = RegId(4);
    let p = RegId(5);

    let mut bb0 = BasicBlock::new(
        BlockId(0),
        Terminator::CondBr {
            cond: Operand::Reg(c0),
            then_blk: BlockId(1),
            then_args: vec![],
            else_blk: BlockId(3),
            else_args: vec![],
        },
    );
    bb0.insts.push(Inst::Alloc {
        dst: buf,
        region: RegionKind::Heap,
        elem: Type::int(32),
        count: Operand::Reg(n),
        align: 4,
    });
    bb0.insts.push(Inst::Assign {
        dst: c0,
        ty: Type::Bool,
        value: csolver_ir::RValue::Cmp {
            op: CmpOp::Sle,
            lhs: Operand::int(64, 0),
            rhs: Operand::Reg(i),
        },
    });

    let mut bb1 = BasicBlock::new(
        BlockId(1),
        Terminator::CondBr {
            cond: Operand::Reg(c1),
            then_blk: BlockId(2),
            then_args: vec![],
            else_blk: BlockId(3),
            else_args: vec![],
        },
    );
    bb1.insts.push(Inst::Assign {
        dst: c1,
        ty: Type::Bool,
        value: csolver_ir::RValue::Cmp {
            op: CmpOp::Slt,
            lhs: Operand::Reg(i),
            rhs: Operand::Reg(n),
        },
    });

    let mut bb2 = BasicBlock::new(BlockId(2), Terminator::Return(None));
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
        align: 4,
    });

    let bb3 = BasicBlock::new(BlockId(3), Terminator::Return(None));

    Function {
        id: FuncId(0),
        name: "safe_buffer_store".into(),
        params: vec![(i, Type::int(64)), (n, Type::int(64))],
        ret_ty: Type::Unit,
        blocks: vec![bb0, bb1, bb2, bb3],
        entry: BlockId(0),
    }
}

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
        align: 4,
    });
    bb2.insts.push(Inst::Assign {
        dst: nj,
        ty: Type::int(64),
        value: csolver_ir::RValue::Bin {
            op: csolver_ir::BinOp::Add,
            lhs: Operand::Reg(j),
            rhs: Operand::int(64, 1),
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
        align: 8,
    });
    bb0.insts.push(Inst::Load {
        dst: p,
        ty: Type::ptr(Type::int(8)),
        ptr: Operand::Reg(slot),
        align: 8,
    });
    bb0.insts.push(Inst::Store {
        ty: Type::int(8),
        ptr: Operand::Reg(p),
        value: Operand::int(8, 0),
        align: 1,
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
        align: 1,
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
        align: 1,
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
