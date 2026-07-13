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
        ret_ref: None,
    });
    eb.insts.push(Inst::Store {
        ty: Type::int(32),
        ptr: Operand::Reg(p),
        value: Operand::int(32, 0),
        align: 4, volatile: false
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
        align: 4, volatile: false
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

/// `ptr_walk_loop()`: the fully-optimized iterator shape — walk a `[i32; 8]` by
/// a moving pointer until it reaches the end pointer.
///
/// ```text
///   bb0: buf = alloc i32 * 8 ; end = buf + 8 ; br bb1(buf)
///   bb1(iter): c = (iter == end) ; condbr c -> bb3 / bb2
///   bb2: x = load iter ; nx = iter + 1 ; br bb1(nx)
///   bb3: return
/// ```
///
/// The loop exits on the **pointer** equality `iter == end`; the equality-exit
/// pointer-induction analysis keeps `iter`'s region provenance with a bounded,
/// stride-aligned offset (`0 ≤ o ≤ end_off ≤ size`, `o ≡ 0 mod 4`), and the guard
/// `iter != end` then proves the `load iter` in bounds → PASS.
pub fn ptr_walk_loop() -> Function {
    ptr_walk_to(8)
}

/// As [`ptr_walk_loop`] but the end pointer is past the buffer (`buf + 16` over a
/// `[i32; 8]`): the walk would read out of bounds, so the load must NOT be
/// proved PASS. The `end_off ≤ size` side-condition fails, so the pointer keeps
/// opaque (the bounded offset is never installed) and the access stays UNKNOWN.
pub fn ptr_walk_loop_oob() -> Function {
    ptr_walk_to(16)
}

fn ptr_walk_to(end_elems: u128) -> Function {
    let buf = RegId(0);
    let end = RegId(1);
    let iter = RegId(2);
    let c = RegId(3);
    let nx = RegId(4);
    let x = RegId(5);

    let mut bb0 = BasicBlock::new(
        BlockId(0),
        Terminator::Br { target: BlockId(1), args: vec![Operand::Reg(buf)] },
    );
    bb0.insts.push(Inst::Alloc {
        dst: buf,
        region: RegionKind::Heap,
        elem: Type::int(32),
        count: Operand::int(64, 8),
        align: 4,
    });
    bb0.insts.push(Inst::PtrOffset {
        dst: end,
        base: Operand::Reg(buf),
        index: Operand::int(64, end_elems),
        elem: Type::int(32),
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
    bb1.params = vec![(iter, Type::ptr(Type::int(32)))];
    bb1.insts.push(Inst::Assign {
        dst: c,
        ty: Type::Bool,
        value: csolver_ir::RValue::Cmp {
            op: CmpOp::Eq,
            lhs: Operand::Reg(iter),
            rhs: Operand::Reg(end),
        },
    });

    let mut bb2 = BasicBlock::new(
        BlockId(2),
        Terminator::Br { target: BlockId(1), args: vec![Operand::Reg(nx)] },
    );
    bb2.insts.push(Inst::Load {
        dst: x,
        ty: Type::int(32),
        ptr: Operand::Reg(iter),
        align: 4, volatile: false
    });
    bb2.insts.push(Inst::PtrOffset {
        dst: nx,
        base: Operand::Reg(iter),
        index: Operand::int(64, 1),
        elem: Type::int(32),
    });

    let bb3 = BasicBlock::new(BlockId(3), Terminator::Return(None));

    Function {
        id: FuncId(0),
        name: "ptr_walk_loop".into(),
        params: vec![],
        ret_ty: Type::Unit,
        blocks: vec![bb0, bb1, bb2, bb3],
        entry: BlockId(0),
    }
}

/// `ptr_walk_bottom_loop(n)`: the **rotated** (`-O`) iterator shape — the load
/// precedes the `next == end` exit check, guarded by an `is_empty` preheader
/// test. Walks an `alloc [i32; n]` of a *symbolic* length.
///
/// ```text
///   bb0: buf = alloc i32 * n ; end = buf + n ; empty = (buf == end)
///        condbr empty -> bb2 / bb1(buf)
///   bb1(iter): x = load iter ; nx = iter + 1 ; atend = (nx == end)
///              condbr atend -> bb2 / bb1(nx)
///   bb2: return
/// ```
///
/// The bound `iter + stride ≤ end` holds because the loop is entered only when
/// `buf != end` (the preheader guard, which the engine reads from the path
/// condition to prove the base case). Verifies PASS.
pub fn ptr_walk_bottom_loop() -> Function {
    ptr_walk_bottom_impl(true)
}

/// As [`ptr_walk_bottom_loop`] but **without** the `is_empty` preheader guard:
/// the load precedes the exit check, so on an empty range (`n == 0`) it would
/// read out of bounds. The base case `0 + stride ≤ end` is then unprovable, so
/// the bounded offset is never installed and the load is not proved PASS — the
/// soundness boundary of the rotated form.
pub fn ptr_walk_bottom_unguarded() -> Function {
    ptr_walk_bottom_impl(false)
}

fn ptr_walk_bottom_impl(guard: bool) -> Function {
    let n = RegId(0);
    let buf = RegId(1);
    let end = RegId(2);
    let empty = RegId(3);
    let iter = RegId(4);
    let x = RegId(5);
    let nx = RegId(6);
    let atend = RegId(7);

    let bb0_term = if guard {
        Terminator::CondBr {
            cond: Operand::Reg(empty),
            then_blk: BlockId(2),
            then_args: vec![],
            else_blk: BlockId(1),
            else_args: vec![Operand::Reg(buf)],
        }
    } else {
        Terminator::Br { target: BlockId(1), args: vec![Operand::Reg(buf)] }
    };
    let mut bb0 = BasicBlock::new(BlockId(0), bb0_term);
    bb0.insts.push(Inst::Alloc {
        dst: buf,
        region: RegionKind::Heap,
        elem: Type::int(32),
        count: Operand::Reg(n),
        align: 4,
    });
    bb0.insts.push(Inst::PtrOffset {
        dst: end,
        base: Operand::Reg(buf),
        index: Operand::Reg(n),
        elem: Type::int(32),
    });
    if guard {
        bb0.insts.push(Inst::Assign {
            dst: empty,
            ty: Type::Bool,
            value: csolver_ir::RValue::Cmp {
                op: CmpOp::Eq,
                lhs: Operand::Reg(buf),
                rhs: Operand::Reg(end),
            },
        });
    }

    let mut bb1 = BasicBlock::new(
        BlockId(1),
        Terminator::CondBr {
            cond: Operand::Reg(atend),
            then_blk: BlockId(2),
            then_args: vec![],
            else_blk: BlockId(1),
            else_args: vec![Operand::Reg(nx)],
        },
    );
    bb1.params = vec![(iter, Type::ptr(Type::int(32)))];
    bb1.insts.push(Inst::Load { dst: x, ty: Type::int(32), ptr: Operand::Reg(iter), align: 4 , volatile: false});
    bb1.insts.push(Inst::PtrOffset {
        dst: nx,
        base: Operand::Reg(iter),
        index: Operand::int(64, 1),
        elem: Type::int(32),
    });
    bb1.insts.push(Inst::Assign {
        dst: atend,
        ty: Type::Bool,
        value: csolver_ir::RValue::Cmp {
            op: CmpOp::Eq,
            lhs: Operand::Reg(nx),
            rhs: Operand::Reg(end),
        },
    });

    let bb2 = BasicBlock::new(BlockId(2), Terminator::Return(None));

    Function {
        id: FuncId(0),
        name: "ptr_walk_bottom".into(),
        params: vec![(n, Type::int(64))],
        ret_ty: Type::Unit,
        blocks: vec![bb0, bb1, bb2],
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
