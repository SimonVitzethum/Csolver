//! Field-sensitive Andersen points-to analysis.
//!
//! **P1** of the sound `obj->ops->fn()` devirtualisation (see
//! `docs/pointsto-devirt-design.md`). A flow-insensitive, inclusion-based (subset)
//! points-to relation over *nodes*: pointer variables and abstract memory objects.
//! A **field cell** `(object, byte offset)` is a distinct node, created on demand,
//! which gives field sensitivity (`obj.ops` stays separate from `obj.other`).
//!
//! The result **over-approximates** the real points-to relation. That is exactly
//! what makes a *singleton* points-to set sound to act on: an over-approximation of
//! size one contains the real target and nothing else, so it *is* the real target.
//! A points-to set that is empty, has more than one element, or contains the
//! designated [`PointsTo::top`] object is **not** resolvable — the field is
//! ambiguous or may be written through an unknown pointer (poisoned).
//!
//! This module is intentionally standalone and unit-tested in isolation: it changes
//! no verdict on its own. Constraint *generation* from MSIR and the executor
//! integration are later phases (P2–P4).

use std::collections::{HashMap, HashSet};

/// A node in the points-to graph: a pointer variable or an abstract memory cell.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct Node(pub u32);

/// A field-sensitive, inclusion-based points-to solver.
///
/// Build it by declaring variables/objects and adding constraints, then call
/// [`solve`](Self::solve) and query [`points_to`](Self::points_to) /
/// [`singleton_object`](Self::singleton_object).
pub struct PointsTo {
    /// Number of nodes allocated.
    n: u32,
    /// `pts[node] = { nodes it may point to }`.
    pts: Vec<HashSet<Node>>,
    /// `p ⊇ {obj}` — `p = &obj`.
    addr: Vec<(Node, Node)>,
    /// `dst ⊇ src` — `dst = src` (a copy / cast).
    copy: Vec<(Node, Node)>,
    /// `dst ⊇ { field(o, off) : o ∈ pts(src) }` — `dst = &src->field` (a gep).
    gep: Vec<(Node, Node, u64)>,
    /// `dst ⊇ *src` — `dst = *src` (a load).
    load: Vec<(Node, Node)>,
    /// `*ptr ⊇ value` — `*ptr = value` (a store of `value` through `ptr`).
    store: Vec<(Node, Node)>,
    /// Interned field cells `(object, byte offset) → node`.
    field_cell: HashMap<(Node, u64), Node>,
    /// Optional human names for objects (debug / query convenience).
    name: HashMap<Node, String>,
    /// The designated **TOP** object: an unknown / over-approximated target. A field
    /// that may be written through an unresolved pointer is given TOP by the constraint
    /// generator, so its points-to set is never a clean singleton (poisoned). TOP is
    /// absorbing: any field of TOP is TOP, and a load/store through TOP yields TOP.
    top: Node,
    /// Objects whose fields may be written through an **unknown offset** (a symbolic gep, a
    /// `memcpy`/`memset`, an opaque writing call): every field cell of such an object carries
    /// TOP, so no field of it is ever a clean singleton. This is what keeps the analysis sound in
    /// the presence of byte-level / aliased writes it cannot resolve to a specific field.
    poisoned: HashSet<Node>,
}

/// The reserved offset for an **unknown / symbolic** field access: a gep with this offset poisons
/// the whole base object (any of its fields may be the target).
pub const ANY_OFFSET: u64 = u64::MAX;

impl Default for PointsTo {
    fn default() -> Self {
        Self::new()
    }
}

impl PointsTo {
    /// A fresh solver with the [`top`](Self::top) object pre-allocated as node 0.
    pub fn new() -> PointsTo {
        let mut p = PointsTo {
            n: 0,
            pts: Vec::new(),
            addr: Vec::new(),
            copy: Vec::new(),
            gep: Vec::new(),
            load: Vec::new(),
            store: Vec::new(),
            field_cell: HashMap::new(),
            name: HashMap::new(),
            top: Node(0),
            poisoned: HashSet::new(),
        };
        let top = p.fresh();
        p.top = top;
        p.name.insert(top, "<top>".to_string());
        p
    }

    /// The absorbing **TOP** object (an unknown / over-approximated target).
    pub fn top(&self) -> Node {
        self.top
    }

    fn fresh(&mut self) -> Node {
        let id = Node(self.n);
        self.n += 1;
        self.pts.push(HashSet::new());
        id
    }

    /// A new pointer variable (a temporary / SSA register).
    pub fn new_var(&mut self) -> Node {
        self.fresh()
    }

    /// A new abstract memory object (a global, allocation site, or stack local).
    pub fn new_object(&mut self, name: impl Into<String>) -> Node {
        let o = self.fresh();
        self.name.insert(o, name.into());
        o
    }

    /// The name recorded for a node, if any.
    pub fn name_of(&self, n: Node) -> Option<&str> {
        self.name.get(&n).map(String::as_str)
    }

    /// `p = &obj` — `obj ∈ pts(p)`.
    pub fn address_of(&mut self, p: Node, obj: Node) {
        self.addr.push((p, obj));
    }

    /// `dst = src` — `pts(src) ⊆ pts(dst)`.
    pub fn assign(&mut self, dst: Node, src: Node) {
        self.copy.push((dst, src));
    }

    /// `dst = &src->field` at byte `offset` — `dst ⊇ { field(o, offset) : o ∈ pts(src) }`.
    pub fn gep(&mut self, dst: Node, src: Node, offset: u64) {
        self.gep.push((dst, src, offset));
    }

    /// `dst = *src` — `∀ o ∈ pts(src): pts(o) ⊆ pts(dst)`.
    pub fn load(&mut self, dst: Node, src: Node) {
        self.load.push((dst, src));
    }

    /// `*ptr = value` — `∀ o ∈ pts(ptr): pts(value) ⊆ pts(o)`.
    pub fn store(&mut self, value: Node, ptr: Node) {
        self.store.push((value, ptr));
    }

    /// The interned field cell `(obj, offset)`. A field of TOP is TOP (absorbing). An
    /// [`ANY_OFFSET`] access poisons the whole object (its target is unknown) and resolves to TOP.
    /// Offset 0 is the object node itself, so a bare object pointer and its first field coincide.
    fn intern_field(&mut self, obj: Node, offset: u64) -> Node {
        if obj == self.top {
            return self.top;
        }
        if offset == ANY_OFFSET {
            self.poison(obj);
            return self.top;
        }
        if offset == 0 {
            return obj;
        }
        if let Some(&c) = self.field_cell.get(&(obj, offset)) {
            return c;
        }
        let c = self.fresh();
        self.field_cell.insert((obj, offset), c);
        self.name.insert(c, format!("{}.{offset}", self.name.get(&obj).map_or("?", |s| s.as_str())));
        if self.poisoned.contains(&obj) {
            self.pts[c.0 as usize].insert(self.top);
        }
        c
    }

    /// Mark an object's fields as possibly written through an unknown offset: TOP is added to every
    /// current and future field cell of it (and to the object node itself, its offset-0 cell), so
    /// no field of it is ever a clean singleton. Sound over-approximation for byte-level / aliased
    /// writes the generator cannot resolve to a specific field.
    pub fn poison(&mut self, obj: Node) {
        if obj == self.top || !self.poisoned.insert(obj) {
            return;
        }
        let top = self.top;
        self.pts[obj.0 as usize].insert(top);
        let cells: Vec<Node> =
            self.field_cell.iter().filter(|((o, _), _)| *o == obj).map(|(_, &c)| c).collect();
        for c in cells {
            self.pts[c.0 as usize].insert(top);
        }
    }

    /// Query a previously-interned field cell without creating one.
    pub fn field_cell(&self, obj: Node, offset: u64) -> Option<Node> {
        self.field_cell.get(&(obj, offset)).copied()
    }

    fn add(&mut self, dst: Node, obj: Node) -> bool {
        self.pts[dst.0 as usize].insert(obj)
    }

    fn union(&mut self, dst: Node, src: Node) -> bool {
        if dst == src {
            return false;
        }
        let srcs: Vec<Node> = self.pts[src.0 as usize].iter().copied().collect();
        let mut changed = false;
        for o in srcs {
            changed |= self.pts[dst.0 as usize].insert(o);
        }
        changed
    }

    /// Solve the constraints to a fixpoint (naive round-robin — correct and simple;
    /// each round is monotone and the lattice is finite, so it terminates). Field
    /// cells created mid-solve start empty and are filled by later rounds.
    pub fn solve(&mut self) {
        for i in 0..self.addr.len() {
            let (p, o) = self.addr[i];
            self.add(p, o);
        }
        let mut changed = true;
        while changed {
            changed = false;
            for i in 0..self.copy.len() {
                let (d, s) = self.copy[i];
                changed |= self.union(d, s);
            }
            for i in 0..self.gep.len() {
                let (d, s, off) = self.gep[i];
                for o in self.pts[s.0 as usize].iter().copied().collect::<Vec<_>>() {
                    let cell = self.intern_field(o, off);
                    changed |= self.add(d, cell);
                }
            }
            for i in 0..self.load.len() {
                let (d, s) = self.load[i];
                for o in self.pts[s.0 as usize].iter().copied().collect::<Vec<_>>() {
                    changed |= self.union(d, o);
                }
            }
            for i in 0..self.store.len() {
                let (v, p) = self.store[i];
                for o in self.pts[p.0 as usize].iter().copied().collect::<Vec<_>>() {
                    changed |= self.union(o, v);
                }
            }
        }
    }

    /// The points-to set of a node (valid after [`solve`](Self::solve)).
    pub fn points_to(&self, n: Node) -> &HashSet<Node> {
        &self.pts[n.0 as usize]
    }

    /// The **single object** `n` may point to, if its points-to set is a clean
    /// singleton — exactly one element and not [`top`](Self::top). This is the
    /// resolvable case: an over-approximation of size one is exact. `None` for an
    /// empty, ambiguous (`> 1`), or poisoned (contains TOP) set.
    pub fn singleton_object(&self, n: Node) -> Option<Node> {
        let set = &self.pts[n.0 as usize];
        match (set.len(), set.iter().next()) {
            (1, Some(&o)) if o != self.top => Some(o),
            _ => None,
        }
    }
}

// ---------------------------------------------------------------------------
// P2: constraint generation from MSIR.
// ---------------------------------------------------------------------------

use csolver_ir::{
    Callee, Const, DataLayout, FuncId, Inst, Module, Operand, RValue, RegId, Type,
};

const LAYOUT: DataLayout = DataLayout::LP64;

/// The whole-module points-to result: the solved relation plus the register→node and
/// object→global maps needed to resolve a register to the single global it points to.
pub struct ModulePointsTo {
    pt: PointsTo,
    reg_node: HashMap<(FuncId, RegId), Node>,
    obj_global: HashMap<Node, String>,
}

impl ModulePointsTo {
    /// The **single global** that register `r` of function `f` provably points to (its points-to
    /// set is a clean singleton object that is a named global), if any. This is the resolvable
    /// devirtualisation case — sound because a singleton over-approximation is exact. `None` when
    /// the register is unresolved, ambiguous, or points to a non-global / poisoned object.
    pub fn devirt_global(&self, f: FuncId, r: RegId) -> Option<&str> {
        let &n = self.reg_node.get(&(f, r))?;
        let obj = self.pt.singleton_object(n)?;
        self.obj_global.get(&obj).map(String::as_str)
    }

    /// The underlying solver (for tests / further queries).
    pub fn solver(&self) -> &PointsTo {
        &self.pt
    }
}

struct Builder {
    pt: PointsTo,
    reg_node: HashMap<(FuncId, RegId), Node>,
    global_obj: HashMap<String, Node>,
    obj_global: HashMap<Node, String>,
}

impl Builder {
    fn reg(&mut self, f: FuncId, r: RegId) -> Node {
        if let Some(&n) = self.reg_node.get(&(f, r)) {
            return n;
        }
        let n = self.pt.new_var();
        self.reg_node.insert((f, r), n);
        n
    }

    fn global(&mut self, name: &str) -> Node {
        if let Some(&o) = self.global_obj.get(name) {
            return o;
        }
        let o = self.pt.new_object(name);
        self.global_obj.insert(name.to_string(), o);
        self.obj_global.insert(o, name.to_string());
        o
    }

    /// A node standing for the pointer *value* of an operand: a register maps to its node; the
    /// address of a global becomes a fresh var pointing at that global; anything else is unknown.
    fn operand_ptr(&mut self, f: FuncId, op: &Operand) -> Option<Node> {
        match op {
            Operand::Reg(r) => Some(self.reg(f, *r)),
            Operand::Const(Const::Symbol(g)) | Operand::Const(Const::SymbolOffset(g, _)) => {
                let obj = self.global(g);
                let v = self.pt.new_var();
                self.pt.address_of(v, obj);
                Some(v)
            }
            _ => None,
        }
    }
}

/// The constant byte offset of a `PtrOffset` (`index * stride`), or `None` if the index is not a
/// compile-time constant (a symbolic array index — an unknown field).
fn const_byte_offset(index: &Operand, elem: &Type) -> Option<u64> {
    let Operand::Const(Const::Int(bv)) = index else { return None };
    let k = u64::try_from(bv.unsigned()).ok()?;
    let stride = elem.stride_bytes(&LAYOUT).unwrap_or(1);
    k.checked_mul(stride)
}

/// Build and solve the field-sensitive points-to relation for a whole module (P2). Direct calls
/// connect each argument to the callee's matching parameter (interprocedural, so a value set up
/// in one function and dispatched in another is tracked); an **opaque** call (indirect / external)
/// conservatively poisons its pointer arguments — it may write through them, and without a summary
/// the analysis cannot know it does not. Sound for a module that is the whole (closed) program.
pub fn analyze_module(m: &Module) -> ModulePointsTo {
    let mut b = Builder {
        pt: PointsTo::new(),
        reg_node: HashMap::new(),
        global_obj: HashMap::new(),
        obj_global: HashMap::new(),
    };
    // Poison an object's fields through a pointer operand (a byte/symbolic/opaque write): a gep at
    // the reserved unknown offset marks every reachable object poisoned when the relation is solved.
    let poison_through = |b: &mut Builder, f: FuncId, op: &Operand| {
        if let Some(p) = b.operand_ptr(f, op) {
            let anyf = b.pt.new_var();
            b.pt.gep(anyf, p, ANY_OFFSET);
        }
    };
    for f in &m.functions {
        let fid = f.id;
        for inst in f.blocks.iter().flat_map(|bl| &bl.insts) {
            match inst {
                Inst::Alloc { dst, .. } => {
                    let o = b.pt.new_object("alloc");
                    let d = b.reg(fid, *dst);
                    b.pt.address_of(d, o);
                }
                Inst::Assign { dst, value, .. } => {
                    let src = match value {
                        RValue::Use(op) | RValue::Cast { operand: op, .. } => b.operand_ptr(fid, op),
                        _ => None,
                    };
                    if let Some(s) = src {
                        let d = b.reg(fid, *dst);
                        b.pt.assign(d, s);
                    }
                }
                Inst::PtrOffset { dst, base: Operand::Reg(bs), index, elem } => {
                    let base = b.reg(fid, *bs);
                    let off = const_byte_offset(index, elem).unwrap_or(ANY_OFFSET);
                    let d = b.reg(fid, *dst);
                    b.pt.gep(d, base, off);
                }
                // A typed MIR field access carries no byte offset here — conservatively unknown.
                Inst::FieldPtr { dst, base: Operand::Reg(bs), .. } => {
                    let base = b.reg(fid, *bs);
                    let d = b.reg(fid, *dst);
                    b.pt.gep(d, base, ANY_OFFSET);
                }
                Inst::Load { dst, ty, ptr: Operand::Reg(p), .. } if ty.is_ptr() => {
                    let pn = b.reg(fid, *p);
                    let d = b.reg(fid, *dst);
                    b.pt.load(d, pn);
                }
                Inst::Store { ptr: Operand::Reg(p), value, .. } => {
                    if let Some(v) = b.operand_ptr(fid, value) {
                        let pn = b.reg(fid, *p);
                        b.pt.store(v, pn);
                    }
                }
                // A bulk write (memcpy/memset) writes an unknown extent of its destination.
                Inst::MemIntrinsic { dst, .. } => poison_through(&mut b, fid, dst),
                Inst::Call { dst, callee: Callee::Direct(g), args, .. } => {
                    // Connect each argument to the callee's matching parameter (interprocedural).
                    if let Some(callee) = m.functions.iter().find(|c| c.id == *g) {
                        for (i, arg) in args.iter().enumerate() {
                            if let (Some((preg, _)), Some(an)) =
                                (callee.params.get(i), b.operand_ptr(fid, arg))
                            {
                                let pn = b.reg(*g, *preg);
                                b.pt.assign(pn, an);
                            }
                        }
                    }
                    // The call result is an unknown pointer (return modelling is a later refinement).
                    if let Some(d) = dst {
                        let dn = b.reg(fid, *d);
                        let top = b.pt.top();
                        b.pt.address_of(dn, top);
                    }
                }
                // An opaque call (indirect / external symbol) may write through its pointer args.
                Inst::Call { dst, args, .. } => {
                    for arg in args {
                        poison_through(&mut b, fid, arg);
                    }
                    if let Some(d) = dst {
                        let dn = b.reg(fid, *d);
                        let top = b.pt.top();
                        b.pt.address_of(dn, top);
                    }
                }
                _ => {}
            }
        }
    }
    b.pt.solve();
    ModulePointsTo { pt: b.pt, reg_node: b.reg_node, obj_global: b.obj_global }
}

#[cfg(test)]
mod tests {
    use super::*;

    // `p = &a` ⇒ pts(p) = {a}; a copy `q = p` shares it.
    #[test]
    fn address_of_and_copy() {
        let mut pt = PointsTo::new();
        let a = pt.new_object("a");
        let p = pt.new_var();
        let q = pt.new_var();
        pt.address_of(p, a);
        pt.assign(q, p);
        pt.solve();
        assert_eq!(pt.singleton_object(p), Some(a));
        assert_eq!(pt.singleton_object(q), Some(a));
    }

    // Field sensitivity: `obj.ops` and `obj.other` are distinct. A store of `&G_ops`
    // into `obj.ops` and a load back resolves to `G_ops`; `obj.other` stays empty.
    #[test]
    fn field_store_then_load_resolves_singleton() {
        let mut pt = PointsTo::new();
        let obj = pt.new_object("obj");
        let g_ops = pt.new_object("g_ops");
        let objp = pt.new_var();
        let opsfield = pt.new_var(); // &obj->ops   (offset 8)
        let val = pt.new_var(); // &g_ops
        pt.address_of(objp, obj);
        pt.address_of(val, g_ops);
        pt.gep(opsfield, objp, 8);
        pt.store(val, opsfield); // *(obj.ops) = &g_ops
        // load it back
        let loaded = pt.new_var();
        pt.load(loaded, opsfield);
        pt.solve();
        assert_eq!(pt.singleton_object(loaded), Some(g_ops), "obj.ops resolves to g_ops");
        // a different field is untouched
        let otherfield = pt.new_var();
        pt.gep(otherfield, objp, 16);
        let other_loaded = pt.new_var();
        pt.load(other_loaded, otherfield);
        pt.solve();
        assert_eq!(pt.singleton_object(other_loaded), None, "obj.other is not obj.ops");
    }

    // Two different globals stored into the same field ⇒ ambiguous, not resolvable.
    #[test]
    fn ambiguous_field_is_not_singleton() {
        let mut pt = PointsTo::new();
        let obj = pt.new_object("obj");
        let g1 = pt.new_object("g1");
        let g2 = pt.new_object("g2");
        let objp = pt.new_var();
        let f = pt.new_var();
        let v1 = pt.new_var();
        let v2 = pt.new_var();
        pt.address_of(objp, obj);
        pt.address_of(v1, g1);
        pt.address_of(v2, g2);
        pt.gep(f, objp, 8);
        pt.store(v1, f);
        pt.store(v2, f);
        let loaded = pt.new_var();
        pt.load(loaded, f);
        pt.solve();
        assert_eq!(pt.points_to(loaded).len(), 2, "field holds both globals");
        assert_eq!(pt.singleton_object(loaded), None, "ambiguous field is not resolvable");
    }

    // A store through an unknown pointer (points to TOP) poisons the field it may
    // reach: even a single named store no longer yields a clean singleton.
    #[test]
    fn top_poisons_a_field() {
        let mut pt = PointsTo::new();
        let obj = pt.new_object("obj");
        let g = pt.new_object("g");
        let objp = pt.new_var();
        let f = pt.new_var();
        let v = pt.new_var();
        pt.address_of(objp, obj);
        pt.address_of(v, g);
        pt.gep(f, objp, 8);
        pt.store(v, f);
        // an unknown pointer that may alias the field: it points at TOP, and we store
        // TOP's address-range into it — model the generator's poison as storing a
        // value that points to TOP through a pointer that also reaches the field.
        let unknown = pt.new_var();
        pt.address_of(unknown, obj); // may alias obj (conservative)
        pt.gep(f, unknown, 8); // reaches obj.ops too
        let topval = pt.new_var();
        pt.address_of(topval, pt.top());
        pt.store(topval, f);
        let loaded = pt.new_var();
        pt.load(loaded, f);
        pt.solve();
        assert_eq!(pt.singleton_object(loaded), None, "a TOP-poisoned field is not resolvable");
        assert!(pt.points_to(loaded).contains(&pt.top()), "the field carries TOP");
    }

    // --- P2: constraint generation from MSIR ---
    use csolver_core::RegionKind;
    use csolver_ir::{
        BasicBlock, BlockId, Const as IrConst, FuncId, Function as IrFunc, Inst as IrInst,
        Module as IrModule, Operand as IrOp, RegId, Terminator, Type as IrTy,
    };

    fn ptr_ty() -> IrTy {
        IrTy::ptr(IrTy::int(8))
    }

    // A function that allocates an object, stores `&G_ops` into its `ops` field (offset 8), and
    // loads it back must resolve the loaded register to `G_ops`.
    #[test]
    fn p2_field_store_load_resolves_to_global() {
        let (obj, field, opsp) = (RegId(0), RegId(1), RegId(2));
        let mut bb = BasicBlock::new(BlockId(0), Terminator::Return(None));
        bb.insts.push(IrInst::Alloc {
            dst: obj,
            region: RegionKind::Heap,
            elem: IrTy::int(8),
            count: IrOp::int(64, 64),
            align: 8,
        });
        bb.insts.push(IrInst::PtrOffset {
            dst: field,
            base: IrOp::Reg(obj),
            index: IrOp::int(64, 8),
            elem: IrTy::int(8),
        });
        bb.insts.push(IrInst::Store {
            ty: ptr_ty(),
            ptr: IrOp::Reg(field),
            value: IrOp::Const(IrConst::Symbol("G_ops".into())),
            align: 8,
            volatile: false,
        });
        bb.insts.push(IrInst::Load {
            dst: opsp,
            ty: ptr_ty(),
            ptr: IrOp::Reg(field),
            align: 8,
            volatile: false,
        });
        let f = IrFunc {
            id: FuncId(0),
            name: "dispatch".into(),
            params: vec![],
            ret_ty: IrTy::Unit,
            blocks: vec![bb],
            entry: BlockId(0),
        };
        let mut m = IrModule::new("m");
        m.functions.push(f);
        let mp = analyze_module(&m);
        assert_eq!(mp.devirt_global(FuncId(0), opsp), Some("G_ops"));
    }

    // A byte-level memset over the object poisons its fields — the same load no longer resolves.
    #[test]
    fn p2_bulk_write_poisons_field() {
        let (obj, field, opsp) = (RegId(0), RegId(1), RegId(2));
        let mut bb = BasicBlock::new(BlockId(0), Terminator::Return(None));
        bb.insts.push(IrInst::Alloc {
            dst: obj,
            region: RegionKind::Heap,
            elem: IrTy::int(8),
            count: IrOp::int(64, 64),
            align: 8,
        });
        bb.insts.push(IrInst::PtrOffset {
            dst: field,
            base: IrOp::Reg(obj),
            index: IrOp::int(64, 8),
            elem: IrTy::int(8),
        });
        bb.insts.push(IrInst::Store {
            ty: ptr_ty(),
            ptr: IrOp::Reg(field),
            value: IrOp::Const(IrConst::Symbol("G_ops".into())),
            align: 8,
            volatile: false,
        });
        // memset(obj, …) — a bulk write of unknown extent poisons every field of obj.
        bb.insts.push(IrInst::MemIntrinsic {
            kind: csolver_ir::MemKind::Set,
            dst: IrOp::Reg(obj),
            src: None,
            len: IrOp::int(64, 64),
        });
        bb.insts.push(IrInst::Load {
            dst: opsp,
            ty: ptr_ty(),
            ptr: IrOp::Reg(field),
            align: 8,
            volatile: false,
        });
        let f = IrFunc {
            id: FuncId(0),
            name: "dispatch".into(),
            params: vec![],
            ret_ty: IrTy::Unit,
            blocks: vec![bb],
            entry: BlockId(0),
        };
        let mut m = IrModule::new("m");
        m.functions.push(f);
        let mp = analyze_module(&m);
        assert_eq!(mp.devirt_global(FuncId(0), opsp), None, "a bulk-written object's field is poisoned");
    }

    // Termination + a two-hop chain `obj.ops -> g_ops`, `g_ops.fn -> target`.
    #[test]
    fn two_hop_ops_chain() {
        let mut pt = PointsTo::new();
        let obj = pt.new_object("obj");
        let g_ops = pt.new_object("g_ops");
        let target = pt.new_object("target");
        let objp = pt.new_var();
        pt.address_of(objp, obj);
        // obj.ops = &g_ops
        let opsf = pt.new_var();
        pt.gep(opsf, objp, 8);
        let vops = pt.new_var();
        pt.address_of(vops, g_ops);
        pt.store(vops, opsf);
        // g_ops.fn = &target  (the constant vtable, offset 0)
        let gp = pt.new_var();
        pt.address_of(gp, g_ops);
        let fnf = pt.new_var();
        pt.gep(fnf, gp, 0);
        let vt = pt.new_var();
        pt.address_of(vt, target);
        pt.store(vt, fnf);
        pt.solve();
        // load obj.ops, then load ops.fn
        let opsp = pt.new_var();
        pt.load(opsp, opsf);
        pt.solve();
        assert_eq!(pt.singleton_object(opsp), Some(g_ops));
        let fnfield = pt.new_var();
        pt.gep(fnfield, opsp, 0);
        let fnp = pt.new_var();
        pt.load(fnp, fnfield);
        pt.solve();
        assert_eq!(pt.singleton_object(fnp), Some(target), "the dispatch resolves to target");
    }
}
