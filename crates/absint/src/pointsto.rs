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
// P2/P3: constraint generation from MSIR — per-module and whole-program (streaming).
// ---------------------------------------------------------------------------

use csolver_ir::{
    Callee, Const, DataLayout, FuncId, Inst, Module, Operand, RValue, RegId, Type,
};

const LAYOUT: DataLayout = DataLayout::LP64;

/// The solved whole-program points-to result: the relation plus the maps needed to resolve a
/// register to the single global it points to. Registers are keyed by a **global function id**
/// (assigned in module-then-function push order — the same id space as the other whole-program
/// fact builders); look one up by name with [`gfid_of`](Self::gfid_of).
pub struct ModulePointsTo {
    pt: PointsTo,
    reg_node: HashMap<(u32, RegId), Node>,
    obj_global: HashMap<Node, String>,
    name_to_gfid: HashMap<String, u32>,
}

impl ModulePointsTo {
    /// The **single global** that register `r` of the function with global id `gfid` provably
    /// points to (its points-to set is a clean-singleton object that is a named global), if any.
    /// This is the resolvable devirtualisation case — sound because a singleton over-approximation
    /// is exact. `None` when the register is unresolved, ambiguous, or points to a non-global /
    /// poisoned object.
    pub fn devirt(&self, gfid: u32, r: RegId) -> Option<&str> {
        let &n = self.reg_node.get(&(gfid, r))?;
        let obj = self.pt.singleton_object(n)?;
        self.obj_global.get(&obj).map(String::as_str)
    }

    /// The global id of an external function by name (first definition wins), for pairing a
    /// per-file function back to its whole-program register nodes.
    pub fn gfid_of(&self, name: &str) -> Option<u32> {
        self.name_to_gfid.get(name).copied()
    }

    /// Single-module convenience: resolve by the module-local [`FuncId`] (its own id is its
    /// global id when only one module was pushed, as in [`analyze_module`]).
    pub fn devirt_global(&self, f: FuncId, r: RegId) -> Option<&str> {
        self.devirt(f.0, r)
    }

    /// The underlying solver (for tests / further queries).
    pub fn solver(&self) -> &PointsTo {
        &self.pt
    }
}

/// A deferred call's callee, resolved at [`ProgramPointsTo::finalize`]: an in-module direct call
/// (already a global id), a cross-module `Symbol` (resolved by name), or an opaque indirect call.
enum DeferredCallee {
    Gfid(u32),
    Name(String),
    Opaque,
}

/// Whole-program field-sensitive points-to, built **incrementally** (P3): fold each module in with
/// [`push_module`](Self::push_module) — after which it may be dropped — then
/// [`finalize`](Self::finalize) resolves cross-module call edges by name and solves. Ids are
/// assigned module-then-function in push order (the same space as `SummaryFacts`/`ContractFacts`),
/// so a `Symbol` call resolves to the same callee the linked program would.
pub struct ProgramPointsTo {
    pt: PointsTo,
    reg_node: HashMap<(u32, RegId), Node>,
    global_obj: HashMap<String, Node>,
    obj_global: HashMap<Node, String>,
    /// Next global function id.
    next: u32,
    /// External function name → global id (first definition wins).
    name_to_gfid: HashMap<String, u32>,
    /// Global id → its parameter registers (for connecting a resolved call's args at finalize).
    fn_params: HashMap<u32, Vec<RegId>>,
    /// Deferred calls `(caller gfid, callee, args)` — resolved at finalize.
    deferred: Vec<(u32, DeferredCallee, Vec<Operand>)>,
}

impl Default for ProgramPointsTo {
    fn default() -> Self {
        Self::new()
    }
}

impl ProgramPointsTo {
    /// A fresh, empty whole-program points-to builder.
    pub fn new() -> ProgramPointsTo {
        ProgramPointsTo {
            pt: PointsTo::new(),
            reg_node: HashMap::new(),
            global_obj: HashMap::new(),
            obj_global: HashMap::new(),
            next: 0,
            name_to_gfid: HashMap::new(),
            fn_params: HashMap::new(),
            deferred: Vec::new(),
        }
    }

    fn reg(&mut self, gfid: u32, r: RegId) -> Node {
        if let Some(&n) = self.reg_node.get(&(gfid, r)) {
            return n;
        }
        let n = self.pt.new_var();
        self.reg_node.insert((gfid, r), n);
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

    /// A node standing for the pointer *value* of an operand under function `gfid`: a register maps
    /// to its node; a global symbol's address becomes a fresh var pointing at that global; anything
    /// else is unknown (`None`).
    fn operand_ptr(&mut self, gfid: u32, op: &Operand) -> Option<Node> {
        match op {
            Operand::Reg(r) => Some(self.reg(gfid, *r)),
            Operand::Const(Const::Symbol(g)) | Operand::Const(Const::SymbolOffset(g, _)) => {
                let obj = self.global(g);
                let v = self.pt.new_var();
                self.pt.address_of(v, obj);
                Some(v)
            }
            _ => None,
        }
    }

    /// A gep at the reserved unknown offset through a pointer operand — poisons every object it may
    /// reach (a byte/symbolic/opaque write the analysis cannot pin to a specific field).
    fn poison_through(&mut self, gfid: u32, op: &Operand) {
        if let Some(p) = self.operand_ptr(gfid, op) {
            let anyf = self.pt.new_var();
            self.pt.gep(anyf, p, ANY_OFFSET);
        }
    }

    /// Fold one module in (droppable afterwards): assign its functions global ids `base..`, record
    /// their parameters and external names, generate the intra-function constraints, and defer the
    /// calls (resolved at finalize).
    pub fn push_module(&mut self, m: &Module) {
        let base = self.next;
        for (i, f) in m.functions.iter().enumerate() {
            let gfid = base + i as u32;
            self.fn_params.insert(gfid, f.params.iter().map(|(r, _)| *r).collect());
            if !m.internal.contains(&f.id) {
                self.name_to_gfid.entry(f.name.clone()).or_insert(gfid);
            }
        }
        for (i, f) in m.functions.iter().enumerate() {
            let gfid = base + i as u32;
            for inst in f.blocks.iter().flat_map(|bl| &bl.insts) {
                match inst {
                    Inst::Alloc { dst, .. } => {
                        let o = self.pt.new_object("alloc");
                        let d = self.reg(gfid, *dst);
                        self.pt.address_of(d, o);
                    }
                    Inst::Assign { dst, value, .. } => {
                        let src = match value {
                            RValue::Use(op) | RValue::Cast { operand: op, .. } => {
                                self.operand_ptr(gfid, op)
                            }
                            _ => None,
                        };
                        if let Some(s) = src {
                            let d = self.reg(gfid, *dst);
                            self.pt.assign(d, s);
                        }
                    }
                    Inst::PtrOffset { dst, base: Operand::Reg(bs), index, elem } => {
                        let base_n = self.reg(gfid, *bs);
                        let off = const_byte_offset(index, elem).unwrap_or(ANY_OFFSET);
                        let d = self.reg(gfid, *dst);
                        self.pt.gep(d, base_n, off);
                    }
                    // A typed MIR field access carries no byte offset here — conservatively unknown.
                    Inst::FieldPtr { dst, base: Operand::Reg(bs), .. } => {
                        let base_n = self.reg(gfid, *bs);
                        let d = self.reg(gfid, *dst);
                        self.pt.gep(d, base_n, ANY_OFFSET);
                    }
                    Inst::Load { dst, ty, ptr: Operand::Reg(p), .. } if ty.is_ptr() => {
                        let pn = self.reg(gfid, *p);
                        let d = self.reg(gfid, *dst);
                        self.pt.load(d, pn);
                    }
                    Inst::Store { ptr: Operand::Reg(p), value, .. } => {
                        if let Some(v) = self.operand_ptr(gfid, value) {
                            let pn = self.reg(gfid, *p);
                            self.pt.store(v, pn);
                        }
                    }
                    // A bulk write (memcpy/memset) writes an unknown extent of its destination.
                    Inst::MemIntrinsic { dst, .. } => self.poison_through(gfid, dst),
                    Inst::Call { dst, callee, args, .. } => {
                        let callee = match callee {
                            Callee::Direct(g) => DeferredCallee::Gfid(base + g.0),
                            Callee::Symbol(n) => DeferredCallee::Name(n.clone()),
                            Callee::Indirect(_) => DeferredCallee::Opaque,
                        };
                        self.deferred.push((gfid, callee, args.clone()));
                        // The call result is an unknown pointer (return modelling is a later refinement).
                        if let Some(d) = dst {
                            let dn = self.reg(gfid, *d);
                            let top = self.pt.top();
                            self.pt.address_of(dn, top);
                        }
                    }
                    _ => {}
                }
            }
        }
        self.next += m.functions.len() as u32;
    }

    /// Resolve the deferred calls (arg→param for a known callee, poison the args of an opaque one)
    /// and solve to a fixpoint. A resolved callee needs no arg poisoning: its own body's stores
    /// into its parameters flow back to the caller's objects through the arg→param edges, so a
    /// callee that writes `param->ops` is captured exactly (and makes the field ambiguous if it
    /// disagrees with another site) — the interprocedural soundness.
    pub fn finalize(mut self) -> ModulePointsTo {
        let deferred = std::mem::take(&mut self.deferred);
        for (caller, callee, args) in deferred {
            let target = match callee {
                DeferredCallee::Gfid(g) => Some(g),
                DeferredCallee::Name(n) => self.name_to_gfid.get(&n).copied(),
                DeferredCallee::Opaque => None,
            };
            match target.and_then(|g| self.fn_params.get(&g).cloned().map(|p| (g, p))) {
                Some((g, params)) => {
                    for (i, arg) in args.iter().enumerate() {
                        if let (Some(&preg), Some(an)) = (params.get(i), self.operand_ptr(caller, arg)) {
                            let pn = self.reg(g, preg);
                            self.pt.assign(pn, an);
                        }
                    }
                }
                // Unresolved external / indirect: it may write through its pointer arguments.
                None => {
                    for arg in &args {
                        self.poison_through(caller, arg);
                    }
                }
            }
        }
        self.pt.solve();
        ModulePointsTo {
            pt: self.pt,
            reg_node: self.reg_node,
            obj_global: self.obj_global,
            name_to_gfid: self.name_to_gfid,
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

/// Build and solve the field-sensitive points-to relation for a **single** module (P2) — the whole
/// program in one module. A thin wrapper over the streaming [`ProgramPointsTo`] (push one, finalize),
/// so both paths share one implementation.
pub fn analyze_module(m: &Module) -> ModulePointsTo {
    let mut p = ProgramPointsTo::new();
    p.push_module(m);
    p.finalize()
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

    // P3: cross-module. Module A allocates an object, stores `&G_ops` into its ops field, and
    // passes it to `use` — defined in module B — which loads the field back. The streaming
    // Symbol-call resolution connects A's argument to B's parameter, so the store flows across the
    // module boundary and B's load resolves to `G_ops`.
    #[test]
    fn p3_cross_module_dispatch_resolves() {
        // Module A: fn make() { obj = alloc; obj.ops(@8) = &G_ops; use(obj); }
        let (obj, field) = (RegId(0), RegId(1));
        let mut abb = BasicBlock::new(BlockId(0), Terminator::Return(None));
        abb.insts.push(IrInst::Alloc {
            dst: obj, region: RegionKind::Heap, elem: IrTy::int(8), count: IrOp::int(64, 64), align: 8,
        });
        abb.insts.push(IrInst::PtrOffset {
            dst: field, base: IrOp::Reg(obj), index: IrOp::int(64, 8), elem: IrTy::int(8),
        });
        abb.insts.push(IrInst::Store {
            ty: ptr_ty(), ptr: IrOp::Reg(field), value: IrOp::Const(IrConst::Symbol("G_ops".into())),
            align: 8, volatile: false,
        });
        abb.insts.push(IrInst::Call {
            dst: None,
            callee: csolver_ir::Callee::Symbol("use".into()),
            args: vec![IrOp::Reg(obj)],
            ret_ty: IrTy::Unit,
            ret_ref: None,
        });
        let make = IrFunc {
            id: FuncId(0), name: "make".into(), params: vec![], ret_ty: IrTy::Unit,
            blocks: vec![abb], entry: BlockId(0),
        };
        let mut ma = IrModule::new("a");
        ma.functions.push(make);

        // Module B: fn use(o) { p = o.ops(@8); }
        let (o, field2, p) = (RegId(0), RegId(1), RegId(2));
        let mut bbb = BasicBlock::new(BlockId(0), Terminator::Return(None));
        bbb.insts.push(IrInst::PtrOffset {
            dst: field2, base: IrOp::Reg(o), index: IrOp::int(64, 8), elem: IrTy::int(8),
        });
        bbb.insts.push(IrInst::Load {
            dst: p, ty: ptr_ty(), ptr: IrOp::Reg(field2), align: 8, volatile: false,
        });
        let usef = IrFunc {
            id: FuncId(0), name: "use".into(), params: vec![(o, ptr_ty())], ret_ty: IrTy::Unit,
            blocks: vec![bbb], entry: BlockId(0),
        };
        let mut mb = IrModule::new("b");
        mb.functions.push(usef);

        let mut pp = ProgramPointsTo::new();
        pp.push_module(&ma);
        pp.push_module(&mb);
        let mp = pp.finalize();
        let use_gfid = mp.gfid_of("use").expect("use resolved");
        assert_eq!(mp.devirt(use_gfid, p), Some("G_ops"), "the store flows across the module boundary");
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
