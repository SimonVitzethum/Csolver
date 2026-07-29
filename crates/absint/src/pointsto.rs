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
    /// Nodes whose points-to set overflowed [`MAX_PTS_SET`] and was collapsed to `{TOP}` (see
    /// [`saturate`](Self::saturate)); further additions to them are dropped, capping solver memory.
    saturated: HashSet<Node>,
}

/// The reserved offset for an **unknown / symbolic** field access: a gep with this offset poisons
/// the whole base object (any of its fields may be the target).
pub const ANY_OFFSET: u64 = u64::MAX;

/// Peak points-to set size before a node is collapsed to `{TOP}` (memory cap; a set this large is
/// never a resolvable singleton, so the cap loses no devirt).
const MAX_PTS_SET: usize = 64;

/// Whole-program node budget (a memory backstop, not the normal path). The worklist [`solve`] scales
/// to millions of nodes, so this is set well above a full-kernel relation (~3–4M nodes): the streaming
/// builder stops accumulating past it, `solve` is skipped past it (empty devirt — sound), and
/// [`intern_field`] resolves new field accesses to TOP past it (bounding solve-time node growth).
/// Only a pathologically large relation hits it; everything real solves.
const MAX_NODES: usize = 10_000_000;

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
            saturated: HashSet::new(),
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
        // Hard node cap: `solve` creates field cells on demand, so an unbounded relation could grow
        // the node count past the budget mid-solve. Beyond the cap, a new field access resolves to
        // TOP (unknown) instead of allocating — a sound over-approximation that bounds total nodes.
        if self.n as usize >= MAX_NODES {
            return self.top;
        }
        let c = self.fresh();
        self.field_cell.insert((obj, offset), c);
        // No debug name for field cells: at whole-kernel scale there are millions of them and the
        // `format!` string per cell is pure overhead — cells are never queried by name (only named
        // globals matter for devirt, tracked separately in `ProgramPointsTo::obj_global`).
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

    /// Collapse a node whose points-to set has grown past [`MAX_PTS_SET`] to the single absorbing
    /// TOP object. A set this large is never a clean singleton anyway, so collapsing it loses no
    /// resolvable devirt; it caps the solver's peak memory (a whole-kernel Andersen relation would
    /// otherwise hold enormous sets). Sound: `{TOP}` over-approximates any set, and a saturated node
    /// stays TOP (further additions are dropped), so the fixpoint still terminates monotonically.
    fn saturate(&mut self, dst: Node) {
        if self.pts[dst.0 as usize].len() > MAX_PTS_SET {
            let top = self.top;
            self.pts[dst.0 as usize].clear();
            self.pts[dst.0 as usize].insert(top);
            self.saturated.insert(dst);
        }
    }

    fn add(&mut self, dst: Node, obj: Node) -> bool {
        if self.saturated.contains(&dst) {
            return false;
        }
        let changed = self.pts[dst.0 as usize].insert(obj);
        if changed {
            self.saturate(dst);
        }
        changed
    }

    fn union(&mut self, dst: Node, src: Node) -> bool {
        if dst == src || self.saturated.contains(&dst) {
            return false;
        }
        let srcs: Vec<Node> = self.pts[src.0 as usize].iter().copied().collect();
        let mut changed = false;
        for o in srcs {
            changed |= self.pts[dst.0 as usize].insert(o);
        }
        if changed {
            self.saturate(dst);
        }
        changed
    }

    /// Solve the constraints to a fixpoint with a **worklist** (Andersen-style): only a node whose
    /// points-to set just grew is reprocessed, and load/store constraints add *dynamic* copy edges
    /// as the pointer's targets become known. This is the same least fixpoint the naive round-robin
    /// computed, but O(propagated changes) instead of O(constraints × rounds) — so a whole-kernel
    /// relation (millions of nodes) is tractable where re-scanning every constraint each round was
    /// not. The [`MAX_PTS_SET`] cap still bounds each set (and hence peak memory); it is applied
    /// identically through [`add`](Self::add)/[`union`](Self::union), so the result is unchanged.
    pub fn solve(&mut self) {
        // Constraint indices, keyed by the node whose points-to set triggers the constraint.
        let mut copy_to: HashMap<Node, HashSet<Node>> = HashMap::new(); // src → { dst : dst ⊇ src }
        for &(d, s) in &self.copy {
            copy_to.entry(s).or_default().insert(d);
        }
        let mut gep_to: HashMap<Node, Vec<(Node, u64)>> = HashMap::new(); // src → (dst, off)
        for &(d, s, off) in &self.gep {
            gep_to.entry(s).or_default().push((d, off));
        }
        let mut load_to: HashMap<Node, Vec<Node>> = HashMap::new(); // src → { dst : dst ⊇ *src }
        for &(d, s) in &self.load {
            load_to.entry(s).or_default().push(d);
        }
        let mut store_from: HashMap<Node, Vec<Node>> = HashMap::new(); // ptr → { v : *ptr ⊇ v }
        for &(v, p) in &self.store {
            store_from.entry(p).or_default().push(v);
        }

        let mut on_work: HashSet<Node> = HashSet::new();
        let mut work: Vec<Node> = Vec::new();
        let push = |n: Node, on: &mut HashSet<Node>, w: &mut Vec<Node>| {
            if on.insert(n) {
                w.push(n);
            }
        };
        // Seed: address-of, plus every node already carrying points-to (poison-seeded field cells).
        for i in 0..self.addr.len() {
            let (p, o) = self.addr[i];
            if self.add(p, o) {
                push(p, &mut on_work, &mut work);
            }
        }
        for n in 0..self.n {
            if !self.pts[n as usize].is_empty() {
                push(Node(n), &mut on_work, &mut work);
            }
        }

        while let Some(n) = work.pop() {
            on_work.remove(&n);
            let pts_n: Vec<Node> = self.pts[n.0 as usize].iter().copied().collect();

            // gep: dst ⊇ { field(o, off) : o ∈ pts(n) }.
            if let Some(edges) = gep_to.get(&n).cloned() {
                for (dst, off) in edges {
                    for &o in &pts_n {
                        let cell = self.intern_field(o, off);
                        if self.add(dst, cell) {
                            push(dst, &mut on_work, &mut work);
                        }
                    }
                }
            }
            // load: dst ⊇ *o for o ∈ pts(n) — a dynamic copy edge o → dst, and flow pts(o) now.
            if let Some(dsts) = load_to.get(&n).cloned() {
                for dst in dsts {
                    for &o in &pts_n {
                        if copy_to.entry(o).or_default().insert(dst) && self.union(dst, o) {
                            push(dst, &mut on_work, &mut work);
                        }
                    }
                }
            }
            // store: *o ⊇ value for o ∈ pts(n) — a dynamic copy edge value → o, and flow pts(value).
            if let Some(values) = store_from.get(&n).cloned() {
                for value in values {
                    for &o in &pts_n {
                        if copy_to.entry(value).or_default().insert(o) && self.union(o, value) {
                            push(o, &mut on_work, &mut work);
                        }
                    }
                }
            }
            // copy: dst ⊇ n for each (static or dynamic) copy edge n → dst.
            if let Some(dsts) = copy_to.get(&n).cloned() {
                for dst in dsts {
                    if self.union(dst, n) {
                        push(dst, &mut on_work, &mut work);
                    }
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
    /// Per global function id: its name and whether it is internal (file-local `static`). Used to
    /// re-key a resolved devirt by the **external** function name — the same soundness discipline
    /// as the other whole-program facts (an internal/static's name may collide across files, so it
    /// is never matched cross-file).
    gfid_meta: HashMap<u32, (String, bool)>,
    /// Every function symbol name in the program. A points-to singleton is only turned into a
    /// devirt target when it names a real function (not a data global), so a data pointer that
    /// happens to be a clean singleton never resolves a call.
    fn_names: HashSet<String>,
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

    /// The resolved indirect-call devirtualisations, keyed by **`(external function name, register)`**
    /// — a register that provably (clean-singleton) points to a named function is mapped to that
    /// function's name. Restricted to **external** (non-internal) caller functions so the key is
    /// unambiguous across files (a static's name may recur), mirroring the whole-program fact
    /// overlays. This is the executor-facing product: an indirect call through such a register is
    /// resolved to a direct call on the named callee (call-target resolution **only** — the loaded
    /// pointer's provenance/safety is untouched, so no uninitialised/null deref is masked).
    pub fn name_keyed_devirt(&self) -> HashMap<(String, RegId), String> {
        let mut out = HashMap::new();
        for (&(gfid, r), &node) in &self.reg_node {
            let Some((name, internal)) = self.gfid_meta.get(&gfid) else { continue };
            if *internal {
                continue;
            }
            let Some(obj) = self.pt.singleton_object(node) else { continue };
            let Some(target) = self.obj_global.get(&obj) else { continue };
            if !self.fn_names.contains(target) {
                continue;
            }
            out.insert((name.clone(), r), target.clone());
        }
        out
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
    /// Global id → `(name, internal)` — carried into the result for name-keyed devirt.
    gfid_meta: HashMap<u32, (String, bool)>,
    /// Every function symbol name seen (devirt targets must name a real function).
    fn_names: HashSet<String>,
    /// Names of globals whose contents are **known ground truth** — a constant (`!writable`)
    /// initializer was ingested via [`global_field_init`]. Every *other* global is poisoned at
    /// [`finalize`], so a load of one of its fields yields TOP rather than the empty set. This is
    /// the soundness fix for the ambiguous-dispatch collapse: if `obj->ops ∈ {G_known, G_unknown}`,
    /// the load of `->fn` must NOT resolve to `G_known`'s target just because `G_unknown`'s field
    /// cell happens to be empty — `G_unknown` could hold any function, so its field is TOP.
    known_const_globals: HashSet<String>,
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
            gfid_meta: HashMap::new(),
            fn_names: HashSet::new(),
            known_const_globals: HashSet::new(),
        }
    }

    /// Seed a constant-global initializer edge `*(global + offset) = &target` — the vtable content
    /// that the module carries out-of-line (in `Module::global_fn_ptrs` / `global_ptr_fields`), not
    /// in any function body. Feeding it as an address-of into the field cell lets the **second hop**
    /// of `obj->ops->fn()` resolve inside the points-to relation: once a heap/param field is known
    /// (hop 1) to hold `&G_ops`, the load of `G_ops->fn` reads back `&target` here. A constant
    /// initializer is ground truth, so this edge is exact (no assumption).
    fn global_field_init(&mut self, gname: &str, offset: u64, target: &str) {
        let obj = self.global(gname);
        let cell = self.pt.intern_field(obj, offset);
        let tobj = self.global(target);
        self.pt.address_of(cell, tobj);
        self.known_const_globals.insert(gname.to_string());
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
        // Stop accumulating once the whole-program relation exceeds the node budget — the naive
        // fixpoint would not scale, so beyond it the analysis degrades to a sound no-op (empty
        // devirt) rather than exhausting memory.
        if self.pt.n as usize >= MAX_NODES {
            return;
        }
        let base = self.next;
        for (i, f) in m.functions.iter().enumerate() {
            let gfid = base + i as u32;
            let internal = m.internal.contains(&f.id);
            self.fn_params.insert(gfid, f.params.iter().map(|(r, _)| *r).collect());
            self.gfid_meta.insert(gfid, (f.name.clone(), internal));
            self.fn_names.insert(f.name.clone());
            if !internal {
                self.name_to_gfid.entry(f.name.clone()).or_insert(gfid);
            }
        }
        // Ingest the out-of-line constant-global initializers (vtables / ops-struct chains). A
        // function-pointer field names a real function (recorded as a devirt-eligible target); a
        // pointer-to-global field chains one constant global to another. Both are ground truth.
        for (gname, entries) in &m.global_fn_ptrs {
            for (off, fid) in entries {
                if let Some(tf) = m.functions.iter().find(|f| f.id == *fid) {
                    let tname = tf.name.clone();
                    self.fn_names.insert(tname.clone());
                    self.global_field_init(gname, *off, &tname);
                }
            }
        }
        for (gname, entries) in &m.global_ptr_fields {
            for (off, target) in entries {
                self.global_field_init(gname, *off, target);
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

    /// Remap a node of `other` into this builder, unifying **named globals by name** (the same
    /// global in two files is one object) and giving every shard-local node (variables, allocation
    /// objects, field cells) a fresh identity here. Field cells recurse through their base object,
    /// so a global's field cell unifies too (via [`PointsTo::intern_field`] reuse) — which is what
    /// lets a vtable initialized in one file resolve a dispatch loaded in another. Memoized in `map`.
    fn remap(
        &mut self,
        n: Node,
        other: &ProgramPointsTo,
        cell_of: &HashMap<Node, (Node, u64)>,
        map: &mut HashMap<Node, Node>,
    ) -> Node {
        if let Some(&m) = map.get(&n) {
            return m;
        }
        let out = if let Some(&(obj, off)) = cell_of.get(&n) {
            let so = self.remap(obj, other, cell_of, map);
            self.pt.intern_field(so, off)
        } else if other.obj_global.contains_key(&n) {
            // A named global: unify by name across shards.
            let name = other.pt.name.get(&n).cloned().unwrap_or_default();
            self.global(&name)
        } else if let Some(nm) = other.pt.name.get(&n).cloned() {
            // A named-but-local object (an allocation site): stays distinct per shard.
            self.pt.new_object(nm)
        } else {
            self.pt.new_var()
        };
        map.insert(n, out);
        out
    }

    /// Fold `other` (a points-to built over a *later* file shard) into this one so shards extracted
    /// concurrently merge in file order into one whole-program relation — the counterpart to
    /// [`WholeProgramFacts::merge`](../../csolver_verifier/wholeprog/struct.WholeProgramFacts.html).
    /// Global ids are rebased by this builder's function count (identical to a single sequential
    /// push), named globals unify, and every local node/constraint is translated through [`remap`].
    /// Called **before** [`finalize`](Self::finalize) — no points-to set has been solved yet, so
    /// only the constraint graph is translated; the fixpoint runs once over the merged whole.
    pub fn merge(&mut self, other: ProgramPointsTo) {
        // Over the node budget, drop the incoming shard's relation (degrade to a sound no-op).
        if self.pt.n as usize >= MAX_NODES {
            return;
        }
        let gbase = self.next;
        let cell_of: HashMap<Node, (Node, u64)> =
            other.pt.field_cell.iter().map(|(&(o, off), &c)| (c, (o, off))).collect();
        let mut map: HashMap<Node, Node> = HashMap::new();
        map.insert(other.pt.top, self.pt.top);
        for &(p, o) in &other.pt.addr {
            let (a, b) = (self.remap(p, &other, &cell_of, &mut map), self.remap(o, &other, &cell_of, &mut map));
            self.pt.address_of(a, b);
        }
        for &(d, s) in &other.pt.copy {
            let (a, b) = (self.remap(d, &other, &cell_of, &mut map), self.remap(s, &other, &cell_of, &mut map));
            self.pt.assign(a, b);
        }
        for &(d, s, off) in &other.pt.gep {
            let (a, b) = (self.remap(d, &other, &cell_of, &mut map), self.remap(s, &other, &cell_of, &mut map));
            self.pt.gep(a, b, off);
        }
        for &(d, s) in &other.pt.load {
            let (a, b) = (self.remap(d, &other, &cell_of, &mut map), self.remap(s, &other, &cell_of, &mut map));
            self.pt.load(a, b);
        }
        for &(v, p) in &other.pt.store {
            let (a, b) = (self.remap(v, &other, &cell_of, &mut map), self.remap(p, &other, &cell_of, &mut map));
            self.pt.store(a, b);
        }
        for &o in &other.pt.poisoned {
            let a = self.remap(o, &other, &cell_of, &mut map);
            self.pt.poison(a);
        }
        for (&(g, r), &nd) in &other.reg_node {
            let a = self.remap(nd, &other, &cell_of, &mut map);
            self.reg_node.insert((g + gbase, r), a);
        }
        for (&g, ps) in &other.fn_params {
            self.fn_params.insert(g + gbase, ps.clone());
        }
        for (&g, meta) in &other.gfid_meta {
            self.gfid_meta.insert(g + gbase, meta.clone());
        }
        for (nm, &g) in &other.name_to_gfid {
            self.name_to_gfid.entry(nm.clone()).or_insert(g + gbase);
        }
        self.fn_names.extend(other.fn_names.iter().cloned());
        self.known_const_globals.extend(other.known_const_globals.iter().cloned());
        for (caller, callee, args) in other.deferred {
            let callee = match callee {
                DeferredCallee::Gfid(g) => DeferredCallee::Gfid(g + gbase),
                c => c,
            };
            self.deferred.push((caller + gbase, callee, args));
        }
        self.next += other.next;
    }

    /// Resolve the deferred calls (arg→param for a known callee, poison the args of an opaque one)
    /// and solve to a fixpoint. A resolved callee needs no arg poisoning: its own body's stores
    /// into its parameters flow back to the caller's objects through the arg→param edges, so a
    /// callee that writes `param->ops` is captured exactly (and makes the field ambiguous if it
    /// disagrees with another site) — the interprocedural soundness.
    pub fn finalize(mut self) -> ModulePointsTo {
        // Poison every global whose constant initializer was NOT ingested: its field contents are
        // unknown, so a load of one of its fields must be TOP, never the empty set. Without this an
        // ambiguous `obj->ops ∈ {G_known, G_unknown}` would unsoundly collapse to `G_known`'s target
        // at the second hop (the unknown's empty field cell contributing nothing to the union).
        let unknown: Vec<Node> = self
            .global_obj
            .iter()
            .filter(|(name, _)| !self.known_const_globals.contains(*name))
            .map(|(_, &node)| node)
            .collect();
        for n in unknown {
            self.pt.poison(n);
        }
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
        // Offline copy-cycle collapse + node compaction: the copy graph is now complete (build +
        // merge + deferred arg→param edges), so collapse SCCs of the subset graph before solving.
        // This shrinks the node count — dominated by per-function pointer registers in a whole-kernel
        // relation — losslessly, which is what lets a relation that would otherwise exceed the budget
        // (and skip devirt entirely) solve. See [`collapse_copy_cycles`].
        let n_before = self.pt.n;
        self.collapse_copy_cycles();
        // Diagnostic on the whole-program-scale relation only (a per-module `analyze_module` relation
        // is tiny and stays silent): report the compaction ratio so a kernel scan can confirm the
        // node drop and whether it brought devirt back under budget.
        if n_before >= 500_000 {
            let pct = 100.0 * (n_before - self.pt.n) as f64 / n_before as f64;
            eprintln!(
                "  points-to: copy-cycle collapse {n_before} -> {} nodes ({pct:.1}% reduction)",
                self.pt.n
            );
        }
        // Over the node budget *after* compaction: skip the solve (it would not scale) and return an
        // unsolved relation — every points-to set is empty, so `name_keyed_devirt` yields nothing.
        // Sound (no devirt), and the scan completes instead of exhausting memory.
        if self.pt.n as usize >= MAX_NODES {
            eprintln!(
                "  points-to: {} nodes exceeds budget ({}) after cycle-collapse, skipping whole-program devirt",
                self.pt.n, MAX_NODES
            );
            return ModulePointsTo {
                pt: self.pt,
                reg_node: self.reg_node,
                obj_global: self.obj_global,
                name_to_gfid: self.name_to_gfid,
                gfid_meta: self.gfid_meta,
                fn_names: self.fn_names,
            };
        }
        self.pt.solve();
        ModulePointsTo {
            pt: self.pt,
            reg_node: self.reg_node,
            obj_global: self.obj_global,
            name_to_gfid: self.name_to_gfid,
            gfid_meta: self.gfid_meta,
            fn_names: self.fn_names,
        }
    }

    /// Offline **copy-cycle collapse with node compaction** (Andersen cycle elimination, applied
    /// offline). Nodes in a strongly-connected component of the copy (subset `⊇`) graph are mutually
    /// inclusive, hence have identical points-to sets at the least fixpoint; collapsing each SCC to a
    /// single representative and **renumbering** the survivors to a dense range shrinks the node
    /// count — dominated by per-function pointer registers in a whole-kernel relation — without
    /// changing any points-to result. This is what lets a relation that would otherwise exceed the
    /// node budget (and thus skip whole-program devirt) fit and solve.
    ///
    /// **Precision- and soundness-preserving.** A `gep`/`load`/`store` keys on the byte offset and on
    /// the (now equal) points-to set of its pointer, not on node identity, so field-sensitivity and
    /// every devirt singleton are preserved. The whole relation *and* the node-keyed side tables
    /// (`reg_node` values, `global_obj` values, `obj_global` keys) are translated together, so a
    /// devirt query still lands on the right object. TOP stays node 0 (absorbing). Field-cell key
    /// collisions (two now-merged objects with a field at the same offset) are equalised by adding
    /// copy edges between the two cells — sound (they converge in `solve`); an `obj_global` name
    /// collision (two *distinct named globals* merged — practically impossible, as function/data
    /// objects are address-of targets, never copy-cycle members) drops the entry so devirt declines
    /// rather than guessing (never a wrong resolution). Run at [`finalize`] after the deferred
    /// arg→param edges exist (the copy graph is complete) and before [`PointsTo::solve`].
    fn collapse_copy_cycles(&mut self) {
        let n = self.pt.n as usize;
        if n <= 1 {
            return;
        }
        // --- 1. Tarjan SCC over the copy graph: edge `src → dst` for each `dst ⊇ src`. ---
        let mut adj: Vec<Vec<u32>> = vec![Vec::new(); n];
        for &(d, s) in &self.pt.copy {
            adj[s.0 as usize].push(d.0);
        }
        let mut index = vec![u32::MAX; n];
        let mut low = vec![0u32; n];
        let mut on_stack = vec![false; n];
        let mut stack: Vec<u32> = Vec::new();
        let mut comp = vec![u32::MAX; n];
        let mut ncomp = 0u32;
        let mut idx = 0u32;
        for start in 0..n as u32 {
            if index[start as usize] != u32::MAX {
                continue;
            }
            // Iterative DFS: (node, next-child-index).
            let mut dfs: Vec<(u32, usize)> = vec![(start, 0)];
            while let Some(&(v, ci)) = dfs.last() {
                if ci == 0 {
                    index[v as usize] = idx;
                    low[v as usize] = idx;
                    idx += 1;
                    stack.push(v);
                    on_stack[v as usize] = true;
                }
                if ci < adj[v as usize].len() {
                    let w = adj[v as usize][ci];
                    // Advance this frame's child cursor before descending. The `dfs.last()`
                    // above just succeeded, so the frame is there; `if let` rather than an
                    // unwrap keeps the loop panic-free by construction.
                    if let Some(top) = dfs.last_mut() {
                        top.1 = ci + 1;
                    }
                    if index[w as usize] == u32::MAX {
                        dfs.push((w, 0));
                    } else if on_stack[w as usize] {
                        low[v as usize] = low[v as usize].min(index[w as usize]);
                    }
                } else {
                    // Finished v: if it roots an SCC, pop the component.
                    if low[v as usize] == index[v as usize] {
                        // Pop the component down to and including its root `v`. Tarjan
                        // guarantees `v` is on the stack, so the loop always breaks at it;
                        // draining on `None` instead of unwrapping means a hypothetical
                        // invariant break degrades to a terminating loop, not a panic.
                        while let Some(w) = stack.pop() {
                            on_stack[w as usize] = false;
                            comp[w as usize] = ncomp;
                            if w == v {
                                break;
                            }
                        }
                        ncomp += 1;
                    }
                    dfs.pop();
                    if let Some(&(p, _)) = dfs.last() {
                        low[p as usize] = low[p as usize].min(low[v as usize]);
                    }
                }
            }
        }
        // --- 2. Representative (smallest old id) per component; TOP=0 is thus its own rep. ---
        let mut comp_rep = vec![u32::MAX; ncomp as usize];
        for v in 0..n as u32 {
            let c = comp[v as usize] as usize;
            if comp_rep[c] == u32::MAX || v < comp_rep[c] {
                comp_rep[c] = v;
            }
        }
        let rep: Vec<u32> = (0..n as u32).map(|v| comp_rep[comp[v as usize] as usize]).collect();
        // Nothing merged → no compaction needed.
        if rep.iter().enumerate().all(|(v, &r)| v as u32 == r) {
            return;
        }
        // --- 3. Dense renumbering of representatives; TOP's rep gets dense id 0. ---
        let mut dense = vec![u32::MAX; n];
        let top_rep = rep[self.pt.top.0 as usize];
        dense[top_rep as usize] = 0;
        let mut nnew = 1u32;
        for v in 0..n as u32 {
            if rep[v as usize] == v && dense[v as usize] == u32::MAX {
                dense[v as usize] = nnew;
                nnew += 1;
            }
        }
        let new_id = |old: Node| -> Node { Node(dense[rep[old.0 as usize] as usize]) };
        // --- 4. Rebuild the points-to sets (elements remapped too). ---
        let mut new_pts: Vec<HashSet<Node>> = vec![HashSet::new(); nnew as usize];
        for (v, set) in self.pt.pts.iter().enumerate() {
            let nv = new_id(Node(v as u32));
            for &t in set {
                new_pts[nv.0 as usize].insert(new_id(t));
            }
        }
        // Names, poison, saturated.
        let mut new_name: HashMap<Node, String> = HashMap::new();
        for (&node, nm) in &self.pt.name {
            new_name.entry(new_id(node)).or_insert_with(|| nm.clone());
        }
        let new_poisoned: HashSet<Node> = self.pt.poisoned.iter().map(|&x| new_id(x)).collect();
        let new_saturated: HashSet<Node> = self.pt.saturated.iter().map(|&x| new_id(x)).collect();
        // Field cells, with key-collision equalisation.
        let mut new_field_cell: HashMap<(Node, u64), Node> = HashMap::new();
        let mut equalize: Vec<(Node, Node)> = Vec::new();
        for (&(obj, off), &cell) in &self.pt.field_cell {
            let key = (new_id(obj), off);
            let val = new_id(cell);
            match new_field_cell.get(&key) {
                Some(&existing) if existing != val => equalize.push((existing, val)),
                Some(_) => {}
                None => {
                    new_field_cell.insert(key, val);
                }
            }
        }
        // Constraint vectors: remap endpoints, drop self-copies, dedup.
        let dedup_pairs = |src: &[(Node, Node)], drop_self: bool, extra: &[(Node, Node)]| {
            let mut seen: HashSet<(Node, Node)> = HashSet::new();
            let mut out: Vec<(Node, Node)> = Vec::new();
            for &(a, b) in src {
                let (a, b) = (new_id(a), new_id(b));
                if drop_self && a == b {
                    continue;
                }
                if seen.insert((a, b)) {
                    out.push((a, b));
                }
            }
            for &(a, b) in extra {
                if drop_self && a == b {
                    continue;
                }
                if seen.insert((a, b)) {
                    out.push((a, b));
                }
            }
            out
        };
        let new_addr = dedup_pairs(&self.pt.addr, false, &[]);
        // Equalise-edges are bidirectional copies between merged field cells.
        let mut eq_edges: Vec<(Node, Node)> = Vec::with_capacity(equalize.len() * 2);
        for (a, b) in equalize {
            eq_edges.push((a, b));
            eq_edges.push((b, a));
        }
        let new_copy = dedup_pairs(&self.pt.copy, true, &eq_edges);
        let new_load = dedup_pairs(&self.pt.load, false, &[]);
        let new_store = dedup_pairs(&self.pt.store, false, &[]);
        let mut seen_gep: HashSet<(Node, Node, u64)> = HashSet::new();
        let mut new_gep: Vec<(Node, Node, u64)> = Vec::new();
        for &(d, s, off) in &self.pt.gep {
            let e = (new_id(d), new_id(s), off);
            if seen_gep.insert(e) {
                new_gep.push(e);
            }
        }
        // Commit the compacted relation.
        self.pt.n = nnew;
        self.pt.pts = new_pts;
        self.pt.name = new_name;
        self.pt.poisoned = new_poisoned;
        self.pt.saturated = new_saturated;
        self.pt.field_cell = new_field_cell;
        self.pt.addr = new_addr;
        self.pt.copy = new_copy;
        self.pt.load = new_load;
        self.pt.store = new_store;
        self.pt.gep = new_gep;
        // TOP is unchanged (rep of its component, dense id 0).
        debug_assert_eq!(new_id(self.pt.top).0, 0);
        // --- 5. Translate the node-keyed side tables. ---
        for v in self.reg_node.values_mut() {
            *v = new_id(*v);
        }
        for v in self.global_obj.values_mut() {
            *v = new_id(*v);
        }
        // obj_global: on a name collision (two distinct named objects merged), drop the entry so
        // devirt declines rather than resolving to an arbitrary one — sound (never a wrong target).
        let mut new_obj_global: HashMap<Node, String> = HashMap::new();
        let mut collided: HashSet<Node> = HashSet::new();
        for (&node, nm) in &self.obj_global {
            let k = new_id(node);
            match new_obj_global.get(&k) {
                Some(existing) if existing != nm => {
                    collided.insert(k);
                }
                _ => {
                    new_obj_global.insert(k, nm.clone());
                }
            }
        }
        for k in collided {
            new_obj_global.remove(&k);
        }
        self.obj_global = new_obj_global;
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

    // Offline copy-cycle collapse must preserve a devirt singleton across a compaction. Build a
    // register cycle `r1 ⊇ r2`, `r2 ⊇ r1` where `r1 = &G` (a named function object): the cycle
    // compacts r1/r2 into one node, and BOTH registers must still resolve to the singleton `G` with
    // its `obj_global` name intact.
    #[test]
    fn collapse_preserves_singleton_through_a_copy_cycle() {
        let mut pp = ProgramPointsTo::new();
        let g = pp.pt.new_object("G");
        let r1 = pp.pt.new_var();
        let r2 = pp.pt.new_var();
        pp.pt.address_of(r1, g); // r1 ⊇ {G}
        pp.pt.assign(r1, r2); // r1 ⊇ r2
        pp.pt.assign(r2, r1); // r2 ⊇ r1  → a copy cycle
        pp.obj_global.insert(g, "G".into());
        pp.reg_node.insert((0, RegId(1)), r1);
        pp.reg_node.insert((0, RegId(2)), r2);
        let n_before = pp.pt.n;
        pp.collapse_copy_cycles();
        assert!(pp.pt.n < n_before, "the r1/r2 copy cycle must compact the node count");
        pp.pt.solve();
        for r in [RegId(1), RegId(2)] {
            let node = pp.reg_node[&(0, r)];
            let obj = pp.pt.singleton_object(node).expect("singleton survives collapse");
            assert_eq!(
                pp.obj_global.get(&obj).map(String::as_str),
                Some("G"),
                "obj_global name must survive the remap for {r:?}"
            );
        }
    }

    // Field-sensitivity must survive a collapse when the base pointer of a field access sits in a
    // copy cycle: `p ⊇ q`, `q ⊇ p`, `p = &obj`; `*(p->8) = &target`; `ld = *(p->8)`. After p/q
    // collapse, the gep endpoint remaps to the representative, the field cell `(obj, 8)` is created
    // for it during solve, and `ld` must still resolve to the clean singleton `target`.
    #[test]
    fn collapse_preserves_field_through_a_cycle_pointer() {
        let mut pp = ProgramPointsTo::new();
        let obj = pp.pt.new_object("obj");
        let target = pp.pt.new_object("target");
        let p = pp.pt.new_var();
        let q = pp.pt.new_var();
        let av = pp.pt.new_var();
        let gp = pp.pt.new_var();
        let ld = pp.pt.new_var();
        pp.pt.address_of(p, obj); // p ⊇ {obj}
        pp.pt.assign(p, q); // p ⊇ q
        pp.pt.assign(q, p); // q ⊇ p → cycle
        pp.pt.address_of(av, target); // av ⊇ {target}
        pp.pt.gep(gp, p, 8); // gp = &p->8 (gep off a cycle node)
        pp.pt.store(av, gp); // *(p->8) = &target
        pp.pt.load(ld, gp); // ld = *(p->8)
        pp.collapse_copy_cycles();
        pp.pt.solve();
        let o = pp.pt.singleton_object(ld).expect("ld resolves to a singleton after collapse");
        assert_eq!(pp.pt.name_of(o), Some("target"), "field-sensitivity survives the cycle collapse");
    }

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

    // A points-to set that overflows the cap collapses to TOP (memory bound) and is then never a
    // clean singleton — the solver stays memory-bounded on huge relations without a false devirt.
    #[test]
    fn oversized_set_saturates_to_top() {
        let mut pt = PointsTo::new();
        let p = pt.new_var();
        // Point `p` at MAX_PTS_SET + 5 distinct objects.
        for i in 0..(MAX_PTS_SET + 5) {
            let o = pt.new_object(format!("o{i}"));
            pt.address_of(p, o);
        }
        pt.solve();
        assert!(pt.points_to(p).contains(&pt.top()), "an overflowing set collapses to TOP");
        assert_eq!(pt.singleton_object(p), None, "a saturated node is never a clean singleton");
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
            valid_range: None,
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
            valid_range: None,
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
            valid_range: None,
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

    // --- P4: heap/param-rooted `obj->ops->fn()` via the constant vtable initializer ---

    // Build a module whose `dispatch` fn allocates an object, stores `&G_ops` into its `ops`
    // field (offset 8), loads it, geps the `fn` field (offset 16) and loads the function pointer
    // — the classic heap dispatch. `G_ops.fn` is supplied out-of-line by `global_fn_ptrs`
    // (the constant vtable), pointing at `target`. `ambiguous` stores a *second* ops global into
    // the same field first, to make the field non-singleton.
    fn dispatch_module(ambiguous: bool) -> (IrModule, RegId) {
        let (obj, opsfield, opsp, fnfield, fnp) = (RegId(0), RegId(1), RegId(2), RegId(3), RegId(4));
        let mut bb = BasicBlock::new(BlockId(0), Terminator::Return(None));
        bb.insts.push(IrInst::Alloc {
            dst: obj, region: RegionKind::Heap, elem: IrTy::int(8), count: IrOp::int(64, 64), align: 8,
        });
        bb.insts.push(IrInst::PtrOffset {
            dst: opsfield, base: IrOp::Reg(obj), index: IrOp::int(64, 8), elem: IrTy::int(8),
        });
        if ambiguous {
            bb.insts.push(IrInst::Store {
                ty: ptr_ty(), ptr: IrOp::Reg(opsfield),
                value: IrOp::Const(IrConst::Symbol("G_other".into())), align: 8, volatile: false,
            });
        }
        bb.insts.push(IrInst::Store {
            ty: ptr_ty(), ptr: IrOp::Reg(opsfield),
            value: IrOp::Const(IrConst::Symbol("G_ops".into())), align: 8, volatile: false,
        });
        bb.insts.push(IrInst::Load {
            dst: opsp, ty: ptr_ty(), ptr: IrOp::Reg(opsfield), align: 8, volatile: false,
            valid_range: None,
        });
        bb.insts.push(IrInst::PtrOffset {
            dst: fnfield, base: IrOp::Reg(opsp), index: IrOp::int(64, 16), elem: IrTy::int(8),
        });
        bb.insts.push(IrInst::Load {
            dst: fnp, ty: ptr_ty(), ptr: IrOp::Reg(fnfield), align: 8, volatile: false,
            valid_range: None,
        });
        let dispatch = IrFunc {
            id: FuncId(0), name: "dispatch".into(), params: vec![], ret_ty: IrTy::Unit,
            blocks: vec![bb], entry: BlockId(0),
        };
        let target = IrFunc {
            id: FuncId(1), name: "target".into(), params: vec![], ret_ty: IrTy::Unit,
            blocks: vec![BasicBlock::new(BlockId(0), Terminator::Return(None))], entry: BlockId(0),
        };
        let mut m = IrModule::new("m");
        m.functions.push(dispatch);
        m.functions.push(target);
        // The constant vtable: `G_ops.fn` (offset 16) holds `&target`.
        m.global_fn_ptrs.insert("G_ops".into(), vec![(16, FuncId(1))]);
        (m, fnp)
    }

    #[test]
    fn p4_heap_dispatch_devirts_via_vtable_initializer() {
        let (m, fnp) = dispatch_module(false);
        let mp = analyze_module(&m);
        assert_eq!(mp.devirt_global(FuncId(0), fnp), Some("target"), "the loaded fn ptr resolves");
        let dv = mp.name_keyed_devirt();
        assert_eq!(dv.get(&("dispatch".to_string(), fnp)).map(String::as_str), Some("target"));
    }

    #[test]
    fn p4_ambiguous_ops_field_does_not_devirt() {
        let (m, fnp) = dispatch_module(true);
        let mp = analyze_module(&m);
        // Two different ops globals reach `obj->ops`, so `opsp` is not a singleton; the `fn` load
        // sees both vtables' entries (only `G_ops`'s is populated, but the field is ambiguous), so
        // no clean devirt. Soundness: an ambiguous dispatch must NOT resolve to one target.
        assert_eq!(mp.name_keyed_devirt().get(&("dispatch".to_string(), fnp)), None);
    }

    // A data global (not a function) that a register cleanly points to must NOT be devirt'd — the
    // resolution is only for call targets that name a real function.
    #[test]
    fn p4_data_singleton_is_not_a_devirt_target() {
        let mut pp = ProgramPointsTo::new();
        let (obj, field, loaded) = (RegId(0), RegId(1), RegId(2));
        let mut bb = BasicBlock::new(BlockId(0), Terminator::Return(None));
        bb.insts.push(IrInst::Alloc {
            dst: obj, region: RegionKind::Heap, elem: IrTy::int(8), count: IrOp::int(64, 64), align: 8,
        });
        bb.insts.push(IrInst::PtrOffset {
            dst: field, base: IrOp::Reg(obj), index: IrOp::int(64, 8), elem: IrTy::int(8),
        });
        bb.insts.push(IrInst::Store {
            ty: ptr_ty(), ptr: IrOp::Reg(field),
            value: IrOp::Const(IrConst::Symbol("some_data".into())), align: 8, volatile: false,
        });
        bb.insts.push(IrInst::Load {
            dst: loaded, ty: ptr_ty(), ptr: IrOp::Reg(field), align: 8, volatile: false,
            valid_range: None,
        });
        let f = IrFunc {
            id: FuncId(0), name: "reader".into(), params: vec![], ret_ty: IrTy::Unit,
            blocks: vec![bb], entry: BlockId(0),
        };
        let mut m = IrModule::new("m");
        m.functions.push(f);
        pp.push_module(&m);
        let mp = pp.finalize();
        assert_eq!(mp.devirt_global(FuncId(0), loaded), Some("some_data"), "resolves the object");
        assert_eq!(mp.name_keyed_devirt().get(&("reader".to_string(), loaded)), None, "but not as a call");
    }

    // `merge` of two shards must give the same devirt as a single sequential push: split the
    // cross-module dispatch (module A stores `&G_ops` and passes the object; module B loads the
    // field and the `fn`) across two independently-built `ProgramPointsTo`, merge in order, and
    // confirm B's function-pointer load still resolves to `target` (globals unified across shards).
    #[test]
    fn p4_merge_across_shards_resolves_like_sequential() {
        // Module A: fn make() { obj = alloc; obj.ops(@8) = &G_ops; use(obj); }  + vtable G_ops.fn=&target
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
            dst: None, callee: csolver_ir::Callee::Symbol("use".into()), args: vec![IrOp::Reg(obj)],
            ret_ty: IrTy::Unit, ret_ref: None,
        });
        let make = IrFunc {
            id: FuncId(0), name: "make".into(), params: vec![], ret_ty: IrTy::Unit,
            blocks: vec![abb], entry: BlockId(0),
        };
        let target = IrFunc {
            id: FuncId(1), name: "target".into(), params: vec![], ret_ty: IrTy::Unit,
            blocks: vec![BasicBlock::new(BlockId(0), Terminator::Return(None))], entry: BlockId(0),
        };
        let mut ma = IrModule::new("a");
        ma.functions.push(make);
        ma.functions.push(target);
        ma.global_fn_ptrs.insert("G_ops".into(), vec![(16, FuncId(1))]);

        // Module B: fn use(o) { opsp = o.ops(@8); fnp = opsp.fn(@16); }
        let (o, field2, opsp, fnfield, fnp) = (RegId(0), RegId(1), RegId(2), RegId(3), RegId(4));
        let mut bbb = BasicBlock::new(BlockId(0), Terminator::Return(None));
        bbb.insts.push(IrInst::PtrOffset {
            dst: field2, base: IrOp::Reg(o), index: IrOp::int(64, 8), elem: IrTy::int(8),
        });
        bbb.insts.push(IrInst::Load {
            dst: opsp, ty: ptr_ty(), ptr: IrOp::Reg(field2), align: 8, volatile: false,
            valid_range: None,
        });
        bbb.insts.push(IrInst::PtrOffset {
            dst: fnfield, base: IrOp::Reg(opsp), index: IrOp::int(64, 16), elem: IrTy::int(8),
        });
        bbb.insts.push(IrInst::Load {
            dst: fnp, ty: ptr_ty(), ptr: IrOp::Reg(fnfield), align: 8, volatile: false,
            valid_range: None,
        });
        let usef = IrFunc {
            id: FuncId(0), name: "use".into(), params: vec![(o, ptr_ty())], ret_ty: IrTy::Unit,
            blocks: vec![bbb], entry: BlockId(0),
        };
        let mut mb = IrModule::new("b");
        mb.functions.push(usef);

        // Build each shard independently, then merge in file order (A before B).
        let mut sa = ProgramPointsTo::new();
        sa.push_module(&ma);
        let mut sb = ProgramPointsTo::new();
        sb.push_module(&mb);
        sa.merge(sb);
        let mp = sa.finalize();
        assert_eq!(
            mp.name_keyed_devirt().get(&("use".to_string(), fnp)).map(String::as_str),
            Some("target"),
            "the vtable (shard A) and the dispatch (shard B) unify across the merge",
        );
    }
}
