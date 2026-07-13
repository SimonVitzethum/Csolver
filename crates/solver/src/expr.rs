//! A hash-consed symbolic bit-vector expression IR.
//!
//! Every distinct sub-expression is interned exactly once in an [`ExprCtx`]
//! (structural sharing / hash-consing), and builders simplify on the fly
//! (constant folding plus algebraic identities). This is the value layer the
//! symbolic executor, path conditions, and the decision procedure all share.
//!
//! Booleans are bit-vectors of width 1; the dedicated [`Node::Bool`] and
//! comparison/connective nodes keep boolean structure explicit for the solver.

use csolver_core::BitVector;
use csolver_core::{FxHashMap, FxHashSet};

/// A handle to an interned expression node within an [`ExprCtx`].
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct ExprId(u32);

impl ExprId {
    /// The underlying interning index.
    pub fn index(self) -> usize {
        self.0 as usize
    }
}

/// Binary bit-vector operators.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum BvOp {
    /// Addition.
    Add,
    /// Subtraction.
    Sub,
    /// Multiplication.
    Mul,
    /// Unsigned division.
    UDiv,
    /// Signed division.
    SDiv,
    /// Unsigned remainder.
    URem,
    /// Signed remainder.
    SRem,
    /// Bitwise and.
    And,
    /// Bitwise or.
    Or,
    /// Bitwise xor.
    Xor,
    /// Shift left.
    Shl,
    /// Logical shift right.
    LShr,
    /// Arithmetic shift right.
    AShr,
}

/// Comparison predicates producing a boolean.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum CmpOp {
    /// Equal.
    Eq,
    /// Not equal.
    Ne,
    /// Unsigned `<`.
    Ult,
    /// Unsigned `<=`.
    Ule,
    /// Unsigned `>`.
    Ugt,
    /// Unsigned `>=`.
    Uge,
    /// Signed `<`.
    Slt,
    /// Signed `<=`.
    Sle,
    /// Signed `>`.
    Sgt,
    /// Signed `>=`.
    Sge,
}

impl CmpOp {
    /// The logical negation of this predicate.
    pub fn negate(self) -> CmpOp {
        match self {
            CmpOp::Eq => CmpOp::Ne,
            CmpOp::Ne => CmpOp::Eq,
            CmpOp::Ult => CmpOp::Uge,
            CmpOp::Uge => CmpOp::Ult,
            CmpOp::Ule => CmpOp::Ugt,
            CmpOp::Ugt => CmpOp::Ule,
            CmpOp::Slt => CmpOp::Sge,
            CmpOp::Sge => CmpOp::Slt,
            CmpOp::Sle => CmpOp::Sgt,
            CmpOp::Sgt => CmpOp::Sle,
        }
    }
}

/// An interned expression node. Children are [`ExprId`]s into the same context.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum Node {
    /// A bit-vector constant.
    Const(BitVector),
    /// A symbolic input variable.
    Sym {
        /// A stable name (used in counterexample models).
        name: String,
        /// Bit width.
        width: u32,
    },
    /// A binary bit-vector operation.
    Bin {
        /// Operator.
        op: BvOp,
        /// Left operand.
        a: ExprId,
        /// Right operand.
        b: ExprId,
    },
    /// A comparison (yields a boolean).
    Cmp {
        /// Predicate.
        op: CmpOp,
        /// Left operand.
        a: ExprId,
        /// Right operand.
        b: ExprId,
    },
    /// A boolean literal.
    Bool(bool),
    /// Boolean negation.
    Not(ExprId),
    /// Boolean conjunction (n-ary, normalized).
    And(Vec<ExprId>),
    /// Boolean disjunction (n-ary, normalized).
    Or(Vec<ExprId>),
    /// If-then-else / select / phi: `if c then t else e`.
    Ite {
        /// Boolean condition.
        c: ExprId,
        /// Then value.
        t: ExprId,
        /// Else value.
        e: ExprId,
    },
    /// Zero-extend `val` to a wider bit width (the node's own width). The high bits
    /// are zero, so numerically the value is unchanged (unsigned).
    Zext(ExprId),
    /// Sign-extend `val` to a wider bit width (the node's own width). The high bits
    /// replicate `val`'s top (sign) bit, so the two's-complement value is unchanged.
    Sext(ExprId),
}

/// The boolean width sentinel.
const BOOL_WIDTH: u32 = 1;

/// A hash-consing arena of expression nodes.
#[derive(Debug, Default)]
pub struct ExprCtx {
    nodes: Vec<Node>,
    widths: Vec<u32>,
    intern: FxHashMap<Node, ExprId>,
}

impl ExprCtx {
    /// Create an empty context.
    pub fn new() -> Self {
        ExprCtx::default()
    }

    /// The number of distinct interned nodes (a proxy for sharing efficiency).
    pub fn len(&self) -> usize {
        self.nodes.len()
    }

    /// Whether the context is empty.
    pub fn is_empty(&self) -> bool {
        self.nodes.is_empty()
    }

    /// The node behind an id.
    pub fn node(&self, id: ExprId) -> &Node {
        &self.nodes[id.index()]
    }

    /// The bit width of an expression (booleans are width 1).
    pub fn width(&self, id: ExprId) -> u32 {
        self.widths[id.index()]
    }

    /// The set of symbolic input variables (`Node::Sym`) reachable from `root`, as sorted, unique
    /// `ExprId`s (each `Sym` is interned once, so its id identifies the variable). Used as a cheap,
    /// exact relevance test — whether two expressions share any variable — so the decision procedure
    /// can drop path-condition assumptions that cannot affect an entailment.
    pub fn symbols_of(&self, root: ExprId) -> Vec<ExprId> {
        let mut set = Vec::new();
        let mut stack = vec![root];
        let mut seen = FxHashSet::default();
        while let Some(x) = stack.pop() {
            if !seen.insert(x) {
                continue;
            }
            match self.node(x) {
                Node::Sym { .. } => set.push(x),
                Node::Const(_) | Node::Bool(_) => {}
                Node::Not(a) | Node::Zext(a) | Node::Sext(a) => stack.push(*a),
                Node::Bin { a, b, .. } | Node::Cmp { a, b, .. } => {
                    stack.push(*a);
                    stack.push(*b);
                }
                Node::And(v) | Node::Or(v) => stack.extend(v.iter().copied()),
                Node::Ite { c, t, e } => {
                    stack.push(*c);
                    stack.push(*t);
                    stack.push(*e);
                }
            }
        }
        set.sort_unstable();
        set.dedup();
        set
    }

    /// The constant value of an expression, if it is a literal.
    pub fn as_const(&self, id: ExprId) -> Option<BitVector> {
        match self.node(id) {
            Node::Const(bv) => Some(*bv),
            _ => None,
        }
    }

    /// The boolean value of an expression, if it is a boolean literal.
    pub fn as_bool(&self, id: ExprId) -> Option<bool> {
        match self.node(id) {
            Node::Bool(b) => Some(*b),
            _ => None,
        }
    }

    fn intern(&mut self, node: Node, width: u32) -> ExprId {
        if let Some(&id) = self.intern.get(&node) {
            return id;
        }
        let id = ExprId(self.nodes.len() as u32);
        self.nodes.push(node.clone());
        self.widths.push(width);
        self.intern.insert(node, id);
        id
    }

    // --- builders (simplifying) --------------------------------------------

    /// A bit-vector constant.
    pub fn constant(&mut self, value: BitVector) -> ExprId {
        let w = value.width();
        self.intern(Node::Const(value), w)
    }

    /// Zero-extend `val` to `to` bits. Identity if already `to` bits or wider (a
    /// wider value is returned unchanged — callers only widen). A constant is folded.
    pub fn zext(&mut self, val: ExprId, to: u32) -> ExprId {
        let w = self.width(val);
        if w >= to {
            return val;
        }
        if let Node::Const(bv) = self.node(val) {
            return self.int(to, bv.unsigned());
        }
        self.intern(Node::Zext(val), to)
    }

    /// Sign-extend `val` to `to` bits (the high bits replicate the sign bit).
    /// Identity if already `to` bits or wider. A constant is folded via its signed value.
    pub fn sext(&mut self, val: ExprId, to: u32) -> ExprId {
        let w = self.width(val);
        if w >= to {
            return val;
        }
        if let Node::Const(bv) = self.node(val) {
            // The signed value re-encoded at the wider width is the sign-extension.
            return self.int(to, bv.signed() as u128);
        }
        self.intern(Node::Sext(val), to)
    }

    /// An integer constant of the given width.
    pub fn int(&mut self, width: u32, value: u128) -> ExprId {
        self.constant(BitVector::new(width, value))
    }

    /// A symbolic variable.
    pub fn symbol(&mut self, name: impl Into<String>, width: u32) -> ExprId {
        self.intern(
            Node::Sym {
                name: name.into(),
                width,
            },
            width,
        )
    }

    /// A boolean literal.
    pub fn boolean(&mut self, b: bool) -> ExprId {
        self.intern(Node::Bool(b), BOOL_WIDTH)
    }

    /// A binary operation, folding constants and applying simple identities.
    pub fn bin(&mut self, op: BvOp, a: ExprId, b: ExprId) -> ExprId {
        let width = self.width(a);
        // Constant folding.
        if let (Some(x), Some(y)) = (self.as_const(a), self.as_const(b)) {
            if x.width() == y.width() {
                if let Some(v) = fold_bin(op, x, y, width) {
                    return self.constant(v);
                }
            }
        }
        // Algebraic identities that are always sound.
        let zero = self.as_const(a).map(|v| v.is_zero());
        let zero_b = self.as_const(b).map(|v| v.is_zero());
        let one = self.as_const(a).map(|v| v.unsigned() == 1);
        let one_b = self.as_const(b).map(|v| v.unsigned() == 1);
        match op {
            BvOp::Add | BvOp::Sub | BvOp::Or | BvOp::Xor if zero_b == Some(true) => return a,
            BvOp::Add | BvOp::Or if zero == Some(true) => return b,
            BvOp::Mul | BvOp::And if zero_b == Some(true) => return b, // x*0 = 0, x&0 = 0
            BvOp::Mul | BvOp::And if zero == Some(true) => return a,
            // x*1 = x / 1*x = x: a unit stride (`&[u8]`, `&[T]` of a 1-byte
            // element) must not leave an opaque `Mul` node — the linear procedure
            // then fails to relate the offset to the length and falls back to the
            // (slow) bit-precise path.
            BvOp::Mul if one_b == Some(true) => return a,
            BvOp::Mul if one == Some(true) => return b,
            BvOp::Sub if a == b => return self.int(width, 0),
            _ => {}
        }
        self.intern(Node::Bin { op, a, b }, width)
    }

    /// A comparison, folding constants.
    pub fn cmp(&mut self, op: CmpOp, a: ExprId, b: ExprId) -> ExprId {
        if let (Some(x), Some(y)) = (self.as_const(a), self.as_const(b)) {
            if x.width() == y.width() {
                return self.boolean(eval_cmp(op, x, y));
            }
        }
        if a == b {
            // x == x is true, x < x is false, etc. — decided structurally.
            let v = matches!(op, CmpOp::Eq | CmpOp::Ule | CmpOp::Uge | CmpOp::Sle | CmpOp::Sge);
            return self.boolean(v);
        }
        self.intern(Node::Cmp { op, a, b }, BOOL_WIDTH)
    }

    /// Boolean negation, pushing through literals/`not`/comparisons.
    pub fn not(&mut self, e: ExprId) -> ExprId {
        match self.node(e).clone() {
            Node::Bool(b) => self.boolean(!b),
            Node::Not(inner) => inner,
            Node::Cmp { op, a, b } => self.cmp(op.negate(), a, b),
            _ => self.intern(Node::Not(e), BOOL_WIDTH),
        }
    }

    /// Boolean conjunction, flattening and dropping trivial operands.
    pub fn and(&mut self, parts: Vec<ExprId>) -> ExprId {
        let mut flat = Vec::new();
        for p in parts {
            match self.node(p).clone() {
                Node::Bool(true) => {}
                Node::Bool(false) => return self.boolean(false),
                Node::And(inner) => flat.extend(inner),
                _ => flat.push(p),
            }
        }
        flat.sort_unstable();
        flat.dedup();
        match flat.len() {
            0 => self.boolean(true),
            1 => flat[0],
            _ => self.intern(Node::And(flat), BOOL_WIDTH),
        }
    }

    /// Boolean disjunction, flattening and dropping trivial operands.
    pub fn or(&mut self, parts: Vec<ExprId>) -> ExprId {
        let mut flat = Vec::new();
        for p in parts {
            match self.node(p).clone() {
                Node::Bool(false) => {}
                Node::Bool(true) => return self.boolean(true),
                Node::Or(inner) => flat.extend(inner),
                _ => flat.push(p),
            }
        }
        flat.sort_unstable();
        flat.dedup();
        match flat.len() {
            0 => self.boolean(false),
            1 => flat[0],
            _ => self.intern(Node::Or(flat), BOOL_WIDTH),
        }
    }

    /// If-then-else, collapsing a constant condition or equal arms.
    pub fn ite(&mut self, c: ExprId, t: ExprId, e: ExprId) -> ExprId {
        if let Some(b) = self.as_bool(c) {
            return if b { t } else { e };
        }
        if t == e {
            return t;
        }
        let width = self.width(t);
        self.intern(Node::Ite { c, t, e }, width)
    }
}

/// Fold a binary op over two constants, or `None` if undefined (e.g. div by 0).
fn fold_bin(op: BvOp, x: BitVector, y: BitVector, width: u32) -> Option<BitVector> {
    let xu = x.unsigned();
    let yu = y.unsigned();
    let w = width;
    let r: u128 = match op {
        BvOp::Add => xu.wrapping_add(yu),
        BvOp::Sub => xu.wrapping_sub(yu),
        BvOp::Mul => xu.wrapping_mul(yu),
        BvOp::UDiv => {
            if yu == 0 {
                return None;
            }
            xu / yu
        }
        BvOp::URem => {
            if yu == 0 {
                return None;
            }
            xu % yu
        }
        BvOp::SDiv => {
            let ys = y.signed();
            if ys == 0 {
                return None;
            }
            x.signed().wrapping_div(ys) as u128
        }
        BvOp::SRem => {
            let ys = y.signed();
            if ys == 0 {
                return None;
            }
            x.signed().wrapping_rem(ys) as u128
        }
        BvOp::And => xu & yu,
        BvOp::Or => xu | yu,
        BvOp::Xor => xu ^ yu,
        BvOp::Shl => {
            if yu >= w as u128 {
                0
            } else {
                xu << yu
            }
        }
        BvOp::LShr => {
            if yu >= w as u128 {
                0
            } else {
                xu >> yu
            }
        }
        BvOp::AShr => {
            let s = x.signed();
            if yu >= w as u128 {
                if s < 0 {
                    u128::MAX
                } else {
                    0
                }
            } else {
                (s >> yu) as u128
            }
        }
    };
    Some(BitVector::new(w, r))
}

/// Evaluate a comparison over two constants.
fn eval_cmp(op: CmpOp, x: BitVector, y: BitVector) -> bool {
    let (xu, yu) = (x.unsigned(), y.unsigned());
    let (xs, ys) = (x.signed(), y.signed());
    match op {
        CmpOp::Eq => xu == yu,
        CmpOp::Ne => xu != yu,
        CmpOp::Ult => xu < yu,
        CmpOp::Ule => xu <= yu,
        CmpOp::Ugt => xu > yu,
        CmpOp::Uge => xu >= yu,
        CmpOp::Slt => xs < ys,
        CmpOp::Sle => xs <= ys,
        CmpOp::Sgt => xs > ys,
        CmpOp::Sge => xs >= ys,
    }
}

#[cfg(test)]
#[path = "expr_tests.rs"]
mod tests;
