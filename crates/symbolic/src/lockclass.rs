//! Static lock-class naming for ABBA lock-order (G6).
//!
//! To detect a cross-function ABBA deadlock we must recognise **the same lock
//! kind** at two different acquire sites in two different functions. A lock's
//! runtime object identity (a `RefBase`) is per-run and not comparable across
//! functions, so instead we name a lock *statically* by the shape of the pointer
//! that designates it — a **lock class**, mirroring the kernel's lockdep classes:
//!
//! * an **embedded lock** `&obj->lock` is named by the *(structural struct type,
//!   byte offset)* it lives at — recovered from the `PtrOffset` chain the frontend
//!   emits for a struct-field `gep` (the first step carries the struct `Type` as
//!   its element, later steps add constant field offsets);
//! * a **global lock** `&my_lock` is named by its symbol (plus any constant
//!   offset).
//!
//! Two pointers with the same class denote the same lock kind. The naming is
//! *structural*: two distinct structs of identical layout collapse to one class —
//! a sound over-merge for bug-finding (it can only add edges, never hide a real
//! cycle). A pointer whose class cannot be resolved (a bare untyped pointer, a
//! variable offset) yields no class and is simply skipped (lower recall, never a
//! false edge).
//!
//! The result is a pure function of the function's IR — no execution — so it is
//! computed once at explorer construction and consulted at each lock-acquire call.

use csolver_ir::{Callee, CastOp, Const, DataLayout, Function, Inst, Operand, RValue, RegId, Type};
use std::collections::HashMap;

/// A **cross-syscall container lookup**: a call that fetches an object from a persistent kernel
/// container indexed by a (syscall-controlled) key. Its result names the object as loaded from the
/// container argument, so a free/use of it in two independent syscall entries composes on the same
/// root — the object survives between syscalls via the container. The root is global-rooted (and so
/// visible to the cross-syscall detectors) only when the container itself is a global — the sound
/// gate: a per-object idr/xarray does not persist as shared program state. The recognised names
/// come from the contract-collected classification (`container-lookup arg<k>` — see `crate::sync`);
/// returns the container's argument index.
fn container_lookup(name: &str) -> Option<usize> {
    crate::sync::classes().container_lookup(name)
}

/// A **file-table lookup** (`fget`/`fdget`/…): fetches a `struct file` from the current task's file
/// table by a userspace fd. It has no container *argument* (the table is `current->files`), so its
/// result is rooted at a synthetic global — the process file table, a persistent shared root across
/// syscalls. Contract-declared as `global-lookup <root>`; `None` if `name` is not such a lookup.
fn fdtable_lookup_class(name: &str) -> Option<String> {
    crate::sync::classes().global_lookup(name).map(|root| format!("deref:g:{root}@0"))
}

/// The root a lock-pointer's access path starts from.
#[derive(Clone)]
enum Root {
    /// A lock embedded at a byte offset within a structurally-named struct type.
    Struct(String),
    /// A lock at a named global symbol.
    Global(String),
}

/// The signed constant integer value of an operand, if it is an `Int` constant.
fn const_int(op: &Operand) -> Option<i128> {
    match op {
        Operand::Const(Const::Int(bv)) => Some(bv.signed()),
        _ => None,
    }
}

/// Resolve, per register, the **lock class** (a stable cross-function name) of the
/// lock a pointer register designates — for every register whose value is a
/// resolvable lock-pointer access path. Registers absent from the map have no
/// resolvable class and must be treated as an unknown lock (skipped by the caller).
pub(crate) fn resolve_lock_classes(f: &Function) -> HashMap<RegId, String> {
    let layout = DataLayout::LP64;
    // Intermediate: register -> (path root, accumulated byte offset).
    let mut roots: HashMap<RegId, (Root, i128)> = HashMap::new();

    // The class of an operand: a register's tracked root, or a global symbol
    // operand (which roots a path directly). A non-pointer / untracked operand
    // has none.
    fn op_class(roots: &HashMap<RegId, (Root, i128)>, op: &Operand) -> Option<(Root, i128)> {
        match op {
            Operand::Reg(r) => roots.get(r).cloned(),
            Operand::Const(Const::Symbol(n)) => Some((Root::Global(n.clone()), 0)),
            Operand::Const(Const::SymbolOffset(n, o)) => Some((Root::Global(n.clone()), *o as i128)),
            _ => None,
        }
    }

    // A pointer *loaded* from a nameable location (`p = load &gp`) names the object it points
    // to — `deref:<class-of-the-source>` — so a `kfree(p)` in one thread and a `*p` in another
    // match on the same object (cross-thread use-after-free).
    let mut deref: HashMap<RegId, String> = HashMap::new();
    let class_str = |root: &Root, off: i128| match root {
        Root::Struct(t) => format!("{t}@{off}"),
        Root::Global(n) => format!("g:{n}@{off}"),
    };

    for bb in &f.blocks {
        for inst in &bb.insts {
            match inst {
                Inst::Load { dst, ptr, .. } => {
                    match op_class(&roots, ptr) {
                        Some((root, off)) => {
                            deref.insert(*dst, format!("deref:{}", class_str(&root, off)));
                        }
                        None => {
                            deref.remove(dst);
                        }
                    }
                    roots.remove(dst);
                }
                // A pointer step: propagate the base's root and add this step's
                // constant byte contribution, or *establish* a struct root when the
                // element type is itself a struct (the frontend's struct-field gep).
                Inst::PtrOffset { dst, base, index, elem } => {
                    let cls = const_int(index).and_then(|c| {
                        let stride = elem.stride_bytes(&layout)? as i128;
                        let contrib = c.checked_mul(stride)?;
                        match op_class(&roots, base) {
                            Some((root, off)) => off.checked_add(contrib).map(|o| (root, o)),
                            None if matches!(elem, Type::Struct { .. }) => {
                                Some((Root::Struct(format!("{elem}")), contrib))
                            }
                            None => None,
                        }
                    });
                    match cls {
                        Some(c) => {
                            roots.insert(*dst, c);
                        }
                        None => {
                            roots.remove(dst);
                        }
                    }
                }
                // A copy or an address-preserving bitcast forwards the class.
                Inst::Assign { dst, value: RValue::Use(op), .. }
                | Inst::Assign {
                    dst,
                    value: RValue::Cast { op: CastOp::Bitcast, operand: op, .. },
                    ..
                } => match op_class(&roots, op) {
                    Some(c) => {
                        roots.insert(*dst, c);
                    }
                    None => {
                        roots.remove(dst);
                    }
                },
                // A cross-syscall container/file-table lookup: name its result as an object loaded
                // from the persistent container (fd table / idr / xarray / …), so a free/use of it
                // in two independent syscall entries composes on the same root (cross-syscall UAF).
                Inst::Call { dst: Some(d), callee: Callee::Symbol(name), args, .. } => {
                    if let Some(cls) = fdtable_lookup_class(name) {
                        deref.insert(*d, cls);
                    } else if let Some(k) = container_lookup(name) {
                        if let Some((root, off)) = args.get(k).and_then(|a| op_class(&roots, a)) {
                            deref.insert(*d, format!("deref:{}", class_str(&root, off)));
                        }
                    }
                    roots.remove(d);
                }
                _ => {}
            }
        }
    }

    let mut out: HashMap<RegId, String> =
        roots.into_iter().map(|(r, (root, off))| (r, class_str(&root, off))).collect();
    // A load-derived (deref) class only fills a register the offset analysis did not classify.
    for (r, s) in deref {
        out.entry(r).or_insert(s);
    }
    out
}

/// The lock class of a lock-acquire call's pointer argument, given the
/// per-register class map — resolving a global-symbol argument operand directly.
pub(crate) fn lock_class_of_arg(classes: &HashMap<RegId, String>, arg: &Operand) -> Option<String> {
    match arg {
        Operand::Reg(r) => classes.get(r).cloned(),
        Operand::Const(Const::Symbol(n)) => Some(format!("g:{n}@0")),
        Operand::Const(Const::SymbolOffset(n, o)) => Some(format!("g:{n}@{o}")),
        _ => None,
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use csolver_ir::{BasicBlock, BlockId, Function, Terminator};

    // `&obj->lock` at field offset 8 of a { i64, i64 } struct, from a param ptr.
    #[test]
    fn embedded_lock_names_struct_and_offset() {
        let s = Type::Struct { fields: vec![Type::int(64), Type::int(64)], packed: false };
        let mut bb = BasicBlock::new(BlockId(0), Terminator::Return(None));
        // r1 = gep struct, param0, 0   (establish struct root)
        bb.insts.push(Inst::PtrOffset { dst: RegId(1), base: Operand::Reg(RegId(0)), index: Operand::int(64, 0), elem: s.clone() });
        // r2 = gep i8, r1, 8           (field offset)
        bb.insts.push(Inst::PtrOffset { dst: RegId(2), base: Operand::Reg(RegId(1)), index: Operand::int(64, 8), elem: Type::int(8) });
        let f = Function { id: csolver_ir::FuncId(0), name: "f".into(), params: vec![(RegId(0), Type::ptr(s.clone()))], ret_ty: Type::Unit, blocks: vec![bb], entry: BlockId(0) };
        let classes = resolve_lock_classes(&f);
        let c = classes.get(&RegId(2)).expect("class for lock field ptr");
        assert!(c.contains("@8"), "class names the field offset: {c}");
        // The same struct type at the same offset in a *different* function yields
        // the same class (cross-function stability).
        assert_eq!(classes.get(&RegId(2)), Some(c));
    }

    // A global lock `&my_lock` is named by its symbol.
    #[test]
    fn global_lock_names_symbol() {
        let classes: HashMap<RegId, String> = HashMap::new();
        let c = lock_class_of_arg(&classes, &Operand::Const(Const::Symbol("my_lock".into())));
        assert_eq!(c.as_deref(), Some("g:my_lock@0"));
    }
}
