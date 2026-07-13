use super::*;

/// Post-pass: inject the two obligation checks that are not tied to a specific call —
/// **resource-leak** checks (K) before every `Return`, and **secret-dependence** checks (L)
/// at every branch condition and memory index. Both are gated on the contracts actually
/// declaring the relevant labels (a leak state, a `secret` taint label), so a codebase that
/// names neither pays nothing.
pub(crate) fn inject_leak_and_secret_checks(f: &mut Function) {
    let leaks = leak_states();
    let secret = prov_interner().id("secret");
    if leaks.is_empty() && secret.is_none() {
        return;
    }
    for b in &mut f.blocks {
        // Secret-dependence at each memory index: inject a `SecretCheck` on the index
        // operand just before each `PtrOffset` (rebuild the inst list to keep order).
        if let Some(taint) = secret {
            let mut out = Vec::with_capacity(b.insts.len());
            for inst in b.insts.drain(..) {
                if let Inst::PtrOffset { index: Operand::Reg(r), .. } = &inst {
                    out.push(Inst::SecretCheck { val: Operand::Reg(*r), taint });
                }
                out.push(inst);
            }
            b.insts = out;
        }
        // Resource-leak checks + secret-dependent branch: appended after the body, before
        // the terminator is evaluated (the executor runs them in the step loop).
        match &b.term {
            Terminator::Return(ret) => {
                for &(protocol, state) in leaks {
                    b.insts.push(Inst::TypestateLeakCheck { protocol, state, escaping: ret.clone() });
                }
            }
            Terminator::CondBr { cond: Operand::Reg(r), .. } => {
                if let Some(taint) = secret {
                    b.insts.push(Inst::SecretCheck { val: Operand::Reg(*r), taint });
                }
            }
            _ => {}
        }
    }
}

/// The `(protocol, state)` leak-state declarations from all contracts (a `typestate-leak`
/// effect), interned to ids — a resource still in one of these states at a return is a leak.
pub(crate) fn leak_states() -> &'static [(u32, u32)] {
    static LEAKS: OnceLock<Vec<(u32, u32)>> = OnceLock::new();
    LEAKS.get_or_init(|| {
        let mut v = Vec::new();
        for c in contracts().iter() {
            for effect in &c.effects {
                if let Effect::TypestateLeak { protocol, state } = effect {
                    if let (Some(p), Some(s)) = (prov_interner().id(protocol), prov_interner().id(state)) {
                        v.push((p, s));
                    }
                }
            }
        }
        v.sort_unstable();
        v.dedup();
        v
    })
}

/// A per-function pre-pass over debug info: the *result* locals of `load ptr`
/// instructions that read a **reference field** of a DWARF-typed struct
/// parameter, mapped to the field's `(pointee size, writable)`. The connecting
/// dataflow is intra-block and mechanical (exactly what rustc emits):
///
/// ```text
/// store ptr %self, %self.dbg.spill        ; the debug spill …
/// %r = load ptr, %self.dbg.spill          ; … reloaded (keeps %self's struct)
/// %f = getelementptr i8, ptr %r, i64 OFF  ; a byte offset into the struct
/// %fld = load ptr, ptr %f                 ; the field pointer — a valid ref
/// ```
///
/// Only the `&T`/`&mut T` fields are recorded (via `member_ref`); a raw-pointer
/// field is left opaque, so the recovery is sound (it grants exactly the
/// reference validity the type system guarantees).
pub(crate) fn dwarf_field_loads(
    f: &LFunc,
    di: &crate::debuginfo::DebugInfo,
) -> HashMap<String, (u64, u32, bool, bool)> {
    let mut out = HashMap::new();
    let Some(sp) = f.dbg else { return out };

    // `local -> DWARF struct type id it points to (at offset 0)`. Seed the
    // reference parameters whose pointee is a struct.
    let mut struct_of: HashMap<String, u32> = HashMap::new();
   
    for (i, p) in f.params.iter().enumerate() {
        if !p.name.is_empty() {
            // Seed from any pointer param (raw included) — a raw pointer's fields are
            // recovered only as `assumed`, honoured under `assume_valid_params`.
            if let Some(s) = di.param_pointee_any(sp, i as u32 + 1) {
                struct_of.insert(p.name.clone(), s);
            }
        }
    }

    // The single lowering pass follows spill round-trips and field geps in
    // program order (rustc emits the spill store/reload adjacent, so one pass
    // over the flattened instruction stream suffices).
    // `slot -> source local` for `store ptr %src, %slot`.
    let mut spill_src: HashMap<String, String> = HashMap::new();
    // `gep-result local -> (struct id, byte offset)`.
    let mut field_at: HashMap<String, (u32, u64)> = HashMap::new();

    for inst in f.blocks.iter().flat_map(|b| &b.insts) {
        match inst {
            LInst::Store { val: LValue::Local(src), ptr: LValue::Local(slot), .. } => {
                spill_src.insert(slot.clone(), src.clone());
            }
            LInst::Load { dst, ptr: LValue::Local(slot), .. } => {
                // A reload of a spilled struct pointer inherits the struct.
                if let Some(s) = spill_src.get(slot).and_then(|src| struct_of.get(src)).copied() {
                    struct_of.insert(dst.clone(), s);
                }
                // A load of a recorded reference field: record its result. A valid
                // reference (`&T`/`T&`) is unconditional; a raw pointer field is
                // recovered only under the `assume_valid_params` opt-in (`assumed`).
                if let Some(&(struct_id, off)) = field_at.get(slot) {
                    if let Some(c) = di.member_ref(struct_id, off) {
                        out.insert(dst.clone(), (c.size, c.align, c.writable, false));
                    } else if let Some((size, align)) = di.member_raw_ptr(struct_id, off) {
                        out.insert(dst.clone(), (size, align, true, true));
                    }
                }
            }
            // `gep i8, ptr %base, i64 OFF` — a byte offset into a struct.
            LInst::Gep {
                dst,
                elem,
                base: LValue::Local(base),
                index: LValue::Int(off),
            } if matches!(elem, LType::Int(8)) && *off >= 0 => {
                if let Some(&s) = struct_of.get(base) {
                    field_at.insert(dst.clone(), (s, *off as u64));
                }
            }
            // `gep %struct.T, ptr %base, 0, K` — the typed struct-field form modern
            // opaque-pointer IR (`-O2`) emits. Record the field's byte offset.
            LInst::GepChain { dst, agg_ty, base: LValue::Local(base), indices } => {
                if let Some(&s) = struct_of.get(base) {
                    if matches!(indices.first(), Some(LValue::Int(0))) {
                        if let Some(off) = gepchain_const_offset(&lower_type(agg_ty), &indices[1..]) {
                            field_at.insert(dst.clone(), (s, off));
                        }
                    }
                }
            }
            _ => {}
        }
    }
    out
}

/// The constant byte offset of an all-constant `GepChain` navigation path into
/// `agg` (struct field / constant array index). `None` on a variable step.
pub(crate) fn gepchain_const_offset(agg: &Type, path: &[LValue]) -> Option<u64> {
    let mut ty = agg;
    let mut offset = 0u64;
    for step in path {
        let LValue::Int(k) = step else { return None };
        let k = u64::try_from(*k).ok()?;
        match ty {
            Type::Struct { fields, .. } => {
                offset = offset.checked_add(struct_field_offset(ty, k as u32)?)?;
                ty = fields.get(k as usize)?;
            }
            Type::Array { elem, .. } => {
                offset = offset.checked_add(k.checked_mul(elem.size_bytes(&LAYOUT)?)?)?;
                ty = elem;
            }
            _ => return None,
        }
    }
    Some(offset)
}

/// Detect a Rust slice parameter: a `ptr` (with an `align` attribute, as `rustc`
/// emits for reference pointers) immediately followed by an integer length
/// parameter, with the element size taken from a `getelementptr` on it. Returns
/// `(length parameter index, element size)`.
pub(crate) fn detect_slice(f: &LFunc, idx: usize) -> Option<(u32, u64)> {
    let p = &f.params[idx];
    p.align?; // a slice/ref pointer carries an alignment
    if p.name.is_empty() {
        return None;
    }
    let len = f.params.get(idx + 1)?;
    if !matches!(len.ty, LType::Int(_)) {
        return None;
    }
    // The candidate must not be a *dereferenced* index of the pointer. If some
    // `gep ptr, cand` result is loaded/stored, `cand` is an index argument
    // (`fn(&[T; N], i)`) mistaken for a slice length — pairing it would size the
    // region by the access index and refute *every* access (a false FAIL; the MIR
    // frontend, having the array type, proves these PASS). A real slice's length
    // *bounds* the index: it may form the one-past-end pointer (`gep ptr, len`),
    // but that pointer is only *compared* (`icmp %next, %end`), never dereferenced.
    if pointer_indexed_and_dereferenced_by(f, &p.name, &len.name) {
        return None;
    }
    // Beyond the negative check, pairing needs *positive* evidence that the
    // integer is a length: it indexes the pointer (the one-past-end pattern) or
    // bounds a value that does (`icmp x, len` + `gep ptr, x`; see
    // `used_as_length`). An adjacent-but-unrelated integer parameter — an index
    // (`fn(&[T; N], i)`), a plain scalar (`fn(&mut State, skipped: u64)`), or a
    // compared-but-never-indexing mask (hashbrown's `bucket_mask`) — must not
    // size the pointee: that both refutes real in-bounds accesses (a false
    // FAIL) and, worse, could *prove* an out-of-bounds access against the
    // phantom size (a false PASS, since the [slice-abi] contract is trusted).
    if !used_as_length(f, &p.name, &len.name) {
        return None;
    }
    let elem_size = slice_elem_size(f, &p.name)?;
    Some(((idx + 1) as u32, elem_size))
}

/// Whether some `getelementptr ptr_name, cand` has its result loaded or stored —
/// the signature of a dereferenced index argument, distinct from a slice length
/// (which may index the pointer to form a one-past-end bound but is only compared).
pub(crate) fn pointer_indexed_and_dereferenced_by(f: &LFunc, ptr_name: &str, cand: &str) -> bool {
    if cand.is_empty() {
        return false;
    }
    f.blocks.iter().flat_map(|b| &b.insts).any(|inst| {
        matches!(inst,
            LInst::Gep { dst, base: LValue::Local(base), index: LValue::Local(ix), .. }
            if base == ptr_name && ix == cand && is_dereferenced(f, dst))
    })
}

/// Positive evidence that `cand` acts as a length for `ptr_name`: it is the
/// index of a `getelementptr` on the pointer (forming the one-past-end bound) or
/// an operand of some comparison (a bounds check). Mere adjacency in the
/// parameter list is not enough to trust the `(ptr, len)` slice ABI.
pub(crate) fn used_as_length(f: &LFunc, ptr_name: &str, cand: &str) -> bool {
    if cand.is_empty() {
        return false;
    }
    let geps_ptr = |name: &str| {
        f.blocks.iter().flat_map(|b| &b.insts).any(|inst| {
            matches!(inst,
                LInst::Gep { base: LValue::Local(base), index: LValue::Local(ix), .. }
                if base == ptr_name && ix == name)
        })
    };
    // The one-past-end pattern: the length itself indexes the pointer.
    if geps_ptr(cand) {
        return true;
    }
    // The bounds-checked-index pattern: a value compared against `cand` must
    // itself index the pointer. A comparison *alone* is not evidence —
    // hashbrown's `(ptr %self, i64 %bucket_mask)` compares the mask against a
    // loaded field without ever indexing `self` by it; pairing there sized the
    // struct by the mask and refuted a real field access (a false FAIL).
    f.blocks.iter().flat_map(|b| &b.insts).any(|inst| {
        let LInst::Icmp { a, b, .. } = inst else { return false };
        let other = match (a, b) {
            (LValue::Local(n), LValue::Local(o)) if n == cand => o,
            (LValue::Local(o), LValue::Local(n)) if n == cand => o,
            _ => return false,
        };
        geps_ptr(other)
    })
}

/// Whether local `name` is used as the address of any `load`/`store`.
pub(crate) fn is_dereferenced(f: &LFunc, name: &str) -> bool {
    f.blocks.iter().flat_map(|b| &b.insts).any(|inst| match inst {
        LInst::Load { ptr: LValue::Local(p), .. } | LInst::Store { ptr: LValue::Local(p), .. } => {
            p == name
        }
        _ => false,
    })
}

/// The byte size of the element type of the first `getelementptr` on `ptr_name`.
pub(crate) fn slice_elem_size(f: &LFunc, ptr_name: &str) -> Option<u64> {
    for b in &f.blocks {
        for inst in &b.insts {
            if let LInst::Gep { base: LValue::Local(name), elem, .. } = inst {
                if name == ptr_name {
                    return lower_type(elem).size_bytes(&LAYOUT);
                }
            }
        }
    }
    None
}
