use super::*;
use std::collections::HashSet;

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
            LInst::Load { dst, ty, ptr: LValue::Local(slot), .. } => {
                // A reload of a spilled struct pointer inherits the struct.
                if let Some(s) = spill_src.get(slot).and_then(|src| struct_of.get(src)).copied() {
                    struct_of.insert(dst.clone(), s);
                }
                // The struct field this load reads: an explicit `gep`'d field, OR — when the
                // slot is *itself* a struct pointer — the field at offset 0 (clang emits a bare
                // `load ptr, ptr %base` for the first field, with no `getelementptr`). Handling
                // offset 0 is essential: the first field of a struct is a very common link, and
                // without it a `p->first->next` chain breaks at the first hop. Only for a pointer
                // load, so a scalar read of offset 0 is never mistaken for a reference field.
                let field = field_at.get(slot).copied().or_else(|| {
                    (*ty == LType::Ptr).then(|| struct_of.get(slot).map(|&s| (s, 0u64))).flatten()
                });
                // A load of a recorded reference field: record its result. A valid
                // reference (`&T`/`T&`) is unconditional; a raw pointer field is
                // recovered only under the `assume_valid_params` opt-in (`assumed`).
                if let Some((struct_id, off)) = field {
                    if let Some(c) = di.member_ref(struct_id, off) {
                        out.insert(dst.clone(), (c.size, c.align, c.writable, false));
                    } else if let Some((size, align)) = di.member_raw_ptr(struct_id, off) {
                        out.insert(dst.clone(), (size, align, true, true));
                    }
                    // Transitive chaining: if the loaded field is a pointer/reference to a
                    // struct, record that the loaded pointer `dst` points at that struct — so
                    // a further field load off it (`p->field->next`) resolves too. This makes
                    // the one-level recovery follow the deep `a->b->c->d` chains kernel code is
                    // built from (the dominant `loaded value (no store-load provenance)` cause).
                    if let Some(pointee) = di.member_pointee(struct_id, off) {
                        struct_of.insert(dst.clone(), pointee);
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
            // opaque-pointer IR (`-O2`) emits. The named type bridges to the DWARF struct:
            // this gep *proves* `%base` designates a `struct T`, so seed `struct_of[%base]`
            // from the DWARF `DICompositeType` of that name — the key generalisation, since it
            // reaches a base that is a field load / call result / global, not just a parameter.
            // (First seed wins, so a parameter-rooted seed already present is not overwritten.)
            LInst::GepChain { dst, agg_ty, base: LValue::Local(base), indices, struct_name } => {
                if let Some(sid) = struct_name.as_deref().and_then(|n| di.composite_by_llvm_name(n)) {
                    struct_of.entry(base.clone()).or_insert(sid);
                }
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

/// The byte size of the struct each local is **indexed as**: a `gep %struct.T, ptr %b, …`
/// proves `%b` points at a `%struct.T`, so `sizeof(%struct.T)` bounds every access through
/// `%b` — recovered straight from the IR, no DWARF needed. The type is authoritative for the
/// accesses the code actually performs through that pointer.
///
/// Used twice: to size a **loaded** field pointer ([`typed_gep_field_loads`]) and to size a
/// **loop-carried** pointer (a moving iterator, `iter = iter->next`), whose region is otherwise
/// unsized — see `Module::reg_ptr_hints` and `--assume-valid-loop-ptrs`.
pub(crate) fn typed_gep_pointee_sizes(f: &LFunc) -> HashMap<&str, (u64, Option<&str>)> {
    let mut pointee: HashMap<&str, (u64, Option<&str>)> = HashMap::new();
    for inst in f.blocks.iter().flat_map(|b| &b.insts) {
        if let LInst::GepChain { agg_ty, base: LValue::Local(b), struct_name, .. } = inst {
            let ty = lower_type(agg_ty);
            if matches!(ty, Type::Struct { .. }) {
                if let Some(sz) = ty.size_bytes(&LAYOUT).filter(|&s| s > 0) {
                    pointee.entry(b.as_str()).or_insert((sz, struct_name.as_deref()));
                }
            }
        }
    }
    pointee
}

/// Recover a pointee size for a **loaded pointer** directly from the struct type of the gep
/// that indexes it — no DWARF needed. A `gep %struct.T, ptr %b, …` proves `%b` points at a
/// `%struct.T`, whose LLVM size bounds every access through it. This reaches the dominant
/// real-kernel case the DWARF *parameter*-rooted recovery ([`dwarf_field_loads`]) cannot: a
/// base pointer that is a field load off `current`, a container/list walk, or a global — not a
/// parameter (`current->cred->…`, `sk->sk_prot->…`). Recorded as a raw-pointer field
/// (`assumed = true`): valid only under `--assume-valid-params`, surfaced as the `param-valid`
/// assumption, so it adds no false PASS without the opt-in and, being an `assumed` region,
/// never refutes a constant field offset (no false FAIL from an under-sized pointee).
pub(crate) fn typed_gep_field_loads(
    f: &LFunc,
    di: &crate::debuginfo::DebugInfo,
) -> HashMap<String, (u64, u32, bool, bool)> {
    let pointee = typed_gep_pointee_sizes(f);
    // A pointer load whose result is used as such a struct base: size its region. The alignment
    // is the struct's declared one where debug info records it (so an over-aligned kernel struct
    // keeps its real alignment), else derived from the size — a valid instance is aligned to its
    // type's alignment, and a type's size is a multiple of that alignment.
    let mut out = HashMap::new();
    for inst in f.blocks.iter().flat_map(|b| &b.insts) {
        if let LInst::Load { dst, ty: LType::Ptr, .. } = inst {
            if let Some(&(sz, struct_name)) = pointee.get(dst.as_str()) {
                let align = struct_name
                    .and_then(|n| di.composite_align_by_llvm_name(n))
                    .unwrap_or_else(|| 1u32 << sz.trailing_zeros().min(4));
                out.insert(dst.clone(), (sz, align, true, true));
            }
        }
    }
    out
}

/// The **trailing-context extent** of each pointer register: the byte extent reached through
/// `getelementptr %struct.T, ptr %p, i64 k` with a constant `k >= 1` — the C idiom where an
/// allocation holds a struct *followed by* a context of its own (`crypto_skcipher_ctx(tfm)` is
/// `tfm + 1`; `netdev_priv(dev)` is `dev + 1`). LLVM's leading gep index strides over the whole
/// pointee, so such a gep navigates into element `k`, whose end is `(k + 1) * sizeof(T)`.
///
/// The object is therefore larger than its declared type, by an amount only the *allocation
/// site* knows — and in per-file kernel IR that site is in another translation unit. Recording
/// the extent the code itself reaches is the best available bound; it is honoured only under
/// `--assume-struct-tail`.
pub(crate) fn struct_tail_extents(f: &LFunc) -> HashMap<&str, u64> {
    let mut out: HashMap<&str, u64> = HashMap::new();
    for inst in f.blocks.iter().flat_map(|b| &b.insts) {
        // Both gep shapes carry the idiom: `gep %T, ptr %p, i64 1` alone (a bare `tfm + 1`,
        // parsed as `Gep` because it has a single index) and `gep %T, ptr %p, i64 1, i32 k`
        // (a field *of* the trailing element, parsed as `GepChain`).
        let (agg_ty, b, lead) = match inst {
            LInst::GepChain { agg_ty, base: LValue::Local(b), indices, .. } => {
                (agg_ty, b, indices.first())
            }
            LInst::Gep { elem, base: LValue::Local(b), index, .. } => (elem, b, Some(index)),
            _ => continue,
        };
        let Some(LValue::Int(k)) = lead else { continue };
        let Ok(k) = u64::try_from(*k) else { continue };
        if k == 0 {
            continue; // the ordinary in-struct navigation, not the tail idiom
        }
        let agg = lower_type(agg_ty);
        if !matches!(agg, Type::Struct { .. }) {
            continue;
        }
        let Some(size) = agg.size_bytes(&LAYOUT).filter(|&s| s > 0) else { continue };
        if let Some(extent) = k.checked_add(1).and_then(|n| n.checked_mul(size)) {
            let e = out.entry(b.as_str()).or_insert(0);
            *e = (*e).max(extent);
        }
    }
    out
}

/// The byte alignment each pointer register is **asserted** to have, recovered from the
/// `align N` clang puts on every load/store. Real kernel IR carries no debug info at all
/// (no `!DICompositeType`), so the pointee type's declared alignment — the natural source —
/// simply does not exist there; clang's own access annotations are the only remaining record
/// of it, and an over-aligned struct (`____cacheline_aligned`, `alignof == 64`) is otherwise
/// unprovable: a size-derived guess is capped at `max_align_t` (16).
///
/// Two shapes contribute, both reading the assertion *backwards* to the base:
///   * a direct access `load … ptr %r, align N` ⇒ `%r` is `N`-aligned;
///   * an access through a **constant** offset `K` off `%r` with `align N`, when `K` is a
///     multiple of `N` ⇒ `base + K ≡ 0 (mod N)` and `K ≡ 0 (mod N)`, hence `%r ≡ 0 (mod N)`.
///     (When `K` is *not* a multiple of `N` the assertion says nothing about the base, so it
///     is dropped — that is what keeps the inference from over-claiming.)
///
/// This learns the *type's* alignment; it does not assume anything about runtime state that
/// `--assume-valid-params` (under which alone these regions exist) does not already assume:
/// a valid instance of `T` is aligned to `alignof(T)`. Only ever *raises* an alignment, and
/// only for a register the frontend already typed.
pub(crate) fn asserted_base_aligns(f: &LFunc) -> HashMap<&str, u32> {
    // `gep result -> (base local, constant byte offset)`, for both gep shapes.
    let mut off_of: HashMap<&str, (&str, u64)> = HashMap::new();
    for inst in f.blocks.iter().flat_map(|b| &b.insts) {
        match inst {
            LInst::GepChain { dst, agg_ty, base: LValue::Local(b), indices, .. } => {
                // LLVM's *leading* gep index strides over the whole pointee (`gep %T, ptr %p,
                // i64 1` is `p + sizeof(T)`); only `indices[1..]` navigate *into* the aggregate.
                // Feeding the leading index to `gepchain_const_offset` would read it as a field
                // index and yield a wrong offset — which here could make `K % align == 0` hold
                // spuriously and *raise* an alignment claim, i.e. a false PASS.
                let agg = lower_type(agg_ty);
                let stride = agg.size_bytes(&LAYOUT);
                if let (Some(lead), Some(stride), Some(inner)) = (
                    indices.first().and_then(|v| match v {
                        LValue::Int(k) if *k >= 0 => u64::try_from(*k).ok(),
                        _ => None,
                    }),
                    stride,
                    gepchain_const_offset(&agg, &indices[1..]),
                ) {
                    if let Some(k) = lead.checked_mul(stride).and_then(|o| o.checked_add(inner)) {
                        off_of.insert(dst.as_str(), (b.as_str(), k));
                    }
                }
            }
            LInst::Gep { dst, elem, base: LValue::Local(b), index: LValue::Int(i) } => {
                if let (Ok(i), Some(stride)) =
                    (u64::try_from(*i), lower_type(elem).size_bytes(&LAYOUT))
                {
                    if let Some(k) = i.checked_mul(stride) {
                        off_of.insert(dst.as_str(), (b.as_str(), k));
                    }
                }
            }
            _ => {}
        }
    }

    let mut out: HashMap<&str, u32> = HashMap::new();
    for inst in f.blocks.iter().flat_map(|b| &b.insts) {
        let (ptr, align) = match inst {
            LInst::Load { ptr: LValue::Local(p), align, .. }
            | LInst::Store { ptr: LValue::Local(p), align, .. } => (p.as_str(), *align),
            _ => continue,
        };
        if !align.is_power_of_two() {
            continue;
        }
        // The access is either on the base itself (offset 0) or through a constant offset.
        let (base, k) = off_of.get(ptr).copied().unwrap_or((ptr, 0));
        if k % u64::from(align) == 0 {
            let e = out.entry(base).or_insert(0);
            *e = (*e).max(align);
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

/// Detect a **C buffer/length parameter pair** — `f(const u8 *key, u32 keylen)` — where
/// [`detect_slice`] cannot: C has no slice ABI, so the pointer carries no `align` attribute
/// and the length need not sit immediately after it. Returns `(length parameter index,
/// element size)`.
///
/// Unlike Rust's `&[T]`, this pairing is **not guaranteed by any ABI** — it is a convention,
/// and a caller may well pass a length that does not describe the buffer. The contract it
/// produces is therefore emitted under its own assumption id (`param-buffer-len`) and honoured
/// only under the opt-in flag; with the flag off the parameter stays uncontracted, exactly as
/// today. That is what keeps a wrong pairing from becoming a false PASS on the default path.
///
/// The evidence required is the same as for a Rust slice, and for the same reasons: the integer
/// must *bound* an index into the pointer ([`used_as_length`]) and must not itself be a
/// dereferenced index ([`pointer_indexed_and_dereferenced_by`]) — an `f(buf, i)` index argument
/// mistaken for a length would size the region by the access and refute every access.
pub(crate) fn detect_c_buffer(f: &LFunc, idx: usize) -> Option<(u32, u64)> {
    let p = &f.params[idx];
    if p.name.is_empty() || !matches!(p.ty, LType::Ptr) {
        return None;
    }
    for (j, len) in f.params.iter().enumerate() {
        if j == idx || len.name.is_empty() || !matches!(len.ty, LType::Int(_)) {
            continue;
        }
        if pointer_indexed_and_dereferenced_by(f, &p.name, &len.name) {
            continue;
        }
        // Either the Rust-grade evidence, or — the shape C code actually takes — an index into
        // the buffer that is *computed from* the length (`buf[len - 4]`, `buf + len/2`). The
        // latter is deliberately NOT folded into `used_as_length`: that is also the evidence for
        // Rust's `slice-abi` contract, which is *trusted*, and admitting a derived index there
        // could turn an index parameter into a phantom length and prove a real overrun safe.
        if !used_as_length(f, &p.name, &len.name)
            && !pointer_index_derived_from(f, &p.name, &len.name)
        {
            continue;
        }
        // A byte buffer (`gep i8`) gives element size 1, which is exactly right: the length
        // then counts bytes. Without any gep on the pointer there is no access to bound.
        let elem_size = slice_elem_size(f, &p.name)?;
        return Some((j as u32, elem_size));
    }
    None
}

/// Whether some `getelementptr ptr_name, IDX` has an `IDX` that is *computed from* `cand`
/// — the ubiquitous C shape `buf[len - 4]`, `buf + len`, `buf + len * 2`, where the index is
/// derived from the length by arithmetic rather than being the length itself.
///
/// A bounded backward walk over the defining instructions (casts and integer arithmetic), so
/// a cyclic or deep chain terminates. Only ever *positive* evidence for the opt-in C pairing.
fn pointer_index_derived_from(f: &LFunc, ptr_name: &str, cand: &str) -> bool {
    // `dst -> operands` for the value-producing integer ops a length flows through.
    let mut def: HashMap<&str, Vec<&str>> = HashMap::new();
    for inst in f.blocks.iter().flat_map(|b| &b.insts) {
        match inst {
            LInst::Cast { dst, val: LValue::Local(a), .. } => {
                def.insert(dst.as_str(), vec![a.as_str()]);
            }
            LInst::Bin { dst, a, b, .. } => {
                let mut ops = Vec::new();
                if let LValue::Local(x) = a {
                    ops.push(x.as_str());
                }
                if let LValue::Local(y) = b {
                    ops.push(y.as_str());
                }
                def.insert(dst.as_str(), ops);
            }
            _ => {}
        }
    }
    let derives_from_cand = |start: &str| {
        let mut seen: HashSet<&str> = HashSet::new();
        let mut work = vec![start];
        while let Some(v) = work.pop() {
            if v == cand {
                return true;
            }
            if !seen.insert(v) || seen.len() > 64 {
                continue;
            }
            if let Some(ops) = def.get(v) {
                work.extend(ops.iter().copied());
            }
        }
        false
    };
    f.blocks.iter().flat_map(|b| &b.insts).any(|inst| {
        matches!(inst,
            LInst::Gep { base: LValue::Local(base), index: LValue::Local(ix), .. }
            if base == ptr_name && derives_from_cand(ix))
    })
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
