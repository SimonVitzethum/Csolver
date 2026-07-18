//! Recovering pointee types from LLVM debug-info metadata (`!DI…`).
//!
//! LLVM's opaque `ptr` type erases *what* a pointer points to — so a reference
//! parameter carries no size, and accesses through it cannot be bounds-checked
//! (the dominant `UNKNOWN` on debug IR). But when the module is compiled with
//! debug info (`-g` / `-C debuginfo=2`, standard across rustc, clang, swiftc),
//! the type is still present as *metadata*: the DWARF type graph embedded in the
//! textual IR. This module reads it back.
//!
//! The chain, per function parameter:
//! ```text
//! define … !dbg !N                          ; N = the DISubprogram
//! !V = !DILocalVariable(arg: k, scope: !N, type: !T)
//! !T = !DIDerivedType(tag: DW_TAG_pointer_type, name: "&mut T", baseType: !P, …)
//! !P = !DICompositeType(… size: <bits>)     ; the pointee, sized in bits
//! ```
//!
//! ## Soundness — validity is language-specific
//!
//! A pointee *size* alone does not make a pointer valid: a C `T*` may dangle. A
//! contract (a live, dereferenceable region) is synthesized **only** for pointer
//! kinds the source language guarantees valid:
//!
//! - a Rust reference — `DW_TAG_pointer_type` whose name begins `&` (`&T` /
//!   `&mut T`; `&mut` ⇒ writable);
//! - a C++ reference — `DW_TAG_reference_type` (`T&`).
//!
//! A raw pointer (`*const T`, C/C++ `T*`, `DW_TAG_pointer_type` not named `&`) is
//! deliberately *not* contracted: its validity is the programmer's obligation,
//! and assuming it would be a false-PASS hole. So the recovery is sound across
//! languages, granting a contract exactly where the type system already does.

use std::collections::HashMap;

/// A parsed subset of the debug-info type graph, keyed by metadata id.
#[derive(Debug, Clone, Default)]
pub(crate) struct DebugInfo {
    nodes: HashMap<u32, DiNode>,
    /// `(subprogram id, 1-based arg index) -> parameter's type node id`.
    params: HashMap<(u32, u32), u32>,
    /// `!DILocalVariable id -> its declared type node id`, for **every** local (parameters
    /// included). A `#dbg_value(ptr %r, !V, …)` record ties an SSA value to one of these, which
    /// is how a *local's* declared type — and hence a pointer's pointee size — is recovered at
    /// `-O1`/`-O2`, where the struct type is canonicalised out of the `getelementptr` (clang
    /// rewrites `gep %struct.T, ptr %p, 0, k` into a byte `gep i8, ptr %p, off`). See
    /// [`DebugInfo::local_pointee_bytes`].
    locals: HashMap<u32, u32>,
    /// `struct/union name -> its `DICompositeType` node id`. Keyed by the bare DWARF name
    /// (`task_struct`), so an LLVM `getelementptr %struct.task_struct, …` can be mapped to the
    /// DWARF struct — the bridge that lets [`super::lower::dwarf_field_loads`] recover field
    /// pointees off *any* typed-gep base, not just a parameter-rooted one. First definition wins.
    by_name: HashMap<String, u32>,
    /// The module's source language (`DICompileUnit(language:)`), which fixes
    /// what pointer kinds are *valid* — the recovery applies each language's own
    /// guarantee, not one hard-coded rule (see `is_valid_ref`).
    lang: Lang,
}

/// The source language, as far as pointer-validity semantics go.
#[derive(Debug, Clone, Copy, Default, PartialEq, Eq)]
enum Lang {
    /// Rust: `&T`/`&mut T` references (`DW_TAG_pointer_type` named `&…`) are
    /// valid; raw `*const T`/`*mut T` are not.
    Rust,
    /// Anything else (C, C++, D, Zig-as-C99, Swift, …): a `DW_TAG_pointer_type`
    /// is a raw pointer that may be null/dangling and is **not** recovered. A
    /// `DW_TAG_reference_type` (C++ `T&`, D `ref`) is a valid reference in every
    /// language that emits it, so it is recovered regardless of `lang`.
    #[default]
    Other,
}

#[derive(Debug, Clone)]
enum DiNode {
    /// A `DW_TAG_pointer_type`: its pointee and whether it is a valid reference
    /// (`&T`/`&mut T`, by the leading `&` in the name) and if so writable.
    Pointer { base: u32, reference: bool, writable: bool },
    /// A `DW_TAG_reference_type` (C++ `T&`): always a valid reference.
    Reference { base: u32, writable: bool },
    /// A struct/union (`DICompositeType`): its `elements` metadata-list id (the
    /// members), byte size, and byte alignment.
    Composite { elements: Option<u32>, size_bytes: Option<u64>, align_bytes: Option<u32> },
    /// A Rust **slice reference** (`&[T]` / `&mut [T]`): a `DICompositeType` whose name is
    /// `&…[T]`, i.e. a 128-bit `{data: *T, len: usize}` fat pointer. Carries the element's
    /// `(byte size, byte align)` and whether it is writable (`&mut`). The *length* is not
    /// here — it lives in a `#dbg_value(iN len, !V, fragment 64 64)` record ([`LFunc::
    /// dbg_slice_lens`]); the two combine to size the slice's backing region. Because the
    /// name begins `&`, it is a Rust reference and the language guarantees its validity — the
    /// same soundness basis as [`DiNode::Pointer { reference: true, .. }`].
    SliceRef { elem_bytes: u64, elem_align: u32, writable: bool },
    /// A struct member (`DIDerivedType(tag: DW_TAG_member)`): its byte offset in
    /// the enclosing struct and its type.
    Member { offset_bytes: u64, base: u32 },
    /// A `!{…}` metadata tuple (a struct's element list): the member node ids.
    Tuple(Vec<u32>),
    /// Any other sized type node (basic type / typedef|qualifier chain): its byte
    /// size and alignment and, for a typedef/qualifier, the underlying type to
    /// follow.
    Sized { size_bytes: Option<u64>, align_bytes: Option<u32>, follows: Option<u32> },
}

/// A pointer parameter's recovered contract: pointee byte size + write access.
pub(crate) struct RefContract {
    pub size: u64,
    pub align: u32,
    pub writable: bool,
}

impl DebugInfo {
    /// The recovered contract for parameter `arg` (1-based) of the function
    /// whose `DISubprogram` id is `subprogram`, when that parameter is a *valid
    /// reference* of statically-known pointee size. `None` for a raw pointer, an
    /// unknown-size pointee, or missing debug info.
    pub(crate) fn param_ref(&self, subprogram: u32, arg: u32) -> Option<RefContract> {
        let ty = *self.params.get(&(subprogram, arg))?;
        let (base, writable) = self.valid_ref(ty)?;
        Some(RefContract { size: self.sized_bytes(base)?, align: self.sized_align(base), writable })
    }

    /// The pointee node and writability of a type node **iff** it is a valid
    /// reference for this module's language: a Rust `&T`/`&mut T`
    /// (`DW_TAG_pointer_type` named `&…`, only when `lang == Rust`), or a
    /// `DW_TAG_reference_type` (C++ `T&`, D `ref` — a valid reference in any
    /// language that emits it). A raw `DW_TAG_pointer_type` (C/C++/D/Zig `T*`,
    /// Rust `*const T`) is never valid — it may dangle, so recovering it would
    /// be a false-PASS hole. `None` otherwise.
    fn valid_ref(&self, ty: u32) -> Option<(u32, bool)> {
        match self.nodes.get(&ty)? {
            DiNode::Pointer { base, reference: true, writable } if self.lang == Lang::Rust => {
                Some((*base, *writable))
            }
            DiNode::Reference { base, writable } => Some((*base, *writable)),
            _ => None,
        }
    }

    /// Follow typedef/qualifier chains to a concrete byte size (a bounded walk).
    fn sized_bytes(&self, mut id: u32) -> Option<u64> {
        for _ in 0..16 {
            match self.nodes.get(&id)? {
                DiNode::Sized { size_bytes: Some(n), .. } => return Some(*n),
                DiNode::Sized { size_bytes: None, follows: Some(next), .. } => id = *next,
                DiNode::Composite { size_bytes: Some(n), .. } => return Some(*n),
                // A pointer/reference *pointee* that is itself a pointer is 8
                // bytes (a thin pointer's storage), the sound size for it.
                DiNode::Pointer { .. } | DiNode::Reference { .. } => return Some(8),
                _ => return None,
            }
        }
        None
    }

    /// The byte alignment of a type node (following typedef chains); 1 when not
    /// recorded (a conservative default — an alignment obligation then fails
    /// soundly rather than assuming).
    fn sized_align(&self, id: u32) -> u32 {
        self.sized_align_opt(id).unwrap_or(1)
    }

    /// The **recorded** byte alignment of a type node, or `None` when debug info does not
    /// state one. Distinct from [`Self::sized_align`], whose `1` default is indistinguishable
    /// from a genuinely 1-aligned type: a caller that wants to *fall back* to deriving the
    /// alignment from the size must know the difference, or every type whose alignment clang
    /// left implicit (the common case — clang emits `align:` only when it is not the natural
    /// one) would be pinned to 1 and no alignment obligation could ever be discharged.
    fn sized_align_opt(&self, mut id: u32) -> Option<u32> {
        for _ in 0..16 {
            match self.nodes.get(&id) {
                Some(DiNode::Sized { align_bytes: Some(a), .. }) => return Some(*a),
                Some(DiNode::Composite { align_bytes: Some(a), .. }) => return Some(*a),
                Some(DiNode::Sized { align_bytes: None, follows: Some(next), .. }) => id = *next,
                Some(DiNode::Pointer { .. } | DiNode::Reference { .. }) => return Some(8),
                _ => return None,
            }
        }
        None
    }

    /// The pointee byte size and alignment of a **raw** pointer parameter (`T*`) of
    /// statically-known pointee size — for the opt-in "the framework passes a valid
    /// pointer" assumption (`param-valid`). Unlike [`param_ref`], this deliberately
    /// accepts a raw pointer: it is the *assumption's* job (not the type's) to
    /// guarantee validity, so it is only ever applied under the caller's opt-in.
    pub(crate) fn param_raw_ptr(&self, subprogram: u32, arg: u32) -> Option<(u64, u32)> {
        let ty = *self.params.get(&(subprogram, arg))?;
        match self.nodes.get(&ty)? {
            DiNode::Pointer { base, .. } => Some((self.sized_bytes(*base)?, self.sized_align(*base))),
            _ => None,
        }
    }

    /// The pointee type node of **any** pointer parameter, including a raw pointer
    /// (`struct T *`) — so field loads through it can resolve members. Used to seed
    /// member-provenance recovery; a raw pointer's *fields* are only trusted under
    /// `assume_valid_params` (they are recorded as `assumed`).
    pub(crate) fn param_pointee_any(&self, subprogram: u32, arg: u32) -> Option<u32> {
        let ty = *self.params.get(&(subprogram, arg))?;
        match self.nodes.get(&ty)? {
            DiNode::Pointer { base, .. } | DiNode::Reference { base, .. } => Some(*base),
            _ => None,
        }
    }

    /// The recovered contract for the member of struct type `struct_id` at byte
    /// `offset`, when that member is a *valid reference* (`&T`/`&mut T`/`T&`) —
    /// so a `load ptr, gep(struct, offset)` yields a known valid reference. The
    /// enclosing struct type may itself be behind a typedef/qualifier chain.
    pub(crate) fn member_ref(&self, struct_id: u32, offset: u64) -> Option<RefContract> {
        let elements = self.composite_elements(struct_id)?;
        let DiNode::Tuple(members) = self.nodes.get(&elements)? else { return None };
        for &m in members {
            if let Some(DiNode::Member { offset_bytes, base }) = self.nodes.get(&m) {
                if *offset_bytes == offset {
                    let (pointee, writable) = self.valid_ref(*base)?;
                    return Some(RefContract {
                        size: self.sized_bytes(pointee)?,
                        align: self.sized_align(pointee),
                        writable,
                    });
                }
            }
        }
        None
    }

    /// Like [`member_ref`], but for a **raw** pointer member (`T*`) of known pointee
    /// size — the pointee `(size, align)`. Recovered only under the opt-in
    /// `assume_valid_params` (a raw pointer field may hold null or a dangling value):
    /// a `dev->child` where `child` is a `struct child *`, so a load of it yields a
    /// valid pointer to a `struct child`.
    pub(crate) fn member_raw_ptr(&self, struct_id: u32, offset: u64) -> Option<(u64, u32)> {
        let elements = self.composite_elements(struct_id)?;
        let DiNode::Tuple(members) = self.nodes.get(&elements)? else { return None };
        for &m in members {
            if let Some(DiNode::Member { offset_bytes, base }) = self.nodes.get(&m) {
                if *offset_bytes == offset {
                    if let DiNode::Pointer { base: pointee, .. } = self.nodes.get(base)? {
                        let size = self.sized_bytes(*pointee)?;
                        // A valid instance is naturally aligned; when debug info omits
                        // the alignment, derive it from the size (a type's size is a
                        // multiple of its alignment), capped at 16 (`max_align_t`).
                        let derived = 1u32 << size.trailing_zeros().min(4);
                        return Some((size, self.sized_align(*pointee).max(derived)));
                    }
                }
            }
        }
        None
    }

    /// The `DICompositeType` node id of a struct/union by its **LLVM type name** (`struct.cred`,
    /// `union.foo`, or a quoted C++ `"class.Bar"`), stripping the `struct.`/`union.`/`class.`
    /// prefix to the bare DWARF name. Lets a `getelementptr %struct.T, ptr %b` seed that `%b`
    /// designates a `struct T`, so field pointees load through it (see `dwarf_field_loads`).
    pub(crate) fn composite_by_llvm_name(&self, llvm_name: &str) -> Option<u32> {
        let bare = llvm_name
            .trim_matches('"')
            .strip_prefix("struct.")
            .or_else(|| llvm_name.trim_matches('"').strip_prefix("union."))
            .or_else(|| llvm_name.trim_matches('"').strip_prefix("class."))
            .unwrap_or(llvm_name.trim_matches('"'));
        self.by_name.get(bare).copied()
    }

    /// The **pointee byte size** of a local variable's declared type, when that type is a
    /// pointer or reference of statically-known pointee size (`struct node *` ⇒
    /// `sizeof(struct node)`). `None` for a non-pointer local or an unsized pointee.
    ///
    /// This is what sizes a **loop-carried pointer** (a moving iterator) at `-O1`/`-O2`: there
    /// the struct type is canonicalised out of the `getelementptr` (a byte `gep i8` remains),
    /// so the type-directed gep recovery finds nothing — but the `#dbg_value` record still ties
    /// the SSA value to its `!DILocalVariable`, whose declared type says exactly what it points
    /// at. Used only under `--assume-valid-loop-ptrs` (which already assumes the iterator
    /// designates a valid live object); the type then says how big that object is.
    /// Returns the pointee's `(size, align)`; the alignment is the type's declared one, so an
    /// over-aligned struct keeps its real alignment instead of one guessed from the size.
    pub(crate) fn local_pointee_bytes(&self, var_id: u32) -> Option<(u64, u32)> {
        let ty = *self.locals.get(&var_id)?;
        match self.nodes.get(&ty)? {
            DiNode::Pointer { base, .. } | DiNode::Reference { base, .. } => {
                Some((self.sized_bytes(*base)?, self.sized_align_opt(*base).unwrap_or(0)))
            }
            _ => None,
        }
    }

    /// If a local's declared type is a Rust **slice reference** (`&[T]`/`&mut [T]`), the
    /// element's `(byte size, byte align, writable)`. Combined with the slice's `len`
    /// ([`LFunc::dbg_slice_lens`]), the backing region is `len * size` bytes — sizing a
    /// `from_raw_parts(ptr, len)` slice whose `from_raw_parts` call the optimizer erased.
    /// Same soundness basis as reference recovery: the `&`-named type is a Rust reference,
    /// so the region is only *applied* under `--assume-valid-params` (the `PtrHint` path).
    pub(crate) fn slice_local_elem(&self, var_id: u32) -> Option<(u64, u32, bool)> {
        match self.nodes.get(self.locals.get(&var_id)?)? {
            DiNode::SliceRef { elem_bytes, elem_align, writable } => {
                Some((*elem_bytes, *elem_align, *writable))
            }
            _ => None,
        }
    }

    /// The declared byte alignment of a struct named as LLVM names it (`%struct.T` ⇒ `T`),
    /// or `None` when debug info records none. Lets a *type-directed* `gep %struct.T` hint
    /// carry the struct's real alignment, which the LLVM type alone does not record — an
    /// over-aligned (`____cacheline_aligned`) kernel struct then discharges a `load … align 64`.
    pub(crate) fn composite_align_by_llvm_name(&self, name: &str) -> Option<u32> {
        self.sized_align_opt(self.composite_by_llvm_name(name)?)
    }

    /// The **pointee type node** of a struct member at `offset`, when that member is a
    /// pointer or reference (valid `&T`/`T&` OR raw `T*`). Used to make member-provenance
    /// recovery **transitive**: a pointer loaded from `p->field` points at this type, so
    /// field loads off *it* (`p->field->next`) resolve against it too. The ref-vs-raw
    /// distinction (which governs the `assumed` opt-in) is decided per load by
    /// [`member_ref`] / [`member_raw_ptr`]; this only recovers the pointee's type so the
    /// next level can be looked up. `None` when the member is not a pointer/reference or
    /// its pointee is not a known type node.
    pub(crate) fn member_pointee(&self, struct_id: u32, offset: u64) -> Option<u32> {
        let elements = self.composite_elements(struct_id)?;
        let DiNode::Tuple(members) = self.nodes.get(&elements)? else { return None };
        for &m in members {
            if let Some(DiNode::Member { offset_bytes, base }) = self.nodes.get(&m) {
                if *offset_bytes == offset {
                    return match self.nodes.get(base)? {
                        DiNode::Pointer { base: p, .. } | DiNode::Reference { base: p, .. } => Some(*p),
                        _ => None,
                    };
                }
            }
        }
        None
    }

    /// The elements-list id of a composite type, following typedef/qualifier
    /// chains to reach the `DICompositeType`.
    fn composite_elements(&self, mut id: u32) -> Option<u32> {
        for _ in 0..16 {
            match self.nodes.get(&id)? {
                DiNode::Composite { elements, .. } => return *elements,
                DiNode::Sized { follows: Some(next), .. } => id = *next,
                _ => return None,
            }
        }
        None
    }
}

/// Parse the debug-info metadata graph out of a textual `.ll` module. Lines that
/// are not `!DI…` definitions (or that do not parse) are ignored — debug info is
/// advisory, never required.
pub(crate) fn parse(src: &str) -> DebugInfo {
    let mut di = DebugInfo::default();
    // For the `-O2`/no-`DILocalVariable` case, recover parameter types from the
    // function signature: `DISubprogram(type: !ST)`, `DISubroutineType(types: !TL)`,
    // `!TL = !{!ret, !arg1, …}`. Collected here, resolved in a post-pass.
    let mut subprogram_ty: HashMap<u32, u32> = HashMap::new(); // subprogram -> subroutine type
    let mut subroutine_types: HashMap<u32, u32> = HashMap::new(); // subroutine type -> types tuple
    // Position-preserving tuples (a `void` return is `null` at index 0 — dropping it
    // would misalign parameter indices), for resolving signatures.
    let mut positional_tuples: HashMap<u32, Vec<Option<u32>>> = HashMap::new();
    for line in src.lines() {
        let line = line.trim_start();
        // A metadata definition: `!123 = [distinct] !DI…(…)`.
        let Some(rest) = line.strip_prefix('!') else { continue };
        let Some((id_str, body)) = rest.split_once(" = ") else { continue };
        let Ok(id) = id_str.parse::<u32>() else { continue };
        // clang marks structs and subprograms `distinct` (a uniquing hint); it
        // prefixes the node body and must be stripped before the tag match.
        let body = body.strip_prefix("distinct ").unwrap_or(body);

        if let Some(args) = tag_body(body, "!DISubprogram(") {
            if let Some(ty) = field_ref(args, "type:") {
                subprogram_ty.insert(id, ty);
            }
        } else if let Some(args) = tag_body(body, "!DISubroutineType(") {
            if let Some(types) = field_ref(args, "types:") {
                subroutine_types.insert(id, types);
            }
        }
        if let Some(args) = tag_body(body, "!DICompileUnit(") {
            // The source language fixes pointer-validity semantics (see `Lang`).
            if let Some(l) = field_word(args, "language:") {
                di.lang = if l == "DW_LANG_Rust" { Lang::Rust } else { Lang::Other };
            }
        } else if let Some(args) = tag_body(body, "!DILocalVariable(") {
            // `arg: k, scope: !N, type: !T`. Parameters (those with `arg:`) are keyed by
            // (subprogram, index); *every* local — parameter or not — is also recorded by its
            // own node id, so a `#dbg_value` naming it recovers its declared type.
            if let Some(ty) = field_ref(args, "type:") {
                di.locals.insert(id, ty);
                if let (Some(arg), Some(scope)) = (field_int(args, "arg:"), field_ref(args, "scope:")) {
                    di.params.insert((scope, arg as u32), ty);
                }
            }
        } else if let Some(args) = tag_body(body, "!DIDerivedType(") {
            insert_derived(&mut di, id, args);
        } else if let Some(args) = tag_body(body, "!DICompositeType(") {
            let name = field_str(args, "name:");
            // A Rust slice reference `&[T]` / `&mut [T]` is a named 128-bit fat-pointer struct.
            // Recognise it by name and record the element `(size, align)` + writability, so its
            // backing region can be sized once the length fragment supplies `N`.
            if let Some((elem_bytes, elem_align, writable)) = name.and_then(slice_ref_elem) {
                di.nodes.insert(id, DiNode::SliceRef { elem_bytes, elem_align, writable });
            } else {
                // A struct/union: its byte size and members-list (`elements: !L`).
                di.nodes.insert(
                    id,
                    DiNode::Composite {
                        elements: field_ref(args, "elements:"),
                        size_bytes: bits_to_bytes(args),
                        align_bytes: bits_to_bytes_u32(args, "align:"),
                    },
                );
            }
            // Index it by name so an LLVM `%struct.<name>` gep can find it. First wins.
            if let Some(name) = name {
                di.by_name.entry(name.to_string()).or_insert(id);
            }
        } else if let Some(args) = tag_body(body, "!DIBasicType(") {
            di.nodes.insert(
                id,
                DiNode::Sized {
                    size_bytes: bits_to_bytes(args),
                    align_bytes: bits_to_bytes_u32(args, "align:"),
                    follows: None,
                },
            );
        } else if let Some(members) = tuple_refs(body) {
            // A `!{!a, !b, …}` metadata tuple — a struct's element list.
            di.nodes.insert(id, DiNode::Tuple(members));
            if let Some(inner) = body.strip_prefix("!{").and_then(|b| b.strip_suffix('}')) {
                positional_tuples.insert(
                    id,
                    inner.split(',').map(|e| e.trim().strip_prefix('!').and_then(|s| s.parse().ok())).collect(),
                );
            }
        }
    }
    // Post-pass: fill parameter types from each function's signature where a
    // `DILocalVariable` did not already provide one (the `-O2` case). `types` is
    // `!{return, arg1, arg2, …}`, so parameter `k` (1-based) is tuple index `k`.
    for (&sp, &st) in &subprogram_ty {
        let Some(tl) = subroutine_types.get(&st) else { continue };
        let Some(types) = positional_tuples.get(tl) else { continue };
        for (k, ty) in types.iter().enumerate().skip(1) {
            if let Some(ty) = ty {
                di.params.entry((sp, k as u32)).or_insert(*ty);
            }
        }
    }
    di
}

/// Recognise a Rust slice-reference DWARF name — `&[T]` or `&mut [T]` — and return the
/// element's `(byte size, byte align, writable)`. `&mut` ⇒ writable. Only a **primitive**
/// element is sized here (`u8`…`u128`, `i8`…`i128`, `usize`/`isize`, `f32`/`f64`, `bool`,
/// `char`) — the common case for raw-memory slices (`&mut [u64]` page tables, `&[u8]`
/// buffers). A composite element yields `None`, so its slice simply gets no region (sound:
/// a conservative miss, never a wrong size). Returns `None` for any non-slice-reference name.
fn slice_ref_elem(name: &str) -> Option<(u64, u32, bool)> {
    let writable = name.starts_with("&mut ");
    let rest = name.strip_prefix("&mut ").or_else(|| name.strip_prefix('&'))?;
    let inner = rest.strip_prefix('[')?.strip_suffix(']')?.trim();
    let (size, align): (u64, u32) = match inner {
        "u8" | "i8" | "bool" => (1, 1),
        "u16" | "i16" => (2, 2),
        "u32" | "i32" | "f32" | "char" => (4, 4),
        "u64" | "i64" | "f64" | "usize" | "isize" => (8, 8),
        "u128" | "i128" => (16, 16),
        _ => return None,
    };
    Some((size, align, writable))
}

/// Parse a bare metadata tuple `!{!a, !b, …}` into its element ids, or `None` if
/// `body` is not a tuple (or holds non-`!N` entries, in which case those slots
/// are simply skipped — a `null` member is harmless).
fn tuple_refs(body: &str) -> Option<Vec<u32>> {
    let inner = body.strip_prefix("!{")?.strip_suffix('}')?;
    Some(
        inner
            .split(',')
            .filter_map(|e| e.trim().strip_prefix('!')?.parse::<u32>().ok())
            .collect(),
    )
}

/// A `DW_TAG_pointer_type` / `reference_type` / typedef|qualifier under
/// `!DIDerivedType(tag: …, …)`.
fn insert_derived(di: &mut DebugInfo, id: u32, args: &str) {
    let tag = field_word(args, "tag:");
    let base = field_ref(args, "baseType:");
    match tag {
        Some("DW_TAG_pointer_type") => {
            let name = field_str(args, "name:");
            // A Rust reference's DWARF name begins `&` (`&T` / `&mut T`); a raw
            // pointer is `*const …`/`*mut …` or unnamed.
            let reference = name.is_some_and(|n| n.starts_with('&'));
            let writable = name.is_some_and(|n| n.starts_with("&mut"));
            if let Some(base) = base {
                di.nodes.insert(id, DiNode::Pointer { base, reference, writable });
            }
        }
        Some("DW_TAG_reference_type") => {
            if let Some(base) = base {
                di.nodes.insert(id, DiNode::Reference { base, writable: true });
            }
        }
        // A struct member: its byte offset (`offset:` is in bits) and type.
        Some("DW_TAG_member") => {
            if let Some(base) = base {
                let offset_bytes = field_int(args, "offset:").unwrap_or(0).max(0) as u64 / 8;
                di.nodes.insert(id, DiNode::Member { offset_bytes, base });
            }
        }
        // A typedef / `const`/`volatile` qualifier: transparent to the size,
        // follow its base. A pointer-sized derived type carries its own size.
        _ => {
            di.nodes.insert(
                id,
                DiNode::Sized {
                    size_bytes: bits_to_bytes(args),
                    align_bytes: bits_to_bytes_u32(args, "align:"),
                    follows: base,
                },
            );
        }
    }
}

/// The argument list inside `!DIXxx( … )`, if `body` starts with `open`.
fn tag_body<'a>(body: &'a str, open: &str) -> Option<&'a str> {
    body.strip_prefix(open)?.strip_suffix(')')
}

/// `field: N` — an integer field.
fn field_int(args: &str, field: &str) -> Option<i64> {
    field_raw(args, field)?.parse().ok()
}

/// `field: !N` — a metadata reference field.
fn field_ref(args: &str, field: &str) -> Option<u32> {
    field_raw(args, field)?.strip_prefix('!')?.parse().ok()
}

/// `field: word` — a bare-word field (e.g. `tag: DW_TAG_pointer_type`).
fn field_word<'a>(args: &'a str, field: &str) -> Option<&'a str> {
    field_raw(args, field)
}

/// `field: "quoted"` — a string field, unquoted.
fn field_str<'a>(args: &'a str, field: &str) -> Option<&'a str> {
    let v = find_field(args, field)?;
    let v = v.strip_prefix('"')?;
    Some(&v[..v.find('"')?])
}

/// A `size:` field (in bits) converted to whole bytes.
fn bits_to_bytes(args: &str) -> Option<u64> {
    let bits: u64 = field_raw(args, "size:")?.parse().ok()?;
    Some(bits / 8)
}

/// A named bit field (`align:`) converted to whole bytes as a `u32`.
fn bits_to_bytes_u32(args: &str, field: &str) -> Option<u32> {
    let bits: u32 = field_raw(args, field)?.parse().ok()?;
    Some((bits / 8).max(1))
}

/// The raw token of `field:` — up to the next comma or end, trimmed. Handles a
/// `"quoted, with commas"` value by not splitting inside the quotes.
fn field_raw<'a>(args: &'a str, field: &str) -> Option<&'a str> {
    let v = find_field(args, field)?;
    if let Some(after) = v.strip_prefix('"') {
        // up to and including the closing quote
        let end = after.find('"')? + 2;
        return Some(v[..end].trim());
    }
    let end = v.find(',').unwrap_or(v.len());
    Some(v[..end].trim())
}

/// The substring just after `field` (a `key:` occurring at a token boundary).
fn find_field<'a>(args: &'a str, field: &str) -> Option<&'a str> {
    let mut from = 0;
    while let Some(rel) = args[from..].find(field) {
        let at = from + rel;
        // Require a boundary before the key so `type:` does not match inside
        // `templateParams:` etc.
        let before_ok = at == 0 || matches!(args.as_bytes()[at - 1], b' ' | b'(' | b',');
        if before_ok {
            return Some(args[at + field.len()..].trim_start());
        }
        from = at + field.len();
    }
    None
}

#[cfg(test)]
#[path = "debuginfo_tests.rs"]
mod tests;
