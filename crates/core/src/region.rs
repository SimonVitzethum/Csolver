//! The kinds of memory region CSolver distinguishes.
//!
//! This tag is shared by the IR (which emits `Alloc`/`Dealloc` against a
//! region kind) and the memory model (which gives each kind its allocation and
//! lifetime discipline), so it lives in `core` to keep those crates siblings.

use std::fmt;

/// The provenance class of an allocation / address.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
#[non_exhaustive]
pub enum RegionKind {
    /// Automatic storage: stack slots and spills, freed at frame teardown.
    Stack,
    /// Dynamic storage from an allocator (`malloc`/`__rust_alloc`/…).
    Heap,
    /// Static storage: `.data`/`.bss`/`.rodata` and program globals.
    Global,
    /// Thread-local storage.
    Tls,
    /// Memory-mapped I/O: reads/writes may have side effects (optional).
    Mmio,
}

impl RegionKind {
    /// A stable machine-friendly identifier.
    pub fn id(self) -> &'static str {
        match self {
            RegionKind::Stack => "stack",
            RegionKind::Heap => "heap",
            RegionKind::Global => "global",
            RegionKind::Tls => "tls",
            RegionKind::Mmio => "mmio",
        }
    }

    /// Whether allocations of this kind can be explicitly deallocated by the
    /// program (heap) versus being managed by frame/thread/program lifetime.
    pub fn is_explicitly_freed(self) -> bool {
        matches!(self, RegionKind::Heap)
    }
}

impl fmt::Display for RegionKind {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str(self.id())
    }
}
