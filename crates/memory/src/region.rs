//! Regions: allocations with a kind, size, alignment, permissions and a
//! temporal lifetime state, owned by a [`MemoryModel`].

use csolver_core::RegionKind;
use std::fmt;

/// Identifies a [`Region`] within a [`MemoryModel`].
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct RegionId(pub u32);

impl fmt::Display for RegionId {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "r{}", self.0)
    }
}

/// Read/write/execute permissions on a region.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Permissions {
    /// Readable.
    pub read: bool,
    /// Writable.
    pub write: bool,
    /// Executable.
    pub exec: bool,
}

impl Permissions {
    /// Readable and writable (typical stack/heap data).
    pub const READ_WRITE: Permissions = Permissions {
        read: true,
        write: true,
        exec: false,
    };
    /// Read-only (e.g. `.rodata`).
    pub const READ_ONLY: Permissions = Permissions {
        read: true,
        write: false,
        exec: false,
    };
    /// Readable and executable (e.g. `.text`).
    pub const READ_EXEC: Permissions = Permissions {
        read: true,
        write: false,
        exec: true,
    };
}

/// The temporal state of a region's storage.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum LifetimeState {
    /// Allocated and live: accesses are temporally valid.
    Live,
    /// Deallocated: any access is a use-after-free; freeing again is a
    /// double-free.
    Freed,
    /// Reserved but not yet allocated (e.g. an `alloca` before its lifetime
    /// start marker). Accesses are invalid.
    Uninitialized,
}

/// A region size that may not be statically known.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum SymSize {
    /// A concrete byte size.
    Exact(u64),
    /// A symbolic size named by a solver variable (e.g. `n * 4`).
    Symbolic(String),
    /// Completely unknown.
    Unknown,
}

impl SymSize {
    /// The concrete size, if known.
    pub fn as_exact(&self) -> Option<u64> {
        match self {
            SymSize::Exact(n) => Some(*n),
            _ => None,
        }
    }
}

/// A single allocation.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Region {
    /// Identifier within the owning model.
    pub id: RegionId,
    /// Region kind / provenance class.
    pub kind: RegionKind,
    /// Size in bytes.
    pub size: SymSize,
    /// Alignment of the region's base address (a power of two).
    pub align: u64,
    /// Temporal state.
    pub state: LifetimeState,
    /// Access permissions.
    pub permissions: Permissions,
    /// A human label for reporting (e.g. variable name, `malloc@bb3`).
    pub label: String,
}

/// The set of regions known to an analysis, plus allocation/deallocation
/// operations with their temporal-safety outcomes.
#[derive(Debug, Clone, Default)]
pub struct MemoryModel {
    regions: Vec<Region>,
}

impl MemoryModel {
    /// An empty model.
    pub fn new() -> Self {
        MemoryModel {
            regions: Vec::new(),
        }
    }

    /// Allocate a new live region and return its id.
    pub fn allocate(
        &mut self,
        kind: RegionKind,
        size: SymSize,
        align: u64,
        permissions: Permissions,
        label: impl Into<String>,
    ) -> RegionId {
        let id = RegionId(self.regions.len() as u32);
        self.regions.push(Region {
            id,
            kind,
            size,
            align,
            state: LifetimeState::Live,
            permissions,
            label: label.into(),
        });
        id
    }

    /// Look up a region.
    pub fn region(&self, id: RegionId) -> Option<&Region> {
        self.regions.get(id.0 as usize)
    }

    /// Number of regions.
    pub fn len(&self) -> usize {
        self.regions.len()
    }

    /// Whether the model has no regions.
    pub fn is_empty(&self) -> bool {
        self.regions.is_empty()
    }

    /// Deallocate a region, returning the `NoDoubleFree` outcome.
    ///
    /// Freeing a live region succeeds and transitions it to `Freed`. Freeing an
    /// already-freed region is a concrete double-free violation. Freeing an
    /// uninitialized region is invalid.
    pub fn deallocate(&mut self, id: RegionId) -> crate::CheckOutcome {
        use crate::CheckOutcome;
        use csolver_core::SafetyProperty::NoDoubleFree;
        let Some(region) = self.regions.get_mut(id.0 as usize) else {
            return CheckOutcome::Residual {
                property: NoDoubleFree,
                condition: format!("region {id} is not tracked"),
            };
        };
        match region.state {
            LifetimeState::Live => {
                region.state = LifetimeState::Freed;
                CheckOutcome::Proven {
                    property: NoDoubleFree,
                    detail: format!("{id} was live; now freed"),
                }
            }
            LifetimeState::Freed => CheckOutcome::Violated {
                property: NoDoubleFree,
                detail: format!("{id} ({}) is already freed", region.label),
            },
            LifetimeState::Uninitialized => CheckOutcome::Violated {
                property: NoDoubleFree,
                detail: format!("{id} ({}) was never allocated", region.label),
            },
        }
    }
}
