//! Checking a memory access against the region it targets.
//!
//! [`MemoryModel::check_access`] is the bridge from the memory model to proof
//! obligations: it evaluates each relevant [`csolver_core::SafetyProperty`] for
//! a given access and reports, per property, whether it is concretely proven,
//! concretely violated, or residual (to be sent to the solver).

use crate::pointer::{Pointer, Provenance, SymOffset};
use crate::region::{LifetimeState, MemoryModel, Permissions, SymSize};
use csolver_core::SafetyProperty;

/// A memory access to be checked.
#[derive(Debug, Clone, Copy)]
pub struct Access {
    /// Number of bytes touched.
    pub size: u64,
    /// Alignment the access type requires (a power of two).
    pub align: u64,
    /// Permissions the access requires.
    pub need: Permissions,
}

impl Access {
    /// A read of `size` bytes at `align`.
    pub fn read(size: u64, align: u64) -> Access {
        Access {
            size,
            align,
            need: Permissions {
                read: true,
                write: false,
                exec: false,
            },
        }
    }

    /// A write of `size` bytes at `align`.
    pub fn write(size: u64, align: u64) -> Access {
        Access {
            size,
            align,
            need: Permissions {
                read: false,
                write: true,
                exec: false,
            },
        }
    }
}

/// The outcome of checking one safety property of one access.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum CheckOutcome {
    /// Concretely safe; no solver query needed.
    Proven {
        /// Which property was established.
        property: SafetyProperty,
        /// Why.
        detail: String,
    },
    /// Concretely unsafe; a counterexample exists.
    Violated {
        /// Which property is violated.
        property: SafetyProperty,
        /// Why.
        detail: String,
    },
    /// Depends on symbolic facts; the rendered `condition` must be discharged
    /// by the solver.
    Residual {
        /// Which property is at stake.
        property: SafetyProperty,
        /// The condition that would establish it.
        condition: String,
    },
}

impl CheckOutcome {
    /// The property this outcome concerns.
    pub fn property(&self) -> SafetyProperty {
        match self {
            CheckOutcome::Proven { property, .. }
            | CheckOutcome::Violated { property, .. }
            | CheckOutcome::Residual { property, .. } => *property,
        }
    }

    /// Whether this outcome is a concrete violation.
    pub fn is_violation(&self) -> bool {
        matches!(self, CheckOutcome::Violated { .. })
    }

    /// The verdict this single outcome contributes.
    pub fn verdict(&self) -> csolver_core::Verdict {
        match self {
            CheckOutcome::Proven { .. } => csolver_core::Verdict::Pass,
            CheckOutcome::Violated { .. } => csolver_core::Verdict::Fail,
            CheckOutcome::Residual { .. } => csolver_core::Verdict::Unknown,
        }
    }
}

/// The per-property outcomes for a single access.
#[derive(Debug, Clone, Default)]
pub struct AccessReport {
    /// The outcomes, one per checked property.
    pub outcomes: Vec<CheckOutcome>,
}

impl AccessReport {
    /// The combined verdict over all checked properties.
    pub fn verdict(&self) -> csolver_core::Verdict {
        csolver_core::Verdict::combine_all(self.outcomes.iter().map(CheckOutcome::verdict))
    }
}

impl MemoryModel {
    /// Check `access` through `ptr`, returning a per-property report.
    ///
    /// The checks evaluated are: no-null-deref, temporal validity
    /// (no-use-after-free), spatial validity (in-bounds), alignment, and
    /// permission (valid-read / valid-write).
    pub fn check_access(&self, ptr: &Pointer, access: Access) -> AccessReport {
        let mut outcomes = Vec::new();

        // --- 1. Null / provenance ------------------------------------------
        let region = match &ptr.provenance {
            Provenance::Null => {
                outcomes.push(CheckOutcome::Violated {
                    property: SafetyProperty::NoNullDeref,
                    detail: "dereference of the null pointer".into(),
                });
                return AccessReport { outcomes };
            }
            Provenance::Invalid => {
                outcomes.push(CheckOutcome::Violated {
                    property: SafetyProperty::NoDanglingDeref,
                    detail: "dereference of a pointer with invalid provenance".into(),
                });
                return AccessReport { outcomes };
            }
            Provenance::Unknown => {
                // We cannot prove anything spatial/temporal without provenance.
                outcomes.push(CheckOutcome::Residual {
                    property: SafetyProperty::ValidReference,
                    condition: "pointer has opaque provenance (e.g. from int-to-ptr); \
                                an explicit assumption is required to dereference it"
                        .into(),
                });
                return AccessReport { outcomes };
            }
            Provenance::Region(id) => match self.region(*id) {
                Some(r) => r,
                None => {
                    outcomes.push(CheckOutcome::Residual {
                        property: SafetyProperty::ValidReference,
                        condition: format!("region {id} is not tracked"),
                    });
                    return AccessReport { outcomes };
                }
            },
        };
        outcomes.push(CheckOutcome::Proven {
            property: SafetyProperty::NoNullDeref,
            detail: "pointer has region provenance, hence non-null".into(),
        });

        // --- 2. Temporal: use-after-free -----------------------------------
        outcomes.push(match region.state {
            LifetimeState::Live => CheckOutcome::Proven {
                property: SafetyProperty::NoUseAfterFree,
                detail: format!("region {} is live", region.id),
            },
            LifetimeState::Freed => CheckOutcome::Violated {
                property: SafetyProperty::NoUseAfterFree,
                detail: format!("region {} ({}) is freed", region.id, region.label),
            },
            LifetimeState::Uninitialized => CheckOutcome::Violated {
                property: SafetyProperty::NoUseAfterFree,
                detail: format!("region {} ({}) is not yet allocated", region.id, region.label),
            },
        });

        // --- 3. Spatial: in-bounds -----------------------------------------
        outcomes.push(bounds_outcome(&ptr.offset, access.size, &region.size));

        // --- 4. Alignment ---------------------------------------------------
        outcomes.push(alignment_outcome(ptr, region.align, access.align));

        // --- 5. Permissions -------------------------------------------------
        if access.need.read {
            outcomes.push(permission_outcome(
                region.permissions.read,
                SafetyProperty::ValidRead,
                "read",
                &region.label,
            ));
        }
        if access.need.write {
            outcomes.push(permission_outcome(
                region.permissions.write,
                SafetyProperty::ValidWrite,
                "write",
                &region.label,
            ));
        }

        AccessReport { outcomes }
    }
}

/// In-bounds: `0 <= offset` and `offset + access_size <= region_size`.
fn bounds_outcome(offset: &SymOffset, access_size: u64, region_size: &SymSize) -> CheckOutcome {
    const P: SafetyProperty = SafetyProperty::InBounds;
    match (offset.as_exact(), region_size.as_exact()) {
        (Some(off), Some(size)) => {
            let end = off + (access_size as i128);
            if off >= 0 && end <= size as i128 {
                CheckOutcome::Proven {
                    property: P,
                    detail: format!("[{off}, {end}) within [0, {size})"),
                }
            } else {
                CheckOutcome::Violated {
                    property: P,
                    detail: format!(
                        "access [{off}, {end}) escapes allocation [0, {size})"
                    ),
                }
            }
        }
        _ => CheckOutcome::Residual {
            property: P,
            condition: format!(
                "0 <= offset && offset + {access_size} <= size  (offset={offset:?}, size={region_size:?})"
            ),
        },
    }
}

/// Alignment: the access address must be a multiple of `access_align`.
fn alignment_outcome(ptr: &Pointer, _region_align: u64, access_align: u64) -> CheckOutcome {
    const P: SafetyProperty = SafetyProperty::Alignment;
    if access_align <= 1 {
        return CheckOutcome::Proven {
            property: P,
            detail: "byte-aligned access is always aligned".into(),
        };
    }
    // `ptr.align` already encodes the guaranteed alignment of the address
    // (region base alignment combined with the concrete offset).
    if ptr.align.is_multiple_of(access_align) {
        CheckOutcome::Proven {
            property: P,
            detail: format!("address is {}-aligned, needs {access_align}", ptr.align),
        }
    } else if matches!(ptr.offset, SymOffset::Exact(_)) {
        // Concrete address whose guaranteed alignment is insufficient.
        CheckOutcome::Violated {
            property: P,
            detail: format!(
                "address guaranteed only {}-aligned but {access_align} required",
                ptr.align
            ),
        }
    } else {
        CheckOutcome::Residual {
            property: P,
            condition: format!("address ≡ 0 (mod {access_align})"),
        }
    }
}

fn permission_outcome(
    granted: bool,
    property: SafetyProperty,
    verb: &str,
    label: &str,
) -> CheckOutcome {
    if granted {
        CheckOutcome::Proven {
            property,
            detail: format!("region {label} permits {verb}"),
        }
    } else {
        CheckOutcome::Violated {
            property,
            detail: format!("region {label} does not permit {verb}"),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use csolver_core::{RegionKind, SafetyProperty, Verdict};

    fn outcome_for(report: &AccessReport, p: SafetyProperty) -> &CheckOutcome {
        report
            .outcomes
            .iter()
            .find(|o| o.property() == p)
            .expect("property checked")
    }

    #[test]
    fn in_bounds_aligned_read_proves() {
        let mut m = MemoryModel::new();
        let r = m.allocate(
            RegionKind::Heap,
            SymSize::Exact(16),
            8,
            Permissions::READ_WRITE,
            "buf",
        );
        let p = Pointer::to_region(r, 8).offset_bytes(8);
        let report = m.check_access(&p, Access::read(8, 8));
        assert_eq!(report.verdict(), Verdict::Pass);
        assert!(matches!(
            outcome_for(&report, SafetyProperty::InBounds),
            CheckOutcome::Proven { .. }
        ));
    }

    #[test]
    fn out_of_bounds_read_is_violation() {
        let mut m = MemoryModel::new();
        let r = m.allocate(
            RegionKind::Heap,
            SymSize::Exact(16),
            8,
            Permissions::READ_WRITE,
            "buf",
        );
        // offset 12, read 8 => [12,20) escapes [0,16).
        let p = Pointer::to_region(r, 8).offset_bytes(12);
        let report = m.check_access(&p, Access::read(8, 4));
        assert_eq!(report.verdict(), Verdict::Fail);
        assert!(outcome_for(&report, SafetyProperty::InBounds).is_violation());
    }

    #[test]
    fn null_deref_is_violation() {
        let m = MemoryModel::new();
        let report = m.check_access(&Pointer::null(), Access::read(1, 1));
        assert_eq!(report.verdict(), Verdict::Fail);
        assert!(outcome_for(&report, SafetyProperty::NoNullDeref).is_violation());
    }

    #[test]
    fn use_after_free_is_violation() {
        let mut m = MemoryModel::new();
        let r = m.allocate(
            RegionKind::Heap,
            SymSize::Exact(8),
            8,
            Permissions::READ_WRITE,
            "b",
        );
        assert!(matches!(
            m.deallocate(r),
            CheckOutcome::Proven { .. }
        ));
        // Second free => double free.
        assert!(m.deallocate(r).is_violation());
        // Access after free => use-after-free.
        let p = Pointer::to_region(r, 8);
        let report = m.check_access(&p, Access::read(8, 8));
        assert!(outcome_for(&report, SafetyProperty::NoUseAfterFree).is_violation());
    }

    #[test]
    fn misaligned_access_is_violation() {
        let mut m = MemoryModel::new();
        let r = m.allocate(
            RegionKind::Heap,
            SymSize::Exact(16),
            8,
            Permissions::READ_WRITE,
            "b",
        );
        // base+1 is only 1-aligned, but we require 4.
        let p = Pointer::to_region(r, 8).offset_bytes(1);
        let report = m.check_access(&p, Access::read(4, 4));
        assert!(outcome_for(&report, SafetyProperty::Alignment).is_violation());
    }

    #[test]
    fn symbolic_offset_is_residual_not_pass() {
        let mut m = MemoryModel::new();
        let r = m.allocate(
            RegionKind::Heap,
            SymSize::Exact(16),
            8,
            Permissions::READ_WRITE,
            "b",
        );
        let p = Pointer {
            provenance: Provenance::Region(r),
            offset: SymOffset::Symbolic("i".into()),
            align: 8,
        };
        let report = m.check_access(&p, Access::read(1, 1));
        assert_eq!(report.verdict(), Verdict::Unknown);
        assert!(matches!(
            outcome_for(&report, SafetyProperty::InBounds),
            CheckOutcome::Residual { .. }
        ));
    }

    #[test]
    fn write_to_readonly_is_violation() {
        let mut m = MemoryModel::new();
        let r = m.allocate(
            RegionKind::Global,
            SymSize::Exact(8),
            8,
            Permissions::READ_ONLY,
            "rodata",
        );
        let p = Pointer::to_region(r, 8);
        let report = m.check_access(&p, Access::write(8, 8));
        assert!(outcome_for(&report, SafetyProperty::ValidWrite).is_violation());
    }
}
