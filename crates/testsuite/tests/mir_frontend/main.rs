//! End-to-end: real Rust MIR text → MSIR (via the MIR frontend) → verified.
//!
//! The point of MIR over LLVM-IR is that the bounds/overflow checks rustc
//! inserts are *explicit* `assert` terminators, so a checked index `s[i]` is
//! proved in bounds precisely because the check is present — and an access
//! without the check is correctly not proved.

use csolver_core::{SafetyProperty, Verdict};
use csolver_ir::Frontend;
use csolver_mir::{MirFrontend, MirInput};
use csolver_verifier::{verify_module, Config};

#[allow(clippy::expect_used)]

mod part_a;
mod part_b;
mod part_c;

pub fn lower(src: &str, name: &str) -> csolver_ir::Module {
    MirFrontend
        .lower(MirInput { source: src.into(), name: name.into() })
        .expect("the MIR frontend lowers the body")
}

#[allow(unused_imports)]
use part_a::*;
#[allow(unused_imports)]
use part_b::*;
#[allow(unused_imports)]
use part_c::*;
