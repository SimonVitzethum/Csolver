//! End-to-end: real LLVM-IR text → MSIR (via the frontend) → verified safe.
//!
//! This is the first input that is *not* hand-built MSIR: it is parsed and
//! lowered from `.ll`, then run through the unchanged, audited analysis core.

use csolver_core::Verdict;
use csolver_ir::Frontend;
use csolver_llvm::{LlvmFrontend, LlvmInput};
use csolver_verifier::{verify_module, Config};

mod part_a;
mod part_b;
mod part_c;
mod part_d;
mod part_e;
mod part_f;
mod part_g;
mod part_h;
mod part_i;
mod part_j;

#[allow(unused_imports)]
use part_a::*;
#[allow(unused_imports)]
use part_b::*;
#[allow(unused_imports)]
use part_c::*;
#[allow(unused_imports)]
use part_d::*;
#[allow(unused_imports)]
use part_e::*;
#[allow(unused_imports)]
use part_f::*;
#[allow(unused_imports)]
use part_g::*;
#[allow(unused_imports)]
use part_h::*;
#[allow(unused_imports)]
use part_i::*;
#[allow(unused_imports)]
use part_j::*;
