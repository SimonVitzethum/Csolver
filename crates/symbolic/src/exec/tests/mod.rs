//! The executor's test suite, split into part files (mechanical refactor).
#![allow(clippy::unwrap_used, clippy::expect_used)]

// Shared scope for the part files (each starts with `use super::*;`).
#[allow(unused_imports)]
use super::*;
#[allow(unused_imports)]
use csolver_ir::{BasicBlock, FuncId};

mod part_a;
mod part_b;
mod part_c;
mod part_d;
mod part_e;
mod part_f;
mod part_g;

use part_a::*;
use part_d::*;
