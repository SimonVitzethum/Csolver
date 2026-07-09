//! The DWARF `.debug_info` reader recovers each pointer parameter's pointee byte
//! size from a real clang-produced `.o`. The fixture is committed (built once with
//! `clang -O1 -g -c`) so the test is hermetic — no compiler needed at test time.
//!
//! Source of `fixtures/deref.o`:
//! ```c
//! int  deref(int  *p) { return *p; }
//! long load8(long *q) { return *q; }
//! ```

use csolver_elf::parameter_pointee_sizes;

const DEREF_O: &[u8] = include_bytes!("fixtures/deref.o");

#[test]
fn recovers_pointer_parameter_pointee_sizes() {
    let image = csolver_elf::load(DEREF_O).expect("load fixture .o");
    let map = parameter_pointee_sizes(&image, DEREF_O);

    // The subprogram name (via DW_FORM_strx1 through the relocated
    // .debug_str_offsets) must resolve to the real function, not the CU filename
    // or the producer string.
    let deref = map
        .get("deref")
        .unwrap_or_else(|| panic!("no `deref` entry; got keys {:?}", map.keys().collect::<Vec<_>>()));
    assert_eq!(deref, &[Some(4)], "int* pointee is 4 bytes");

    let load8 = map
        .get("load8")
        .unwrap_or_else(|| panic!("no `load8` entry; got keys {:?}", map.keys().collect::<Vec<_>>()));
    assert_eq!(load8, &[Some(8)], "long* pointee is 8 bytes");
}
