use super::*;

const SRC: &str = r#"
!0 = distinct !DICompileUnit(language: DW_LANG_Rust, file: !1)
define float @f(ptr align 8 %self) !dbg !7 {
start:
  ret float 0.0
}
!7 = distinct !DISubprogram(name: "f", scope: !9)
!42 = !DILocalVariable(name: "self", arg: 1, scope: !7, file: !8, line: 104, type: !39)
!39 = !DIDerivedType(tag: DW_TAG_pointer_type, name: "&mut lib::Rand32", baseType: !9, size: 64, align: 64)
!9 = !DICompositeType(tag: DW_TAG_structure_type, name: "Rand32", size: 128, align: 64)
!40 = !DIDerivedType(tag: DW_TAG_pointer_type, name: "*const u8", baseType: !41, size: 64)
!41 = !DIBasicType(name: "u8", size: 8, encoding: DW_ATE_unsigned)
!50 = !DILocalVariable(name: "p", arg: 2, scope: !7, type: !40)
"#;

#[test]
fn recovers_rust_mut_reference_pointee_size() {
    let di = parse(SRC);
    let c = di.param_ref(7, 1).expect("&mut Rand32 param");
    assert_eq!(c.size, 16, "Rand32 is 128 bits = 16 bytes");
    assert!(c.writable, "&mut is writable");
}

#[test]
fn raw_pointer_param_is_not_contracted() {
    let di = parse(SRC);
    // `*const u8` (arg 2) is a raw pointer — validity not guaranteed, so no
    // contract (recovering one would be a false-PASS hole).
    assert!(di.param_ref(7, 2).is_none());
}

const STRUCT_SRC: &str = r#"
!0 = distinct !DICompileUnit(language: DW_LANG_Rust, file: !1)
!7 = distinct !DISubprogram(name: "f")
!42 = !DILocalVariable(name: "self", arg: 1, scope: !7, type: !39)
!39 = !DIDerivedType(tag: DW_TAG_pointer_type, name: "&mut Wrap", baseType: !9, size: 64)
!9 = !DICompositeType(tag: DW_TAG_structure_type, name: "Wrap", size: 128, elements: !12)
!12 = !{!13, !15}
!13 = !DIDerivedType(tag: DW_TAG_member, name: "tag", baseType: !14, size: 64, offset: 0)
!14 = !DIBasicType(name: "u64", size: 64)
!15 = !DIDerivedType(tag: DW_TAG_member, name: "inner", baseType: !16, size: 64, offset: 64)
!16 = !DIDerivedType(tag: DW_TAG_pointer_type, name: "&u8", baseType: !17, size: 64)
!17 = !DIBasicType(name: "u8", size: 8)
"#;

#[test]
fn resolves_reference_struct_member_at_offset() {
    let di = parse(STRUCT_SRC);
    let s = di.param_pointee_any(7, 1).expect("&mut Wrap pointee");
    // Member `inner: &u8` is at byte offset 8 (bit offset 64).
    let c = di.member_ref(s, 8).expect("reference member at offset 8");
    assert_eq!(c.size, 1, "&u8 pointee is 1 byte");
    assert!(!c.writable, "&u8 is read-only");
    // Member `tag: u64` at offset 0 is not a reference → no contract.
    assert!(di.member_ref(s, 0).is_none());
}
