use super::*;

#[test]
fn line_at_finds_the_covering_row() {
    let rows = vec![(0x1000u64, 3u32), (0x1008, 4), (0x1010, 5)];
    assert_eq!(dwarf_line::line_at(&rows, 0x1000), Some(3));
    assert_eq!(dwarf_line::line_at(&rows, 0x1004), Some(3), "between rows → the earlier line");
    assert_eq!(dwarf_line::line_at(&rows, 0x100c), Some(4));
    assert_eq!(dwarf_line::line_at(&rows, 0x1010), Some(5));
    assert_eq!(dwarf_line::line_at(&rows, 0x0fff), None, "before the first row");
}

#[test]
fn empty_without_debug_line() {
    // An image with no `.debug_line` section yields no rows (not a panic).
    let img = Image { machine: EM_X86_64, ..Image::default() };
    assert!(dwarf_line::line_rows(&img, &[]).is_empty());
}
