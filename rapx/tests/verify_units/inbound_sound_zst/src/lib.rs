#![feature(register_tool)]
#![register_tool(rapx)]
#![allow(dead_code)]

// SOUND: a ZST element type (`()`) has byte size 0, but the slice still tracks
// its *element* length via `slice_len` (not `size / elem_size`, which is 0/0).
#[rapx::verify]
pub fn sound_zst_slice_len(s: &[()]) -> usize {
    s.len()
}

// SOUND: element-level bounds hold for a ZST slice (the index is compared
// against the element count, not the zero byte size).
#[rapx::verify]
pub fn sound_zst_index_in_bounds(s: &[()], i: usize) {
    if i < s.len() {
        let _ = &s[i];
    }
}
