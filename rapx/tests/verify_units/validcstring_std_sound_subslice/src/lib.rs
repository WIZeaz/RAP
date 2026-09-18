#![feature(register_tool)]
#![register_tool(rapx)]
#![allow(dead_code)]

use std::ffi::CStr;
use std::slice;

// SOUND: a `from_raw_parts` sub-slice starting at a non-zero offset is still a
// NUL-terminated C string (the trailing NUL is inside the sub-slice).
#[rapx::verify]
pub fn sound_subslice_cstr() -> usize {
    let bytes = b"xxhello\0";            // 8 bytes, NUL at offset 7
    let q = unsafe { bytes.as_ptr().add(2) }; // points at "hello\0"
    let sub = unsafe { slice::from_raw_parts(q, 6) }; // "hello\0"
    let cstr = unsafe { CStr::from_bytes_with_nul_unchecked(sub) };
    cstr.to_bytes().len()
}
