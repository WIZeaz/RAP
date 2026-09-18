#![feature(register_tool)]
#![register_tool(rapx)]
#![allow(dead_code)]

use std::ffi::CStr;
use std::slice;

// UNSOUND: the sub-slice "hello" (from b"xx\0hello"[3..]) has no trailing NUL,
// yet a CStr is formed from it.
#[rapx::verify]
pub fn unsound_subslice_cstr() -> usize {
    let bytes = b"xx\0hello";             // NUL at offset 2
    let q = unsafe { bytes.as_ptr().add(3) }; // points at "hello" (no NUL)
    let sub = unsafe { slice::from_raw_parts(q, 5) }; // "hello" — NOT NUL-terminated
    let cstr = unsafe { CStr::from_bytes_with_nul_unchecked(sub) };
    cstr.to_bytes().len()
}
