#![feature(register_tool)]
#![register_tool(rapx)]
#![allow(dead_code)]

/// UNSOUND: a shared slice is cast to *mut and written through, mutating the
/// immutable data the &[i32] points to.
#[rapx::verify]
pub unsafe fn unsound_shared_slice_cast_write(slice: &[i32]) -> &mut i32 {
    let ptr = slice.as_ptr() as *mut i32;
    unsafe { &mut *ptr }
}
