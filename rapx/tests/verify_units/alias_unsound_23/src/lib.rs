#![feature(register_tool)]
#![register_tool(rapx)]
#![allow(dead_code)]

/// UNSOUND: a shared slice from `*const` is written through a safe cast to `*mut`.
#[rapx::requires(NonNull(ptr))]
#[rapx::requires(ValidPtr(ptr, u32, len))]
#[rapx::requires(Align(ptr, u32))]
#[rapx::requires(Init(ptr, u32, len))]
#[rapx::requires(Alive(ptr))]
#[rapx::requires(Owning(ptr))]
#[rapx::requires(ValidNum(size_of(u32) * len <= isize::MAX))]
#[rapx::verify]
pub unsafe fn unsound_const_slice_then_cast_write(ptr: *const u32, len: usize) -> u32 {
    let slice = unsafe { std::slice::from_raw_parts(ptr, len) };

    if !slice.is_empty() {
        let q = ptr as *mut u32;
        unsafe {
            *q = 9;
        }
        slice[0]
    } else {
        0
    }
}
