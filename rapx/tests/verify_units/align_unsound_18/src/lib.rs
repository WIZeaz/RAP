#![feature(register_tool)]
#![register_tool(rapx)]
#![allow(dead_code)]

#[rapx::requires(Align(_ptr, T), kind = "precond")]
unsafe fn require_align<T>(_ptr: *const T) {}

// UNSOUND: `&[u8]` is only 1-byte aligned, while an unconstrained `T` may
// require a larger alignment (e.g. `u64`).  The old `align = 1` fallback for
// a generic `T` used to discharge this as SOUND.
#[rapx::verify]
pub fn unsound_unbounded_generic_cross_cast<T>(data: &[u8]) {
    let ptr = data.as_ptr() as *const T;

    unsafe {
        require_align::<T>(ptr);
    }
}
