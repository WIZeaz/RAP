#![feature(register_tool)]
#![register_tool(rapx)]
#![allow(dead_code)]

/// UNSOUND: `&*p` on a one-past-end (out-of-bounds) pointer.  The raw-ptr-deref
/// checkpoint checks `NonNull + Allocated + InBound` (the `ValidPtr` part of the
/// `Ptr2Ref` compound), so the out-of-bounds deref is rejected by `InBound`.
#[rapx::verify]
pub unsafe fn unsound_oob_deref_missing_validptr<T>(slice: &[T]) -> &T {
    let p = unsafe { slice.as_ptr().add(slice.len()) };
    unsafe { &*p }
}
