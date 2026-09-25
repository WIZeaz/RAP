#![feature(register_tool)]
#![register_tool(rapx)]
#![allow(unused)]

// Regression: `Alive` on a raw-pointer field must NOT be proved from the
// struct parameter alone.
//
// `h: &Holder` only guarantees that the `Holder` struct itself is alive; it
// says nothing about the memory `h.ptr` points to — a raw pointer field has no
// liveness guarantee (that is what raw pointers are for).  The caller can only
// prove `Alive(h.ptr)` if `Holder` carries an invariant such as
// `#[rapx::invariant(Allocated(ptr, i32, 1))]` / `#[rapx::invariant(Alive(ptr, 'a))]`.
//
// BUG: `check_alive` classifies the target via `resolve_origin`'s *origin kind*,
// which here resolves to the temporary `&mut i32` returned by `as_ref_mut`
// (a `MutRef`) instead of the value's own type (`*mut i32`).  A `MutRef` origin
// is treated as "reference ⇒ alive", so `Alive(h.ptr)` is wrongly proved.

pub struct Holder {
    ptr: *mut i32,
}

#[rapx::verify]
#[rapx::requires(Alive(ptr, 'a))]
pub unsafe fn as_ref_mut<'a>(ptr: *mut i32) -> &'a mut i32 {
    unsafe { &mut *ptr }
}

// This must be UNSOUND: `Alive(h.ptr)` cannot be proved without a struct
// invariant, but the caller currently reports `Alive | Proved`.
#[rapx::verify]
pub unsafe fn use_after_free(h: &Holder) -> i32 {
    let r = unsafe { as_ref_mut(h.ptr) };
    *r
}
