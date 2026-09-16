#![feature(register_tool)]
#![register_tool(rapx)]
#![allow(dead_code)]

/// UNSOUND: `p: *mut T` is an *independent* raw pointer — it carries no aliasing
/// guarantee, so a sound analysis must assume it may alias the shared `self_`.
/// `&mut *p` produces a mutable reference that can therefore alias the live
/// `&[T]` (shared-xor-mut is violated).  The `Alias` hazard must be reported,
/// not discharged by the "the function has a shared reference" heuristic.
#[rapx::verify]
#[rapx::requires(Init(p, T, 1))]
#[rapx::requires(Align(p, T))]
pub unsafe fn unsound_independent_mut_ptr_aliases_shared<'a, T>(
    self_: &'a [T],
    p: *mut T,
) -> &'a mut T {
    unsafe { &mut *p }
}
