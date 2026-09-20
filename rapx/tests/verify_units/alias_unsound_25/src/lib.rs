#![feature(register_tool)]
#![register_tool(rapx)]
#![allow(dead_code)]

struct Node {
    next: *mut Node,
}

impl Node {
    /// UNSOUND: `&self` produces `&mut` through a private raw field; calling it
    /// twice yields two `&mut` aliases to the same pointee.
    #[rapx::verify]
    pub unsafe fn next_mut(&self) -> &mut Node {
        unsafe { &mut *self.next }
    }
}
