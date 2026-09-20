#![feature(register_tool)]
#![register_tool(rapx)]
#![allow(dead_code)]

struct Inner {
    ptr: *mut i32,
}

struct Outer {
    node: Inner,
}

impl Outer {
    /// UNSOUND: a safe free function exposes the nested raw field
    /// (`Inner::ptr`), letting external code write through it, aliasing the
    /// `&i32` this returns.
    #[rapx::verify]
    pub unsafe fn get(&self) -> &i32 {
        unsafe { &*self.node.ptr }
    }
}

fn expose_ptr(inner: &Inner) -> *mut i32 {
    inner.ptr
}
