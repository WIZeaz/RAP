#![feature(register_tool)]
#![register_tool(rapx)]
#![allow(dead_code)]

/// UNSOUND: a shared view `&*p` is still live when a `&mut *p` is produced from
/// the same raw pointer, violating shared-XOR-mutable.
#[rapx::verify]
pub unsafe fn shared_then_mut<'a, T>(p: *mut T) -> &'a mut T {
    let r = unsafe { &*p };
    let m = unsafe { &mut *p };
    m
}
