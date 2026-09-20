#![feature(register_tool)]
#![register_tool(rapx)]
#![allow(dead_code)]

struct Node {
    next: *mut Node,
}

impl Node {
    /// UNSOUND: a safe free function exposes the private raw field (through a
    /// non-first parameter), letting external code write through it, aliasing
    /// the `&Node` this method returns.
    #[rapx::verify]
    pub unsafe fn get_next(&self) -> &Node {
        unsafe { &*self.next }
    }
}

fn expose_next(_tag: i32, node: &Node) -> *mut Node {
    node.next
}
