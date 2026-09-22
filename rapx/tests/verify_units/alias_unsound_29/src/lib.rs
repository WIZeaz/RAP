#![feature(register_tool)]
#![register_tool(rapx)]
#![allow(dead_code)]

/// UNSOUND: a shared view `&[u8]` split from a leaked `Box` is still live when a
/// unique view `&mut [u8]` is split from the same box. Two raw pointers split
/// off one owned origin produce a `&` and a `&mut` that alias, violating
/// shared-XOR-mutable (the tree-based Alias check catches this even though the
/// slice views carry a different provenance `AllocId` than the raw pointer).
#[rapx::verify]
pub unsafe fn unsound_split_shared_then_mut() -> usize {
    let b = Box::new(1u8);
    let ptr = Box::into_raw(b);
    let s1 = std::slice::from_raw_parts(ptr as *const u8, 1);
    let s2 = std::slice::from_raw_parts_mut(ptr, 1);
    s1.len() + s2.len()
}
