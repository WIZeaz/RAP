#![feature(register_tool)]
#![register_tool(rapx)]
#![allow(dead_code)]

/// SOUND: the shared view `s1` goes out of scope (its inner block ends, so its
/// `StorageDead` precedes the unique view) before `s2` is produced from the same
/// box. There is no live `&` when the `&mut` is created, so shared-XOR-mutable
/// holds.
#[rapx::verify]
pub unsafe fn sound_split_shared_dead_then_mut() -> usize {
    let b = Box::new(1u8);
    let ptr = Box::into_raw(b);
    let n;
    {
        let s1 = std::slice::from_raw_parts(ptr as *const u8, 1);
        n = s1.len();
    }
    let s2 = std::slice::from_raw_parts_mut(ptr, 1);
    n + s2.len()
}
