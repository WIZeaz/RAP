#![feature(register_tool)]
#![register_tool(rapx)]
#![allow(dead_code)]

struct TwoPtr {
    a: *mut u8,
    b: *mut u8,
}

/// SOUND: `a` and `b` are two independent raw fields of one struct, pointing at
/// two different `Box` allocations. `&*a` and `&mut *b` do not alias, so the
/// tree-based Alias check must not conflate them via a shared struct root.
#[rapx::verify]
pub unsafe fn sound_two_independent_fields() -> usize {
    let t = TwoPtr {
        a: Box::into_raw(Box::new(1u8)),
        b: Box::into_raw(Box::new(2u8)),
    };
    let ra = &*t.a;
    let rb = &mut *t.b;
    *ra as usize + *rb as usize
}
