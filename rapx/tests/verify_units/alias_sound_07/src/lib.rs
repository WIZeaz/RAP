#![feature(register_tool)]
#![register_tool(rapx)]
#![allow(dead_code)]

pub struct PrivateSlot {
    ptr: *mut u32,
}

impl PrivateSlot {
    pub fn new(value: &mut u32) -> Self {
        Self { ptr: value }
    }

    // SOUND: a &mut self returns a unique view through the private raw field.
    #[rapx::verify]
    pub fn as_slice_mut(&mut self) -> &mut [u32] {
        unsafe { std::slice::from_raw_parts_mut(self.ptr, 1) }
    }
}
