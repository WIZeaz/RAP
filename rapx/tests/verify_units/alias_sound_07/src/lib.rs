#![feature(register_tool)]
#![register_tool(rapx)]
#![allow(dead_code)]

use std::marker::PhantomData;

#[rapx::invariant(Alive(ptr, 'a))]
pub struct PrivateSlot<'a> {
    ptr: *mut u32,
    _marker: PhantomData<&'a mut u32>,
}

impl<'a> PrivateSlot<'a> {
    pub fn new(value: &'a mut u32) -> Self {
        Self {
            ptr: value,
            _marker: PhantomData,
        }
    }

    // SOUND: a &mut self returns a unique view through the private raw field.
    #[rapx::verify]
    pub fn as_slice_mut(&mut self) -> &mut [u32] {
        unsafe { std::slice::from_raw_parts_mut(self.ptr, 1) }
    }
}
