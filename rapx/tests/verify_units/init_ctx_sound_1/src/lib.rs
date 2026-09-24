#![feature(register_tool)]
#![register_tool(rapx)]
#![allow(dead_code)]

use std::mem::MaybeUninit;

/// # Safety
/// `ptr` must be non-null, aligned for `u32`, and point to allocated (not
/// dangling) memory.
#[rapx::requires(ValidPtr(ptr, u32, 1))]
#[rapx::requires(Align(ptr, u32))]
#[rapx::verify]
unsafe fn maybe_init_slot(ptr: *mut u32, value: u32, flag: bool) {
    if flag {
        unsafe { ptr.write(value) }
    }
}

// SOUND: the caller passes a literal `true`, so the helper's conditional write
// is guaranteed to fire. Phase 1 (context-insensitive must-write) intersects the
// write set over *all* paths (the `flag == false` path writes nothing), yielding
// an empty must-write and falsely reporting `assume_init_read` on uninitialized
// memory; Phase 2 prunes the `flag == false` path via the concrete call context
// and proves the write always happens.
#[rapx::verify]
pub fn sound_context_sensitive_conditional_init(value: u32) -> u32 {
    let mut slot = MaybeUninit::<u32>::uninit();
    let ptr = slot.as_mut_ptr();

    unsafe { maybe_init_slot(ptr, value, true) }

    unsafe { slot.assume_init_read() }
}
