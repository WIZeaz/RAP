unsafe fn callee(p: *mut i32) {
    unsafe {
        *p += 1;
    }
}

unsafe fn caller(p: *mut i32) {
    unsafe {
        callee(p);
    }
}

fn main() {
    let mut value = 0i32;
    let ptr: *mut i32 = &mut value as *mut i32;

    unsafe {
        caller(ptr);
    }

    println!("value = {}", value);
}

