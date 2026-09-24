pub fn f(n: usize) -> usize {
    let b = Box::new(n);
    eprintln!("{n}");
    *b
}

// `transmute::<Box<T>, *mut T>` yields a real raw pointer (not the compiler's
// safe `*box` deref), so dereferencing it is an unsafe raw-pointer deref and
// must not be skipped as a safe Box deref.
pub unsafe fn transmute_deref(n: usize) -> usize {
    let b = Box::new(n);
    let p: *mut usize = std::mem::transmute(b);
    *p
}
