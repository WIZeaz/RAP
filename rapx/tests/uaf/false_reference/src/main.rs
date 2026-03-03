fn main() {
    let a = String::new();
    let s = S { a: &a };
    drop(s);
}

struct S<'a> {
    a: &'a str,
}

impl Drop for S<'_> {
    fn drop(&mut self) {}
}
