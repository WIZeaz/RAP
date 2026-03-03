fn main() {
    let mut s = String::new();
    #[allow(clippy::never_loop, unused_assignments)]
    loop {
        drop(s);
        s = String::new();
        return;
    }
}
