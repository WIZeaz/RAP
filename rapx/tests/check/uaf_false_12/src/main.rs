struct S {
    a: usize,
}

fn set(s: &mut S) {
    s.a = 1;
}

fn main() {
    let mut s = S { a: 0 };
    set(&mut s);
    println!("{}", s.a);
}
