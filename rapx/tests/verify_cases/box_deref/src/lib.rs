pub fn f(n: usize) -> usize {
    let b = Box::new(n);
    eprintln!("{n}");
    *b
}
