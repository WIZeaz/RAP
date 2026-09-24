fn walk(x: u32) -> u32 {
    let mut a = x;
    if a & 1 != 0 {
        a = walk(a >> 1);
    }
    a
}

pub fn target(xs: &[u32]) -> String {
    format!("{}", walk(xs[0]))
}
