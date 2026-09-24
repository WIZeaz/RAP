fn param_or_local(name: &String) -> usize {
    let h = String::new();
    std::cmp::max(&h, name).len()
}

fn two_locals() -> usize {
    let a = String::new();
    let b = String::new();
    std::cmp::max(&a, &b).len()
}

fn main() {
    let name = String::new();
    let _ = param_or_local(&name) + two_locals();
}
