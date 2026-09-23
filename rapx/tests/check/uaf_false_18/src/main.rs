fn pick(first: Vec<u8>) -> Vec<u8> {
    if first.is_empty() { Vec::new() } else { first }
}

fn main() {
    pick(Vec::new());
}
