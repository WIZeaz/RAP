fn main() {
    let mut a = Vec::from([1, 2]);
    drop(std::mem::take(&mut a));
}
