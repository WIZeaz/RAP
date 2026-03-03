fn main() {
    let mut a = Vec::from([1, 2]);
    foo(&mut a);
}

fn foo(v: &mut Vec<i32>) -> Vec<i32> {
    let res = v.clone();
    *v = Vec::new();
    res
}
