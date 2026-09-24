struct V {
    a: String,
    #[allow(dead_code)]
    b: String,
    #[allow(dead_code)]
    c: String,
}

fn take(v: V) -> String {
    v.a
}

fn main() {
    let v = V {
        a: String::new(),
        b: String::new(),
        c: String::new(),
    };
    let _ = take(v);
}
