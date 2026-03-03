struct S {
    field: String,
}

fn main() {
    let mut s = S {
        field: String::new(),
    };
    s.field = foo(&s)
}

fn foo(v: &S) -> String {
    v.field.clone()
}
