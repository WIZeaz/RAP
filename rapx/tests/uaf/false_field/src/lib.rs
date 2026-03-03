struct S {
    field: String,
}

impl S {
    fn mutate(&mut self, s: String) {
        self.field = s;
    }
}
