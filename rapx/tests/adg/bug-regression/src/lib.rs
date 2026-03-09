// nested type
// fuzzable check should not cause stack overflow
pub struct A {
    pub a: Vec<A>,
    pub b: Vec<A>,
}

pub fn dummy(a: A) {}
