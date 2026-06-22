mod a {
    pub fn foo() {}
    pub fn bar() {}
    pub trait Foo {
        fn foo();
    }
    impl Foo for crate::A {
        fn foo() {}
    }
}

mod b {
    pub struct B;
    pub trait OnlyB {}
    impl OnlyB for B {}

    pub fn foob<T: OnlyB>() {}
}
struct A;

pub use a::Foo as _; // A::foo is visitable
pub use a::bar; // bar is visitable
pub use a::foo as _; // foo can not be visited
// foob::<B>
pub use b::*;



#[cfg(test)]
mod test {
    use super::*;
    #[test]
    fn test_visibility() {
        A::foo();
        foob::<B>();
    }
}
