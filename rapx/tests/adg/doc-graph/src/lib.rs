pub struct S1 {
    pub a: i32,
    pub b: f32,
}

pub struct S2 {
    pub a: i32,
    pub b: f32,
}

pub struct S3 {
    pub a: i32,
    pub b: f32,
}

pub fn api1(arg1: i32, arg2: &f32) -> S1 {
    S1 { a: arg1, b: *arg2 }
}
pub fn api2(arg1: &mut i32, arg2: f32) -> S2 {
    S2 { a: *arg1, b: arg2 }
}

pub fn api3(arg1: &S1, arg2: &S2) -> S3 {
    S3 {
        a: arg1.a,
        b: arg2.b,
    }
}
