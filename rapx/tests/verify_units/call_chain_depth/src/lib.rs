fn l4(a: u32) -> u32 {
    a ^ 1
}

fn l3(mut a: u32) -> u32 {
    if a & 1 != 0 {
        a = l4(a)
    }
    if a & 2 != 0 {
        a = l4(a)
    }
    if a & 4 != 0 {
        a = l4(a)
    }
    if a & 8 != 0 {
        a = l4(a)
    }
    a
}

fn l2(mut a: u32) -> u32 {
    if a & 1 != 0 {
        a = l3(a)
    }
    if a & 2 != 0 {
        a = l3(a)
    }
    if a & 4 != 0 {
        a = l3(a)
    }
    if a & 8 != 0 {
        a = l3(a)
    }
    a
}

fn l1(mut a: u32) -> u32 {
    if a & 1 != 0 {
        a = l2(a)
    }
    if a & 2 != 0 {
        a = l2(a)
    }
    if a & 4 != 0 {
        a = l2(a)
    }
    if a & 8 != 0 {
        a = l2(a)
    }
    a
}

fn l0(mut a: u32) -> u32 {
    if a & 1 != 0 {
        a = l1(a)
    }
    if a & 2 != 0 {
        a = l1(a)
    }
    if a & 4 != 0 {
        a = l1(a)
    }
    if a & 8 != 0 {
        a = l1(a)
    }
    a
}

pub fn target(xs: &[u32]) -> String {
    format!("{}", l0(xs[0]))
}
