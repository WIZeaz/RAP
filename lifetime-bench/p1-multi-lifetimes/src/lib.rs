// Challenge: multi-lifetime API where the return lifetime is tied to only one
// input. A conservative model may lock `x` because it is passed as `&mut` to a
// function returning a reference, but rustc accepts the later shared borrow.

pub struct Item(String);

static mut ID: u32 = 0;

pub fn item() -> Item {
    Item(String::new())
}

pub fn select_second<'a, 'b>(x: &'a mut Item, y: &'b Item) -> &'b Item {
    x.0 = "flag".into();
    y
}

pub fn read(x: &Item, r: &Item) {
    assert!(x.0 != "flag");
}

#[cfg(test)]
mod test {
    use super::*;

    #[test]
    fn unexpected() {
        let mut x = item();
        let y = item();
        let r = select_second(&mut x, &y);
        read(&x); // assertion fail
    }
}
