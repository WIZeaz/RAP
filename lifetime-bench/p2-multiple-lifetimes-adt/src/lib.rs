// Challenge: ADT with multiple lifetime parameters. The API exposes references
// through a compound type, and the synthesizer must track which lifetime each
// field carries.

pub struct Item(String);

pub struct ItemView<'a, 'b> {
    pub left: &'a mut Item,
    pub right: &'b mut Item,
}

pub fn item() -> Item {
    Item(String::new())
}

pub fn make_view<'a, 'b>(lhs: &'a mut Item, rhs: &'b mut Item) -> ItemView<'a, 'b> {
    lhs.0 = "flag".into();
    ItemView {
        left: lhs,
        right: rhs,
    }
}

pub fn consume<'a, 'b>(view: ItemView<'a, 'b>) -> &'b Item {
    view.right
}

pub fn read(x: &Item) {
    assert!(x.0 != "flag");
}

#[cfg(test)]
mod test {
    use super::*;
    
    #[test]
    fn expected() {
        let mut x = item();
        let mut y = item();
        let view = make_view(&mut x, &mut y);
        let t = consume(view);
        read(&x); // assertion failed
    }
}
