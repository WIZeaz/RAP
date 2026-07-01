// Challenge: get_item_mut returns a MutView<'a>, to trigger assertion failure,
// the synthesizer must first drop MutView<'a> so the compiler can accept the program.
// The assertion failure must be triggered when secondly mutably borrow item.
pub struct Item(String);

pub fn item() -> Item {
    Item(String::new())
}

pub struct MutView<'a> {
    item: &'a mut Item,
}

pub fn get_item_mut<'a>(item: &'a mut Item) -> MutView<'a> {
    if item.0.is_empty() {
        item.0 = "tmp".into();
    } else {
        item.0 = "flag".into();
    }
    MutView { item }
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
        let y = item();
        let view = get_item_mut(&mut x);
        // view explicitly dropped here.
        let view2 = get_item_mut(&mut x);
        read(&x); // assertion fail
    }
}
