// Challenge: get_item_mut returns a MutView<'a>, to trigger assertion failure,
// the synthesizer must first drop MutView<'a> so the compiler can accept the program.
// The assertion failure must be triggered when secondly mutably borrow item.

pub struct Item(String);

static mut ID: u32 = 0;

pub fn item() -> Item {
    Item(unsafe {
        ID += 1;
        let id = ID;
        format!("item-{}", id)
    })
}

pub struct ImmutView<'a> {
    item: &'a Item,
    id_str: String,
}

pub fn get_immut<'a>(item: &'a mut Item) -> ImmutView<'a> {
    ImmutView {
        item,
        id_str: item.0.clone(),
    }
}

pub fn get_id<'a>(view: &ImmutView<'a>) -> String {
    view.id_str.clone()
}

pub fn get_mut<'a>(item: &'a mut Item, id_str: String) {
    if item.0 == id_str {
        item.0 = "flag".into();
    }
}

pub fn read(x: &Item) {
    assert!(x.0 != "flag");
}

#[cfg(test)]
mod test {
    use super::*;

    #[test]
    fn expeceted() {
        let mut x = item();
        let view = get_immut(&mut x);
        let id_str = get_id(&view);
        get_mut(&mut x, id_str);
        read(&x); // assertion fail
    }
}
