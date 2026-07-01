// Challenge: type outlives bound `T: 'a`. The synthesizer must inspect
// lifetimes contained in `T`, not only direct reference parameters.

pub struct Item(String);

pub fn item() -> Item {
    Item(String::new())
}

pub fn type_bound<'a, 'b>(_anchor: &'a Item, y: &'b Item) -> &'b Item
where
    &'a Item: 'b,
{
    y
}

pub fn read(x: &Item) {}

pub fn read_mut(x: &mut Item) {}

#[cfg(test)]
mod test {
    use super::*;

    #[test]
    fn unexpected() {
        let mut x = item();
        let y = item();
        let r = type_bound(&x, &y);
        read_mut(&mut x);
        read(r);
    }
}
