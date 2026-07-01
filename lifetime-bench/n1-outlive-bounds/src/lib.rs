// Challenge: explicit lifetime bound `'a: 'b`. The return type is `'b`, but
// the implementation returns an input with lifetime `'a`, relying on the bound.
// Negative test: the synthesizer does not generate invalid test

pub struct Item(String);

pub fn item() -> Item {
    Item(String::new())
}

pub fn choose_with_bound<'a, 'b>(x: &'a Item, y: &'b Item) -> &'b Item
where
    'a: 'b,
{
    y
}

pub fn read(x: &Item) {}

pub fn read_mut(x: &mut Item) {}

#[cfg(test)]
mod test {
    use super::*;

    // could not compile
    #[test]
    fn unexpected() { 
        let x = item();
        let y = item();
        let r = choose_with_bound(&x, &y);
        read_mut(&mut x); // can not borrow `x` as mutable
        read(r);
    }
}
