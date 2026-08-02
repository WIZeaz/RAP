use std::fmt::{self, Display};

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct Var(pub usize, pub bool); // bool is true if the var is an input var

impl Display for Var {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        if self == &DUMMY_INPUT_VAR {
            return write!(f, "DUMMY_INPUT_VAR");
        }
        if self == &DUMMY_UNIT_VAR {
            return write!(f, "DUMMY_UNIT_VAR");
        }
        write!(f, "v{}", self.0)
    }
}

impl Var {
    pub fn index(&self) -> usize {
        self.0
    }
    pub fn is_from_input(&self) -> bool {
        self.1
    }
    pub fn is_dummy(&self) -> bool {
        self.0 == 0
    }
}

pub static DUMMY_INPUT_VAR: Var = Var(0, true);
pub static DUMMY_UNIT_VAR: Var = Var(0, false);
