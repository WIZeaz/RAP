use rustc_hir::def_id::DefId;
use rustc_middle::ty::{self, Ty};
use std::fmt;
use std::fmt::Display;
use std::rc::Rc;

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]

pub struct Var(pub usize, pub bool); // bool is true if the var is an input var

impl Display for Var {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "v{}", self.0)
    }
}

impl Var {
    pub fn unique_id(&self) -> usize {
        self.0
    }
}

pub static DUMMY_INPUT_VAR: Var = Var(0, true);

#[derive(Debug, Clone, Eq, Hash, PartialEq)]
pub struct ApiCall {
    pub fn_did: DefId,
    pub args: Vec<Var>,
}

impl ApiCall {
    pub fn new(fn_did: DefId, args: Vec<Var>) -> Self {
        Self { fn_did, args }
    }

    pub fn args(&self) -> &[Var] {
        &self.args
    }

    pub fn fn_did(&self) -> DefId {
        self.fn_did
    }
}

// pub type StmtRef<'tcx> = Rc<Stmt<'tcx>>;

#[derive(Clone, Debug, Eq, Hash, PartialEq)]
pub enum StmtKind {
    Input,
    Call(ApiCall),
    Split(usize, Vec<Var>),        // (a, b) -> a, b
    Concat(Vec<Var>),              // a, b -> (a, b)
    Ref(Box<Var>, ty::Mutability), // a -> &(mut) b
    Deref(Box<Var>),               // &a -> a
    Drop(Box<Var>),
}

impl StmtKind {
    pub fn is_input(&self) -> bool {
        matches!(self, StmtKind::Input)
    }
}

#[derive(Clone, Debug, Eq, Hash, PartialEq)]
pub struct Stmt {
    pub kind: StmtKind,
    pub place: Var,
}

impl Stmt {
    pub fn input(place: Var) -> Stmt {
        Stmt {
            kind: StmtKind::Input,
            place,
        }
    }

    pub fn kind(&self) -> &StmtKind {
        &self.kind
    }

    pub fn place(&self) -> Var {
        self.place
    }

    pub fn call(call: ApiCall, retval: Var) -> Stmt {
        Stmt {
            kind: StmtKind::Call(call),
            place: retval,
        }
    }

    pub fn ref_(place: Var, ref_place: Var, mutability: ty::Mutability) -> Stmt {
        Stmt {
            kind: StmtKind::Ref(Box::new(ref_place), mutability),
            place,
        }
    }

    pub fn drop_(place: Var, dropped: Var) -> Stmt {
        Stmt {
            kind: StmtKind::Drop(Box::new(dropped)),
            place,
        }
    }

    pub fn api_call(&self) -> &ApiCall {
        match self.kind() {
            StmtKind::Call(call) => call,
            _ => panic!("not a call"),
        }
    }

    pub fn var_for_call_arg(&self, no: usize) -> Var {
        match self.kind() {
            StmtKind::Call(call) => {
                if no == 0 {
                    self.place()
                } else {
                    call.args()[no - 1]
                }
            }
            _ => panic!("not a call"),
        }
    }
}
