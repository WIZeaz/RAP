use super::utils;
use super::var::Var;
use crate::analysis::testgen::context::Context;
use rustc_hir::def_id::DefId;
use rustc_middle::ty::{self, TyCtxt};

#[derive(Debug, Clone, Eq, Hash, PartialEq)]
pub struct ApiCall<'tcx> {
    pub fn_did: DefId,
    pub args: Vec<Var>,
    pub generic_args: ty::GenericArgsRef<'tcx>,
}

impl<'tcx> ApiCall<'tcx> {
    pub fn new(fn_did: DefId, args: Vec<Var>, tcx: TyCtxt<'tcx>) -> Self {
        Self {
            fn_did,
            args,
            generic_args: tcx.mk_args(&[]),
        }
    }

    pub fn args(&self) -> &[Var] {
        &self.args
    }

    pub fn fn_did(&self) -> DefId {
        self.fn_did
    }

    pub fn generic_args(&self) -> &[ty::GenericArg<'tcx>] {
        self.generic_args
    }

    pub fn fn_sig(&self, tcx: TyCtxt<'tcx>) -> ty::FnSig<'tcx> {
        utils::fn_sig_with_generic_args(self.fn_did, self.generic_args, tcx)
    }
}

#[derive(Clone, Debug, Eq, Hash, PartialEq)]
pub enum UseKind {
    Debug, // use by Debug trait
}

#[derive(Clone, Debug, Eq, Hash, PartialEq)]
pub enum StmtKind<'tcx> {
    Input,
    Tuple(Vec<Var>),               // place = (..)
    Array(Vec<Var>),               // place = [..]
    SliceRef(Var, ty::Mutability), // place = &[..]
    Call(ApiCall<'tcx>),
    SpecialCall(String, Vec<Var>),
    Ref(Box<Var>, ty::Mutability), // a -> &(mut) b
    // Deref(Box<Var>, ty::Mutability), // &T -> &U
    Exploit(Var, UseKind),
}

impl<'tcx> StmtKind<'tcx> {
    pub fn is_input(&self) -> bool {
        matches!(self, StmtKind::Input)
    }
    pub fn is_call(&self) -> bool {
        matches!(self, StmtKind::Call(_))
    }
}

#[derive(Clone, Debug, Eq, Hash, PartialEq)]
pub struct Stmt<'tcx> {
    pub kind: StmtKind<'tcx>,
    pub place: Var,
}

impl<'tcx> Stmt<'tcx> {
    pub fn input(place: Var) -> Stmt<'tcx> {
        Stmt {
            kind: StmtKind::Input,
            place,
        }
    }

    pub fn kind(&self) -> &StmtKind<'tcx> {
        &self.kind
    }

    pub fn place(&self) -> Var {
        self.place
    }

    pub fn call(call: ApiCall<'tcx>, retval: Var) -> Stmt<'tcx> {
        Stmt {
            kind: StmtKind::Call(call),
            place: retval,
        }
    }

    pub fn special_call(path: impl ToString, args: Vec<Var>, retval: Var) -> Stmt<'tcx> {
        Stmt {
            kind: StmtKind::SpecialCall(path.to_string(), args),
            place: retval,
        }
    }

    pub fn ref_(place: Var, ref_place: Var, mutability: ty::Mutability) -> Stmt<'tcx> {
        Stmt {
            kind: StmtKind::Ref(Box::new(ref_place), mutability),
            place,
        }
    }

    pub fn box_(place: Var, boxed: Var) -> Stmt<'tcx> {
        Self::special_call("Box::new", vec![boxed], place)
    }

    pub fn drop_(place: Var, dropped: Var) -> Stmt<'tcx> {
        Self::special_call("drop", vec![dropped], place)
    }

    pub fn tuple(place: Var, elems: Vec<Var>) -> Stmt<'tcx> {
        Stmt {
            kind: StmtKind::Tuple(elems),
            place,
        }
    }

    pub fn array(place: Var, elems: Vec<Var>) -> Stmt<'tcx> {
        Stmt {
            kind: StmtKind::Array(elems),
            place,
        }
    }

    pub fn slice_ref(place: Var, slice: Var, mutability: ty::Mutability) -> Stmt<'tcx> {
        Stmt {
            kind: StmtKind::SliceRef(slice, mutability),
            place,
        }
    }

    pub fn exploit(place: Var, var: Var, use_kind: UseKind) -> Stmt<'tcx> {
        Stmt {
            kind: StmtKind::Exploit(var, use_kind),
            place,
        }
    }

    pub fn as_apicall(&self) -> &ApiCall<'tcx> {
        match self.kind() {
            StmtKind::Call(call) => call,
            _ => panic!("stmt is not a call: {self:?}"),
        }
    }

    pub fn as_call_arg_at(&self, no: usize) -> Var {
        match self.kind() {
            StmtKind::Call(call) => {
                if no == 0 {
                    self.place()
                } else {
                    call.args()[no - 1]
                }
            }
            _ => panic!("stmt is not a call: {self:?}"),
        }
    }

    pub fn mk_fn_sig_with_var_tys(&self, cx: &Context<'tcx>) -> ty::FnSig<'tcx> {
        match self.kind() {
            StmtKind::Call(call) => {
                let tcx = cx.tcx;
                let fn_sig = utils::fn_sig_with_identities(call.fn_did(), tcx);
                let var_ty = cx.type_of(self.place());

                // get actual vid of input in the pattern
                let mut inputs = Vec::new();
                for var in call.args() {
                    let ty = cx.type_of(*var);
                    inputs.push(ty);
                }
                tcx.mk_fn_sig(
                    inputs.into_iter(),
                    var_ty,
                    fn_sig.c_variadic,
                    fn_sig.safety,
                    fn_sig.abi,
                )
            }
            _ => panic!("not a call"),
        }
    }
}
