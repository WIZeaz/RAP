use super::utils;
use super::var::Var;
use crate::analysis::testgen::context::{Context, var::DUMMY_UNIT_VAR};
use rustc_abi::VariantIdx;
use rustc_hir::def_id::DefId;
use rustc_middle::ty::{self, AdtDef, GenericArgsRef, TyCtxt};

#[derive(Debug, Clone, Eq, Hash, PartialEq)]
pub struct ApiCall<'tcx> {
    pub fn_did: DefId,
    pub generic_args: ty::GenericArgsRef<'tcx>,
    pub args: Vec<Var>,
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

    pub fn args_mut(&mut self) -> &mut [Var] {
        &mut self.args
    }

    pub fn fn_did(&self) -> DefId {
        self.fn_did
    }

    pub fn generic_args(&self) -> GenericArgsRef<'tcx> {
        self.generic_args
    }

    pub fn fn_sig(&self, tcx: TyCtxt<'tcx>) -> ty::FnSig<'tcx> {
        utils::fn_sig_with_generic_args(self.fn_did, self.generic_args, tcx)
    }
}

#[derive(Clone, Debug, Eq, Hash, PartialEq)]
pub enum ExploitKind {
    Debug, // use by Debug trait
}

#[derive(Clone, Debug, Eq, Hash, PartialEq)]
pub struct CtorDict<'tcx> {
    pub adt_def: AdtDef<'tcx>,
    pub variant_idx: VariantIdx,
    pub field_vars: Vec<(String, Var)>,
}

#[derive(Clone, Debug, Eq, Hash, PartialEq)]
pub enum StmtKind<'tcx> {
    Input,
    Tuple(Vec<Var>), // place = (..)
    Array(Vec<Var>), // place = [..]
    Call(ApiCall<'tcx>),
    SpecialCall(String, Vec<Var>),
    Ref(Var, ty::Mutability), // a -> &(mut) b
    AsRef(Var),               // as_ref
    AsMut(Var),               // as_mut
    Ctor(CtorDict<'tcx>),
    Comment(String),
    // Deref(Box<Var>, ty::Mutability), // &T -> &U
    Exploit(Var, ExploitKind),
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

    pub fn ctor(place: Var, dict: CtorDict<'tcx>) -> Stmt<'tcx> {
        Stmt {
            kind: StmtKind::Ctor(dict),
            place,
        }
    }

    pub fn comment(comment: String) -> Stmt<'tcx> {
        Stmt {
            kind: StmtKind::Comment(comment),
            place: DUMMY_UNIT_VAR,
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
            kind: StmtKind::Ref(ref_place, mutability),
            place,
        }
    }

    pub fn as_ref_(place: Var, ref_place: Var) -> Stmt<'tcx> {
        Stmt {
            kind: StmtKind::AsRef(ref_place),
            place,
        }
    }

    pub fn as_mut_(place: Var, ref_place: Var) -> Stmt<'tcx> {
        Stmt {
            kind: StmtKind::AsMut(ref_place),
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

    pub fn exploit(place: Var, var: Var, use_kind: ExploitKind) -> Stmt<'tcx> {
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

    pub fn call_inputs_and_output_var_at(&self, no: usize) -> Var {
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
                rap_trace!("mk_fn_sig_with_var_tys for call: {:?}", call);
                let tcx = cx.tcx;
                let fn_sig = utils::fn_sig_with_identities(call.fn_did(), tcx);
                let var_ty = cx.type_of(self.place());
                rap_trace!("place -> {:?}", var_ty);

                // get actual vid of input in the pattern
                let mut inputs = Vec::new();
                for var in call.args() {
                    let ty = cx.type_of(*var);
                    rap_trace!("var {:?} -> {:?}", var, ty);
                    inputs.push(ty);
                }
                let fn_sig = tcx.mk_fn_sig(
                    inputs.into_iter(),
                    var_ty,
                    fn_sig.c_variadic,
                    fn_sig.safety,
                    fn_sig.abi,
                );
                rap_trace!("fn_sig = {:?}", fn_sig);
                fn_sig
            }
            _ => panic!("not a call"),
        }
    }
}
