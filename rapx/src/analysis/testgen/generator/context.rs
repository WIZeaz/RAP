use super::stmt::{ApiCall, Stmt, StmtKind, Var, DUMMY_INPUT_VAR};
use super::utils;
use crate::rap_debug;
use crate::rustc_infer::infer::TyCtxtInferExt;
use rustc_hir::def_id::DefId;
use rustc_infer::traits::{Obligation, ObligationCause};
use rustc_middle::ty::{self, ParamEnv, Ty, TyCtxt, TyKind};
use rustc_span::{Span, DUMMY_SP};
use rustc_trait_selection::traits::query::evaluate_obligation::InferCtxtExt;
use std::{
    collections::{HashMap, HashSet},
    rc::Rc,
};

#[derive(Clone)]

pub struct Context<'tcx> {
    stmts: Vec<Stmt>,
    available: HashSet<Var>,
    var_ty: HashMap<Var, Ty<'tcx>>,
    tcx: TyCtxt<'tcx>,
}

impl<'tcx> Context<'tcx> {
    pub fn tcx(&self) -> TyCtxt<'tcx> {
        self.tcx
    }

    pub fn complexity(&self) -> usize {
        self.stmts.len()
    }

    pub fn new(tcx: TyCtxt<'tcx>) -> Context<'tcx> {
        Context {
            stmts: Vec::new(),
            available: HashSet::new(),
            var_ty: HashMap::new(),
            tcx,
        }
    }

    pub fn available_values(&self) -> &HashSet<Var> {
        &self.available
    }

    pub fn type_of(&self, var: Var) -> Ty<'tcx> {
        *self.var_ty.get(&var).expect("no type for var")
    }

    pub fn stmts(&self) -> &[Stmt] {
        &self.stmts
    }

    pub fn all_possible_providers(&self, ty: Ty<'tcx>) -> Vec<Var> {
        let mut ret = Vec::new();
        if utils::is_fuzzable_ty(ty, self.tcx) {
            ret.push(DUMMY_INPUT_VAR);
        }
        for val in self.available_values() {
            // assume all type are concrete
            let infcx = self.tcx.infer_ctxt().build();
            let env = ParamEnv::reveal_all();
            // TODO: How to deal with lifetime?
            let res = infcx.at(&ObligationCause::dummy(), env).eq(
                rustc_infer::infer::DefineOpaqueTypes::Yes,
                ty,
                self.type_of(*val),
            );
            if res.is_ok() {
                ret.push(val.clone());
            }
        }
        ret
    }

    fn mk_var(&mut self, ty: Ty<'tcx>, is_input: bool) -> Var {
        let next_var = Var(self.var_ty.len(), is_input);
        self.var_ty.insert(next_var, ty);
        next_var
    }

    fn add_input_stmt(&mut self, ty: Ty<'tcx>) -> Var {
        let var;
        if let ty::Ref(_, inner_ty, mutability) = ty.kind() {
            let inner_var = self.add_input_stmt(*inner_ty);
            var = self.mk_var(ty, false);
            self.stmts.push(Stmt::ref_(var, inner_var, *mutability));
        } else {
            var = self.mk_var(ty, true);
            self.stmts.push(Stmt::input(var));
        }
        var
    }

    pub fn add_call_stmt(&mut self, mut call: ApiCall) -> Var {
        let fn_sig = utils::jump_all_binders(call.fn_did, self.tcx);
        let output_ty = fn_sig.output();
        for idx in 0..fn_sig.inputs().len() {
            let arg = call.args[idx];
            let input_ty = fn_sig.inputs()[idx];
            self.remove_var_from_available(arg);
            if arg == DUMMY_INPUT_VAR {
                let var = self.add_input_stmt(input_ty);
                call.args[idx] = var;
            }
        }
        let var = self.mk_var(output_ty, false);
        let stmt = Stmt {
            kind: StmtKind::Call(call),
            place: var,
        };
        self.stmts.push(stmt);
        var
    }

    // if the output_ty of expr does not implement Copy, we need to remove the expr from the available set
    pub fn remove_var_from_available(&mut self, var: Var) -> bool {
        if var == DUMMY_INPUT_VAR {
            return false;
        }
        if !self.available.contains(&var) {
            panic!("var {:?} not in available set", var);
        }

        let output_ty = self.type_of(var);
        let is_mut_ref =
            output_ty.is_ref() && matches!(output_ty.ref_mutability(), Some(ty::Mutability::Mut));

        if !is_mut_ref && utils::is_ty_impl_copy(output_ty, self.tcx) {
            return false;
        }

        self.available.remove(&var);
        true
    }
}
