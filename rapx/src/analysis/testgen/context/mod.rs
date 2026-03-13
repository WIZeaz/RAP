mod stmt;
mod var;
mod var_set;

use super::utils::{self};
use itertools::Itertools;
use rustc_middle::ty::{self, Ty, TyCtxt};
use std::collections::HashMap;
pub use stmt::{ApiCall, ExploitKind, Stmt, StmtKind};
pub use var::*;

#[derive(Clone)]
pub struct Context<'tcx> {
    stmts: Vec<Stmt<'tcx>>,
    var_ty: HashMap<Var, Ty<'tcx>>,
    var_mut: HashMap<Var, ty::Mutability>,
    num_apicall: usize,
    tcx: TyCtxt<'tcx>,
}

impl<'tcx> Context<'tcx> {
    pub fn new(tcx: TyCtxt<'tcx>) -> Context<'tcx> {
        Context {
            stmts: Vec::new(),
            var_ty: HashMap::new(),
            var_mut: HashMap::new(),
            num_apicall: 0,
            tcx,
        }
    }

    pub fn num_apicall(&self) -> usize {
        self.num_apicall
    }

    pub fn num_stmt(&self) -> usize {
        self.stmts.len()
    }

    pub fn stmts(&self) -> &[Stmt<'tcx>] {
        &self.stmts
    }

    pub fn tcx(&self) -> TyCtxt<'tcx> {
        self.tcx
    }

    pub fn add_stmt(&mut self, stmt: Stmt<'tcx>) -> &Stmt<'tcx> {
        if stmt.kind().is_call() {
            self.num_apicall += 1;
        }
        self.stmts.push(stmt);
        self.stmts.last().unwrap()
    }

    pub fn vars<'a>(&'a self) -> impl Iterator<Item = Var> + 'a {
        self.var_mut.keys().copied()
    }

    pub fn lift_mutability(&mut self, var: Var, mutability: ty::Mutability) {
        if matches!(mutability, ty::Mutability::Mut) {
            self.var_mut.insert(var, ty::Mutability::Mut);
        }
    }

    pub fn var_mutability(&self, var: Var) -> ty::Mutability {
        *self.var_mut.get(&var).unwrap_or(&ty::Mutability::Not)
    }

    pub fn type_of(&self, var: Var) -> Ty<'tcx> {
        if var == DUMMY_UNIT_VAR {
            return self.tcx.types.unit;
        }
        self.var_ty[&var]
    }

    pub fn mk_var(&mut self, ty: Ty<'tcx>, is_input: bool) -> Var {
        let next_var = Var(self.var_ty.len() + 1, is_input);
        self.var_ty.insert(next_var, ty);
        self.var_mut.insert(next_var, ty::Mutability::Not);

        next_var
    }
}
