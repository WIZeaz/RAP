use super::ContextBuilder;
use crate::analysis::testgen::context::{DUMMY_INPUT_VAR, Var};
use crate::analysis::testgen::utils;
use rustc_middle::ty::{self, Ty};
use std::fmt::{self, Display};

/// only Live, Moved, Borrowed is used
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum VarState {
    Live,
    Moved,
    Borrowed(ty::Mutability, Var),
}

impl VarState {
    pub fn is_live(&self) -> bool {
        matches!(self, VarState::Live)
    }

    pub fn is_dead(&self) -> bool {
        matches!(self, VarState::Moved)
    }

    pub fn is_borrowed(&self) -> bool {
        matches!(self, VarState::Borrowed(..))
    }

    pub fn live() -> Self {
        VarState::Live
    }

    pub fn moved() -> Self {
        VarState::Moved
    }

    pub fn borrowed(mutability: ty::Mutability, borrowed_by: Var) -> Self {
        VarState::Borrowed(mutability, borrowed_by)
    }
}

impl Display for VarState {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            VarState::Live => write!(f, "Live"),
            VarState::Moved => write!(f, "Moved"),
            VarState::Borrowed(mutability, borrowed_by) => {
                write!(
                    f,
                    "{}Borrowed({})",
                    if mutability.is_mut() { "Mut" } else { "" },
                    borrowed_by
                )
            }
        }
    }
}

impl<'tcx, 'a> ContextBuilder<'tcx, 'a> {
    pub fn set_var_state(&mut self, var: Var, state: VarState) {
        self.state.insert(var, state);
    }

    pub fn var_state(&self, var: Var) -> VarState {
        self.state
            .get(&var)
            .cloned()
            .expect(&format!("var {} does not exist", var))
    }

    pub fn available_vars<'b>(&'b self) -> impl Iterator<Item = Var> + use<'b, 'tcx> {
        let iter = self.cx.vars().filter_map(|var| match self.var_state(var) {
            VarState::Live | VarState::Borrowed(..) => Some(var),
            _ => None,
        });
        iter
    }

    pub fn providers_for(&self, ty: Ty<'tcx>) -> Vec<Var> {
        let mut ret = Vec::new();
        if utils::is_fuzzable_ty(ty, self.tcx) {
            ret.push(DUMMY_INPUT_VAR);
        }
        for var in self.available_vars() {
            if utils::is_ty_eq(ty, self.cx.type_of(var), self.tcx) {
                ret.push(var.clone());
            }
        }
        rap_trace!("providers for ty {ty:?}: {ret:?}");
        ret
    }
}
