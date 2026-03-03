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
    Borrowed,
    BorrowedMut,
    Dropped,
}

impl VarState {
    pub fn is_dropped(&self) -> bool {
        matches!(self, VarState::Dropped)
    }

    pub fn is_live(&self) -> bool {
        matches!(self, VarState::Live)
    }

    pub fn is_dead(&self) -> bool {
        matches!(self, VarState::Dropped | VarState::Moved)
    }

    pub fn is_borrowed(&self) -> bool {
        matches!(self, VarState::Borrowed | VarState::BorrowedMut)
    }

    pub fn is_borrowed_mut(&self) -> bool {
        matches!(self, VarState::BorrowedMut)
    }

    pub fn borrowed(mutability: ty::Mutability) -> Self {
        match mutability {
            ty::Mutability::Not => VarState::Borrowed,
            ty::Mutability::Mut => VarState::BorrowedMut,
        }
    }
}

impl Display for VarState {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            VarState::Live => write!(f, "Live"),
            VarState::Moved => write!(f, "Moved"),
            VarState::Borrowed => write!(f, "Borrowed"),
            VarState::BorrowedMut => write!(f, "BorrowedMut"),
            VarState::Dropped => write!(f, "Dropped"),
        }
    }
}

impl<'tcx, 'a> ContextBuilder<'tcx, 'a> {
    pub fn is_borrowed(&self, var: Var) -> bool {
        self.var_borrow[&var].intersection(&self.live_state).count() > 0
    }

    pub fn is_live(&self, var: Var) -> bool {
        self.live_state.contains(var.index())
    }

    pub fn var_state(&self, var: Var) -> VarState {
        if !self.is_live(var) {
            return VarState::Moved;
        }

        if self.is_borrowed(var) {
            return VarState::Borrowed;
        }

        VarState::Live
    }

    pub fn available_vars<'b>(&'b self) -> impl Iterator<Item = Var> + use<'b, 'tcx> {
        let iter = self.cx.vars().filter_map(|var| match self.var_state(var) {
            VarState::Live => Some(var),
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
        ret
    }
}
