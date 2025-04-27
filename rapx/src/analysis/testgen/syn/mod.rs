pub mod impls;
pub mod input;
pub mod project;

use super::context::Context;
use rustc_middle::ty::TyCtxt;

pub struct SynOption {
    pub crate_name: String,
}

pub trait Synthesizer<'tcx> {
    fn syn<C: Context<'tcx>>(&mut self, cx: C, tcx: TyCtxt<'tcx>) -> String;
}
