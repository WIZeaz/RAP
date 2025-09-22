pub mod impls;
pub mod input;
pub mod project;
pub mod visible_path;

use super::context::Context;
use rustc_middle::ty::TyCtxt;

pub struct SynOption {
    pub crate_name: String,
}

pub trait Synthesizer<'tcx> {
    fn syn(&mut self, cx: &Context<'tcx>, tcx: TyCtxt<'tcx>) -> String;
}
