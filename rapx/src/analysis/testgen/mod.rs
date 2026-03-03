mod context;
mod context_builder;
mod driver;
mod generator;
mod ltgen;
mod path;
mod syn;
mod utils;

use crate::analysis::testgen::driver::driver_main;
use rustc_middle::ty::TyCtxt;

/// Automatic Test Generator for detecting lifetime-related bugs
pub struct Testgen<'tcx> {
    pub tcx: TyCtxt<'tcx>,
}

impl<'tcx> Testgen<'tcx> {
    pub fn new(tcx: TyCtxt<'tcx>) -> Testgen<'tcx> {
        Testgen { tcx }
    }

    pub fn tcx(&self) -> TyCtxt<'tcx> {
        self.tcx
    }

    pub fn start(&self) {
        for env_var in [
            "TESTGEN_DISABLE_ALIAS",
            "TESTGEN_DISABLE_WEIGHT",
            "TESTGEN_DISABLE_INJECT",
        ] {
            rap_info!("env:{} = {}", env_var, utils::is_env_var_exist(env_var));
        }
        match driver_main(self.tcx) {
            Ok(_) => rap_info!("testgen completed successfully"),
            Err(e) => rap_error!("testgen failed:\n{}", e),
        }
    }
}
