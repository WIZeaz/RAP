mod context;
mod driver;
mod generator;
mod path;
mod syn;
mod utils;

use crate::analysis::testgen::driver::driver_main;
use crate::{rap_error, rap_info};
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
        match driver_main(self.tcx) {
            Ok(_) => rap_info!("testgen completed successfully"),
            Err(e) => rap_error!("testgen failed:\n{}", e),
        }
    }
}
