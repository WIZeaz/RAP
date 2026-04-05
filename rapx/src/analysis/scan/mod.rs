mod statistic;
/// NOTE: This analysis module is currently under development and is highly unstable.
/// The #[allow(unused)] attribute is applied to suppress excessive lint warnings.
/// Once the analysis stabilizes, this marker should be removed.

#[allow(unused)]
mod visitor;
use crate::analysis::utils::path::get_path_resolver;
use crate::analysis::{Analysis, scan::visitor::FnVisitor};
use rustc_hir::def_id::LOCAL_CRATE;
use rustc_middle::ty::TyCtxt;

/// Scan Analysis - obtain basic information for crate
pub struct ScanAnalysis<'tcx> {
    tcx: TyCtxt<'tcx>,
}

impl<'tcx> Analysis for ScanAnalysis<'tcx> {
    fn name(&self) -> &'static str {
        "Scan Analysis"
    }

    fn run(&mut self) {
        let crate_name = self.tcx.crate_name(LOCAL_CRATE);
        let crate_type = self.tcx.crate_types()[0];
        rap_info!("======== Crate Info ========");
        rap_info!("name: {}", crate_name.as_str());
        rap_info!("type: {}", crate_type);
        rap_info!("============================");
        rap_info!("========= API Info =========");
        let mut fn_visitor = FnVisitor::new(self.tcx);
        self.tcx.hir_visit_all_item_likes_in_crate(&mut fn_visitor);
        let stats = fn_visitor.statistic();
        stats.info().print_log();
        rap_info!("======== Path Info =========");
        let resolver = get_path_resolver(self.tcx);
        for (did, path_str) in resolver.paths() {
            rap_info!(
                "kind: {}, actual: {}, public: {}",
                self.tcx.def_descr(did),
                self.tcx.def_path_str(did),
                path_str
            );
        }
    }

    fn reset(&mut self) {}
}

impl<'tcx> ScanAnalysis<'tcx> {
    pub fn new(tcx: TyCtxt<'tcx>) -> Self {
        ScanAnalysis { tcx }
    }
}
