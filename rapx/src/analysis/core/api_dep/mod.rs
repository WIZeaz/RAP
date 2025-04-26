/// NOTE: This analysis module is currently under development and is highly unstable.
/// The #[allow(unused)] attribute is applied to suppress excessive lint warnings.
/// Once the analysis stabilizes, this marker should be removed.

#[allow(unused)]
pub mod graph;
#[allow(unused)]
mod visitor;

use crate::{rap_debug, rap_info};
pub use graph::ApiDepGraph;
pub use graph::{DepEdge, DepNode};
use rustc_hir::def_id::LOCAL_CRATE;
use rustc_middle::ty::TyCtxt;
use visitor::FnVisitor;

pub struct ApiDep<'tcx> {
    pub tcx: TyCtxt<'tcx>,
}

impl<'tcx> ApiDep<'tcx> {
    pub fn new(tcx: TyCtxt<'tcx>) -> ApiDep<'tcx> {
        ApiDep { tcx }
    }
    pub fn start(&self, pub_only: bool) -> ApiDepGraph<'tcx> {
        let local_crate_name = self.tcx.crate_name(LOCAL_CRATE);
        let local_crate_type = self.tcx.crate_types()[0];
        let graph_all_pub_api = if pub_only {
            "all APIs including private APIs"
        } else {
            "only public APIs"
        };
        rap_debug!(
            "Build API dependency graph on {} ({}), graph based on {}",
            local_crate_name.as_str(),
            local_crate_type,
            graph_all_pub_api,
        );
        let config = graph::Config { pub_only };
        let mut api_graph = ApiDepGraph::new(config, self.tcx);
        api_graph.build();

        let statistics = api_graph.statistics();
        // print all statistics
        rap_debug!(
            "API Graph contains {} API nodes, {} type nodes, {} generic parameter def nodes",
            statistics.api_count,
            statistics.type_count,
            statistics.generic_param_count
        );

        let dot_filename = format!("api_graph_{}_{}.dot", local_crate_name, local_crate_type);
        rap_info!("Dump API dependency graph to {}", dot_filename);
        api_graph.dump_to_dot(dot_filename, self.tcx);
        api_graph
    }
}
