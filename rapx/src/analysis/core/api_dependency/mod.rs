/// NOTE: This analysis module is currently under development and is highly unstable.
/// The #[allow(unused)] attribute is applied to suppress excessive lint warnings.
/// Once the analysis stabilizes, this marker should be removed.

#[allow(unused)]
pub mod graph;
mod mono;
mod utils;
#[allow(unused)]
mod visitor;

use crate::analysis::Analysis;
pub use graph::ApiDependencyGraph;
pub use graph::{DepEdge, DepNode};
use rustc_hir::def_id::LOCAL_CRATE;
use rustc_middle::ty::TyCtxt;
use serde::Deserialize;
pub use utils::{is_def_id_public, is_fuzzable_ty};

#[derive(Debug, Clone, Copy, Eq, PartialEq, PartialOrd, Deserialize)]
pub struct Config {
    pub pub_only: bool,
    pub resolve_generic: bool,
    pub ignore_const_generic: bool,
    pub include_unsafe: bool,
    pub include_drop: bool,
    pub max_generic_search_iteration: usize,
}

impl Default for Config {
    fn default() -> Self {
        Config {
            pub_only: true,
            resolve_generic: true,
            ignore_const_generic: true,
            include_unsafe: false,
            include_drop: false,
            max_generic_search_iteration: 10,
        }
    }
}

pub trait ApiDependencyAnalysis<'tcx> {
    fn get_api_dependency_graph(&self) -> ApiDependencyGraph<'tcx>;
}

pub struct ApiDependencyAnalyzer<'tcx> {
    tcx: TyCtxt<'tcx>,
    config: Config,
    api_graph: ApiDependencyGraph<'tcx>,
}

impl<'tcx> ApiDependencyAnalyzer<'tcx> {
    pub fn new(tcx: TyCtxt<'tcx>, config: Config) -> ApiDependencyAnalyzer<'tcx> {
        ApiDependencyAnalyzer {
            tcx,
            config,
            api_graph: ApiDependencyGraph::new(tcx),
        }
    }
}

impl<'tcx> Analysis for ApiDependencyAnalyzer<'tcx> {
    fn name(&self) -> &'static str {
        "Default API dependency graph analysis algorithm."
    }

    fn run(&mut self) {
        let local_crate_name = self.tcx.crate_name(LOCAL_CRATE);
        let local_crate_type = self.tcx.crate_types()[0];
        let config = self.config;
        rap_info!(
            "Build API dependency graph on {} ({}), config = {:?}",
            local_crate_name.as_str(),
            local_crate_type,
            config,
        );

        let api_graph = &mut self.api_graph;
        api_graph.build(config);
        let (estimate, total) = api_graph.estimate_coverage();

        let statistics = api_graph.statistics();
        // print all statistics
        rap_info!(
            "API Graph contains {} API nodes, {} type nodes, {} edges",
            statistics.api_count,
            statistics.type_count,
            statistics.edge_cnt
        );
        rap_info!(
            "estimate coverage: {:.2} ({}/{})",
            estimate as f64 / total as f64,
            estimate,
            total
        );
        let dot_path = format!("api_graph_{}_{}.dot", local_crate_name, local_crate_type);
        let json_path = format!("api_graph_{}_{}.json", local_crate_name, local_crate_type);
        let api_file_path = format!("apis_{}_{}.log", local_crate_name, local_crate_type);
        rap_info!("uncovered APIs: {:?}", api_graph.uncovered_api());
        rap_info!("Dump API dependency graph to {}", dot_path);
        api_graph.dump_to_dot(dot_path);
        api_graph
            .dump_to_json(&json_path)
            .expect("failed to dump API graph to JSON");
        api_graph.dump_apis(api_file_path);
        rap_info!("Dump API dependency graph to {}", json_path);
    }

    fn reset(&mut self) {
        todo!();
    }
}

impl<'tcx> ApiDependencyAnalysis<'tcx> for ApiDependencyAnalyzer<'tcx> {
    fn get_api_dependency_graph(&self) -> ApiDependencyGraph<'tcx> {
        self.api_graph.clone()
    }
}
