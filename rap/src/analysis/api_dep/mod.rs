use crate::{rap_info, utils::fs::rap_create_file};

use graph::ApiDepGraph;
use rustc_hir::{
    def_id::{DefId, LocalDefId},
    intravisit::{self, FnKind, Visitor},
    BodyId, FnDecl,
};
use rustc_middle::{dep_graph, ty::TyCtxt};
use rustc_span::Span;
pub mod graph;
pub mod visitor;
use std::io::Write;
use visitor::FnVisitor;

pub struct ApiDep<'tcx> {
    pub tcx: TyCtxt<'tcx>,
}

impl<'tcx> ApiDep<'tcx> {
    pub fn new(tcx: TyCtxt<'tcx>) -> ApiDep<'tcx> {
        ApiDep { tcx }
    }
    pub fn start(&self) {
        rap_info!("Build API dependency graph");
        let mut api_graph = ApiDepGraph::new();
        let mut fn_visitor = FnVisitor::new(self.tcx, &mut api_graph);
        self.tcx
            .hir()
            .visit_all_item_likes_in_crate(&mut fn_visitor);
        rap_info!("visitor find {} APIs.", fn_visitor.fn_cnt());
        let mut file = rap_create_file("visitor.txt", "fail when create file");
        fn_visitor.write_funcs(&mut file);

        api_graph.dump_to_dot("api_graph.dot", self.tcx);

        let mut file = rap_create_file("traverse.txt", "fail when create file");
        let mut fn_cnt = 0;
        for local_def_id in self.tcx.iter_local_def_id() {
            let hir_map = self.tcx.hir();
            if hir_map.maybe_body_owned_by(local_def_id).is_some() {
                write!(&mut file, "{}\n", self.tcx.def_path_str(local_def_id))
                    .expect("fail when write file");
                // rap_info!("find API: {}", self.tcx.def_path_str(local_def_id));
                fn_cnt += 1;
            }
        }
        rap_info!("find {} APIs.", fn_cnt);
    }
}
