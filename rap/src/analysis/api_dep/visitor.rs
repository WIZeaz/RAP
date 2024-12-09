use std::io::Write;

use super::graph::ApiDepGraph;
use super::graph::DepNode;
use petgraph::data::Build;
use rustc_hir::{
    def_id::{DefId, LocalDefId},
    intravisit::{self, FnKind, Visitor},
    BodyId, FnDecl,
};
use rustc_middle::query::Key;
use rustc_middle::ty::TyCtxt;
use rustc_span::Span;

pub struct FnVisitor<'tcx, 'a> {
    fn_cnt: usize,
    tcx: TyCtxt<'tcx>,
    funcs: Vec<DefId>,
    graph: &'a mut ApiDepGraph,
}

impl<'tcx, 'a> FnVisitor<'tcx, 'a> {
    pub fn new(tcx: TyCtxt<'tcx>, graph: &'a mut ApiDepGraph) -> FnVisitor<'tcx, 'a> {
        let fn_cnt = 0;
        let funcs = Vec::new();
        FnVisitor {
            fn_cnt,
            tcx,
            graph,
            funcs,
        }
    }
    pub fn fn_cnt(&self) -> usize {
        self.fn_cnt
    }
    pub fn write_funcs<T: Write>(&self, F: &mut T) {
        for id in &self.funcs {
            write!(F, "{}\n", self.tcx.def_path_str(id)).expect("fail when write funcs");
        }
    }
}

impl<'tcx, 'a> Visitor<'tcx> for FnVisitor<'tcx, 'a> {
    fn visit_fn<'v>(
        &mut self,
        fk: FnKind<'v>,
        fd: &'v FnDecl<'v>,
        b: BodyId,
        span: Span,
        id: LocalDefId,
    ) -> Self::Result {
        self.fn_cnt += 1;
        let api_node = self.graph.get_node(DepNode::api(id));
        self.funcs.push(id.to_def_id());
        let fn_sig = self.tcx.fn_sig(id).skip_binder().skip_binder();

        for input in fn_sig.inputs() {
            let input_node = self.graph.get_node(DepNode::ty(input.ty_def_id()));
            self.graph.add_edge(input_node, api_node);
        }
        let output_node = self
            .graph
            .get_node(DepNode::ty(fn_sig.output().ty_def_id()));
        self.graph.add_edge(api_node, output_node);
    }
}
