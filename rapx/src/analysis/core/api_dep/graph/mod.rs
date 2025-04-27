pub mod dep_edge;
pub mod dep_node;
mod ty_wrapper;

use crate::analysis::core::api_dep::visitor::FnVisitor;
use crate::utils::fs::rap_create_file;
pub use dep_edge::{DepEdge, TransformKind};
pub use dep_node::{desc_str, DepNode};
use petgraph::dot;
use petgraph::graph::NodeIndex;
use petgraph::Direction;
use petgraph::Graph;
use rustc_middle::ty::{self, Ty, TyCtxt};
use std::collections::HashMap;
use std::hash::Hash;
use std::io::Write;
use std::path::Path;
pub use ty_wrapper::TyWrapper;

type InnerGraph<'tcx> = Graph<DepNode<'tcx>, DepEdge>;
pub struct ApiDepGraph<'tcx> {
    graph: InnerGraph<'tcx>,
    node_indices: HashMap<DepNode<'tcx>, NodeIndex>,
    config: Config,
    tcx: TyCtxt<'tcx>,
}

pub struct Statistics {
    pub api_count: usize,
    pub type_count: usize,
    pub generic_param_count: usize,
    pub edge_cnt: usize,
}

#[derive(Debug, Clone, Copy)]
pub struct Config {
    pub pub_only: bool,
}

impl<'tcx> ApiDepGraph<'tcx> {
    pub fn new(config: Config, tcx: TyCtxt<'tcx>) -> ApiDepGraph<'tcx> {
        ApiDepGraph {
            graph: Graph::new(),
            node_indices: HashMap::new(),
            config,
            tcx,
        }
    }

    pub fn num_api(&self) -> usize {
        self.graph
            .node_indices()
            .filter(|index| matches!(self.graph[*index], DepNode::Api(_)))
            .count()
    }

    pub fn num_ty(&self) -> usize {
        self.graph
            .node_indices()
            .filter(|index| matches!(self.graph[*index], DepNode::Ty(_)))
            .count()
    }

    fn tcx(&self) -> TyCtxt<'tcx> {
        self.tcx
    }

    pub fn build(&mut self) {
        // 1. scan
        let tcx = self.tcx();
        let mut fn_visitor = FnVisitor::new(tcx, self);
        tcx.hir().visit_all_item_likes_in_crate(&mut fn_visitor);

        // 2. add transform node
        self.add_transform_edges();

        // 3. prune redundant nodes
        self.prune_redundant_nodes();
    }

    pub fn add_transform_edges(&mut self) {
        // let mut transforms =
        for node_index in self.graph.node_indices() {
            if let DepNode::Ty(ty) = self.graph[node_index] {
                self.add_possible_transform::<3>(ty, 0);
            }
        }
    }

    fn add_possible_transform<const MAX_DEPTH: usize>(
        &mut self,
        current_ty: TyWrapper<'tcx>,
        depth: usize,
    ) -> Option<NodeIndex> {
        if depth > 0 {
            let index = self.get_index_by_node(DepNode::Ty(current_ty));
            if index.is_some() {
                return index;
            }
        }

        if depth >= MAX_DEPTH {
            return None;
        }

        let mut ret = None;
        for kind in TransformKind::all() {
            let new_ty = current_ty.transform(*kind, self.tcx()); // &T or &mut T
            if let Some(next_index) = self.add_possible_transform::<MAX_DEPTH>(new_ty, depth + 1) {
                let current_index = self.get_node(DepNode::Ty(current_ty));
                self.add_edge_once(current_index, next_index, DepEdge::transform(*kind));
                ret = Some(current_index);
            }
        }
        ret
    }

    pub fn prune_redundant_nodes(&mut self) {}

    pub fn is_ty_exist(&self, ty: Ty<'tcx>) -> bool {
        self.node_indices.contains_key(&DepNode::Ty(ty.into()))
    }

    pub fn pub_only(&self) -> bool {
        self.config.pub_only
    }

    pub fn inner_graph(&self) -> &InnerGraph<'tcx> {
        &self.graph
    }

    pub fn statistics(&self) -> Statistics {
        let mut api_cnt = 0;
        let mut ty_cnt = 0;
        let mut generic_param_cnt = 0;
        let mut edge_cnt = 0;

        for node in self.graph.node_indices() {
            match self.graph[node] {
                DepNode::Api(_) => api_cnt += 1,
                DepNode::Ty(_) => ty_cnt += 1,
                DepNode::GenericParamDef(..) => generic_param_cnt += 1,
            }
        }

        for edge in self.graph.edge_indices() {
            edge_cnt += 1;
        }

        Statistics {
            api_count: api_cnt,
            type_count: ty_cnt,
            generic_param_count: generic_param_cnt,
            edge_cnt,
        }
    }

    pub fn get_node(&mut self, node: DepNode<'tcx>) -> NodeIndex {
        if let Some(node_index) = self.node_indices.get(&node) {
            *node_index
        } else {
            let node_index = self.graph.add_node(node.clone());
            self.node_indices.insert(node, node_index);
            node_index
        }
    }

    pub fn get_index_by_node(&self, node: DepNode<'tcx>) -> Option<NodeIndex> {
        self.node_indices.get(&node).map(|index| *index)
    }

    pub fn add_edge(&mut self, src: NodeIndex, dst: NodeIndex, edge: DepEdge) {
        self.graph.add_edge(src, dst, edge);
    }

    pub fn add_edge_once(&mut self, src: NodeIndex, dst: NodeIndex, edge: DepEdge) {
        if !self.graph.contains_edge(src, dst) {
            self.graph.add_edge(src, dst, edge);
        }
    }

    /// return all types that can be transformed into `ty`
    pub fn provider_tys(&self, ty: Ty<'tcx>) -> Vec<Ty<'tcx>> {
        let index = self
            .get_index_by_node(DepNode::Ty(ty.into()))
            .expect(&format!("{ty:?} should be existed in api graph"));
        let mut tys = Vec::new();

        for node_index in self.graph.neighbors_directed(index, Direction::Incoming) {
            if let DepNode::Ty(ty) = self.graph[node_index] {
                tys.push(ty.ty());
            }
        }
        tys
    }

    /// return all transform kind for `ty` that we intersted in.
    pub fn all_transform_for(&self, ty: Ty<'tcx>) -> Vec<TransformKind> {
        let mut tfs = Vec::new();
        if let Some(index) = self.get_index_by_node(DepNode::Ty(ty.into())) {
            for edge in self.graph.edges_directed(index, Direction::Outgoing) {
                if let DepEdge::Transform(kind) = edge.weight() {
                    tfs.push(*kind);
                }
            }
        }
        tfs
    }

    pub fn dump_to_dot<P: AsRef<Path>>(&self, path: P, tcx: TyCtxt<'tcx>) {
        let get_edge_attr =
            |graph: &Graph<DepNode<'tcx>, DepEdge>,
             edge_ref: petgraph::graph::EdgeReference<DepEdge>| {
                let color = match edge_ref.weight() {
                    DepEdge::Arg(_) | DepEdge::Ret => "black",
                    DepEdge::Fn2Generic => "grey",
                    DepEdge::Transform(_) => "darkorange",
                };
                format!("label=\"{}\", color = {}", edge_ref.weight(), color)
            };
        let get_node_attr = |graph: &Graph<DepNode<'tcx>, DepEdge>,
                             node_ref: (NodeIndex, &DepNode<'tcx>)| {
            format!("label={:?}, ", desc_str(node_ref.1.clone(), tcx))
                + match node_ref.1 {
                    DepNode::Api(_) => "color = blue",
                    DepNode::Ty(_) => "color = red",
                    DepNode::GenericParamDef(..) => "color = green",
                }
                + ", shape=box"
        };

        let dot = dot::Dot::with_attr_getters(
            &self.graph,
            &[dot::Config::NodeNoLabel, dot::Config::EdgeNoLabel],
            &get_edge_attr,
            &get_node_attr,
        );
        let mut file = rap_create_file(path, "can not create dot file");
        write!(&mut file, "{:?}", dot).expect("fail when writing data to dot file");
        // println!("{:?}", dot);
    }
}
