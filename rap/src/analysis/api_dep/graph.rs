use petgraph::dot::{Config, Dot};
use petgraph::graph::NodeIndex;
use petgraph::Graph;
use rustc_hir::def_id::DefId;
use rustc_hir::{HirId, Ty};
use rustc_middle::query::IntoQueryParam;
use rustc_middle::ty::TyCtxt;
use std::collections::{HashMap, HashSet};
use std::fmt::Display;
use std::io::Write;
use std::path::Path;

use crate::utils::fs::rap_create_file;

#[derive(Clone, Copy, Eq, PartialEq, Hash, Debug)]
pub enum DepNode {
    Api(DefId),
    Ty(Option<DefId>),
    // Lifetime
}
pub enum DepEdge {
    Ty2Fn,
    Fn2Ty,
}
pub struct ApiDepGraph {
    graph: Graph<DepNode, ()>,
    node_indices: HashMap<DepNode, NodeIndex>,
}

impl DepNode {
    pub fn api(id: impl IntoQueryParam<DefId>) -> DepNode {
        DepNode::Api(id.into_query_param())
    }
    pub fn ty(opt_id: Option<DefId>) -> DepNode {
        DepNode::Ty(opt_id)
    }

    pub fn desc_str<'tcx>(&self, tcx: TyCtxt<'tcx>) -> String {
        match self {
            DepNode::Api(def_id) => tcx.def_path_str(def_id),
            DepNode::Ty(def_id) => def_id.map_or("()".to_owned(), |x| tcx.def_path_str(x)),
        }
    }
}

// impl Display for DepNode {
//     fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
//         f.
//         match self{
//             DepNode::Api(def_id) => std.
//             DepNode::Ty(hir_id) => todo!(),
//         }
//     }
// }

impl ApiDepGraph {
    pub fn new() -> ApiDepGraph {
        ApiDepGraph {
            graph: Graph::new(),
            node_indices: HashMap::new(),
        }
    }

    pub fn get_node(&mut self, node: DepNode) -> NodeIndex {
        if let Some(node_index) = self.node_indices.get(&node) {
            *node_index
        } else {
            let node_index = self.graph.add_node(node);
            self.node_indices.insert(node, node_index);
            node_index
        }
    }

    pub fn add_edge(&mut self, src: NodeIndex, dst: NodeIndex) {
        self.graph.add_edge(src, dst, ());
    }
    pub fn dump_to_dot<'tcx, P: AsRef<Path>>(&self, path: P, tcx: TyCtxt<'tcx>) {
        // let dot = Dot::with_config(&self.graph, &[Config::NodeIndexLabel]);
        let get_edge_attr = |graph, edge_ref| "".to_owned();
        let get_node_attr = |graph, node_ref: (NodeIndex, &DepNode)| {
            format!("label=\"{}\", ", node_ref.1.desc_str(tcx))
                + match node_ref.1 {
                    DepNode::Api(_) => "color = blue",
                    DepNode::Ty(_) => "color = red",
                }
                + ", shape=box"
        };

        let dot = Dot::with_attr_getters(
            &self.graph,
            &[Config::NodeNoLabel, Config::EdgeNoLabel],
            &get_edge_attr,
            &get_node_attr,
        );
        let mut file = rap_create_file(path, "can not create dot file");
        write!(&mut file, "{:?}", dot).expect("fail when writing data to dot file");
        // println!("{:?}", dot);
    }
}
