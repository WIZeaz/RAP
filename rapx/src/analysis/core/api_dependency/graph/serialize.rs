use super::dep_edge::DepEdge;
use super::dep_node::DepNode;
use crate::analysis::core::api_dependency::ApiDependencyGraph;
use crate::analysis::utils::path::{PathResolver, get_path_resolver};
use itertools::Itertools;
use rustc_middle::ty::{self, Ty, TyCtxt, TyKind};
use rustc_middle::ty::{GenericArgsRef, List};
use serde::{Serialize, ser::SerializeMap};
use std::mem::MaybeUninit;
use std::path::Path;

#[derive(Debug, Clone, Serialize)]
#[serde(tag = "type")]
enum NodeInfo {
    Api {
        path: String,
        generic_args: Vec<String>,
    },
    Ty {
        path: String,
    },
}

#[derive(Debug, Clone, Serialize)]
struct EdgeInfo {
    from: usize,
    to: usize,
    kind: DepEdge,
}

impl<'tcx> ApiDependencyGraph<'tcx> {
    pub fn dump(&self, path: impl AsRef<Path>) -> std::io::Result<()> {
        let dump_path = path.as_ref();
        match dump_path.extension() {
            Some(ext) if ext == "json" => {
                self.dump_to_json(dump_path)
                    .expect("failed to dump API graph to JSON");
            }
            Some(ext) if ext == "dot" => {
                self.dump_to_dot(dump_path);
            }
            _ => {
                rap_info!(
                    "Unsupported dump format: {:?}, skip dumping API graph",
                    dump_path.extension()
                );
            }
        }
        rap_info!("Dump API dependency graph to {}", dump_path.display());
        Ok(())
    }

    pub fn dump_to_json(&self, path: impl AsRef<Path>) -> std::io::Result<()> {
        let file = std::fs::File::create(path)?;
        serde_json::to_writer_pretty(file, self)?;
        Ok(())
    }
}

impl<'tcx> DepNode<'tcx> {
    fn to_node_info(&self, resolver: &PathResolver<'tcx>) -> NodeInfo {
        match self {
            DepNode::Api(def_id, args) => NodeInfo::Api {
                path: resolver.path_str_with_args(*def_id, ty::GenericArgs::empty()),
                generic_args: args
                    .iter()
                    .map(|arg| resolver.generic_arg_str(arg))
                    .collect_vec(),
            },
            DepNode::Ty(ty_wrapper) => NodeInfo::Ty {
                path: resolver.ty_str(ty_wrapper.ty()),
            },
        }
    }
}

impl DepEdge {
    fn to_edge_info(&self, from: usize, to: usize) -> EdgeInfo {
        EdgeInfo {
            from,
            to,
            kind: *self,
        }
    }
}

// schema:
// nodes: [{type: "api"/"type", path}]
// edges: [{from,to,type}]
impl<'tcx> Serialize for ApiDependencyGraph<'tcx> {
    fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
    where
        S: serde::Serializer,
    {
        let mut map = serializer.serialize_map(Some(2))?;
        let resolver = get_path_resolver(self.tcx);

        let node_len = self.graph.node_count();
        let mut nodes = Box::<[NodeInfo]>::new_uninit_slice(node_len);
        let mut initialized_count = 0usize;

        for (expected_offset, node_index) in self.graph.node_indices().enumerate() {
            let offset = node_index.index();
            assert!(offset < node_len, "node index out of bounds");

            let node = self
                .graph
                .node_weight(node_index)
                .expect("node index from node_indices must exist");
            nodes[offset].write(node.to_node_info(&resolver));
            initialized_count += 1;
        }

        assert_eq!(
            initialized_count, node_len,
            "all node slots must be initialized"
        );

        // SAFETY: we assert that indices are contiguous and in-bounds, and we initialize
        // each slot exactly once, so every element is fully initialized here.
        let nodes = unsafe { nodes.assume_init() }.into_vec();

        let mut edges = Vec::with_capacity(self.graph.edge_count());
        for edge_index in self.graph.edge_indices() {
            let (from, to) = self
                .graph
                .edge_endpoints(edge_index)
                .expect("edge index from edge_indices must have endpoints");
            let edge = self
                .graph
                .edge_weight(edge_index)
                .expect("edge index from edge_indices must exist");
            edges.push(edge.to_edge_info(from.index(), to.index()));
        }

        map.serialize_entry("nodes", &nodes)?;
        map.serialize_entry("edges", &edges)?;
        map.end()
    }
}
