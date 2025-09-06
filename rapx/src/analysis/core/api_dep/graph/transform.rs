use super::dep_edge::DepEdge;
use super::{ApiDepGraph, DepNode, TyWrapper};
use petgraph::graph::NodeIndex;
use rustc_middle::ty::{self};
use std::fmt::Display;

static ALL_TRANSFORMKIND: [TransformKind; 2] = [
    TransformKind::Ref(ty::Mutability::Not),
    TransformKind::Ref(ty::Mutability::Mut),
    // TransformKind::Deref,
    // TransformKind::Box,
];

#[derive(Clone, Copy, Eq, PartialEq, Debug, Hash)]
pub enum TransformKind {
    Ref(ty::Mutability),
    Unwrap, // unwrap Option<T>, Result<T, E>
}

impl TransformKind {
    pub fn all() -> &'static [TransformKind] {
        &ALL_TRANSFORMKIND
    }
}

impl Display for TransformKind {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            TransformKind::Ref(mutability) => write!(f, "{}T", mutability.ref_prefix_str()),
            TransformKind::Unwrap => write!(f, "Unwrap"),
        }
    }
}

impl<'tcx> ApiDepGraph<'tcx> {
    pub fn update_transform_edges(&mut self) {
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
            let index = self.get_index(DepNode::Ty(current_ty));
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
                let current_index = self.get_or_create_index(DepNode::Ty(current_ty));
                self.add_edge_once(current_index, next_index, DepEdge::transform(*kind));
                ret = Some(current_index);
            }
        }
        ret
    }
}
