use super::pattern::EdgePatterns;
use super::pattern::PatternNode;
use crate::analysis::testgen::context::Var;
use bit_set::BitSet;
use petgraph::dot::{Config, Dot};
use petgraph::graph::NodeIndex;
use rustc_middle::ty::{self, Ty, TyCtxt, TypeFoldable};
use std::collections::VecDeque;
use std::fmt::Display;
use std::io::Write;

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum RegionNode {
    Static,
    Named(Var),
    Anon,
}

impl RegionNode {
    pub fn as_var(&self) -> Option<Var> {
        match self {
            RegionNode::Named(var) => Some(*var),
            _ => None,
        }
    }
}

impl Display for RegionNode {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            RegionNode::Static => write!(f, "static"),
            RegionNode::Named(var) => write!(f, "'{}", var),
            RegionNode::Anon => write!(f, "_"),
        }
    }
}

pub struct RegionGraph {
    inner: petgraph::Graph<RegionNode, ()>,
    static_rid: Rid,
}

// Region Graph Id
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct Rid(NodeIndex);

impl Rid {
    pub fn index(&self) -> usize {
        self.0.index()
    }
}

impl Display for Rid {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "'{}", self.index())
    }
}

impl From<NodeIndex> for Rid {
    fn from(index: NodeIndex) -> Self {
        Rid(index)
    }
}

impl Into<NodeIndex> for Rid {
    fn into(self) -> NodeIndex {
        self.0
    }
}

impl Into<usize> for Rid {
    fn into(self) -> usize {
        self.index()
    }
}

impl From<usize> for Rid {
    fn from(index: usize) -> Self {
        Rid(NodeIndex::new(index))
    }
}

impl From<ty::RegionVid> for Rid {
    fn from(vid: ty::RegionVid) -> Self {
        Rid(NodeIndex::new(vid.index()))
    }
}

impl Into<ty::RegionVid> for Rid {
    fn into(self) -> ty::RegionVid {
        ty::RegionVid::from_usize(self.index())
    }
}

pub fn region_to_rid(region: ty::Region<'_>) -> Rid {
    region.as_var().index().into()
}

impl RegionGraph {
    pub fn is_static(&self, rid: Rid) -> bool {
        self.static_rid == rid
    }

    pub fn inner(&self) -> &petgraph::Graph<RegionNode, ()> {
        &self.inner
    }

    pub fn add_node(&mut self, node: RegionNode) -> Rid {
        let index = self.inner.add_node(node);
        Rid(index)
    }

    pub fn new() -> RegionGraph {
        let mut graph = petgraph::Graph::new();
        let static_index = Rid(graph.add_node(RegionNode::Static));

        RegionGraph {
            inner: graph,
            static_rid: static_index,
        }
    }

    pub fn add_edge_by_region(&mut self, from: ty::Region<'_>, to: ty::Region<'_>) {
        let from = region_to_rid(from);
        let to = region_to_rid(to);
        self.add_edge(from, to);
    }

    fn static_rid(&self) -> Rid {
        self.static_rid
    }

    fn dfs_find_path(&self, current: NodeIndex, target: NodeIndex, visited: &mut [bool]) -> bool {
        visited[current.index()] = true;
        if current == target {
            return true;
        }
        for neighbor in self.inner.neighbors(current) {
            if !visited[neighbor.index()] {
                if self.dfs_find_path(neighbor, target, visited) {
                    return true;
                }
            }
        }
        false
    }

    /// prove there is a path from `from` to `to`
    /// from: the index of start named node
    /// to: the index of end named node
    pub fn prove(&self, from: Rid, to: Rid) -> bool {
        rap_debug!("try to prove {} -> {}", from, to);
        let mut visited = vec![false; self.inner.node_count()];
        self.dfs_find_path(from.into(), to.into(), &mut visited)
    }

    pub fn get_node(&self, rid: Rid) -> RegionNode {
        *self.inner.node_weight(rid.into()).unwrap()
    }

    pub fn add_edges_by_patterns<'tcx>(&mut self, patterns: &EdgePatterns, subst: &[Rid]) {
        assert!(subst.len() == patterns.named_region_num());

        let mut temp = Vec::new();

        // initiate named and temp node we will use
        for _ in 0..patterns.temp_num() {
            temp.push(self.next_anon_node_index());
        }

        for pattern in patterns.patterns() {
            let get_index = |node: &PatternNode| match node {
                PatternNode::Static => self.static_rid(),
                PatternNode::Named(i) => subst[*i],
                PatternNode::Temp(i) => temp[*i],
            };
            let from = get_index(&pattern.from());
            let to = get_index(&pattern.to());
            self.add_edge(from, to);
        }
    }

    fn next_anon_node_index(&mut self) -> Rid {
        self.add_node(RegionNode::Anon)
    }

    pub fn register_var<'tcx>(&mut self, var: Var) -> Rid {
        self.add_node(RegionNode::Named(var))
    }

    pub fn register_ty<'tcx>(&mut self, ty: Ty<'tcx>, tcx: TyCtxt<'tcx>) -> Ty<'tcx> {
        let mut folder = FreeVarFolder::new(tcx, self);
        ty.fold_with(&mut folder)
    }

    pub fn add_edge(&mut self, from: Rid, to: Rid) {
        rap_trace!("[region_graph] add edge: {} -> {}", from, to);
        self.inner.update_edge(from.into(), to.into(), ());
    }

    pub fn dump(&self, os: &mut impl Write) -> std::result::Result<(), Box<dyn std::error::Error>> {
        let _dot = petgraph::dot::Dot::new(&self.inner);

        let get_node_attr = |_, node_ref: (NodeIndex, &RegionNode)| {
            format!(
                "label=\"[{}] {}\", shape=box",
                node_ref.0.index(),
                node_ref.1
            )
        };

        let dot = Dot::with_attr_getters(
            &self.inner,
            &[Config::NodeNoLabel, Config::EdgeNoLabel],
            &|_, _| "".into(),
            &get_node_attr,
        );

        write!(os, "{:?}", dot)?;
        Ok(())
    }

    pub fn total_node_count(&self) -> usize {
        self.inner.node_count()
    }

    /// Iterates through all sink nodes reachable from the given region node.
    ///
    /// A sink node is defined as a region node with no outgoing edges.
    /// This method performs a breadth-first search (BFS) starting from the given `rid`,
    /// visiting all reachable nodes and invoking the closure `f` for each sink node encountered.
    ///
    /// # Arguments
    /// * `rid` - The starting region ID from which to search
    /// * `f` - A closure that will be called for each sink node found during the traversal
    ///
    /// # Example
    /// ```ignore
    /// let mut sinks = Vec::new();
    /// graph.for_each_sink(some_rid, &mut |sink_rid| {
    ///     sinks.push(sink_rid);
    /// });
    /// ```
    pub fn for_each_sink_from(&self, rid: Rid, f: &mut impl FnMut(Rid)) {
        let mut visited = BitSet::with_capacity(self.total_node_count());
        let mut q = VecDeque::new();
        q.push_back(rid.into());
        visited.insert(rid.index());
        while let Some(node) = q.pop_front() {
            let mut outgoing_cnt = 0;
            for neighbor in self.inner.neighbors(node) {
                outgoing_cnt += 1;
                if visited.insert(neighbor.index()) {
                    q.push_back(neighbor);
                }
            }
            if outgoing_cnt == 0 {
                f(node.into());
            }
        }
    }

    pub fn for_each_var_from(&self, src_rid: Rid, f: &mut impl FnMut(Var)) {
        let mut visited = BitSet::with_capacity(self.total_node_count());
        let mut q = VecDeque::new();
        let _src_var = self.get_node(src_rid).as_var().unwrap();
        q.push_back(src_rid);
        visited.insert(src_rid.index());
        while let Some(rid) = q.pop_front() {
            if let Some(var) = self.get_node(rid).as_var() {
                if src_rid != rid {
                    f(var);
                }
            }
            for next_idx in self.inner.neighbors(rid.into()) {
                if visited.insert(next_idx.index()) {
                    q.push_back(next_idx.into());
                }
            }
        }
    }
}

pub fn visit_ty_region_with<'tcx, F: FnMut(ty::Region<'tcx>, ty::Region<'tcx>)>(
    ty: ty::Ty<'tcx>,
    prev: Option<ty::Region<'tcx>>,
    tcx: TyCtxt<'tcx>,
    f: &mut F,
) {
    match ty.kind() {
        ty::TyKind::Ref(region, inner_ty, _) => {
            if let Some(prev_region) = prev {
                f(prev_region, *region);
            }
            visit_ty_region_with(*inner_ty, Some(*region), tcx, f);
        }

        ty::TyKind::Array(inner_ty, _) | ty::TyKind::Slice(inner_ty) => {
            visit_ty_region_with(*inner_ty, prev, tcx, f);
        }

        // Tuple
        ty::TyKind::Tuple(tys) => {
            for ty in tys.iter() {
                visit_ty_region_with(ty, prev, tcx, f);
            }
        }

        // ADT
        ty::TyKind::Adt(_, substs) => {
            for arg in substs.iter() {
                match arg.kind() {
                    ty::GenericArgKind::Lifetime(region) => {
                        if let Some(prev_region) = prev {
                            f(prev_region, region);
                        }
                    }
                    ty::GenericArgKind::Type(inner_ty) => {
                        visit_ty_region_with(inner_ty, prev, tcx, f);
                    }
                    _ => {}
                }
            }
        }
        _ => {}
    }
}

pub struct FreeVarFolder<'tcx, 'a> {
    tcx: TyCtxt<'tcx>,
    graph: &'a mut RegionGraph,
}

impl<'tcx, 'a> FreeVarFolder<'tcx, 'a> {
    pub fn new(tcx: TyCtxt<'tcx>, graph: &'a mut RegionGraph) -> FreeVarFolder<'tcx, 'a> {
        FreeVarFolder { tcx, graph }
    }
}

impl<'tcx, 'a> ty::TypeFolder<TyCtxt<'tcx>> for FreeVarFolder<'tcx, 'a> {
    fn cx(&self) -> TyCtxt<'tcx> {
        self.tcx
    }
    fn fold_region(&mut self, region: ty::Region<'tcx>) -> ty::Region<'tcx> {
        match region.kind() {
            ty::ReVar(_) => region,
            ty::ReStatic => ty::Region::new_var(self.cx(), self.graph.static_rid().into()),
            _ => ty::Region::new_var(self.cx(), self.graph.next_anon_node_index().into()),
        }
    }
}
