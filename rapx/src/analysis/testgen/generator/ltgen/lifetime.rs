use super::folder::*;
use crate::analysis::testgen::context::Var;
use crate::analysis::testgen::utils;
use crate::rap_debug;
use petgraph::dot::{Config, Dot};
use petgraph::graph::NodeIndex;
use rustc_hir::def_id::DefId;
use rustc_infer::infer::region_constraints::Constraint;
use rustc_infer::infer::{self, InferCtxt, TyCtxtInferExt};
use rustc_infer::traits::ObligationCause;
use rustc_middle::ty::{self, ParamEnv, Ty, TyCtxt, TypeFoldable};
use std::collections::{HashMap, VecDeque};
use std::fmt::Display;
use std::io::Write;

#[derive(Debug)]
pub enum PatternNode {
    Named(usize),
    Temp(usize),
}

#[derive(Debug)]
pub struct EdgePattern(PatternNode, PatternNode);

#[derive(Debug, Default)]
pub struct EdgePatterns {
    named_region_num: usize,
    temp_num: usize,
    patterns: Vec<EdgePattern>,
}

impl EdgePatterns {
    pub fn named_region_num(&self) -> usize {
        self.named_region_num
    }

    pub fn temp_num(&self) -> usize {
        self.temp_num
    }

    pub fn patterns(&self) -> &[EdgePattern] {
        &self.patterns
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum RegionNode {
    Static,
    Named(Var),
    Anon,
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
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Rid(NodeIndex);

impl Rid {
    pub fn index(&self) -> usize {
        self.0.index()
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
    pub fn inner(&self) -> &petgraph::Graph<RegionNode, ()> {
        &self.inner
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
        let mut visited = vec![false; self.inner.node_count()];
        self.dfs_find_path(from.into(), to.into(), &mut visited)
    }

    pub fn get_node(&self, rid: Rid) -> RegionNode {
        *self.inner.node_weight(rid.into()).unwrap()
    }

    pub fn add_edges_with<'tcx>(&mut self, patterns: &EdgePatterns, subst: &[Rid]) {
        assert!(subst.len() == patterns.named_region_num());

        let mut temp = Vec::new();

        // initiate named and temp node we will use
        for _ in 0..patterns.temp_num() {
            temp.push(self.next_anon_node_index());
        }

        for pattern in patterns.patterns() {
            let get_index = |node: &PatternNode| match node {
                PatternNode::Named(i) => subst[*i],
                PatternNode::Temp(i) => temp[*i],
            };
            let from = get_index(&pattern.0);
            let to = get_index(&pattern.1);
            self.add_edge(from, to);
        }
    }

    fn next_anon_node_index(&mut self) -> Rid {
        self.inner.add_node(RegionNode::Anon).into()
    }

    pub fn register_var<'tcx>(&mut self, var: Var) -> Rid {
        self.inner.add_node(RegionNode::Named(var)).into()
    }

    pub fn register_ty<'tcx>(&mut self, ty: Ty<'tcx>, tcx: TyCtxt<'tcx>) -> Ty<'tcx> {
        let mut folder = FreeVarFolder::new(tcx, self);
        ty.fold_with(&mut folder)
    }

    pub fn add_edge(&mut self, from: Rid, to: Rid) {
        self.inner.update_edge(from.into(), to.into(), ());
    }

    pub fn dump(&self, os: &mut impl Write) -> std::result::Result<(), Box<dyn std::error::Error>> {
        let dot = petgraph::dot::Dot::new(&self.inner);

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

    pub fn find_sources(&self, rid: Rid) -> Vec<Rid> {
        let mut visited = vec![false; self.total_node_count()];
        let mut sources = Vec::new();
        let mut q = VecDeque::new();
        q.push_back(rid.into());
        visited[rid.index()] = true;
        while let Some(node) = q.pop_front() {
            let mut outgoing_cnt = 0;
            for neighbor in self.inner.neighbors(node) {
                outgoing_cnt += 1;
                if !visited[neighbor.index()] {
                    visited[neighbor.index()] = true;
                    q.push_back(neighbor);
                }
            }
            if outgoing_cnt == 0 {
                sources.push(node.into());
            }
        }
        sources
    }
}

fn region_vid_str(vid: ty::RegionVid) -> String {
    format!("{:?}", vid)
}

fn region_str(region: ty::Region<'_>) -> String {
    region.get_name_or_anon().to_string()
}

pub fn constraint_str<'tcx>(constraint: Constraint<'tcx>) -> String {
    let (a, b) = match constraint {
        Constraint::VarSubVar(a, b) => (region_vid_str(a), region_vid_str(b)),
        Constraint::RegSubVar(a, b) => (region_str(a), region_vid_str(b)),
        Constraint::VarSubReg(a, b) => (region_vid_str(a), region_str(b)),
        Constraint::RegSubReg(a, b) => (region_str(a), region_str(b)),
    };
    format!("{} <= {}", a, b)
}

pub fn visit_structure_region_with<'tcx, F: FnMut(ty::Region<'tcx>, ty::Region<'tcx>)>(
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
            visit_structure_region_with(*inner_ty, Some(*region), tcx, f);
        }

        ty::TyKind::Array(inner_ty, _) | ty::TyKind::Slice(inner_ty) => {
            visit_structure_region_with(*inner_ty, prev, tcx, f);
        }

        // Tuple
        ty::TyKind::Tuple(tys) => {
            for ty in tys.iter() {
                visit_structure_region_with(ty, prev, tcx, f);
            }
        }

        // ADT
        ty::TyKind::Adt(_, substs) => {
            for arg in substs.iter() {
                match arg.unpack() {
                    ty::GenericArgKind::Lifetime(region) => {
                        if let Some(prev_region) = prev {
                            f(prev_region, region);
                        }
                    }
                    _ => {}
                }
            }
        }
        _ => {}
    }
}

pub fn extract_constraints<'tcx>(fn_did: DefId, tcx: TyCtxt<'tcx>) -> EdgePatterns {
    let infcx = tcx.infer_ctxt().build();
    let mut folder = InfcxVarFolder::new(&infcx, tcx);

    let fn_sig = utils::fn_sig_without_binders(fn_did, tcx);
    let fn_with_free_vars = fn_sig.fold_with(&mut folder);

    let param_env = tcx.param_env(fn_did);

    let res = infcx
        .at(&ObligationCause::dummy(), param_env)
        .sub(infer::DefineOpaqueTypes::Yes, fn_sig, fn_with_free_vars)
        .unwrap();
    res.obligations.into_iter().for_each(|obligation| {
        rap_debug!("obligation: {obligation:?}");
    });

    let dummy = ObligationCause::dummy();
    let at = infcx.at(&dummy, param_env);
    let mut f = |prev_region, region| {
        let _ = at
            .sub(infer::DefineOpaqueTypes::Yes, region, prev_region)
            .unwrap();
    };

    for input in fn_sig.inputs().iter() {
        visit_structure_region_with(*input, None, tcx, &mut f);
    }
    visit_structure_region_with(fn_sig.output(), None, tcx, &mut f);

    let region_constraint_data = infcx.take_and_reset_region_constraints();
    let mut map = HashMap::new();
    let mut temp_region_no = |region: ty::Region<'tcx>| -> usize {
        if region.is_var() {
            panic!("region is var");
        }
        let len = map.len();
        *map.entry(*region).or_insert(len)
    };
    let mut subgraph = EdgePatterns::default();

    for (constraint, _) in region_constraint_data.constraints {
        let edge = match constraint {
            Constraint::VarSubVar(a, b) => EdgePattern(
                PatternNode::Named(a.as_usize()),
                PatternNode::Named(b.as_usize()),
            ),
            Constraint::RegSubVar(a, b) => EdgePattern(
                PatternNode::Temp(temp_region_no(a)),
                PatternNode::Named(b.as_usize()),
            ),
            Constraint::VarSubReg(a, b) => EdgePattern(
                PatternNode::Named(a.as_usize()),
                PatternNode::Temp(temp_region_no(b)),
            ),
            Constraint::RegSubReg(a, b) => EdgePattern(
                PatternNode::Temp(temp_region_no(a)),
                PatternNode::Temp(temp_region_no(b)),
            ),
        };
        subgraph.patterns.push(edge);
    }

    // extract constraints from where clauses of Fn
    let predicates = tcx.predicates_of(fn_did);
    predicates.predicates.iter().for_each(|(pred, _)| {
        if let Some(outlive_pred) = pred.as_region_outlives_clause() {
            let outlive_pred = outlive_pred.skip_binder();
            // lhs : rhs
            let (lhs, rhs) = (outlive_pred.0, outlive_pred.1);

            // build edge from rhs to lhs
            subgraph.patterns.push(EdgePattern(
                PatternNode::Temp(temp_region_no(rhs)),
                PatternNode::Temp(temp_region_no(lhs)),
            ));
        }
    });

    subgraph.named_region_num = folder.cnt();
    subgraph.temp_num = map.len();
    subgraph
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
