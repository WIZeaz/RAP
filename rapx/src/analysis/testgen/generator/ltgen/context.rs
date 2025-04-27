use super::folder::extract_rids;
use super::lifetime::{RegionGraph, Rid};
use super::{destruct_ret_alias, FnAliasMap, RegionSubgraphMap};
use crate::analysis::testgen::context::{ApiCall, Context, HoldTyCtxt};
use crate::analysis::testgen::context::{Stmt, StmtKind, Var};
use crate::analysis::testgen::generator::ltgen::folder::RidExtractFolder;
use crate::analysis::testgen::generator::ltgen::lifetime::{
    visit_structure_region_with, RegionNode,
};
use crate::analysis::testgen::utils;
use crate::{rap_debug, rap_info, rap_warn};
use rustc_hir::def_id::DefId;
use rustc_middle::ty::{self, GenericArg, Ty, TyCtxt, TyKind, TypeFoldable};
use std::collections::{HashMap, HashSet, VecDeque};
use std::io::Write;

pub struct LtContext<'tcx, 'a, 'b> {
    stmts: Vec<Stmt>,
    available: HashSet<Var>,
    var_ty: HashMap<Var, Ty<'tcx>>,
    var_is_mut: HashMap<Var, ty::Mutability>,
    var_rid: HashMap<Var, Rid>,
    // a weak version to track use chains
    var_depend: HashMap<Var, Vec<Var>>,
    tcx: TyCtxt<'tcx>,
    region_graph: RegionGraph,
    subgraph_map: &'b RegionSubgraphMap,
    alias_map: &'a FnAliasMap,
    covered_api: HashSet<DefId>,
}

impl<'tcx, 'a, 'b> HoldTyCtxt<'tcx> for LtContext<'tcx, 'a, 'b> {
    fn tcx(&self) -> TyCtxt<'tcx> {
        self.tcx
    }
}

impl<'tcx, 'a, 'b> Context<'tcx> for LtContext<'tcx, 'a, 'b> {
    fn stmts(&self) -> &[Stmt] {
        &self.stmts
    }

    fn add_stmt(&mut self, stmt: Stmt) {
        let var = stmt.place();
        // maintain lifetime relationship between ref and var
        match stmt.kind() {
            StmtKind::Call(apicall) => {
                let fn_did = apicall.fn_did();

                self.covered_api.insert(fn_did);

                let real_fn_sig = self.mk_fn_sig(&stmt);
                let mut folder = RidExtractFolder::new(self.tcx());
                real_fn_sig.fold_with(&mut folder);

                // get pattern
                let patterns = self.subgraph_map.get(&fn_did).unwrap();
                rap_debug!("patterns: {:?}", patterns);
                rap_debug!("regions: {:?}", folder.rids());

                self.region_graph.add_edges_with(patterns, folder.rids());

                for arg in apicall.args() {
                    self.depend(var, *arg);
                }
                // automatically inject drop stmts
            }
            StmtKind::Ref(inner_var, _) => {
                self.depend(var, **inner_var);
            }
            StmtKind::Deref(inner_var) => {
                self.depend(var, **inner_var);
                todo!()
            }
            _ => {}
        }
        self.stmts.push(stmt);
    }

    fn lift_mutability(&mut self, var: Var, mutability: ty::Mutability) {
        if matches!(mutability, ty::Mutability::Mut) {
            self.var_is_mut.insert(var, ty::Mutability::Mut);
        }
    }

    fn var_mutability(&self, var: Var) -> ty::Mutability {
        *self.var_is_mut.get(&var).unwrap_or(&ty::Mutability::Not)
    }

    fn available_values(&self) -> &HashSet<Var> {
        &self.available
    }

    fn mk_var(&mut self, ty: Ty<'tcx>, is_input: bool) -> Var {
        let next_var = Var(self.var_ty.len() + 1, is_input);
        let ty = self.region_graph.register_ty(ty, self.tcx());
        let rid = self.region_graph.register_var(next_var);

        rap_debug!("[mk_var] ('?{}) {}: {:?}", rid.index(), next_var, ty);

        self.var_ty.insert(next_var, ty);
        self.var_rid.insert(next_var, rid);
        self.available.insert(next_var);

        // add structural constraint between 'var and 'a where carry by the type of var
        visit_structure_region_with(
            ty,
            Some(self.region_of(next_var)),
            self.tcx(),
            &mut |from, to| {
                self.region_graph.add_edge_by_region(from, to);
            },
        );
        next_var
    }

    fn ref_region(&self, var: Var) -> ty::Region<'tcx> {
        self.region_of(var)
    }

    fn set_var_unavailable_unchecked(&mut self, var: Var) {
        self.available.remove(&var);
    }

    fn type_of(&self, var: Var) -> Ty<'tcx> {
        *self.var_ty.get(&var).expect("no type for var")
    }
}

impl<'tcx, 'a, 'b> LtContext<'tcx, 'a, 'b> {
    pub fn new(
        tcx: TyCtxt<'tcx>,
        subgraph_map: &'b RegionSubgraphMap,
        alias_map: &'a FnAliasMap,
    ) -> Self {
        Self {
            stmts: Vec::new(),
            available: HashSet::new(),
            var_ty: HashMap::new(),
            var_rid: HashMap::new(),
            var_depend: HashMap::new(),
            tcx,
            var_is_mut: HashMap::new(),
            region_graph: RegionGraph::new(),
            subgraph_map,
            alias_map,
            covered_api: HashSet::new(),
        }
    }

    pub fn region_graph(&self) -> &RegionGraph {
        &self.region_graph
    }

    pub fn depend(&mut self, var: Var, depended: Var) {
        self.var_depend.entry(depended).or_default().push(var);
    }

    pub fn detect_potential_vulnerability(&self, stmt: &Stmt) -> Option<HashMap<Var, Vec<Rid>>> {
        let mut ret: HashMap<Var, Vec<Rid>> = HashMap::new();
        let mut check_potential_region_leak = |lhs_ty, lhs_var, rhs_ty| {
            let lhs_result = utils::ty_check_ptr(lhs_ty, self.tcx());
            let rhs_rids = extract_rids(rhs_ty, self.tcx());
            if lhs_result.has_unsafe_ptr() {
                let lhs_rid = self.rid_of(lhs_var);
                let unsafe_region_rids = rhs_rids.iter().filter_map(|rid| {
                    if self.region_graph().prove(lhs_rid, *rid) {
                        None
                    } else {
                        Some(*rid)
                    }
                });
                let entry: &mut _ = ret.entry(lhs_var).or_default();
                // add all unsafe regions into entry
                for unsafe_region in unsafe_region_rids {
                    entry.push(unsafe_region);
                }
            }
        };

        let call = stmt.api_call();
        let fn_sig = self.mk_fn_sig(stmt);
        rap_debug!("make fn_sig: {:?}", fn_sig);

        if let Some(ret_alias) = self.alias_map.get(&call.fn_did()) {
            for alias in ret_alias.aliases() {
                let (lhs_ty, rhs_ty) = dbg!(destruct_ret_alias(fn_sig, alias, self.tcx()));
                let lhs_var = stmt.var_for_call_arg(alias.left_index);
                let rhs_var = stmt.var_for_call_arg(alias.right_index);

                check_potential_region_leak(lhs_ty, lhs_var, rhs_ty);
                check_potential_region_leak(rhs_ty, rhs_var, lhs_ty);
            }
            Some(ret)
        } else {
            None
        }
    }

    pub fn rid_of(&self, var: Var) -> Rid {
        self.var_rid[&var]
    }

    pub fn region_of(&self, var: Var) -> ty::Region<'tcx> {
        ty::Region::new_var(
            self.tcx(),
            ty::RegionVid::from_usize(self.rid_of(var).into()),
        )
    }

    pub fn dbg_var_rid(&self, o: &mut impl Write) {
        for (var, vid) in self.var_rid.iter() {
            writeln!(o, "var: {var:?} rid: {vid:?}");
        }
    }

    fn add_drop_stmt(&mut self, dropped: Var) -> Var {
        let var = self.mk_var(self.tcx().types.unit, false);
        self.add_stmt(Stmt::drop_(var, dropped));
        self.set_var_unavailable_recursive(dropped);
        var
    }

    fn set_var_unavailable_recursive(&mut self, var: Var) {
        let mut q = VecDeque::from([self.rid_of(var).into()]);
        let mut visited = vec![false; self.region_graph.total_node_count()];
        visited[self.rid_of(var).index()] = true;
        while let Some(rid) = q.pop_front() {
            if let RegionNode::Named(var) = self.region_graph.get_node(rid) {
                rap_debug!("set var {} unavailable", var);
                self.set_var_unavailable(var);
            }
            for next_idx in self
                .region_graph
                .inner()
                .neighbors_directed(rid.into(), petgraph::Direction::Incoming)
            {
                if !visited[next_idx.index()] {
                    visited[next_idx.index()] = true;
                    q.push_back(next_idx.into());
                }
            }
        }
    }

    pub fn try_inject_drop(&mut self) -> bool {
        let stmt = self.stmts().last().unwrap();
        match stmt.kind() {
            StmtKind::Call(_) => {
                if let Some(vec) = self.detect_potential_vulnerability(&stmt) {
                    for (var, rids) in vec {
                        rap_warn!("[unsafe] variable {} lack of binding with {:?}", var, rids);
                        for rid in rids {
                            let dropped_var = self.region_graph.find_sources(rid).iter().fold(
                                Vec::new(),
                                |mut v, rid| match self.region_graph.get_node(*rid) {
                                    RegionNode::Named(var) => {
                                        self.add_drop_stmt(var);
                                        v.push(var);
                                        v
                                    }
                                    _ => {
                                        panic!("not a node")
                                    }
                                },
                            );
                            rap_warn!("[unsafe] drop var: {:?}", dropped_var);
                        }
                    }
                }
                true
            }
            _ => false,
        }
    }

    pub fn num_covered_api(&self) -> usize {
        self.covered_api.len()
    }
}
