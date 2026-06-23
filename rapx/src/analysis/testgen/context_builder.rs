mod build_stmt;
mod lifetime;
mod pattern;
mod safety;
mod var_state;

use crate::analysis::core::alias_analysis::FnAliasMap;
use crate::analysis::testgen::context::{Context, DUMMY_UNIT_VAR, ExploitKind, Var};
use crate::analysis::testgen::context_builder::lifetime::RegionNode;
use crate::analysis::testgen::utils;
use bit_set::BitSet;
use itertools::Itertools;
use lifetime::visit_ty_region_with;
use lifetime::{RegionGraph, Rid};
use pattern::PatternProvider;
use rustc_hir::def_id::DefId;
use rustc_infer::infer::TyCtxtInferExt;
use rustc_middle::ty::{self, ParamEnv, Ty, TyCtxt, TypingMode};
use rustc_trait_selection::infer::InferCtxtExt;
use std::collections::HashMap;
pub use var_state::VarState;

pub fn is_ty_moved_on_call<'tcx>(ty: Ty<'tcx>, tcx: TyCtxt<'tcx>) -> bool {
    !utils::is_ty_impl_copy(ty, tcx)
}
pub struct ContextBuilder<'tcx, 'a> {
    tcx: TyCtxt<'tcx>,
    cx: Context<'tcx>,
    var_rid: HashMap<Var, Rid>,
    state: HashMap<Var, VarState>,
    var_steps: HashMap<Var, usize>,
    region_graph: RegionGraph,
    pat_provider: PatternProvider<'tcx>,
    alias_map: &'a FnAliasMap,
    explicit_droped_cnt: usize,
    lack_of_alias: Vec<DefId>,
}

impl<'tcx, 'a> ContextBuilder<'tcx, 'a> {
    pub fn new(tcx: TyCtxt<'tcx>, alias_map: &'a FnAliasMap) -> Self {
        Self {
            tcx,
            cx: Context::new(tcx),
            var_rid: HashMap::new(),
            region_graph: RegionGraph::new(),
            state: HashMap::new(),
            var_steps: HashMap::new(),
            pat_provider: PatternProvider::new(tcx),
            alias_map,
            explicit_droped_cnt: 0,
            lack_of_alias: Vec::new(),
        }
    }

    pub fn cx(&self) -> &Context<'tcx> {
        &self.cx
    }

    pub fn region_graph(&self) -> &RegionGraph {
        &self.region_graph
    }

    pub fn rid_of(&self, var: Var) -> Rid {
        self.var_rid[&var]
    }

    pub fn region_of(&self, var: Var) -> ty::Region<'tcx> {
        ty::Region::new_var(
            self.tcx,
            ty::RegionVid::from_usize(self.rid_of(var).index()),
        )
    }

    pub fn step_of(&self, var: Var) -> usize {
        self.var_steps.get(&var).copied().unwrap_or(1)
    }

    fn set_step_of(&mut self, var: Var, step: usize) {
        self.var_steps.insert(var, step);
    }

    pub fn dropped_count(&self) -> usize {
        self.explicit_droped_cnt
    }

    fn mk_var(&mut self, ty: Ty<'tcx>, is_input: bool) -> Var {
        if ty.is_unit() {
            return DUMMY_UNIT_VAR;
        }

        let ty = self.region_graph.register_ty(ty, self.tcx);
        let next_var = self.cx.mk_var(ty, is_input);
        let rid = self.region_graph.register_var(next_var);

        rap_debug!(
            "[mk_var] register ['?{}] {}: {:?}",
            rid.index(),
            next_var,
            ty
        );

        self.var_rid.insert(next_var, rid);
        self.set_var_state(next_var, VarState::live());

        // add structural constraint between 'var and 'a where carry by the type of var
        visit_ty_region_with(
            ty,
            Some(self.region_of(next_var)),
            self.tcx,
            &mut |from, to| {
                self.region_graph.add_edge_by_region(from, to);
            },
        );
        next_var
    }

    pub fn try_add_exploit_stmt_for(&mut self, var: Var) -> bool {
        let ty = self.cx.type_of(var);

        if ty.is_unit() || !self.var_state(var).is_live() {
            return false;
        }
        let debug_def_id = self
            .tcx
            .get_diagnostic_item(rustc_span::sym::Debug)
            .unwrap();
        let infcx = self.tcx.infer_ctxt().build(TypingMode::PostAnalysis);
        let param_env = ParamEnv::empty();

        if infcx
            .type_implements_trait(debug_def_id, [ty], param_env)
            .must_apply_modulo_regions()
        {
            self.add_exploit_stmt(var, ExploitKind::Debug);
            return true;
        }
        false
    }

    /// try to add exploit stmt for all live vars
    pub fn finally_exploit_vars(&mut self) {
        let debug_def_id = self
            .tcx
            .get_diagnostic_item(rustc_span::sym::Debug)
            .unwrap();
        let infcx = self.tcx.infer_ctxt().build(TypingMode::PostAnalysis);
        let param_env = ParamEnv::empty();
        // let live_vars = self.live_vars().collect_vec();
        let mut vars = Vec::new();

        self.region_graph.topo_visit(|_, rnode| {
            if let RegionNode::Named(var) = rnode {
                vars.push(*var);
            }
        });

        for var in vars {
            if self.var_state(var).is_dead() {
                continue;
            }
            let ty = self.cx.type_of(var);
            if ty != self.tcx.types.unit
                && infcx
                    .type_implements_trait(debug_def_id, [ty], param_env)
                    .must_apply_modulo_regions()
            {
                self.add_exploit_stmt(var, ExploitKind::Debug);
            }
        }
    }
}
