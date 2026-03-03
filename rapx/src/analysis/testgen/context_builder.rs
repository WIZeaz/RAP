mod build_stmt;
mod folder;
mod lifetime;
mod pattern;
mod safety;
mod var_state;

use crate::analysis::core::alias_analysis::{FnAliasMap, FnAliasPairs};
use crate::analysis::testgen::context::{Context, DUMMY_UNIT_VAR, ExploitKind, Var};
use crate::analysis::testgen::utils;
use crate::rap_debug;
use bit_set::BitSet;
use lifetime::visit_ty_region_with;
use lifetime::{RegionGraph, Rid};
use pattern::PatternProvider;
use rustc_hir::def_id::DefId;
use rustc_infer::infer::TyCtxtInferExt;
use rustc_middle::ty::{self, ParamEnv, Ty, TyCtxt, TypingMode};
use rustc_trait_selection::infer::InferCtxtExt;
use std::collections::{HashMap, HashSet};

pub fn is_ty_move_on_call<'tcx>(ty: Ty<'tcx>, tcx: TyCtxt<'tcx>) -> bool {
    !utils::is_ty_impl_copy(ty, tcx) || ty.is_ref()
}
pub struct ContextBuilder<'tcx, 'a> {
    tcx: TyCtxt<'tcx>,
    cx: Context<'tcx>,
    var_rid: HashMap<Var, Rid>,
    var_borrow: HashMap<Var, BitSet>,
    var_steps: HashMap<Var, usize>,
    live_state: BitSet,
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
            var_borrow: HashMap::new(),
            var_steps: HashMap::new(),
            live_state: BitSet::new(),
            pat_provider: PatternProvider::new(tcx),
            alias_map,
            explicit_droped_cnt: 0,
            lack_of_alias: Vec::new(),
        }
    }

    pub fn cx(&self) -> &Context<'tcx> {
        &self.cx
    }

    pub fn cx_mut(&mut self) -> &mut Context<'tcx> {
        &mut self.cx
    }

    pub fn into_cx(self) -> Context<'tcx> {
        self.cx
    }

    pub fn live_state(&self) -> &BitSet {
        &self.live_state
    }

    pub fn region_graph(&self) -> &RegionGraph {
        &self.region_graph
    }

    pub fn rid_of(&self, var: Var) -> Rid {
        self.var_rid[&var]
    }

    pub fn region_of(&self, var: Var) -> ty::Region<'tcx> {
        ty::Region::new_var(self.tcx, ty::RegionVid::from_usize(self.rid_of(var).into()))
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
        self.live_state.insert(next_var.index());
        self.var_borrow.insert(next_var, BitSet::new());

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
        if !self.var_state(var).is_live() {
            return false;
        }
        let debug_def_id = self
            .tcx
            .get_diagnostic_item(rustc_span::sym::Debug)
            .unwrap();
        let infcx = self.tcx.infer_ctxt().build(TypingMode::PostAnalysis);
        let param_env = ParamEnv::empty();
        let ty = self.cx.type_of(var);
        if ty.is_unit() {
            return false;
        }
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
    pub fn try_add_exploit_stmts(&mut self) {
        let vars: Vec<Var> = self.available_vars().collect();
        let debug_def_id = self
            .tcx
            .get_diagnostic_item(rustc_span::sym::Debug)
            .unwrap();
        let infcx = self.tcx.infer_ctxt().build(TypingMode::PostAnalysis);
        let param_env = ParamEnv::empty();

        for var in vars {
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
