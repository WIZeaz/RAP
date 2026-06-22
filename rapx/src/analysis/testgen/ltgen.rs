mod select;

use super::context_builder::ContextBuilder;
use crate::analysis::core::alias_analysis::FnAliasMap;
use crate::analysis::core::api_dependency::{ApiDependencyGraph, DepNode, graph::TransformKind};
use crate::analysis::testgen::context::{ApiCall, DUMMY_INPUT_VAR};
use crate::analysis::testgen::driver;
use crate::analysis::testgen::ltgen::select::Provider;
use crate::analysis::testgen::utils::{self};
use itertools::Itertools;
use rand::rngs::ThreadRng;
use rand::{self, Rng};
use rustc_hir::def_id::DefId;
use rustc_middle::ty::{self, TyCtxt};
use std::cell::RefCell;
use std::collections::{HashMap, HashSet};
use std::ops::{AddAssign, MulAssign};

pub struct LtGenBuilder<'tcx, 'a, R: Rng> {
    tcx: TyCtxt<'tcx>,
    rng: R,
    max_complexity: usize,
    max_iteration: usize,
    alias_map: &'a FnAliasMap,
    api_graph: ApiDependencyGraph<'tcx>,
}

impl<'tcx, 'a> LtGenBuilder<'tcx, 'a, ThreadRng> {
    pub fn new(
        tcx: TyCtxt<'tcx>,
        alias_map: &'a FnAliasMap,
        api_graph: ApiDependencyGraph<'tcx>,
    ) -> LtGenBuilder<'tcx, 'a, ThreadRng> {
        LtGenBuilder {
            tcx,
            rng: rand::rng(),
            max_complexity: 20,
            max_iteration: 1000,
            alias_map,
            api_graph: api_graph,
        }
    }
}

impl<'tcx, 'a, R: Rng> LtGenBuilder<'tcx, 'a, R> {
    pub fn build(self) -> LtGen<'tcx, 'a, R> {
        LtGen::new(
            self.tcx,
            self.alias_map,
            self.rng,
            self.max_complexity,
            self.max_iteration,
            self.api_graph,
        )
    }

    pub fn max_iteration(mut self, max_iteration: usize) -> Self {
        self.max_iteration = max_iteration;
        self
    }

    pub fn max_complexity(mut self, max_complexity: usize) -> Self {
        self.max_complexity = max_complexity;
        self
    }

    pub fn rng(mut self, rng: R) -> Self {
        self.rng = rng;
        self
    }
}

pub struct Config {
    max_complexity: usize,
    max_iteration: usize,
    num_samples: usize,
    top_k: usize,
    alpha: f64, // drop decay factor
    initial_drop_prob: f64,
}

fn get_initial_drop_prob() -> f64 {
    if utils::is_env_var_exist("TESTGEN_DISABLE_INJECT") {
        0.0
    } else {
        1.0
    }
}

pub struct GlobalState<'tcx> {
    // covered_api: HashSet<DefId>,
    reach_map: HashMap<DepNode<'tcx>, usize>,
    drop_prob: HashMap<DepNode<'tcx>, f64>,
    num_estimated: usize,
    num_total: usize,
}

impl<'tcx> GlobalState<'tcx> {
    pub fn new(api_graph: &ApiDependencyGraph<'tcx>) -> Self {
        let (estimated, total) = api_graph.estimate_coverage();
        Self {
            // covered_api: HashSet::new(),
            reach_map: HashMap::new(),
            drop_prob: HashMap::new(),
            num_estimated: estimated,
            num_total: total,
        }
    }

    pub fn covered_apis(&self) -> impl Iterator<Item = (DefId, ty::GenericArgsRef<'tcx>)> + '_ {
        self.reach_map
            .iter()
            .filter_map(|(node, count)| match node {
                DepNode::Api(did, args) if *count > 0 => Some((*did, *args)),
                _ => None,
            })
    }

    pub fn num_global_covered_api(&self) -> usize {
        self.covered_apis().count()
    }

    pub fn num_estimate_covered_api(&self) -> usize {
        self.num_estimated
    }

    pub fn num_total_api(&self) -> usize {
        self.num_total
    }

    pub fn reach(&mut self, node: DepNode<'tcx>) {
        self.reach_map.entry(node).or_default().add_assign(1);
    }

    pub fn num_reach(&self, node: DepNode<'tcx>) -> usize {
        self.reach_map.get(&node).copied().unwrap_or_default()
    }
}

pub struct LtGen<'tcx, 'a, R: Rng> {
    tcx: TyCtxt<'tcx>,
    rng: RefCell<R>,
    config: Config,
    alias_map: &'a FnAliasMap,
    api_graph: ApiDependencyGraph<'tcx>,
    depth_map: HashMap<DepNode<'tcx>, usize>,
    global: GlobalState<'tcx>,
}

impl<'tcx, 'a, R: Rng> LtGen<'tcx, 'a, R> {
    fn new(
        tcx: TyCtxt<'tcx>,
        alias_map: &'a FnAliasMap,
        rng: R,
        max_complexity: usize,
        max_iteration: usize,
        api_graph: ApiDependencyGraph<'tcx>,
    ) -> Self {
        let config = Config {
            max_complexity,
            max_iteration,
            num_samples: 5,
            top_k: 20,
            alpha: 0.9,
            initial_drop_prob: get_initial_drop_prob(),
        };
        let global = GlobalState::new(&api_graph);
        let depth_map = api_graph.depth_map();

        LtGen {
            tcx,
            rng: RefCell::new(rng),
            config,
            alias_map,
            api_graph,
            depth_map,
            global,
        }
    }

    pub fn state(&self) -> &GlobalState<'tcx> {
        &self.global
    }

    fn cx_complexity(&self, builder: &ContextBuilder<'tcx, 'a>) -> usize {
        builder.cx().num_apicall()
    }

    fn depth_of(&self, node: DepNode<'tcx>) -> Option<usize> {
        self.depth_map.get(&node).copied()
    }

    pub fn log_depth_map(&self) {
        rap_debug!("depth map = {:?}", self.depth_map);
    }

    pub fn generate(&mut self) -> ContextBuilder<'tcx, 'a> {
        let mut builder = ContextBuilder::new(self.tcx, &self.alias_map);
        let mut count = 0;
        let mut num_drop_inject = 0;
        let mut current_reach = HashSet::new();
        loop {
            count += 1;
            rap_info!("<<<<< Iter {} >>>>>", count);

            if count > self.config.max_iteration {
                rap_info!("max iteration reached, generation terminate");
                break;
            }

            if self.cx_complexity(&builder) > self.config.max_complexity {
                rap_info!("complexity limit reached, generation terminate");
                break;
            }

            // 1. generate next call action
            let Some(action) = self.next(&mut builder) else {
                rap_info!("no eligable action, generation terminate");
                break;
            };

            builder.comment_current_state();

            rap_debug!(
                "[next] select API call: {}({})",
                self.tcx
                    .def_path_str_with_args(action.fn_did, self.tcx.mk_args(action.generic_args)),
                action
                    .providers
                    .iter()
                    .map(|provider| format!("{}", provider))
                    .join(", ")
            );

            let mut call = ApiCall {
                fn_did: action.fn_did,
                generic_args: action.generic_args,
                args: Vec::new(),
            };
            // 2. build stmts for this call action
            // first build transform stmts for vars
            for provider in action.providers.iter() {
                let mut var = provider.var;
                rap_trace!("var = {}, transforms = {:?}", var, provider.transforms);
                if var == DUMMY_INPUT_VAR {
                    rap_trace!("skip DUMMY INPUT");
                    call.args.push(var);
                    continue;
                }
                for transform in provider.transforms.iter() {
                    match transform {
                        TransformKind::Ref(mutability) => {
                            var = builder.get_or_borrow(var, *mutability)
                        }
                        _ => {
                            unimplemented!();
                        }
                    }
                }
                call.args.push(var);
            }
            let place = builder.add_call_stmt(call);

            // 3. update global state
            self.global.reach(action.node());
            current_reach.insert(action.node());

            // 4. test drop injection
            if !driver::disable_alias() {
                let drop_prob = self
                    .global
                    .drop_prob
                    .entry(action.node())
                    .or_insert(self.config.initial_drop_prob);

                rap_info!("test drop prob: {:.2}", drop_prob);
                if !self.rng.borrow_mut().random_bool(*drop_prob) {
                    rap_info!("skip drop injection");
                } else if builder.try_inject_drop() {
                    num_drop_inject += 1;
                    drop_prob.mul_assign(self.config.alpha);
                    rap_info!(
                        "successfully inject drop, drop_prob update to {}",
                        drop_prob
                    );
                }
            }

            // 5. try add exploit stmt
            if builder.try_add_exploit_stmt_for(place) {
                rap_info!("add exploit stmt for {place}");
            }

            // 5. log statistics
            let current = current_reach.len();
            let global = self.global.num_global_covered_api();
            let total = self.global.num_total_api();
            let estimate = self.global.num_estimated;
            rap_info!(
                "num_stmt={}, complexity={}, num_drop_inject={}, covered_api(current/global/estimate/total)={}/{}/{}/{}",
                builder.cx().num_stmt(),
                self.cx_complexity(&builder),
                num_drop_inject,
                current,
                global,
                estimate,
                total,
            );

            rap_info!(
                "coverage={:.3}/{:.3}/{:.3} (current/global/estimated_max)",
                current as f32 / total as f32,
                global as f32 / total as f32,
                estimate as f32 / total as f32
            );
        }
        builder.comment_current_state();
        builder.finally_exploit_vars();
        builder.comment_current_state();
        builder
    }

    pub fn uncovered_apis(&self) -> Vec<(DefId, ty::GenericArgsRef<'tcx>)> {
        let mut res = vec![];
        for idx in 0..self.api_graph.num_api() {
            let api_node = self.api_graph.api_node_at(idx);
            if self
                .global
                .reach_map
                .get(&api_node)
                .copied()
                .unwrap_or_default()
                == 0
            {
                res.push(api_node.expect_api());
            }
        }
        res
    }

    pub fn statistic_str(&self) -> String {
        let mut s = String::new();
        s.push_str(&format!("# APIs = {}\n", self.api_graph.num_api()));
        s.push_str(&format!(
            "# covered APIs = {}\n",
            self.global.covered_apis().count()
        ));
        s.push_str("covered APIs:\n");
        s.push_str(
            &self
                .global
                .covered_apis()
                .map(|did| format!("{:?}", did))
                .join(", "),
        );
        s.push_str("\nuncovered APIs:\n");
        s.push_str(
            &self
                .uncovered_apis()
                .iter()
                .map(|(did, args)| self.tcx.def_path_str_with_args(did, args))
                .join(", "),
        );

        s
    }
}
