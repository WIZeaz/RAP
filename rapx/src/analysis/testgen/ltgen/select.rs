use crate::analysis::core::api_dependency::DepNode;
use crate::analysis::core::api_dependency::graph::{TransformKind, TyWrapper};
use crate::analysis::testgen::context::{ApiCall, Var};
use crate::analysis::testgen::context_builder::{ContextBuilder, is_ty_move_on_call};
use crate::analysis::testgen::ltgen::LtGen;
use crate::analysis::testgen::utils;
use itertools::Itertools;
use petgraph::graph::NodeIndex;
use petgraph::visit::EdgeRef;
use rand::distr::weighted::WeightedIndex;
use rand::{self, Rng};
use rustc_hir::def_id::DefId;
use rustc_middle::ty::{self, Ty, TyCtxt};
use std::collections::{HashMap, HashSet};

#[derive(Clone, Debug)]
pub struct Action<'tcx> {
    call: ApiCall<'tcx>,
    node: DepNode<'tcx>,
    transforms: Vec<Vec<TransformKind>>,
}

impl<'tcx> Action<'tcx> {
    pub fn call(&self) -> &ApiCall<'tcx> {
        &self.call
    }
    pub fn transforms(&self) -> &[Vec<TransformKind>] {
        &self.transforms
    }
    pub fn transforms_at(&self, no: usize) -> &[TransformKind] {
        &self.transforms[no]
    }
    pub fn into_call(self) -> ApiCall<'tcx> {
        self.call
    }
    pub fn node(&self) -> DepNode<'tcx> {
        self.node
    }
    pub fn pretty_str(&self, tcx: TyCtxt<'tcx>) -> String {
        format!(
            "{}({})",
            tcx.def_path_str_with_args(self.call.fn_did, self.call.generic_args),
            self.call
                .args
                .iter()
                .map(|var| format!("{}", var))
                .join(", ")
        )
    }
}

fn top_k_idx_by_weight(actions: &[Action], weights: &[f32], top_k: usize) -> Vec<usize> {
    let mut res = (0..actions.len()).collect_vec();
    res.sort_by(|lhs, rhs| weights[*lhs].partial_cmp(&weights[*rhs]).unwrap().reverse());
    res[..top_k.min(res.len())].to_vec()
}

impl<'tcx, 'a, R: Rng> LtGen<'tcx, 'a, R> {
    fn sample_eligable_calls(
        &self,
        list_of_providers: &[Vec<Var>],
        is_ty_move: &[bool],
    ) -> Option<Vec<Var>> {
        let mut moved_vars = Vec::with_capacity(16);
        let mut args = Vec::with_capacity(16);

        let mut select_provider = |providers: &[Var], is_move| -> bool {
            const MAX_FAIL_COUNT: usize = 10;

            if providers.is_empty() {
                rap_trace!("no possible providers");
                return false;
            }

            for _ in 0..MAX_FAIL_COUNT {
                rap_trace!("select provider: {providers:?}");
                let idx = self.rng.borrow_mut().random_range(0..providers.len());
                let provider = &providers[idx];

                // the provider is moved by another arg, try again
                if !provider.is_from_input() && is_move && moved_vars.contains(provider) {
                    continue;
                }

                args.push(*provider);
                if !provider.is_from_input() && is_move {
                    moved_vars.push(*provider);
                }
                return true;
            }
            false
        };

        for (providers, is_move) in list_of_providers.iter().zip(is_ty_move) {
            if !select_provider(&providers, *is_move) {
                return None;
            }
        }

        Some(args)
    }

    fn search_possible_tys_and_transforms(
        &self,
        current: NodeIndex,
        transform: &mut [TransformKind],
        visited_ty: &mut HashSet<TyWrapper<'tcx>>,
        last_steps: usize,
        f: &mut impl FnMut(Ty<'tcx>, &[TransformKind], usize),
    ) {
        let Some(ty) = self.api_graph.get_node_from_index(current).as_ty() else {
            unreachable!("transform edge should only exist between two type nodes");
        };

        // if ty is already visited, return immediately
        if !visited_ty.insert(ty) {
            return;
        }

        // for a new discovered type, invoke callback
        f(ty.ty(), transform, last_steps);

        if last_steps == 0 {
            return;
        }

        for edge_ref in self
            .api_graph
            .inner_graph()
            .edges_directed(current, petgraph::Incoming)
        {
            let edge = edge_ref.weight();
            if let Some(kind) = edge.as_transform_kind() {
                transform[last_steps - 1] = kind;
                self.search_possible_tys_and_transforms(
                    edge_ref.source(),
                    transform,
                    visited_ty,
                    last_steps - 1,
                    f,
                );
            }
        }
    }

    fn providers_and_transforms_for(
        &self,
        ty: Ty<'tcx>,
        builder: &ContextBuilder<'tcx, '_>,
    ) -> HashMap<Var, Vec<TransformKind>> {
        let num_steps = 3;
        let mut transform_buffer = vec![TransformKind::Unwrap; num_steps];
        let mut visited_ty = HashSet::new();
        let mut res = HashMap::new();
        let Some(index) = self.api_graph.get_index_by_ty(ty) else {
            return res;
        };
        self.search_possible_tys_and_transforms(
            index,
            &mut transform_buffer,
            &mut visited_ty,
            num_steps,
            &mut |ty, transforms, steps| {
                let vars = builder.providers_for(ty);
                let tt = transforms[steps..].to_vec();
                res.extend(vars.into_iter().map(|var| (var, tt.clone())));
            },
        );
        res
    }

    fn sample_k_eligable_actions(
        &self,
        node: DepNode<'tcx>,
        fn_did: DefId,
        generic_args: ty::GenericArgsRef<'tcx>,
        builder: &ContextBuilder<'tcx, 'a>,
    ) -> Vec<Action<'tcx>> {
        let tcx = self.tcx;
        let num_samples = self.config.num_samples;

        let fn_sig = utils::fn_sig_with_generic_args(fn_did, generic_args, tcx);

        rap_trace!(
            "sample eligible api: {}",
            tcx.def_path_str_with_args(fn_did, generic_args)
        );

        let mut res = Vec::with_capacity(num_samples);
        let mut list_of_providers = Vec::with_capacity(16);
        let mut list_of_transform_map = Vec::with_capacity(16);
        let mut is_ty_move = Vec::with_capacity(16);
        for &input_ty in fn_sig.inputs() {
            rap_trace!("input_ty = {input_ty}");
            let transform_map = self.providers_and_transforms_for(input_ty, builder);
            let providers = transform_map.keys().copied().collect_vec();
            list_of_providers.push(providers);
            list_of_transform_map.push(transform_map);
            is_ty_move.push(is_ty_move_on_call(input_ty, tcx));
        }
        rap_trace!("list_of_providers: {:?}", list_of_providers);
        for _ in 0..num_samples {
            let args = self.sample_eligable_calls(&list_of_providers, &is_ty_move);
            if let Some(args) = args {
                let transforms = args
                    .iter()
                    .zip(&list_of_transform_map)
                    .map(|(var, map)| map.get(var).unwrap().clone())
                    .collect_vec();
                let call = ApiCall {
                    fn_did,
                    args: args,
                    generic_args: generic_args,
                };

                res.push(Action {
                    node,
                    call,
                    transforms,
                });
            }
        }

        res
    }

    /// search all possible next actions, and calculate their weights.
    ///
    /// # Weight Algorithm
    /// `penalty = -total_reach_of(api))`;
    /// `api_score = depth_of(api)`;
    /// `arg_score = sum(steps(args))`
    ///
    /// `weight = penalty + api_score + arg_score`
    fn eligable_actions_with_weights(
        &self,
        builder: &ContextBuilder<'tcx, 'a>,
    ) -> (Vec<Action<'tcx>>, Vec<f32>) {
        let mut actions = Vec::new();
        let mut weights = Vec::new();

        // let evaluate_weight_for_apicall = |apicall| {};
        for idx in 0..self.api_graph.num_api() {
            let node = self.api_graph.api_node_at(idx);

            if let DepNode::Api(fn_did, generic_args) = node {
                let num_of_reach = self.global.num_reach(node);
                let global_penalty = 1.0 / (1.0 + num_of_reach as f32);
                let current_actions =
                    self.sample_k_eligable_actions(node, fn_did, &generic_args, &builder);

                let current_weights = current_actions.iter().map(|action| {
                    // calculate score for each action
                    let arg_score = action
                        .call
                        .args()
                        .iter()
                        .fold(1.0, |acc, &var| acc + builder.step_of(var) as f32);

                    // FIXME: depth_of sometimes return LARGE_ENOUGH
                    let api_score = self
                        .depth_of(action.node)
                        .expect(&format!("visit unexpected node: {:?}", action.node))
                        as f32;

                    let weight = global_penalty * arg_score;

                    rap_trace!(
                        "weight of {} = {:.2} * {} = {:.2}",
                        action.pretty_str(self.tcx),
                        global_penalty,
                        arg_score,
                        weight
                    );

                    weight
                });

                rap_trace!(
                    "{}: {}",
                    self.tcx.def_path_str_with_args(fn_did, generic_args),
                    current_actions
                        .iter()
                        .map(|act| act.pretty_str(self.tcx))
                        .join(", ")
                );

                weights.extend(current_weights);
                actions.extend(current_actions);
            }
        }
        assert!(actions.len() == weights.len());
        (actions, weights)
    }

    pub fn next(&mut self, builder: &mut ContextBuilder<'tcx, 'a>) -> Option<Action<'tcx>> {
        rap_debug!(
            "live vars: {}",
            builder
                .available_vars()
                .map(|var| format!("{var}: {:?}", builder.cx().type_of(var)))
                .join(", ")
        );

        rap_debug!(
            "varstate: {}",
            builder
                .cx()
                .vars()
                .map(|var| { format!("{} -> {}", var, builder.var_state(var)) })
                .join(", ")
        );

        rap_debug!("live state: {:?}", builder.live_state());

        let mut weights;

        let actions;
        if !utils::is_env_var_exist("TESTGEN_DISABLE_WEIGHT") {
            (actions, weights) = self.eligable_actions_with_weights(builder);
        } else {
            (actions, _) = self.eligable_actions_with_weights(builder);
            weights = vec![1.0; actions.len()];
        };

        weights.iter_mut().for_each(|weight| {
            *weight = weight.clamp(0.0, 1000.0);
        });

        rap_debug!("# eligible actions = {}", actions.len());

        // No action can do
        if actions.is_empty() {
            return None;
        }

        // rap_debug!("raw weights = {:?}", weights);

        // Softmax
        // weights.iter_mut().for_each(|weight| *weight = weight.exp());

        rap_debug!("weights = {:?}", weights);

        rap_trace!(
            "actions, weights: {}",
            actions
                .iter()
                .zip(weights.iter())
                .map(|(action, weight)| {
                    format!("{}: {:.2}", action.pretty_str(self.tcx), weight)
                })
                .collect::<Vec<_>>()
                .join(", ")
        );

        let top_k = top_k_idx_by_weight(&actions, &weights, self.config.top_k);
        let weights_top_k = top_k.iter().map(|&idx| weights[idx]).collect_vec();

        rap_trace!(
            "(top_k) actions, weights: {}",
            top_k
                .iter()
                .map(|&idx| {
                    let action = &actions[idx];
                    let weight = &weights[idx];
                    format!("{}: {:.2}", action.pretty_str(self.tcx), weight)
                })
                .collect::<Vec<_>>()
                .join(", ")
        );

        let dist = WeightedIndex::new(&weights_top_k).unwrap();
        let idx = self.rng.borrow_mut().sample(dist);

        Some(actions[top_k[idx]].clone())
    }
}
