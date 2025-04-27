use crate::analysis::core::api_dep::{self, DepNode};
use crate::analysis::testgen::api_dep::graph::TyWrapper;
use crate::analysis::testgen::api_dep::DepEdge;
use crate::analysis::testgen::context::DUMMY_INPUT_VAR;
use crate::analysis::testgen::context::{ApiCall, Context};
use crate::analysis::testgen::utils;
use crate::analysis::testgen::utils::is_fuzzable_ty;
use crate::analysis::testgen::ContextBase;
use crate::rap_debug;
use crate::rap_info;
use petgraph::visit::EdgeRef;
use petgraph::visit::IntoNodeReferences;
use petgraph::Direction;
use rand::prelude::IndexedRandom;
use rand::Rng;
use rustc_hir::def_id::DefId;
use rustc_middle::ty::{self, AdtDef, FieldDef, FnSig, Ty, TyCtxt, TyKind};
use std::collections::{HashMap, HashSet, VecDeque};

use crate::analysis::testgen::context::Var;
pub struct Rulf {
    max_coverage: Option<(i32, i32)>,
}

impl Rulf {
    pub fn new() -> Self {
        Self { max_coverage: None }
    }
    fn find_api_starts<'tcx>(
        &self,
        graph: &api_dep::ApiDepGraph<'tcx>,
        tcx: TyCtxt<'tcx>,
    ) -> Vec<api_dep::DepNode<'tcx>> {
        let mut api_starts = Vec::new();
        for (node_idx, node) in graph.inner_graph().node_references() {
            if let api_dep::DepNode::Api(_) = node {
                let all_params_primitive = graph
                    .inner_graph()
                    .edges_directed(node_idx, Direction::Incoming)
                    .filter(|e| matches!(e.weight(), api_dep::DepEdge::Arg(_)))
                    .all(|e| {
                        if let api_dep::DepNode::Ty(ty_wrapper) = &graph.inner_graph()[e.source()] {
                            is_fuzzable_ty(ty_wrapper.ty(), tcx)
                        } else {
                            false
                        }
                    });
                if all_params_primitive {
                    api_starts.push(node.clone());
                }
            }
        }
        api_starts
    }
    pub fn rulf_algorithm<'tcx, R: Rng>(
        &mut self,
        tcx: TyCtxt<'tcx>,
        graph: &mut api_dep::ApiDepGraph<'tcx>,
        max_depth: usize,
        cx: &mut ContextBase<'tcx>,
        rng: &mut R,
    ) {
        let mut queue = VecDeque::new();
        let visited: &mut HashSet<api_dep::DepNode<'tcx>> = &mut HashSet::new();
        let mut type_to_api_calls: HashMap<Ty<'tcx>, Vec<Vec<DefId>>> = HashMap::new();
        // 1. find start nodes
        let api_starts = self.find_api_starts(graph, tcx);
        rap_info!("start_api stage");

        for start_api in api_starts {
            if let api_dep::DepNode::Api(def_id) = start_api {
                let fn_sig = utils::fn_sig_without_binders(def_id, tcx);
                let mut args = Vec::new();
                for input_ty in fn_sig.inputs() {
                    let providers = cx.all_possible_providers(*input_ty);
                    let var = if providers.is_empty() {
                        panic!(
                            "no providers for start node , need input type {:?}",
                            input_ty
                        );
                    } else {
                        providers[0]
                    };
                    args.push(var);
                }
                let call = ApiCall {
                    fn_did: def_id,
                    args,
                };
                cx.add_call_stmt(call);
                visited.insert(start_api.clone());
                queue.push_back((start_api, vec![def_id], 1));
                let output_ty = fn_sig.output();
                let mut transform_queue = VecDeque::new();
                if let Some(ty_idx) =
                    graph.get_index_by_node(DepNode::Ty(TyWrapper::from(output_ty)))
                {
                    transform_queue.push_back((ty_idx, TyWrapper::from(output_ty), 0));
                }
                while let Some((ty_idx, current_ty, depth)) = transform_queue.pop_front() {
                    if depth >= 3 {
                        continue;
                    }
                    type_to_api_calls
                        .entry(current_ty.ty())
                        .or_insert_with(Vec::new)
                        .push(vec![def_id]);
                    let transform_edges = graph
                        .inner_graph()
                        .edges_directed(ty_idx, Direction::Outgoing)
                        .filter(|e| matches!(e.weight(), DepEdge::Transform(_)));
                    for edge in transform_edges {
                        if let api_dep::DepNode::Ty(target_ty) = &graph.inner_graph()[edge.target()]
                        {
                            if let DepEdge::Transform(kind) = edge.weight() {
                                transform_queue.push_back((edge.target(), *target_ty, depth + 1));
                            }
                        }
                    }
                }
            }
        }
        // 3. BFS
        rap_info!("start BFS");
        while let Some((last_api, current_seq, depth)) = queue.pop_front() {
            if depth > max_depth {
                break; // depth bigger than max_depth, stop BFS
            }
            if visited.contains(&last_api) {
                continue; // Skip already visited APIs
            }
            let last_idx = graph.get_node(last_api);
            // 4. produce edge
            let ret_edges = graph
                .inner_graph()
                .edges_directed(last_idx, Direction::Outgoing)
                .filter(|e| matches!(e.weight(), DepEdge::Ret));
            for ret_edge in ret_edges {
                let ret_type_node = &graph.inner_graph()[ret_edge.target()];
                if let api_dep::DepNode::Ty(ret_ty) = ret_type_node {
                    // 5. consume edge
                    let consumer_edges = graph
                        .inner_graph()
                        .edges_directed(ret_edge.target(), Direction::Outgoing)
                        .filter(|e| matches!(e.weight(), DepEdge::Arg(_)));
                    // find consumers that are not visited
                    let mut unvisited_consumers = Vec::new();
                    for consumer_edge in consumer_edges {
                        let consumer_api_idx = consumer_edge.target();
                        let consumer_api = graph.inner_graph()[consumer_api_idx].clone();
                        if let api_dep::DepNode::Api(_) = consumer_api {
                            if !visited.contains(&consumer_api) {
                                unvisited_consumers.push(consumer_api);
                            }
                        }
                    }
                    // process unvisited consume api
                    for consumer_api in unvisited_consumers {
                        if let api_dep::DepNode::Api(def_id) = consumer_api {
                            let fn_sig = utils::fn_sig_without_binders(def_id, tcx);
                            let mut param_providers: Vec<Vec<_>> = Vec::new();
                            let mut satisfy_all_input = true;
                            for input_ty in fn_sig.inputs() {
                                if let ty::Ref(_, inner_ty, ty::Mutability::Mut) = input_ty.kind() {
                                    if inner_ty.is_str() {
                                        rap_debug!("Skipping &mut str input type {:?}", input_ty);
                                        satisfy_all_input = false;
                                        break;
                                    }
                                }
                                let providers = cx.all_possible_providers_mut(*input_ty);
                                if providers.is_empty() {
                                    rap_debug!(
                                        "no providers for consumer node now, need input type {:?}",
                                        input_ty
                                    );
                                    satisfy_all_input = false;
                                    break;
                                } else {
                                    param_providers.push(providers);
                                }
                            }
                            if !satisfy_all_input {
                                continue;
                            }
                            // params have diversity, generate at most 3 call seq
                            for _ in 0..3 {
                                let mut args = Vec::new();
                                let enough_param = param_providers.iter().all(|p| p.len() > 0);
                                if !enough_param {
                                    break;
                                }
                                for providers in &mut param_providers {
                                    let var =
                                        providers.swap_remove(rng.random_range(0..providers.len()));
                                    args.push(var);
                                }
                                let call = ApiCall {
                                    fn_did: def_id,
                                    args,
                                };
                                cx.add_call_stmt(call);
                                let mut new_seq = current_seq.clone();
                                new_seq.push(def_id);
                                // update type_to_api_calls
                                let output_ty = fn_sig.output();
                                let mut transform_queue = VecDeque::new();
                                if let Some(ty_idx) =
                                    graph.get_index_by_node(DepNode::Ty(TyWrapper::from(output_ty)))
                                {
                                    transform_queue.push_back((
                                        ty_idx,
                                        TyWrapper::from(output_ty),
                                        0,
                                    ));
                                }
                                while let Some((ty_idx, current_ty, depth)) =
                                    transform_queue.pop_front()
                                {
                                    if depth >= 3 {
                                        continue;
                                    }
                                    type_to_api_calls
                                        .entry(current_ty.ty())
                                        .or_insert_with(Vec::new)
                                        .push(new_seq.clone());
                                    let transform_edges = graph
                                        .inner_graph()
                                        .edges_directed(ty_idx, Direction::Outgoing)
                                        .filter(|e| matches!(e.weight(), DepEdge::Transform(_)));
                                    for edge in transform_edges {
                                        if let api_dep::DepNode::Ty(target_ty) =
                                            &graph.inner_graph()[edge.target()]
                                        {
                                            if let DepEdge::Transform(kind) = edge.weight() {
                                                transform_queue.push_back((
                                                    edge.target(),
                                                    *target_ty,
                                                    depth + 1,
                                                ));
                                            }
                                        }
                                    }
                                }
                                visited.insert(consumer_api.clone());
                                queue.push_back((consumer_api.clone(), new_seq, depth + 1));
                            }
                        }
                    }
                } else {
                    rap_info!("ret_type_node is not DepNode::Ty");
                }
            }
        }
        rap_info!("start backward search");
        //backward search
        let all_api_nodes: HashSet<_> = graph
            .inner_graph()
            .node_references()
            .filter_map(|(_, node)| {
                if let api_dep::DepNode::Api(_) = node {
                    Some(node.clone())
                } else {
                    None
                }
            })
            .collect();
        let mut unvisited_api_nodes: HashSet<_> =
            all_api_nodes.difference(&visited).cloned().collect();
        let mut prev_unvisited_count = unvisited_api_nodes.len() + 1;
        let mut current_unvisited: Vec<_> = unvisited_api_nodes.iter().cloned().collect();

        while !unvisited_api_nodes.is_empty() && prev_unvisited_count > current_unvisited.len() {
            prev_unvisited_count = current_unvisited.len();
            let mut i = 0;
            while i < current_unvisited.len() {
                let target_api = current_unvisited[i].clone();
                //rap_info!("backward search for target_api: {:?}", target_api);
                if self.backward_search(graph, &target_api, cx, &mut type_to_api_calls, rng, tcx) {
                    visited.insert(target_api.clone());
                    unvisited_api_nodes.remove(&target_api);
                    current_unvisited.swap_remove(i);
                } else {
                    i += 1;
                }
            }
        }
        self.max_coverage = Some((visited.len() as i32, all_api_nodes.len() as i32));
        rap_info!("Use Rulf, Max coverage: {:?}", self.max_coverage);
    }

    fn backward_search<'tcx, R: Rng>(
        &self,
        graph: &mut api_dep::ApiDepGraph<'tcx>,
        target_api: &api_dep::DepNode<'tcx>,
        cx: &mut ContextBase<'tcx>,
        type_to_api_calls: &mut HashMap<Ty<'tcx>, Vec<Vec<DefId>>>,
        rng: &mut R,
        tcx: TyCtxt<'tcx>,
    ) -> bool {
        if let api_dep::DepNode::Api(def_id) = target_api {
            rap_info!("backward search for target_api: {:?}", target_api);
            let fn_sig = utils::fn_sig_without_binders(*def_id, tcx);
            let mut vars = Vec::new();
            let mut dependency_seqs = Vec::new();
            let mut used_vars = HashSet::new();
            // process input_ty
            for input_ty in fn_sig.inputs() {
                if let ty::Ref(_, inner_ty, ty::Mutability::Mut) = input_ty.kind() {
                    if inner_ty.is_str() {
                        rap_debug!("Skipping &mut str input type {:?}", input_ty);
                        return false;
                    }
                }
                let providers = cx.all_possible_providers_mut(*input_ty);
                let vaild_providers: Vec<_> = providers
                    .into_iter()
                    .filter(|&var| !used_vars.contains(&var))
                    .collect();
                if !vaild_providers.is_empty() {
                    // have providers in cx
                    let idx = rng.random_range(0..vaild_providers.len());
                    let var = vaild_providers[idx];
                    rap_info!("input_ty: {:?}, var: {:?} from providers", input_ty, var);
                    vars.push(var);
                    used_vars.insert(var);
                    if var == DUMMY_INPUT_VAR {
                        continue;
                    } else {
                        if let Some(api_seqs) = type_to_api_calls.get(input_ty) {
                            // choose var from type_to_api_calls
                            if let Some(api_seq) = api_seqs.choose(rng) {
                                dependency_seqs.push(api_seq.clone());
                            } else {
                                rap_debug!("no api seq for input type {:?}", input_ty);
                                return false;
                            }
                        } else {
                            let input_peel_ref = input_ty.peel_refs();
                            if let Some(api_seqs) = type_to_api_calls.get(&input_peel_ref) {
                                // choose var from type_to_api_calls
                                if let Some(api_seq) = api_seqs.choose(rng) {
                                    dependency_seqs.push(api_seq.clone());
                                } else {
                                    rap_info!("no api seq for input type {:?}", input_ty);
                                    return false;
                                }
                            }
                        }
                    }
                } else if let Some(api_seqs) = type_to_api_calls.get(&input_ty.peel_refs()) {
                    // choose var from type_to_api_calls
                    if let Some(api_seq) = api_seqs.choose(rng) {
                        let input_ref_mut =
                            if let ty::Ref(_, inner_ty, mutability) = input_ty.kind() {
                                Some(*mutability)
                            } else {
                                None
                            };
                        if let Some(var) = self.seq2call(
                            api_seq,
                            cx,
                            &type_to_api_calls,
                            &mut used_vars,
                            rng,
                            tcx,
                            input_ref_mut,
                        ) {
                            rap_info!("input_ty: {:?}, var: {:?} from seq2call", input_ty, var);
                            let mut ref_vec: Vec<(Ty, ty::Mutability)> = vec![];
                            let mut iter_ty = input_ty;
                            while let ty::Ref(_, inner_ty, mutability) = iter_ty.kind() {
                                ref_vec.push((*inner_ty, *mutability));
                                iter_ty = inner_ty;
                            }
                            let mut ref_input_var = var;
                            while !ref_vec.is_empty() {
                                if let Some((_inner_ty, mutability)) = ref_vec.pop() {
                                    used_vars.insert(ref_input_var);
                                    ref_input_var = cx.add_ref_stmt(ref_input_var, mutability);
                                }
                            }
                            vars.push(ref_input_var);
                            used_vars.insert(ref_input_var);
                            dependency_seqs.push(api_seq.clone());
                        } else {
                            return false;
                        }
                    } else {
                        return false;
                    }
                } else {
                    return false;
                }
            }
            // rap_info!(
            //     "target_api: {:?}, dependency_seqs: {:?}",
            //     target_api,
            //     dependency_seqs
            // );
            // add new seq into target_seq
            let mut target_seq = Vec::new();
            for dep_seq in dependency_seqs {
                target_seq.extend(dep_seq);
            }
            target_seq.push(*def_id);

            // generate new call
            let call = ApiCall {
                fn_did: *def_id,
                args: vars,
            };
            cx.add_call_stmt(call);

            // update type_to_api_calls
            let output_ty = fn_sig.output();
            let mut transform_queue = VecDeque::new();
            if let Some(ty_idx) = graph.get_index_by_node(DepNode::Ty(TyWrapper::from(output_ty))) {
                transform_queue.push_back((ty_idx, TyWrapper::from(output_ty), 0));
            }
            while let Some((ty_idx, current_ty, depth)) = transform_queue.pop_front() {
                if depth >= 3 {
                    continue;
                }
                type_to_api_calls
                    .entry(current_ty.ty())
                    .or_insert_with(Vec::new)
                    .push(target_seq.clone());
                let transform_edges = graph
                    .inner_graph()
                    .edges_directed(ty_idx, Direction::Outgoing)
                    .filter(|e| matches!(e.weight(), DepEdge::Transform(_)));
                for edge in transform_edges {
                    if let api_dep::DepNode::Ty(target_ty) = &graph.inner_graph()[edge.target()] {
                        if let DepEdge::Transform(kind) = edge.weight() {
                            transform_queue.push_back((edge.target(), *target_ty, depth + 1));
                        }
                    }
                }
            }
            true
        } else {
            false
        }
    }

    fn seq2call<'tcx, R: Rng>(
        &self,
        seq: &Vec<DefId>,
        cx: &mut ContextBase<'tcx>,
        type_to_api_calls: &HashMap<Ty<'tcx>, Vec<Vec<DefId>>>,
        used_vars: &mut HashSet<Var>,
        rng: &mut R,
        tcx: TyCtxt<'tcx>,
        input_ref_mut: Option<ty::Mutability>,
    ) -> Option<Var> {
        let mut ret_var: Option<Var> = None;
        for &def_id in seq {
            let fn_sig = utils::fn_sig_without_binders(def_id, tcx);
            let mut args = Vec::new();

            // find var for every input type
            for input_ty in fn_sig.inputs() {
                if let ty::Ref(_, inner_ty, ty::Mutability::Mut) = input_ty.kind() {
                    if inner_ty.is_str() {
                        rap_debug!("Skipping &mut str input type {:?}", input_ty);
                        return None;
                    }
                }
                let providers = cx.all_possible_providers_mut(*input_ty);
                let valid_providers: Vec<_> = providers
                    .into_iter()
                    .filter(|&var| !used_vars.contains(&var))
                    .collect();

                let var = if valid_providers.is_empty() {
                    if let Some(api_seqs) = type_to_api_calls.get(input_ty) {
                        // choose var from type_to_api_calls
                        if let Some(api_seq) = api_seqs.choose(rng) {
                            let iter_ty_mut =
                                if let ty::Ref(_, inner_ty, mutability) = input_ty.kind() {
                                    Some(*mutability)
                                } else {
                                    None
                                };
                            if let Some(var) = self.seq2call(
                                api_seq,
                                cx,
                                &type_to_api_calls,
                                used_vars,
                                rng,
                                tcx,
                                iter_ty_mut,
                            ) {
                                //rap_info!("input_ty: {:?}, var: {:?} from seq2call", input_ty, var);
                                let mut ref_vec: Vec<(Ty, ty::Mutability)> = vec![];
                                let mut iter_ty = input_ty;
                                while let ty::Ref(_, inner_ty, mutability) = iter_ty.kind() {
                                    ref_vec.push((*inner_ty, *mutability));
                                    iter_ty = inner_ty;
                                }
                                let mut ref_input_var = var;
                                while !ref_vec.is_empty() {
                                    if let Some((_inner_ty, mutability)) = ref_vec.pop() {
                                        used_vars.insert(ref_input_var);
                                        ref_input_var = cx.add_ref_stmt(ref_input_var, mutability);
                                    }
                                }
                                used_vars.insert(ref_input_var);
                                ref_input_var
                            } else {
                                panic!(
                                    "no providers for node {:?} , need input type {:?}",
                                    def_id, input_ty
                                );
                            }
                        } else {
                            panic!(
                                "no providers for node {:?} , need input type {:?}",
                                def_id, input_ty
                            );
                        }
                    } else {
                        panic!(
                            "no providers for node {:?} , need input type {:?}",
                            def_id, input_ty
                        );
                    }
                } else {
                    // choose provider randomly
                    let idx = rng.random_range(0..valid_providers.len());
                    let var = valid_providers[idx];
                    var
                };
                args.push(var);
            }

            // generate ApiCall and add into cx
            let call = ApiCall {
                fn_did: def_id,
                args,
            };
            ret_var = Some(cx.add_call_stmt(call));
        }
        match input_ref_mut {
            Some(mutability) => {
                if let Some(ret_v) = ret_var {
                    cx.lift_mutability(ret_v, mutability);
                }
            }
            None => {}
        }
        ret_var
    }

    pub fn max_coverage<'tcx>(
        &self,
        graph: &mut api_dep::ApiDepGraph<'tcx>,
        tcx: TyCtxt<'tcx>,
    ) -> Option<(i32, i32)> {
        // collect all API nodes
        let all_api_nodes: HashSet<_> = graph
            .inner_graph()
            .node_references()
            .filter_map(|(_, node)| {
                if let api_dep::DepNode::Api(_) = node {
                    Some(node.clone())
                } else {
                    None
                }
            })
            .collect();

        // initialization
        let mut queue = VecDeque::from(self.find_api_starts(graph, tcx));
        let mut visited: HashSet<api_dep::DepNode<'tcx>> = HashSet::new();
        let mut available_types: HashSet<Ty<'tcx>> = HashSet::new();

        // BFS
        rap_info!("Starting BFS for max_coverage");
        while let Some(current_api) = queue.pop_front() {
            if visited.contains(&current_api) {
                continue;
            }
            visited.insert(current_api.clone());
            let current_idx = graph.get_node(current_api.clone());

            if let api_dep::DepNode::Api(def_id) = current_api {
                let fn_sig = utils::fn_sig_without_binders(def_id, tcx);
                let output_ty = fn_sig.output();
                available_types.insert(output_ty);

                // Transform edges
                let mut transform_queue = VecDeque::new();
                transform_queue.push_back((TyWrapper::from(output_ty), 0));
                while let Some((current_ty, depth)) = transform_queue.pop_front() {
                    if depth >= 3 {
                        continue;
                    }
                    available_types.insert(current_ty.ty());
                    if let Some(ty_idx) = graph.get_index_by_node(api_dep::DepNode::Ty(current_ty))
                    {
                        let transform_edges = graph
                            .inner_graph()
                            .edges_directed(ty_idx, Direction::Outgoing)
                            .filter(|e| matches!(e.weight(), DepEdge::Transform(_)));
                        for edge in transform_edges {
                            if let api_dep::DepNode::Ty(target_ty) =
                                &graph.inner_graph()[edge.target()]
                            {
                                transform_queue.push_back((*target_ty, depth + 1));
                            }
                        }
                    }
                }

                // consumer API
                let ret_edges = graph
                    .inner_graph()
                    .edges_directed(current_idx, Direction::Outgoing)
                    .filter(|e| matches!(e.weight(), DepEdge::Ret));
                for ret_edge in ret_edges {
                    let ret_type_node = &graph.inner_graph()[ret_edge.target()];
                    if let api_dep::DepNode::Ty(ret_ty) = ret_type_node {
                        let consumer_edges = graph
                            .inner_graph()
                            .edges_directed(ret_edge.target(), Direction::Outgoing)
                            .filter(|e| matches!(e.weight(), DepEdge::Arg(_)));
                        for consumer_edge in consumer_edges {
                            let consumer_api_idx = consumer_edge.target();
                            let consumer_api = graph.inner_graph()[consumer_api_idx].clone();
                            if let api_dep::DepNode::Api(def_id) = consumer_api {
                                if !visited.contains(&consumer_api) {
                                    let fn_sig = utils::fn_sig_without_binders(def_id, tcx);
                                    let all_inputs_satisfied =
                                        fn_sig.inputs().iter().all(|input_ty| {
                                            if let ty::Ref(_, inner_ty, ty::Mutability::Mut) =
                                                input_ty.kind()
                                            {
                                                if inner_ty.is_str() {
                                                    rap_debug!(
                                                        "Skipping &mut str input type {:?}",
                                                        input_ty
                                                    );
                                                    return false;
                                                }
                                            }
                                            is_fuzzable_ty(*input_ty, tcx)
                                                || available_types.iter().any(|avail_ty| {
                                                    utils::is_ty_eq(*input_ty, *avail_ty, tcx)
                                                })
                                        });
                                    if all_inputs_satisfied {
                                        queue.push_back(consumer_api);
                                    } else {
                                        rap_debug!("Consumer API {:?} not reachable", def_id);
                                    }
                                }
                            }
                        }
                    }
                }
            }
        }

        // Backward Search
        rap_info!("Starting Backward Search for max_coverage");
        let mut unvisited_api_nodes: Vec<_> = all_api_nodes.difference(&visited).cloned().collect();
        let mut prev_unvisited_count = unvisited_api_nodes.len() + 1;

        while !unvisited_api_nodes.is_empty() && prev_unvisited_count > unvisited_api_nodes.len() {
            prev_unvisited_count = unvisited_api_nodes.len();
            let mut i = 0;
            while i < unvisited_api_nodes.len() {
                let target_api = unvisited_api_nodes[i].clone();
                let reachable = if let api_dep::DepNode::Api(def_id) = target_api {
                    let fn_sig = utils::fn_sig_without_binders(def_id, tcx);
                    let all_inputs_satisfied = fn_sig.inputs().iter().all(|input_ty| {
                        if let ty::Ref(_, inner_ty, ty::Mutability::Mut) = input_ty.kind() {
                            if inner_ty.is_str() {
                                rap_debug!("Skipping &mut str input type {:?}", input_ty);
                                return false;
                            }
                        }
                        is_fuzzable_ty(*input_ty, tcx)
                            || available_types
                                .iter()
                                .any(|avail_ty| utils::is_ty_eq(*input_ty, *avail_ty, tcx))
                    });
                    if all_inputs_satisfied {
                        visited.insert(target_api.clone());
                        let output_ty = fn_sig.output();
                        available_types.insert(output_ty);
                        // Transform edges
                        let mut transform_queue = VecDeque::new();
                        transform_queue.push_back((TyWrapper::from(output_ty), 0));
                        while let Some((current_ty, depth)) = transform_queue.pop_front() {
                            if depth >= 3 {
                                continue;
                            }
                            available_types.insert(current_ty.ty());
                            if let Some(ty_idx) =
                                graph.get_index_by_node(api_dep::DepNode::Ty(current_ty))
                            {
                                let transform_edges = graph
                                    .inner_graph()
                                    .edges_directed(ty_idx, Direction::Outgoing)
                                    .filter(|e| matches!(e.weight(), DepEdge::Transform(_)));
                                for edge in transform_edges {
                                    if let api_dep::DepNode::Ty(target_ty) =
                                        &graph.inner_graph()[edge.target()]
                                    {
                                        transform_queue.push_back((*target_ty, depth + 1));
                                    }
                                }
                            }
                        }
                        true
                    } else {
                        rap_debug!("Backward search: API {:?} not reachable", def_id);
                        false
                    }
                } else {
                    false
                };

                if reachable {
                    unvisited_api_nodes.swap_remove(i);
                } else {
                    i += 1;
                }
            }
        }
        Some((visited.len() as i32, all_api_nodes.len() as i32))
    }
}

// api-graph max coverage
// 辅助边 a-&a
// AFL
// driver 命令输出
