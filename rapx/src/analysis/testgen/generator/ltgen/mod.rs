pub mod context;
mod folder;
mod lifetime;

use crate::analysis::core::alias::{FnRetAlias, RetAlias};
use crate::analysis::core::api_dep::ApiDepGraph;
use crate::analysis::testgen::api_dep::graph::TransformKind;
use crate::analysis::testgen::context::{ApiCall, Context, Stmt, StmtKind, Var};
use crate::analysis::testgen::utils::{self, get_all_pub_apis};
use crate::{rap_debug, rap_info};
use context::LtContext;

use lifetime::EdgePatterns;
use rand::rngs::ThreadRng;
use rand::{self, Rng};
use rustc_data_structures::fx::FxHashMap;
use rustc_hir::def_id::DefId;
use rustc_middle::ty::{self, Ty, TyCtxt, TyKind};
use std::cell::RefCell;
use std::collections::HashMap;

type FnAliasMap = FxHashMap<DefId, FnRetAlias>;
type RegionSubgraphMap = HashMap<DefId, EdgePatterns>;

pub fn initialize_subgraph_map<'tcx>(tcx: TyCtxt<'tcx>) -> RegionSubgraphMap {
    let mut map = HashMap::new();
    for fn_did in get_all_pub_apis(tcx) {
        if utils::fn_requires_monomorphization(fn_did, tcx) {
            continue;
        }
        map.insert(fn_did, lifetime::extract_constraints(fn_did, tcx));
    }
    map
}

pub struct LtGenBuilder<'tcx, 'a, R: Rng> {
    tcx: TyCtxt<'tcx>,
    rng: R,
    max_complexity: usize,
    alias_map: &'a FnAliasMap,
    api_graph: &'a ApiDepGraph<'tcx>,
    population_size: usize,
}

impl<'tcx, 'a> LtGenBuilder<'tcx, 'a, ThreadRng> {
    pub fn new(
        tcx: TyCtxt<'tcx>,
        alias_map: &'a FnAliasMap,
        api_graph: &'a ApiDepGraph<'tcx>,
    ) -> LtGenBuilder<'tcx, 'a, ThreadRng> {
        LtGenBuilder {
            tcx,
            rng: rand::rng(),
            max_complexity: 20,
            population_size: 100,
            alias_map,
            api_graph,
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
            self.api_graph,
        )
    }

    pub fn max_complexity(mut self, max_complexity: usize) -> Self {
        self.max_complexity = max_complexity;
        self
    }

    pub fn population_size(mut self, population_size: usize) -> Self {
        self.population_size = population_size;
        self
    }

    pub fn rng(mut self, rng: R) -> Self {
        self.rng = rng;
        self
    }
}

// pub struct CrateInfo<'tcx> {
//     pub subgraph_map: RegionSubgraphMap,
//     pub alias_map: FnAliasMap,
//     pub api_graph: ApiDepGraph<'tcx>,
// }

// impl CrateInfo<'tcx> {
//     pub fn new(tcx: TyCtxt<'tcx>) -> Self {
//         let subgraph_map = initialize_subgraph_map(tcx);
//     }
// }

pub struct LtGen<'tcx, 'a, R: Rng> {
    pub_api: Vec<DefId>,
    tcx: TyCtxt<'tcx>,
    rng: RefCell<R>,
    max_complexity: usize,
    alias_map: &'a FnAliasMap,
    subgraph_map: RegionSubgraphMap,
    api_graph: &'a ApiDepGraph<'tcx>,
}

fn ty_project_to<'tcx>(mut ty: Ty<'tcx>, proj: &[usize], tcx: TyCtxt<'tcx>) -> Ty<'tcx> {
    for field_no in proj {
        ty = match ty.peel_refs().kind() {
            TyKind::Adt(adt_def, args) => {
                let did = adt_def
                    .all_fields()
                    .nth(*field_no)
                    .expect("field not found")
                    .did;
                tcx.type_of(did).instantiate(tcx, args)
            }
            _ => {
                panic!("not a struct type");
            }
        }
    }
    ty
}

fn get_fn_arg_ty_at<'tcx>(no: usize, fn_sig: ty::FnSig<'tcx>) -> Ty<'tcx> {
    if no == 0 {
        fn_sig.output()
    } else {
        fn_sig.inputs()[no - 1]
    }
}

fn destruct_ret_alias<'tcx>(
    fn_sig: ty::FnSig<'tcx>,
    ret_alias: &RetAlias,
    tcx: TyCtxt<'tcx>,
) -> (Ty<'tcx>, Ty<'tcx>) {
    let lhs_no = ret_alias.left_index;
    let rhs_no = ret_alias.right_index;

    (
        ty_project_to(
            get_fn_arg_ty_at(lhs_no, fn_sig),
            &ret_alias.left_field_seq,
            tcx,
        ),
        ty_project_to(
            get_fn_arg_ty_at(rhs_no, fn_sig),
            &ret_alias.right_field_seq,
            tcx,
        ),
    )
}

impl<'tcx, 'a, R: Rng> LtGen<'tcx, 'a, R> {
    fn new(
        tcx: TyCtxt<'tcx>,
        alias_map: &'a FnAliasMap,
        rng: R,
        max_complexity: usize,
        api_graph: &'a ApiDepGraph<'tcx>,
    ) -> Self {
        LtGen {
            pub_api: utils::get_all_pub_apis(tcx),
            tcx,
            rng: RefCell::new(rng),
            max_complexity,
            alias_map,
            subgraph_map: initialize_subgraph_map(tcx),
            api_graph,
        }
    }

    fn tcx(&self) -> TyCtxt<'tcx> {
        self.tcx
    }

    pub fn pub_api_def_id(&self) -> &[DefId] {
        &self.pub_api
    }

    // Vec<Var, [LifetimeBinding]>
    // drop(LifetimeRelated)
    // use(Projection)
    // 如果alias（a，b），且a中含有unsafe ptr，则a -> all_lifetime(b)，对于b也一样
    pub fn is_api_vulnerable(&self, did: DefId) -> bool {
        if let Some(fn_ret_alias) = self.alias_map.get(&did) {
            let fn_sig = utils::fn_sig_without_binders(did, self.tcx());
            let mut is_vulnerable = false;
            for ret_alias in fn_ret_alias.aliases() {
                let (lhs_ty, rhs_ty) = destruct_ret_alias(fn_sig, ret_alias, self.tcx());
                let lhs_result = utils::ty_check_ptr(lhs_ty, self.tcx());
                let rhs_result = utils::ty_check_ptr(rhs_ty, self.tcx());
                let has_unsafe_ptr = lhs_result.has_unsafe_ptr || rhs_result.has_unsafe_ptr;
                // let has_ptr = lhs_result.has_any_ptr || rhs_result.has_any_ptr;
                is_vulnerable = is_vulnerable || has_unsafe_ptr;
                rap_debug!("{did:?} is_vulnerable={is_vulnerable} lhs: {lhs_ty}, rhs: {rhs_ty}");
            }
            is_vulnerable
        } else {
            panic!("Cannot find alias result: {:?}", did);
        }
    }

    pub fn check_all_vulnerable_api(&self) -> Vec<DefId> {
        let mut vulnerable_apis = Vec::new();
        for fn_did in self.pub_api_def_id() {
            if self.is_api_vulnerable(*fn_did) {
                vulnerable_apis.push(*fn_did);
            }
        }
        vulnerable_apis
    }

    pub fn is_api_eligable<C: Context<'tcx>>(&self, fn_did: DefId, cx: &C) -> Option<ApiCall> {
        let tcx = self.tcx();

        let mut api_call = ApiCall {
            fn_did,
            args: Vec::new(),
        };

        // TODO: now only consider fn_sig without type & const parameters
        if tcx.generics_of(fn_did).requires_monomorphization(tcx) {
            return None;
        }
        let fn_sig = utils::fn_sig_without_binders(fn_did, tcx);

        rap_debug!("check eligible api: {fn_did:?}");
        for input_ty in fn_sig.inputs().iter() {
            rap_debug!("input_ty = {input_ty:?}");
            let providers = cx.all_possible_providers(*input_ty);
            if providers.is_empty() {
                rap_debug!("no possible providers");
                return None;
            }
            rap_debug!("providers: {providers:?}");
            let idx = self.rng.borrow_mut().random_range(0..providers.len());
            api_call.args.push(providers[idx].clone());
        }

        Some(api_call)
    }

    fn choose_eligable_api(&self, cx: &LtContext<'tcx, 'a, '_>) -> Option<ApiCall> {
        let mut eligable_calls = Vec::new();
        for fn_did in self.pub_api_def_id() {
            if let Some(call) = self.is_api_eligable(*fn_did, cx) {
                eligable_calls.push(call);
            }
        }
        if eligable_calls.is_empty() {
            return None;
        }
        rap_debug!("eligable calls: {eligable_calls:?}");
        let idx = self.rng.borrow_mut().random_range(0..eligable_calls.len());
        Some(eligable_calls.swap_remove(idx))
    }

    fn choose_transform(&self, cx: &mut LtContext<'tcx, 'a, '_>) -> Option<(Var, TransformKind)> {
        let mut vec: Vec<(Var, TransformKind)> = Vec::new();
        for var in cx.available_values() {
            let ty = cx.type_of(*var);
            for transform in self.api_graph.all_transform_for(ty) {
                vec.push((*var, transform));
            }
        }
        if vec.is_empty() {
            return None;
        }

        let idx = self.rng.borrow_mut().random_range(0..vec.len());
        Some(vec.swap_remove(idx))
    }

    pub fn next_operation(&self, cx: &mut LtContext<'tcx, 'a, '_>) {
        let hit = self.rng.borrow_mut().random_ratio(2, 3);

        if hit {
            if let Some(call) = self.choose_eligable_api(cx) {
                if self.is_api_vulnerable(call.fn_did()) {
                    rap_info!("{:?} is vulnerable", call.fn_did());
                }
                cx.add_call_stmt(call);
                if cx.try_inject_drop() {
                    rap_info!("successfully inject drop");
                }
            }
        } else {
            if let Some((var, kind)) = self.choose_transform(cx) {
                match kind {
                    TransformKind::Ref(mutability) => {
                        cx.add_ref_stmt(var, mutability);
                    }
                    _ => {}
                }
            }
        }
    }

    pub fn gen(&mut self) -> LtContext<'tcx, 'a, '_> {
        let mut cx = LtContext::new(self.tcx(), &self.subgraph_map, &self.alias_map);
        let (estimated, total) = utils::estimate_max_coverage(self.api_graph, self.tcx());
        while cx.complexity() < self.max_complexity {
            self.next_operation(&mut cx);
            rap_info!(
                "complexity = {}, covered/estimated/total api = {}/{}/{} {{estimated/total}} coverage = {:.3}/{:.3} ",
                cx.complexity(),
                cx.num_covered_api(),
                estimated,
                total,
                cx.num_covered_api() as f32 / estimated as f32,
                cx.num_covered_api() as f32 / total as f32
            );
        }

        let mut file = std::fs::File::create("region_graph.dot").unwrap();
        // cx.region_graph().dump(&mut std::io::stdout()).unwrap();
        cx.region_graph().dump(&mut file).unwrap();
        cx
    }
}
