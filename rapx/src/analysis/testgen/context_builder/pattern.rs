use super::lifetime;
use super::lifetime::visit_ty_region_with;
use crate::analysis::testgen::context_builder::lifetime::extract_rids;
use crate::analysis::testgen::utils;
use rustc_hir::def_id::DefId;
use rustc_infer::infer;
use rustc_infer::infer::{InferCtxt, RegionVariableOrigin};
use rustc_infer::{infer::TyCtxtInferExt as _, traits::ObligationCause};
use rustc_middle::ty::{self, TyCtxt, TypeFoldable as _};
use rustc_span::DUMMY_SP;
use std::collections::HashMap;

#[derive(Debug, Clone, Copy, Eq, PartialEq)]
pub enum PatternNode {
    Static,
    Named(usize),
    Temp(usize),
}

#[derive(Debug)]
pub struct EdgePattern(PatternNode, PatternNode);
impl EdgePattern {
    pub fn from(&self) -> PatternNode {
        self.0
    }
    pub fn to(&self) -> PatternNode {
        self.1
    }
}

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

pub struct PatternProvider<'tcx> {
    tcx: TyCtxt<'tcx>,
    map: HashMap<DefId, EdgePatterns>,
}

impl<'tcx> PatternProvider<'tcx> {
    pub fn new(tcx: TyCtxt<'tcx>) -> PatternProvider<'tcx> {
        PatternProvider {
            tcx: tcx,
            map: HashMap::new(),
        }
    }
    pub fn get_patterns_with<T>(
        &mut self,
        fn_did: DefId,
        args: &[ty::GenericArg<'tcx>],
        mut f: impl FnMut(&EdgePatterns) -> T,
    ) -> T {
        let tcx = self.tcx;
        if !utils::fn_requires_monomorphization(fn_did, tcx) {
            f(self
                .map
                .entry(fn_did)
                .or_insert_with(|| extract_constraints(fn_did, args, tcx)))
        } else {
            f(&extract_constraints(fn_did, args, tcx))
        }
    }
}

pub fn extract_constraints<'tcx>(
    fn_did: DefId,
    generic_args: &[ty::GenericArg<'tcx>],
    tcx: TyCtxt<'tcx>,
) -> EdgePatterns {
    struct InfcxVarFolder<'tcx, 'a> {
        infcx: &'a InferCtxt<'tcx>,
        tcx: TyCtxt<'tcx>,
    }

    impl<'tcx, 'a> ty::TypeFolder<TyCtxt<'tcx>> for InfcxVarFolder<'tcx, 'a> {
        fn cx(&self) -> TyCtxt<'tcx> {
            self.tcx
        }
        fn fold_region(&mut self, _: ty::Region<'tcx>) -> ty::Region<'tcx> {
            self.infcx
                .next_region_var(RegionVariableOrigin::Misc(DUMMY_SP))
        }
    }

    rap_trace!(
        "[extract_constraints] fn_did: {:?}, generic_args: {:?}",
        fn_did,
        generic_args
    );

    let infcx = tcx.infer_ctxt().build(ty::TypingMode::PostAnalysis);
    let mut folder = InfcxVarFolder { infcx: &infcx, tcx };

    // instantiate generic args with fresh inference variables
    let fresh_args =
        tcx.mk_args_from_iter(generic_args.iter().map(|arg| arg.fold_with(&mut folder)));
    rap_trace!("[extract_contraints] fresh_args = {:?}", fresh_args);

    let generic_fn_sig = tcx.fn_sig(fn_did);
    // instantiate the generic fn_sig with fresh generic args
    let fn_binder = generic_fn_sig.instantiate(tcx, fresh_args);
    let fn_sig = infcx.instantiate_binder_with_fresh_vars(
        DUMMY_SP,
        infer::BoundRegionConversionTime::FnCall,
        fn_binder,
    );

    let temp_cnt = infcx.num_region_vars();
    assert!(infcx.num_ty_vars() == 0);

    // this fn_sig indicates an aribtary instantiation of the fn
    let free_fn_sig = fn_sig.fold_with(&mut folder);
    let rids = extract_rids(free_fn_sig);
    rap_trace!("[extract_contraints] rids = {:?}", rids);
    // assert rids should be in ascending order
    assert!(rids.windows(2).all(|w| w[0].index() < w[1].index()));

    rap_trace!("[extract_contraints] fn_sig = {:?}", fn_sig);
    rap_trace!("[extract_contraints] free_fn_sig = {:?}", free_fn_sig);

    let param_env = tcx.param_env(fn_did);

    let dummy = ObligationCause::dummy();

    let res = infcx
        .at(&dummy, param_env)
        .sub(infer::DefineOpaqueTypes::Yes, fn_sig, free_fn_sig)
        .unwrap();

    rap_trace!("infcx result: {res:?}");

    let at = infcx.at(&dummy, param_env);
    let mut f = |prev_region, region| {
        let _ = at
            .sub(infer::DefineOpaqueTypes::Yes, region, prev_region)
            .unwrap();
    };

    for input in fn_sig.inputs().iter() {
        lifetime::visit_ty_region_with(*input, None, tcx, &mut f);
    }
    lifetime::visit_ty_region_with(fn_sig.output(), None, tcx, &mut f);

    let region_constraint_data = infcx.take_and_reset_region_constraints();
    let get_pattern_node = |region: ty::Region<'tcx>| -> PatternNode {
        if region.is_static() {
            return PatternNode::Static;
        }
        let id = region.as_var().as_usize();
        if id < temp_cnt {
            PatternNode::Temp(id)
        } else {
            PatternNode::Named(id - temp_cnt)
        }
    };

    let mut subgraph = EdgePatterns::default();

    for (constraint, _) in region_constraint_data.constraints {
        let edge = EdgePattern(
            get_pattern_node(constraint.sub),
            get_pattern_node(constraint.sup),
        );
        subgraph.patterns.push(edge);
    }

    // extract constraints from where clauses of Fn
    let predicates = tcx.predicates_of(fn_did).instantiate(tcx, fresh_args);
    predicates.predicates.iter().for_each(|clause| {
        match clause.kind().skip_binder() {
            // T: 'a
            ty::ClauseKind::TypeOutlives(pred) => {
                let ty = pred.0;
                let region = pred.1;
                rap_trace!("pred: {:?} {:?}", ty, region);
                visit_ty_region_with(ty, Some(region), tcx, &mut |prev, current| {
                    subgraph.patterns.push(EdgePattern(
                        get_pattern_node(prev),
                        get_pattern_node(current),
                    ));
                });
            }
            // 'a : 'r
            ty::ClauseKind::RegionOutlives(outlive_pred) => {
                let outlive_pred = outlive_pred;
                // lhs : rhs
                let (lhs, rhs) = (outlive_pred.0, outlive_pred.1);

                // build edge from rhs to lhs
                subgraph
                    .patterns
                    .push(EdgePattern(get_pattern_node(rhs), get_pattern_node(lhs)));
            }
            _ => {}
        }
    });

    subgraph.named_region_num = infcx.num_region_vars() - temp_cnt;
    subgraph.temp_num = temp_cnt;
    subgraph
}
