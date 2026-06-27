use super::statistic::Statistics;
use crate::{rap_debug, rap_info, rap_trace};
use rustc_hir::{
    BodyId, BodyOwnerKind, FnDecl,
    def_id::{DefId, LocalDefId},
    intravisit::{FnKind, Visitor, walk_block, walk_fn},
};
use rustc_middle::{
    hir::nested_filter,
    ty::{self, FnSig, ParamEnv, Ty, TyCtxt, TyKind},
};
use rustc_span::Span;
use serde::Serialize;
use std::io::Write;

pub struct FnVisitor<'tcx> {
    tcx: TyCtxt<'tcx>,
    stats: Statistics<'tcx>,
    lifetime_info: Vec<ApiLifetimeInfo>,
}

#[derive(Serialize)]
pub struct ApiLifetimeInfo {
    pub path: String,
    pub num_lifetime_params: usize,
    pub has_outlive_pred: bool,
    pub has_compound_type: bool,
}

fn is_api_public(fn_def_id: impl Into<DefId>, tcx: TyCtxt<'_>) -> bool {
    let fn_def_id: DefId = fn_def_id.into();
    let local_id = fn_def_id.expect_local();
    rap_trace!(
        "vis: {:?} (path: {}) => {:?}",
        fn_def_id,
        tcx.def_path_str(fn_def_id),
        tcx.effective_visibilities(()).effective_vis(local_id)
    );
    tcx.effective_visibilities(()).is_directly_public(local_id)
        || tcx.effective_visibilities(()).is_exported(local_id)
}

fn num_lifetime_params(did: impl Into<DefId>, tcx: TyCtxt<'_>) -> usize {
    let fn_def_id: DefId = did.into();
    let generics = tcx.generics_of(fn_def_id);

    let parent_count = if let Some(parent) = generics.parent {
        num_lifetime_params(parent, tcx)
    } else {
        0
    };

    let own_count = generics
        .own_params
        .iter()
        .filter(|p| matches!(p.kind, ty::GenericParamDefKind::Lifetime { .. }))
        .count();

    own_count + parent_count
}

fn num_late_bound_lifetime_params(did: impl Into<DefId>, tcx: TyCtxt<'_>) -> usize {
    let fn_def_id: DefId = did.into();
    tcx.fn_sig(fn_def_id)
        .skip_binder()
        .bound_vars()
        .iter()
        .filter(|kind| matches!(kind, ty::BoundVariableKind::Region(_)))
        .count()
}

fn is_api_has_multi_lifetime_params(fn_def_id: impl Into<DefId>, tcx: TyCtxt<'_>) -> bool {
    let fn_def_id: DefId = fn_def_id.into();
    let generics = tcx.generics_of(fn_def_id);

    let early_count = num_lifetime_params(fn_def_id, tcx);
    let late_count = num_late_bound_lifetime_params(fn_def_id, tcx);
    rap_debug!("num of lifetime params = {}", early_count + late_count);
    (early_count + late_count) > 1
}

fn has_outlive_pred(fn_def_id: impl Into<DefId>, tcx: TyCtxt<'_>) -> bool {
    let fn_def_id: DefId = fn_def_id.into();
    let generics = tcx.generics_of(fn_def_id);
    let predicates = tcx.explicit_predicates_of(fn_def_id);
    predicates
        .predicates
        .iter()
        .any(|(pred, _)| match pred.kind().skip_binder() {
            ty::ClauseKind::RegionOutlives(_) | ty::ClauseKind::TypeOutlives(..) => true,
            _ => false,
        })
}

fn has_complex_type(fn_def_id: impl Into<DefId>, tcx: TyCtxt<'_>) -> bool {
    let fn_def_id: DefId = fn_def_id.into();
    let fn_sig = tcx.fn_sig(fn_def_id);
    fn_sig
        .instantiate_identity()
        .inputs_and_output()
        .iter()
        .any(|ty| match ty.skip_binder().kind() {
            TyKind::Adt(adt_def, args) => {
                args.iter().filter(|arg| arg.as_region().is_some()).count() >= 1
            }
            _ => false,
        })
}

impl<'tcx> FnVisitor<'tcx> {
    pub fn new(tcx: TyCtxt<'tcx>) -> FnVisitor<'tcx> {
        FnVisitor {
            tcx,
            stats: Statistics::default(),
            lifetime_info: Vec::new(),
        }
    }
    pub fn statistic(self) -> Statistics<'tcx> {
        self.stats
    }
    fn work_at_fn<'v>(
        &mut self,
        fk: FnKind<'v>,
        fd: &'v FnDecl<'v>,
        b: BodyId,
        span: Span,
        id: LocalDefId,
    ) {
        let fn_did = id.to_def_id();
        rap_debug!("API path: {}", self.tcx.def_path_str(fn_did));
        rap_debug!(
            "fn_sig: {}",
            self.tcx.type_of(fn_did).instantiate_identity()
        );
        rap_debug!(
            "visibility: {:?}",
            self.tcx
                .effective_visibilities(())
                .effective_vis(fn_did.as_local().unwrap())
        );

        if !is_api_public(fn_did, self.tcx) {
            rap_debug!("skip for not public API");
            return;
        }

        let is_api_has_multi_lifetime_params = is_api_has_multi_lifetime_params(fn_did, self.tcx);
        let is_api_has_outlive_pred = has_outlive_pred(fn_did, self.tcx);
        let is_api_has_complex_type = has_complex_type(fn_did, self.tcx);

        rap_debug!(
            "is_api_has_multi_lifetime_params: {}, is_api_has_outlive_pred: {}, is_api_has_complex_type: {}",
            is_api_has_multi_lifetime_params,
            is_api_has_outlive_pred,
            is_api_has_complex_type
        );

        self.lifetime_info.push(ApiLifetimeInfo {
            path: self.tcx.def_path_str(fn_did),
            num_lifetime_params: num_lifetime_params(fn_did, self.tcx)
                + num_late_bound_lifetime_params(fn_did, self.tcx),
            has_outlive_pred: is_api_has_outlive_pred,
            has_compound_type: is_api_has_complex_type,
        });

        let is_type_generic = self
            .tcx
            .generics_of(fn_did)
            .requires_monomorphization(self.tcx);
        let fn_sig = self.tcx.fn_sig(fn_did);
        for input in fn_sig.instantiate_identity().inputs_and_output().iter() {
            rap_debug!("param: {:?}", input);
            let input_ty = input.skip_binder();
            if let TyKind::Ref(r, ty, _) = input.skip_binder().kind() {
                rap_debug!("region kind: {:?} {:?}", r.type_flags(), r.kind());
                match r.kind() {
                    ty::ReEarlyParam(re) => {
                        rap_debug!("ReEarlyParam: {:?}", re);
                    }
                    ty::ReBound(idx, bound) => {
                        rap_debug!("ReBound: {:?} {:?}", idx, bound);
                    }
                    _ => {}
                }
            }
        }

        rap_debug!("type(debug): {:?}", self.tcx.type_of(fn_did));
        rap_debug!("fn_sig(debug): {:?}", fn_sig);
        let late_fn_sig = self
            .tcx
            .liberate_late_bound_regions(fn_did, fn_sig.instantiate_identity());
        rap_debug!("late_fn_sig: {:?}", late_fn_sig);

        if is_type_generic {
            self.stats.pub_generic_api.insert(fn_did);
        } else {
            self.stats.pub_non_generic_api.insert(fn_did);
        }

        if fk.header().map_or(false, |header| header.is_unsafe()) {
            self.stats.pub_unsafe_api.insert(fn_did);
        }
    }

    pub fn dump_lifetime_info(&self, mut writer: impl Write) -> std::io::Result<()> {
        serde_json::to_writer_pretty(&mut writer, &self.lifetime_info)?;
        Ok(())
    }
}

impl<'tcx> Visitor<'tcx> for FnVisitor<'tcx> {
    type NestedFilter = nested_filter::OnlyBodies;

    fn maybe_tcx(&mut self) -> Self::MaybeTyCtxt {
        self.tcx
    }

    fn visit_fn(
        &mut self,
        fk: FnKind<'tcx>,
        fd: &'tcx FnDecl<'tcx>,
        b: BodyId,
        span: Span,
        id: LocalDefId,
    ) -> Self::Result {
        self.work_at_fn(fk, fd, b, span, id);
        walk_fn(self, fk, fd, b, id);
    }

    fn visit_block(&mut self, b: &'tcx rustc_hir::Block<'tcx>) -> Self::Result {
        let r = b.rules;
        if matches!(r, rustc_hir::BlockCheckMode::UnsafeBlock(_)) {
            self.stats.unsafe_block.push(*b)
        }
        walk_block(self, b);
    }
}
