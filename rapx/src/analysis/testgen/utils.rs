pub use crate::analysis::core::api_dep::is_api_public;
use crate::{
    analysis::core::api_dep::{ApiDepGraph, DepNode},
    rap_debug, rap_info,
};
use rustc_hir::{
    def_id::{DefId, LocalDefId, LOCAL_CRATE},
    BodyOwnerKind, ItemKind,
};
use rustc_infer::infer::TyCtxtInferExt as _;
use rustc_middle::{
    query::cached::effective_visibilities,
    ty::{
        self, AdtFlags, FnSig, ParamEnv, Ty, TyCtxt, TyKind, TypeFoldable, TypeVisitable,
        TypeVisitor, TypingEnv,
    },
};
use rustc_trait_selection::infer::InferCtxtExt;
use std::collections::VecDeque;

/// return all DefId of all pub APIs
pub fn get_all_pub_apis(tcx: TyCtxt<'_>) -> Vec<DefId> {
    let mut apis = Vec::new();

    for local_def_id in tcx.hir_body_owners() {
        if matches!(tcx.hir_body_owner_kind(local_def_id), BodyOwnerKind::Fn)
            && is_api_public(local_def_id, tcx)
        {
            // tcx.hir().
            apis.push(local_def_id.to_def_id());
        }
    }
    apis
}

pub fn fn_requires_monomorphization<'tcx>(fn_did: DefId, tcx: TyCtxt<'_>) -> bool {
    tcx.generics_of(fn_did).requires_monomorphization(tcx)
}

pub fn is_ty_impl_copy<'tcx>(ty: Ty<'tcx>, tcx: TyCtxt<'tcx>) -> bool {
    let infcx = tcx.infer_ctxt().build(ty::TypingMode::PostAnalysis);
    let param_env = ParamEnv::empty();
    infcx.type_is_copy_modulo_regions(param_env, ty)
    // let copy_trait = tcx.require_lang_item(rustc_hir::LangItem::Copy, None);
    // let copy_pred = ty::TraitRef::new(tcx, copy_trait, vec![ty]);
    // let obligation = Obligation::new(tcx, ObligationCause::dummy(), param_env, copy_pred);
    // infcx.predicate_must_hold_modulo_regions(&obligation)
    // tcx.type_is_copy_modulo_regions(ty::TypingMode::PostAnalysis, ty)
}

pub fn is_ty_eq<'tcx>(ty1: Ty<'tcx>, ty2: Ty<'tcx>, tcx: TyCtxt<'tcx>) -> bool {
    let ty1 = tcx.erase_regions(ty1);
    let ty2 = tcx.erase_regions(ty2);
    return ty1 == ty2;
}

pub fn is_fuzzable_ty<'tcx>(ty: Ty<'tcx>, tcx: TyCtxt<'tcx>) -> bool {
    match ty.kind() {
        // Basical data type
        TyKind::Bool
        | TyKind::Char
        | TyKind::Int(_)
        | TyKind::Uint(_)
        | TyKind::Float(_)
        | TyKind::Str => true,

        // Infer
        TyKind::Infer(
            ty::InferTy::IntVar(_)
            | ty::InferTy::FreshIntTy(_)
            | ty::InferTy::FloatVar(_)
            | ty::InferTy::FreshFloatTy(_),
        ) => true,

        // Reference, Array, Slice
        TyKind::Ref(_, inner_ty, _) | TyKind::Array(inner_ty, _) | TyKind::Slice(inner_ty) => {
            is_fuzzable_ty(inner_ty.peel_refs(), tcx)
        }

        // Tuple
        TyKind::Tuple(tys) => tys
            .iter()
            .all(|inner_ty| is_fuzzable_ty(inner_ty.peel_refs(), tcx)),

        // ADT
        TyKind::Adt(adt_def, substs) => {
            if adt_def.is_struct() {
                // 检查所有字段是否为 pub 且类型可 Fuzz
                adt_def.all_fields().all(|field| {
                    field.vis.is_public() && // 字段必须是 pub
                    is_fuzzable_ty(field.ty(tcx, substs).peel_refs(), tcx)
                })
            } else if adt_def.is_enum() {
                adt_def.variants().iter().all(|variant| {
                    variant
                        .fields
                        .iter()
                        .all(|field| is_fuzzable_ty(field.ty(tcx, substs).peel_refs(), tcx))
                })
            } else {
                false // union 暂不处理
            }
        }

        // 其他类型默认不可 Fuzz
        _ => false,
    }
}

pub fn fn_sig_without_binders<'tcx>(fn_did: DefId, tcx: TyCtxt<'tcx>) -> FnSig<'tcx> {
    let early_fn_sig = tcx.fn_sig(fn_did);
    let binder_fn_sig = early_fn_sig.instantiate_identity();
    tcx.liberate_late_bound_regions(fn_did, binder_fn_sig)
}

pub fn fn_sig_with_generic_args<'tcx>(
    fn_did: DefId,
    args: &[ty::GenericArg<'tcx>],
    tcx: TyCtxt<'tcx>,
) -> FnSig<'tcx> {
    let early_fn_sig = tcx.fn_sig(fn_did);
    let binder_fn_sig = early_fn_sig.instantiate(tcx, args);
    tcx.liberate_late_bound_regions(fn_did, binder_fn_sig)
}

#[derive(Debug, Copy, Clone, Default)]
pub struct PtrCheckResult {
    pub has_any_ptr: bool,
    pub has_raw_ptr: bool,
}

impl PtrCheckResult {
    fn or(self, other: Self) -> Self {
        PtrCheckResult {
            has_any_ptr: self.has_any_ptr || other.has_any_ptr,
            has_raw_ptr: self.has_raw_ptr || other.has_raw_ptr,
        }
    }

    pub fn has_ref(&self) -> bool {
        self.has_any_ptr && !self.has_raw_ptr
    }

    pub fn has_raw_ptr(&self) -> bool {
        self.has_raw_ptr
    }
}

pub fn ty_check_ptr<'tcx>(ty: Ty<'tcx>, tcx: TyCtxt<'tcx>) -> PtrCheckResult {
    let mut res = PtrCheckResult::default();
    res.has_any_ptr = ty.is_any_ptr();
    res.has_raw_ptr = ty.is_raw_ptr();

    match ty.kind() {
        // Reference, Array, Slice
        TyKind::Ref(_, inner_ty, _) | TyKind::Array(inner_ty, _) | TyKind::Slice(inner_ty) => {
            res.or(ty_check_ptr(*inner_ty, tcx))
        }

        // Tuple
        TyKind::Tuple(tys) => tys.iter().fold(PtrCheckResult::default(), |res, inner_ty| {
            res.or(ty_check_ptr(inner_ty, tcx))
        }),

        // ADT
        TyKind::Adt(adt_def, substs) => {
            if adt_def.is_struct() {
                // 检查所有字段是否为 pub 且类型可 Fuzz
                adt_def.all_fields().fold(res, |res, inner_ty| {
                    res.or(ty_check_ptr(inner_ty.ty(tcx, substs), tcx))
                })
            } else if adt_def.is_enum() {
                adt_def
                    .variants()
                    .iter()
                    .fold(res, |res: PtrCheckResult, variant| {
                        variant.fields.iter().fold(res, |res, inner_ty| {
                            res.or(ty_check_ptr(inner_ty.ty(tcx, substs), tcx))
                        })
                    })
            } else {
                // union 暂不处理
                PtrCheckResult::default()
            }
        }
        _ => res,
    }
}

/// only count local api
pub fn estimate_max_coverage<'tcx>(graph: &ApiDepGraph<'tcx>, tcx: TyCtxt<'tcx>) -> (usize, usize) {
    let inner_graph = graph.inner_graph();
    let num_total = get_all_pub_apis(tcx).len();
    let mut num_reachable = 0;
    let mut reachable = vec![false; inner_graph.node_count()];
    let mut worklist = VecDeque::from_iter(inner_graph.node_indices().filter(|index| {
        match inner_graph[*index] {
            DepNode::Ty(ty) => {
                if is_fuzzable_ty(ty.ty(), tcx) {
                    reachable[index.index()] = true;
                    return true;
                }
            }
            DepNode::Api(fn_did, _) => {
                if fn_requires_monomorphization(fn_did, tcx) {
                    return false;
                }
                if fn_sig_without_binders(fn_did, tcx).inputs().len() == 0 {
                    return true;
                }
            }
            _ => {}
        }

        false
    }));

    // initialize queue with fuzzable type
    while let Some(index) = worklist.pop_front() {
        if let DepNode::Api(did, _) = inner_graph[index] {
            if did.is_local() {
                num_reachable += 1;
            }
        }

        for next in inner_graph.neighbors(index) {
            match inner_graph[next] {
                DepNode::Ty(_) => {
                    if !reachable[next.index()] {
                        reachable[next.index()] = true;
                        worklist.push_back(next);
                    }
                }
                DepNode::Api(fn_did, _) => {
                    // regard the function as unreachalbe if it need monomorphization
                    if fn_requires_monomorphization(fn_did, tcx) {
                        continue;
                    }

                    if reachable[next.index()] {
                        continue;
                    }

                    let mut flag = true;
                    for nnbor in inner_graph.neighbors_directed(next, petgraph::Direction::Incoming)
                    {
                        if inner_graph[nnbor].is_ty() && !reachable[nnbor.index()] {
                            flag = false;
                            break;
                        }
                    }

                    if flag {
                        reachable[next.index()] = true;
                        worklist.push_back(next);
                    }
                }
                _ => {}
            }
        }
    }
    (num_reachable, num_total)
}

pub fn visit_ty_while<'tcx>(ty: Ty<'tcx>, tcx: TyCtxt<'tcx>, f: &mut impl FnMut(Ty<'tcx>) -> bool) {
    if !f(ty) {
        return;
    }
    match ty.kind() {
        TyKind::Ref(_, inner_ty, _) | TyKind::Array(inner_ty, _) | TyKind::Slice(inner_ty) => {
            visit_ty_while(*inner_ty, tcx, f);
        }

        // Tuple
        TyKind::Tuple(tys) => tys
            .iter()
            .for_each(|inner_ty| visit_ty_while(inner_ty, tcx, f)),

        // ADT
        TyKind::Adt(adt_def, substs) => {
            adt_def.all_fields().for_each(|field| {
                visit_ty_while(field.ty(tcx, &substs), tcx, f);
            });
        }
        _ => {}
    }
}
