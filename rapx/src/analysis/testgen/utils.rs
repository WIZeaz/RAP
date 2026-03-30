pub use crate::analysis::core::api_dependency::{is_def_id_directly_public, is_fuzzable_ty};
use rustc_hir::{BodyOwnerKind, def_id::DefId};
use rustc_infer::infer::TyCtxtInferExt as _;
use rustc_middle::ty::{self, FnSig, ParamEnv, Ty, TyCtxt, TyKind};
use rustc_span::STDLIB_STABLE_CRATES;
use rustc_trait_selection::infer::InferCtxtExt;

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
    let ty1 = tcx.erase_and_anonymize_regions(ty1);
    let ty2 = tcx.erase_and_anonymize_regions(ty2);
    return ty1 == ty2;
}

pub fn fn_sig_with_identities<'tcx>(fn_did: DefId, tcx: TyCtxt<'tcx>) -> FnSig<'tcx> {
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

pub fn is_env_var_exist(var_name: &str) -> bool {
    match std::env::var(var_name) {
        Ok(_) => true,
        Err(_) => false,
    }
}

pub fn visit_ty_fields_while<'tcx>(
    ty: Ty<'tcx>,
    tcx: TyCtxt<'tcx>,
    f: &mut impl FnMut(Ty<'tcx>) -> bool,
) {
    if !f(ty) {
        return;
    }
    match ty.kind() {
        TyKind::RawPtr(inner_ty, _) | TyKind::Ref(_, inner_ty, _) => {
            if !f(*inner_ty) {
                return;
            }
        }
        TyKind::Array(inner_ty, _) | TyKind::Slice(inner_ty) => {
            visit_ty_fields_while(*inner_ty, tcx, f);
        }

        // Tuple
        TyKind::Tuple(tys) => tys
            .iter()
            .for_each(|inner_ty| visit_ty_fields_while(inner_ty, tcx, f)),

        // ADT
        TyKind::Adt(adt_def, substs) => {
            adt_def.all_fields().for_each(|field| {
                visit_ty_fields_while(field.ty(tcx, &substs), tcx, f);
            });
        }
        _ => {}
    }
}

pub fn def_id_from_std<'tcx>(def_id: DefId, tcx: TyCtxt<'tcx>) -> bool {
    let crate_name = tcx.crate_name(def_id.krate);
    STDLIB_STABLE_CRATES.contains(&crate_name)
}
