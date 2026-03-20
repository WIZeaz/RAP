use rustc_hir::LangItem;
use rustc_middle::ty::{self, Ty, TyCtxt};
use rustc_span::sym;

pub fn std_vec<'tcx>(element_ty: Ty<'tcx>, tcx: TyCtxt<'tcx>) -> Option<Ty<'tcx>> {
    let vec_def_id = tcx.get_diagnostic_item(sym::Vec)?;
    let alloc_def_id = tcx.lang_items().global_alloc_ty()?;
    let alloc_ty = tcx.type_of(alloc_def_id).skip_binder();
    let args = tcx.mk_args(&[
        ty::GenericArg::from(element_ty),
        ty::GenericArg::from(alloc_ty),
    ]);
    Some(Ty::new_adt(tcx, tcx.adt_def(vec_def_id), args))
}

pub fn std_string<'tcx>(tcx: TyCtxt<'tcx>) -> Option<Ty<'tcx>> {
    let string_def_id = tcx.lang_items().string()?;
    Some(tcx.type_of(string_def_id).skip_binder())
}
