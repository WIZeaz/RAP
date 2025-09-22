use rustc_hir::def::Namespace;
use rustc_hir::def_id::{DefId, DefIndex};
use rustc_middle::ty::print::{FmtPrinter, PrettyPrinter, PrintError, Printer};
use rustc_middle::ty::{GenericArgsRef, TyCtxt};

pub fn get_visible_path_with_args<'tcx>(
    tcx: TyCtxt<'tcx>,
    def_id: DefId,
    args: GenericArgsRef<'tcx>,
) -> String {
    let base_path = get_visible_path(tcx, def_id);

    // Add generic args
    if !args.is_empty() {
        let type_args: Vec<String> = args
            .iter()
            .filter_map(|arg| {
                match arg.kind() {
                    rustc_middle::ty::GenericArgKind::Type(ty) => Some(format!("{}", ty)),
                    rustc_middle::ty::GenericArgKind::Const(ct) => Some(format!("{}", ct)),
                    // Omit lifetimes
                    rustc_middle::ty::GenericArgKind::Lifetime(_) => None,
                }
            })
            .collect();

        if !type_args.is_empty() {
            return format!("{}::<{}>", base_path, type_args.join(", "));
        }
    }

    base_path
}

pub fn get_visible_path<'tcx>(tcx: TyCtxt<'tcx>, def_id: DefId) -> String {
    // For local items, search through all modules to find re-exports
    if def_id.is_local() {
        // Start from the crate root and search for re-exports
        let crate_def_id = rustc_hir::def_id::CRATE_DEF_ID.to_def_id();
        if let Some(reexport_name) = find_reexport_in_module(tcx, crate_def_id, def_id) {
            return reexport_name;
        }

        // Also check parent modules recursively
        let mut current_parent = tcx.opt_parent(def_id);
        while let Some(parent) = current_parent {
            if let Some(reexport_name) = find_reexport_in_module(tcx, parent, def_id) {
                return reexport_name;
            }
            current_parent = tcx.opt_parent(parent);
        }
    }
    let ret = tcx.def_path_str(def_id);
    rap_error!(
        "Could not find re-export for {:?}, falling back to def path: {}",
        def_id,
        ret
    );
    // Fallback to regular path
    ret
}

fn find_reexport_in_module<'tcx>(
    tcx: TyCtxt<'tcx>,
    module_def_id: DefId,
    target_def_id: DefId,
) -> Option<String> {
    if let Some(module_def_id) = module_def_id.as_local() {
        let children = tcx.module_children_local(module_def_id);
        for child in children.iter() {
            if child.res.opt_def_id() == Some(target_def_id)
                && child.vis.is_public()
                && child.ident.name != rustc_span::symbol::kw::Underscore
            {
                return Some(child.ident.name.to_string());
            }
        }
    } else {
        // For non-local modules, use the regular module_children query
        let children =
            tcx.module_children(rustc_hir::def_id::ModDefId::new_unchecked(module_def_id));
        for child in children.iter() {
            if child.res.opt_def_id() == Some(target_def_id)
                && child.vis.is_public()
                && child.ident.name != rustc_span::symbol::kw::Underscore
            {
                return Some(child.ident.name.to_string());
            }
        }
    }
    None
}
