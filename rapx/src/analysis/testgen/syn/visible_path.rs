use crate::rustc_middle::ty::print::PrintTraitRefExt;
use crate::{def_id, rap_error};
use rustc_hir::def::DefKind;
use rustc_hir::def_id::DefId;
use rustc_middle::ty::{
    AssocItemContainer, GenericArgKind, GenericArgsRef, GenericParamDefKind, TyCtxt, TyKind,
};

pub fn get_visible_path_with_args<'tcx>(
    tcx: TyCtxt<'tcx>,
    def_id: DefId,
    args: GenericArgsRef<'tcx>,
) -> String {
    // Distinguish by DefKind: free functions vs associated functions
    match tcx.def_kind(def_id) {
        DefKind::AssocFn => {
            // Associated function/method
            return format_assoc_path_with_args(tcx, def_id, args);
        }
        DefKind::Fn => {
            // Regular function
            let base_path = get_fn_visible_path(tcx, def_id);
            return format_fn_visible_path_with_args(tcx, def_id, args, base_path);
        }
        _ => {
            let def_path = tcx.def_path_str(def_id);
            rap_error!(
                "At get_visible_with_args: DefId {:?} is neither a function nor an associated function. Falling back to def path: {}",
                def_id,
                def_path
            );
            def_path
        }
    }
}

pub fn get_fn_visible_path<'tcx>(tcx: TyCtxt<'tcx>, def_id: DefId) -> String {
    if def_id.is_local() {
        // Find direct re-exported path
        let crate_def_id = rustc_hir::def_id::CRATE_DEF_ID.to_def_id();
        //rap_info!("The {:?} of crate_def_id is {:?}", def_id, crate_def_id);
        if let Some(reexport_name) = find_reexport_in_module(tcx, crate_def_id, def_id) {
            return reexport_name;
        }

        // If not found, check parent module's re-export and concatenate path
        if let Some(parent) = tcx.opt_parent(def_id) {
            if let Some(parent_reexport) = find_reexport_in_module(tcx, crate_def_id, parent) {
                if let Some(item_name) = tcx.opt_item_name(def_id) {
                    return format!("{}::{}", parent_reexport, item_name);
                } else {
                    let def_path = tcx.def_path_str(def_id);
                    rap_error!(
                        "At get_fn_visible_1: DefId {:?} has no item name, falling back to def path: {}",
                        def_id,
                        def_path
                    );
                    return def_path;
                }
            }

            // Traverse up the module hierarchy to find a re-export
            let mut current_parent = tcx.opt_parent(parent);
            while let Some(ancestor) = current_parent {
                if let Some(ancestor_reexport) =
                    find_reexport_in_module(tcx, crate_def_id, ancestor)
                {
                    // Get the relative path from ancestor to def_id
                    let relative_path = get_relative_path(tcx, ancestor, def_id);
                    return format!("{}::{}", ancestor_reexport, relative_path);
                }
                current_parent = tcx.opt_parent(ancestor);
            }
        }
    } else {
        // rap_error!(
        //     "At get_fn_visible_2: DefId {:?} is not local. Falling back to def path: {}",
        //     def_id,
        //     tcx.def_path_str(def_id)
        // );
    }
    let ret = tcx.def_path_str(def_id);
    // rap_error!(
    //     "Could not find re-export for {:?}, falling back to def path: {}",
    //     def_id,
    //     ret
    // );
    // Fallback to regular path
    ret
}

fn format_fn_visible_path_with_args<'tcx>(
    tcx: TyCtxt<'tcx>,
    def_id: DefId,
    args: GenericArgsRef<'tcx>,
    base_path: String,
) -> String {
    if args.is_empty() {
        return base_path;
    }
    let type_args: Vec<_> = args
        .iter()
        .filter_map(|arg| match arg.kind() {
            GenericArgKind::Type(ty) => Some(ty.to_string()),
            GenericArgKind::Const(ct) => Some(ct.to_string()),
            GenericArgKind::Lifetime(_) => None,
        })
        .collect();
    if type_args.is_empty() {
        base_path
    } else {
        format!("{}::<{}>", base_path, type_args.join(", "))
    }
}

fn find_reexport_in_module<'tcx>(
    tcx: TyCtxt<'tcx>,
    module_def_id: DefId,
    target_def_id: DefId,
) -> Option<String> {
    // Extract common logic to avoid code duplication
    let check_child = |child: &rustc_middle::metadata::ModChild| -> Option<String> {
        if child.res.opt_def_id() == Some(target_def_id)
            && child.vis.is_public()
            && child.ident.name != rustc_span::symbol::kw::Underscore
        {
            Some(child.ident.name.to_string())
        } else {
            None
        }
    };

    if let Some(local_id) = module_def_id.as_local() {
        tcx.module_children_local(local_id)
            .iter()
            .find_map(check_child)
    } else {
        tcx.module_children(rustc_hir::def_id::ModDefId::new_unchecked(module_def_id))
            .iter()
            .find_map(check_child)
    }
}

fn get_relative_path<'tcx>(tcx: TyCtxt<'tcx>, ancestor: DefId, target: DefId) -> String {
    let mut path_components = Vec::new();
    let mut current = target;

    while current != ancestor {
        let name = tcx.item_name(current).to_string();
        path_components.push(name);
        if let Some(parent) = tcx.opt_parent(current) {
            current = parent;
        } else {
            break;
        }
    }

    path_components.reverse();
    path_components.join("::")
}

/// Convert Ty to string, prioritizing re-export names for local ADTs
fn ty_to_string_with_visible_path<'tcx>(
    tcx: TyCtxt<'tcx>,
    ty: rustc_middle::ty::Ty<'tcx>,
) -> String {
    match ty.kind() {
        TyKind::Adt(adt_def, substs) => {
            let base = get_fn_visible_path(tcx, adt_def.did()); // Reuse function path finding logic
                                                                // Collect type/const arguments, ignoring lifetimes
            let mut parts: Vec<String> = Vec::new();
            for arg in substs.iter() {
                match arg.kind() {
                    GenericArgKind::Type(t) => parts.push(ty_to_string_with_visible_path(tcx, t)),
                    GenericArgKind::Const(c) => parts.push(c.to_string()),
                    GenericArgKind::Lifetime(_) => {}
                }
            }
            if parts.is_empty() {
                base
            } else {
                format!("{}::<{}>", base, parts.join(", "))
            }
        }
        _ => {
            //rap_info!("{:?} appear , TyKind:{:?}", ty, ty.kind());
            ty.to_string()
        }
    }
}

/// Count type/const parameters (ignoring lifetimes)
fn count_type_const_params<'tcx>(tcx: TyCtxt<'tcx>, def_id: DefId) -> usize {
    let generics = tcx.generics_of(def_id);
    generics
        .own_params
        .iter()
        .filter(|p| {
            matches!(
                p.kind,
                GenericParamDefKind::Type { .. } | GenericParamDefKind::Const { .. }
            )
        })
        .count()
}

fn get_assoc_visible_path<'tcx>(tcx: TyCtxt<'tcx>, def_id: DefId) -> String {
    let assoc = tcx.associated_item(def_id);
    let assoc_name = tcx
        .opt_item_name(def_id)
        .map(|s| s.to_string())
        .unwrap_or_else(|| {
            rap_error!(
                "At get_assoc_visible_path_1: Associated item DefId {:?} has no name, falling back to def path: {}",
                def_id,
                tcx.def_path_str(def_id)
            );
            tcx.def_path_str(def_id)
        });

    match assoc.container {
        AssocItemContainer::Trait => {
            let trait_def_id = match assoc.trait_container(tcx) {
                Some(did) => did,
                None => {
                    rap_error!(
                        "At get_assoc_visible_path_2: AssocItemContainer::Trait but no trait container for DefId {:?}, falling back to def path: {}",
                        def_id,
                        tcx.def_path_str(def_id)
                    );
                    return tcx.def_path_str(def_id);
                }
            };
            let trait_path = get_fn_visible_path(tcx, trait_def_id);
            format!("{}::{}", trait_path, assoc_name)
        }

        AssocItemContainer::Impl => {
            let impl_def_id = match assoc.impl_container(tcx) {
                Some(did) => did,
                None => {
                    rap_error!(
                        "At get_assoc_visible_path_3: AssocItemContainer::Impl but no impl container for DefId {:?}, falling back to def path: {}",
                        def_id,
                        tcx.def_path_str(def_id)
                    );
                    return tcx.def_path_str(def_id);
                }
            };

            let self_ty = tcx.type_of(impl_def_id).instantiate_identity();
            let self_ty_str = ty_to_string_with_visible_path(tcx, self_ty);

            //  Self::method format
            format!("{}::{}", self_ty_str, assoc_name)
        }
    }
}

fn format_assoc_path_with_args<'tcx>(
    tcx: TyCtxt<'tcx>,
    assoc_def_id: DefId,
    args: GenericArgsRef<'tcx>,
) -> String {
    let assoc = tcx.associated_item(assoc_def_id);

    let type_args: Vec<String> = args
        .iter()
        .filter_map(|arg| match arg.kind() {
            GenericArgKind::Type(ty) => Some(ty.to_string()),
            GenericArgKind::Const(ct) => Some(ct.to_string()),
            GenericArgKind::Lifetime(_) => None,
        })
        .collect();

    let assoc_name = tcx
        .opt_item_name(assoc_def_id)
        .map(|s| s.to_string())
        .unwrap_or_else(|| {
            rap_error!(
                "At format_assoc_1: Associated item DefId {:?} has no name, falling back to def path: {}",
                assoc_def_id,
                tcx.def_path_str(assoc_def_id)
            );
            "unknown_method".to_string()
        });

    match assoc.container {
        // Trait: Use qualified path, for this situation, we think this method can be called directly without some types impl this trait
        AssocItemContainer::Trait => {
            let trait_def_id = match assoc.trait_container(tcx) {
                Some(did) => did,
                None => {
                    rap_error!(
                        "At format_assoc_2: AssocItemContainer::Trait but no trait container for DefId {:?}, falling back to def path: {}",
                        assoc_def_id,
                        tcx.def_path_str(assoc_def_id)
                    );
                    panic!("Inconsistent state: AssocItemContainer::Trait but no trait container");
                }
            };
            let trait_path = get_fn_visible_path(tcx, trait_def_id);

            let method_gen = if type_args.len() > 0 {
                format!("::<{}>", type_args.join(", "))
            } else {
                String::new()
            };

            let self_ty = assoc.name(); // Now don't know name() returns what a symbol
            format!(
                "<{} as {}>::{}{}",
                self_ty, trait_path, assoc_name, method_gen
            )
        }

        // Impl: If Trait, Use qualified path; If methods, use type::method()
        AssocItemContainer::Impl => {
            let impl_def_id = assoc.impl_container(tcx).unwrap();

            if let Some(trait_ref) = tcx.impl_trait_ref(impl_def_id) {
                let trait_ref = trait_ref.instantiate(tcx, args);
                let trait_with_generics = trait_ref.print_trait_sugared().to_string();
                let self_ty = trait_ref.self_ty();
                //let trait_path = get_fn_visible_path(tcx, trait_ref.def_id);
                //let self_ty_str = ty_to_string_with_visible_path(tcx, self_ty);

                let impl_generics = tcx.generics_of(impl_def_id);
                let method_args = &args[impl_generics.count()..];
                //rap_info!("trait_ref: {:?}, trait_with_generics: {:?}, self_ty: {:?}, trait_path: {}, self_ty_str: {}, impl_generics: {:?}, method_args: {:?}", trait_ref, trait_with_generics, self_ty, trait_path, self_ty_str, impl_generics, method_args);
                let method_gen = if method_args.is_empty() {
                    String::new()
                } else {
                    let method_type_args: Vec<String> = method_args
                        .iter()
                        .filter_map(|arg| match arg.kind() {
                            GenericArgKind::Type(ty) => Some(ty.to_string()),
                            GenericArgKind::Const(ct) => Some(ct.to_string()),
                            GenericArgKind::Lifetime(_) => None,
                        })
                        .collect();
                    if method_type_args.is_empty() {
                        String::new()
                    } else {
                        format!("::<{}>", method_type_args.join(", "))
                    }
                };
                return format!(
                    "<{} as {}>::{}{}",
                    self_ty, trait_with_generics, assoc_name, method_gen
                );
            } else {
                let impl_param_cnt = count_type_const_params(tcx, impl_def_id);

                let self_ty_str = if type_args.is_empty() {
                    // use original Self type without generics
                    let self_ty = tcx.type_of(impl_def_id).instantiate_identity();
                    ty_to_string_with_visible_path(tcx, self_ty)
                } else {
                    // use monomorphized Self type: construct Self type from the first few args
                    let self_ty = tcx.type_of(impl_def_id).instantiate_identity();
                    construct_monomorphized_self_type(tcx, self_ty, &type_args, impl_param_cnt)
                };

                let method_args = if type_args.len() > impl_param_cnt {
                    &type_args[impl_param_cnt..]
                } else {
                    &[][..]
                };

                let method_gen = if method_args.is_empty() {
                    String::new()
                } else {
                    format!("::<{}>", method_args.join(", "))
                };

                return format!("{}::{}{}", self_ty_str, assoc_name, method_gen);
            }
        }
    }
}

/// Construct monomorphized Self type string
fn construct_monomorphized_self_type<'tcx>(
    tcx: TyCtxt<'tcx>,
    self_ty: rustc_middle::ty::Ty<'tcx>,
    type_args: &[String],
    impl_param_cnt: usize,
) -> String {
    match self_ty.kind() {
        TyKind::Adt(adt_def, _) => {
            let base_name = get_fn_visible_path(tcx, adt_def.did());

            // Extract the first impl_param_cnt parameters as type parameters
            let self_type_args = if type_args.len() >= impl_param_cnt && impl_param_cnt > 0 {
                &type_args[..impl_param_cnt]
            } else {
                &[][..]
            };

            if self_type_args.is_empty() {
                base_name
            } else {
                format!("{}::<{}>", base_name, self_type_args.join(", "))
            }
        }
        _ => {
            // For non-ADT types, use string representation directly
            self_ty.to_string()
        }
    }
}
