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
            let base_path = get_assoc_visible_path(tcx, def_id);
            if args.is_empty() {
                return base_path;
            }
            return format_assoc_path_with_args(tcx, def_id, args, base_path);
        }
        DefKind::Fn => {
            // Regular function
            let base_path = get_fn_visible_path(tcx, def_id);
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
        rap_error!(
            "At get_fn_visible_2: DefId {:?} is not local. Falling back to def path: {}",
            def_id,
            tcx.def_path_str(def_id)
        );
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
            rap_info!("{:?} appear , TyKind:{:?}", ty, ty.kind());
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
            "unknown_method".to_string()
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
    base_path: String,
) -> String {
    let assoc = tcx.associated_item(assoc_def_id);

    // 收集类型/常量参数（忽略生命周期）
    let type_args: Vec<String> = args
        .iter()
        .filter_map(|arg| match arg.kind() {
            GenericArgKind::Type(ty) => Some(ty_to_string_with_visible_path(tcx, ty)),
            GenericArgKind::Const(ct) => Some(ct.to_string()),
            GenericArgKind::Lifetime(_) => None,
        })
        .collect();

    if type_args.is_empty() {
        return base_path;
    }

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
        // Trait 容器：<Self as Trait>::method::<MethodArgs>
        AssocItemContainer::Trait => {
            let trait_def_id = match assoc.trait_container(tcx) {
                Some(did) => did,
                None => {
                    rap_error!(
                        "At format_assoc_2: AssocItemContainer::Trait but no trait container for DefId {:?}, falling back to def path: {}",
                        assoc_def_id,
                        tcx.def_path_str(assoc_def_id)
                    );
                    return base_path;
                }
            };
            let trait_path = get_fn_visible_path(tcx, trait_def_id);

            // 第一个类型参数通常是 Self
            let self_ty_str = type_args.get(0).cloned().unwrap_or_default();
            if self_ty_str.is_empty() {
                return base_path;
            }

            // 剩余参数作为方法泛型
            let method_gen = if type_args.len() > 1 {
                format!("::<{}>", type_args[1..].join(", "))
            } else {
                String::new()
            };

            format!(
                "<{} as {}>::{}{}",
                self_ty_str, trait_path, assoc_name, method_gen
            )
        }

        // Impl 容器：统一使用 Self::method 格式（不区分 trait impl 和固有 impl）
        AssocItemContainer::Impl => {
            let impl_def_id = match assoc.impl_container(tcx) {
                Some(did) => did,
                None => return base_path,
            };

            // 获取 impl 的类型/常量参数数量
            let impl_param_cnt = count_type_const_params(tcx, impl_def_id);

            // 构造单态化的 Self 类型
            let self_ty_str = if type_args.is_empty() {
                // 如果没有类型参数，使用原始类型
                let self_ty = tcx.type_of(impl_def_id).instantiate_identity();
                ty_to_string_with_visible_path(tcx, self_ty)
            } else {
                // 使用单态化后的 Self 类型：从 args 的前几个参数构造 Self 类型
                let self_ty = tcx.type_of(impl_def_id).instantiate_identity();
                construct_monomorphized_self_type(tcx, self_ty, &type_args, impl_param_cnt)
            };

            // 统一处理：Self::method::<MethodArgs> 格式
            // 方法泛型参数：跳过前 impl_param_cnt 个参数（属于 Self 类型）
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

            format!("{}::{}{}", self_ty_str, assoc_name, method_gen)
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

/// Replace generic placeholders in a path that already contains generics
fn replace_generics_in_path(
    path: String,
    type_args: &[String],
    impl_params_count: usize,
) -> String {
    //rap_info!("Replacing generics in path: {}", path);

    // Split type args between impl generics and method generics
    let (impl_args, method_args) = if type_args.len() <= impl_params_count {
        (type_args, &[][..])
    } else {
        let split_point = impl_params_count;
        (&type_args[..split_point], &type_args[split_point..])
    };

    // rap_info!(
    //     "Split for replacement - impl: {:?}, method: {:?}",
    //     impl_args,
    //     method_args
    // );

    // Handle patterns like "S::<T>::foo" -> "S::<u128>::foo::<u16>"
    let mut result = path;

    // Step 1: Replace the first ::<...> (impl generics) with actual types
    if !impl_args.is_empty() {
        if let Some(start) = result.find("::<") {
            if let Some(end_pos) = find_matching_angle_bracket(&result, start + 3) {
                let replacement = format!("::<{}>", impl_args.join(", "));
                result.replace_range(start..end_pos + 1, &replacement);
                //rap_info!("After impl replacement: {}", result);
            }
        }
    } else {
        // If no impl args, remove existing impl generics placeholder
        if let Some(start) = result.find("::<") {
            if let Some(end_pos) = find_matching_angle_bracket(&result, start + 3) {
                result.replace_range(start..end_pos + 1, "");
                //rap_info!("After removing impl placeholder: {}", result);
            }
        }
    }

    // Step 2: Add method generics at the end if needed
    if !method_args.is_empty() {
        let additional_capacity =
            3 + method_args.iter().map(|s| s.len()).sum::<usize>() + (method_args.len() - 1) * 2;
        result.reserve(additional_capacity);
        result.push_str("::<");
        for (i, arg) in method_args.iter().enumerate() {
            if i > 0 {
                result.push_str(", ");
            }
            result.push_str(arg);
        }
        result.push('>');
        //rap_info!("After adding method generics: {}", result);
    }

    //rap_info!("Final replaced generics result: {}", result);
    result
}

/// Find the matching closing angle bracket for generics, handling nested brackets
fn find_matching_angle_bracket(s: &str, start: usize) -> Option<usize> {
    // Avoid allocating Vec<char>, use char_indices instead
    let mut depth = 1;

    for (i, ch) in s[start..].char_indices() {
        match ch {
            '<' => depth += 1,
            '>' => {
                depth -= 1;
                if depth == 0 {
                    return Some(start + i);
                }
            }
            _ => {}
        }
    }
    None
}