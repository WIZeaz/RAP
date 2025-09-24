use crate::rap_error;
use rustc_hir::def_id::DefId;
use rustc_middle::ty::{GenericArgsRef, TyCtxt};

pub fn get_visible_path_with_args<'tcx>(
    tcx: TyCtxt<'tcx>,
    def_id: DefId,
    args: GenericArgsRef<'tcx>,
) -> String {
    // Check if this is a method call (has a parent impl block)
    let is_method = is_method_def(tcx, def_id);

    let base_path = get_visible_path(tcx, def_id);
    if !args.is_empty() {
        if is_method {
            // For methods, we need to separate impl generics from method generics
            // rap_info!(
            //     "Formatting method path for Path {:?} with args {:?}",
            //     base_path,
            //     args
            // );
            return format_method_path_with_args(tcx, def_id, args, base_path);
        } else {
            // For regular functions/types, treat all args as function generics
            // Use iterator chain to avoid intermediate Vec allocation
            let type_args: Vec<_> = args
                .iter()
                .filter_map(|arg| {
                    match arg.kind() {
                        rustc_middle::ty::GenericArgKind::Type(ty) => Some(ty.to_string()),
                        rustc_middle::ty::GenericArgKind::Const(ct) => Some(ct.to_string()),
                        // Omit lifetimes
                        rustc_middle::ty::GenericArgKind::Lifetime(_) => None,
                    }
                })
                .collect();

            if !type_args.is_empty() {
                // Pre-calculate capacity to avoid reallocations
                let capacity = base_path.len()
                    + 5
                    + type_args.iter().map(|s| s.len()).sum::<usize>()
                    + (type_args.len() - 1) * 2;
                let mut result = String::with_capacity(capacity);
                result.push_str(&base_path);
                result.push_str("::<");
                for (i, arg) in type_args.iter().enumerate() {
                    if i > 0 {
                        result.push_str(", ");
                    }
                    result.push_str(arg);
                }
                result.push('>');
                return result;
            }
        }
    }

    base_path
}

pub fn get_visible_path<'tcx>(tcx: TyCtxt<'tcx>, def_id: DefId) -> String {
    if def_id.is_local() {
        // find direct re-exported path
        let crate_def_id = rustc_hir::def_id::CRATE_DEF_ID.to_def_id();
        //rap_info!("The {:?} of crate_def_id is {:?}", def_id, crate_def_id);
        if let Some(reexport_name) = find_reexport_in_module(tcx, crate_def_id, def_id) {
            return reexport_name;
        }

        // If not found, check parent module's re-export and concatenate path
        if let Some(parent) = tcx.opt_parent(def_id) {
            if let Some(parent_reexport) = find_reexport_in_module(tcx, crate_def_id, parent) {
                let item_name = tcx.item_name(def_id);
                return format!("{}::{}", parent_reexport, item_name);
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
        rap_error!("DefId {:?} is not local. Falling back to def path.", def_id);
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

/// Check if a DefId represents a method in an impl block
fn is_method_def<'tcx>(tcx: TyCtxt<'tcx>, def_id: DefId) -> bool {
    if let Some(parent) = tcx.opt_parent(def_id) {
        // Check if parent is an impl block
        matches!(tcx.def_kind(parent), rustc_hir::def::DefKind::Impl { .. })
    } else {
        false
    }
}

/// Format method path with proper separation of impl generics and method generics
fn format_method_path_with_args<'tcx>(
    tcx: TyCtxt<'tcx>,
    method_def_id: DefId,
    args: GenericArgsRef<'tcx>,
    base_path: String,
) -> String {
    // rap_info!(
    //     "Formatting method path: base_path={}, args={:?}",
    //     base_path,
    //     args
    // );

    // Get the impl block def_id
    let impl_def_id = tcx
        .opt_parent(method_def_id)
        .expect("Method should have parent impl");

    // Get generics count for impl
    let impl_generics = tcx.generics_of(impl_def_id);
    let impl_params_count = impl_generics.count();

    // Pre-calculate count to avoid Vec reallocation
    let type_count = args
        .iter()
        .filter(|arg| {
            matches!(
                arg.kind(),
                rustc_middle::ty::GenericArgKind::Type(_)
                    | rustc_middle::ty::GenericArgKind::Const(_)
            )
        })
        .count();

    if type_count == 0 {
        return base_path;
    }

    let mut type_args = Vec::with_capacity(type_count);
    for arg in args.iter() {
        match arg.kind() {
            rustc_middle::ty::GenericArgKind::Type(ty) => type_args.push(ty.to_string()),
            rustc_middle::ty::GenericArgKind::Const(ct) => type_args.push(ct.to_string()),
            rustc_middle::ty::GenericArgKind::Lifetime(_) => continue,
        }
    }

    // rap_info!(
    //     "Type args: {:?}, impl_params_count: {}",
    //     type_args,
    //     impl_params_count
    // );

    // Check if base_path already contains generics (has ::<> pattern)
    if base_path.contains("::<") {
        //rap_info!("Base path already contains generics, need to replace them");
        return replace_generics_in_path(base_path, &type_args, impl_params_count);
    }

    // Split type args between impl generics and method generics
    let (impl_args, method_args) = if type_args.len() <= impl_params_count {
        // All args belong to impl
        (type_args, Vec::new())
    } else {
        // Split args between impl and method
        let split_point = impl_params_count;
        (
            type_args[..split_point].to_vec(),
            type_args[split_point..].to_vec(),
        )
    };

    // rap_info!(
    //     "Split args - impl: {:?}, method: {:?}",
    //     impl_args,
    //     method_args
    // );

    // Parse the base_path to construct proper method path
    if let Some(method_name_start) = base_path.rfind("::") {
        let (type_path, method_name) = base_path.split_at(method_name_start + 2);
        let type_path = &type_path[..type_path.len() - 2]; // Remove the trailing "::"

        // Calculate total capacity needed for the result string
        let capacity = type_path.len() + method_name.len() + 4 + // base + "::" + method
            if !impl_args.is_empty() { 3 + impl_args.iter().map(|s| s.len()).sum::<usize>() + (impl_args.len() - 1) * 2 } else { 0 } +
            if !method_args.is_empty() { 3 + method_args.iter().map(|s| s.len()).sum::<usize>() + (method_args.len() - 1) * 2 } else { 0 };

        let mut result = String::with_capacity(capacity);
        result.push_str(type_path);

        if !impl_args.is_empty() {
            result.push_str("::<");
            for (i, arg) in impl_args.iter().enumerate() {
                if i > 0 {
                    result.push_str(", ");
                }
                result.push_str(arg);
            }
            result.push('>');
        }

        result.push_str("::");
        result.push_str(method_name);

        if !method_args.is_empty() {
            result.push_str("::<");
            for (i, arg) in method_args.iter().enumerate() {
                if i > 0 {
                    result.push_str(", ");
                }
                result.push_str(arg);
            }
            result.push('>');
        }

        //rap_info!("Generated method path: {}", result);
        result
    } else {
        // Fallback: treat as regular function
        let all_args: Vec<String> = args
            .iter()
            .filter_map(|arg| match arg.kind() {
                rustc_middle::ty::GenericArgKind::Type(ty) => Some(format!("{}", ty)),
                rustc_middle::ty::GenericArgKind::Const(ct) => Some(format!("{}", ct)),
                rustc_middle::ty::GenericArgKind::Lifetime(_) => None,
            })
            .collect();

        if !all_args.is_empty() {
            format!("{}::<{}>", base_path, all_args.join(", "))
        } else {
            base_path
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