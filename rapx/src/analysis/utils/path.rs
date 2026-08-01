use itertools::Itertools;
use rustc_hir::def::DefKind;
use rustc_hir::def_id::{DefId, LOCAL_CRATE};
use rustc_middle::ty::{self, Ty, TyCtxt, TyKind};
use std::cell::{Ref, RefCell};
use std::collections::HashMap;

/// A utility to resolve the actual visible path for re-export items.
pub struct PathResolver<'tcx> {
    tcx: TyCtxt<'tcx>,
    path_map: HashMap<DefId, String>,
    ///  `non_local_def_ids` is used to record the def_ids that are not from local crate, but printed by [PathResolver].
    ///  This is used for testgen to create neccessary dep info for these def_ids.
    non_local_def_ids: RefCell<Vec<DefId>>,
}

pub fn get_path_resolver<'tcx>(tcx: TyCtxt<'tcx>) -> PathResolver<'tcx> {
    let mut resolver = PathResolver::new(tcx);
    resolver.build(LOCAL_CRATE.as_def_id(), String::new());
    for (DefId, path) in resolver.paths() {
        rap_trace!("def_id: {:?}, path: {}", DefId, path);
    }
    resolver
}

fn join_path_with_double_colon(parts: &[&str]) -> String {
    parts.iter().filter(|s| !s.is_empty()).join("::")
}

fn is_std_def_id(def_id: DefId, tcx: TyCtxt) -> bool {
    let krate_name = tcx.crate_name(def_id.krate);
    krate_name.as_str() == "std" || krate_name.as_str() == "core" || krate_name.as_str() == "alloc"
}

impl<'tcx> PathResolver<'tcx> {
    fn new(tcx: TyCtxt<'tcx>) -> Self {
        PathResolver {
            tcx,
            path_map: HashMap::new(),
            non_local_def_ids: RefCell::new(Vec::new()),
        }
    }

    fn build(&mut self, mod_id: DefId, current_path: String) {
        rap_trace!("enter module: {:?}, path: {}", mod_id, current_path);
        let childs = if mod_id.is_local() {
            self.tcx.module_children_local(mod_id.expect_local())
        } else {
            self.tcx.module_children(mod_id)
        };

        for child in childs {
            rap_trace!(
                "processing child: {:?}, ident = {}",
                child.res,
                child.ident.as_str()
            );
            if !child.vis.is_public() || child.ident.as_str() == "_" {
                continue;
            }
            if let Some(did) = child.res.opt_def_id() {
                let path = join_path_with_double_colon(&[&current_path, child.ident.as_str()]);
                self.path_map.entry(did).or_insert(path.clone());
                if self.tcx.def_kind(did).is_module_like() {
                    self.build(did, path);
                }
            }
        }
    }

    pub fn non_local_def_ids(&self) -> Ref<[DefId]> {
        let ref_ = self.non_local_def_ids.borrow();
        Ref::map(ref_, |v| v.as_slice())
    }

    pub fn reset_non_local_def_ids(&self) {
        self.non_local_def_ids.borrow_mut().clear();
    }

    fn non_assoc_path_str(&self, def_id: DefId) -> String {
        match self.path_map.get(&def_id) {
            Some(path) => path.clone(),
            None => {
                // if def_id is from local crate, but we cannot find it in path_map,
                // report this error.
                if def_id.is_local() {
                    rap_error!(
                        "[PathResolver] cannot find path for {:?}, fallback to self.tcx.def_path_str",
                        def_id
                    );
                } else if !is_std_def_id(def_id, self.tcx) {
                    self.non_local_def_ids.borrow_mut().push(def_id);
                }
                self.tcx.def_path_str(def_id)
            }
        }
    }

    pub fn paths(&self) -> impl Iterator<Item = (DefId, &str)> {
        self.path_map.iter().map(|(did, s)| (*did, s.as_str()))
    }

    pub fn path_exists(&self, did: DefId) -> bool {
        let Some((assoc_id, kind)) = self.tcx.assoc_parent(did) else {
            // check non associated item
            return did.is_local() && self.path_map.contains_key(&did)
            // for did from other crate, we rely on tcx.visibility, 
            // which is not 100% accurate, but should be good enough in most cases.
                || !did.is_local() && self.tcx.visibility(did).is_public();
        };

        if !self.tcx.visibility(did).is_public() {
            return false;
        }

        match kind {
            DefKind::Impl { .. } => {
                let self_ty = self.tcx.type_of(assoc_id).instantiate_identity();
                match self_ty.kind() {
                    // Theoretically, we need to check visibility of generic args.
                    // However, it is a bit complicated and we currently do not consider it.
                    TyKind::Adt(adt_def, _) => return self.path_exists(adt_def.did()),
                    _ => return true,
                }
            }
            DefKind::Trait => return self.path_exists(assoc_id),
            _ => panic!(
                "unexpected parent kind: {:?} for assoc item: {:?}",
                kind, did
            ),
        }
    }

    pub fn ty_str(&self, ty: Ty<'tcx>) -> String {
        match ty.kind() {
            TyKind::Adt(adt_def, args) => self.path_str_with_args(adt_def.did(), args),
            TyKind::Array(inner_ty, const_) => {
                format!("[{};{}]", self.ty_str(*inner_ty), const_)
            }
            TyKind::Tuple(tys) => {
                format!("({})", tys.iter().map(|ty| self.ty_str(ty)).join(", "))
            }
            TyKind::Ref(region, inner_ty, mutability) => {
                format!(
                    "&{} {}{}",
                    region,
                    mutability.prefix_str(),
                    self.ty_str(*inner_ty)
                )
            }
            TyKind::RawPtr(inner_ty, mutability) => {
                format!("*{} {}", mutability.ptr_str(), self.ty_str(*inner_ty))
            }
            TyKind::Slice(inner_ty) => {
                format!("[{}]", self.ty_str(*inner_ty))
            }
            TyKind::Alias(kind, ty) => match kind {
                ty::AliasTyKind::Projection => self.path_str_with_args(ty.def_id, ty.args),
                ty::AliasTyKind::Opaque => {
                    let ty_str = ty.to_string();
                    rap_warn!("encounter opaque type {}, type string might be private", ty);
                    ty_str
                }
                _ => {
                    panic!("unexpected alias kind: {:?} for ty: {:?}", kind, ty);
                }
            },
            _ => ty.to_string(),
        }
    }

    pub fn path_str(&self, def_id: DefId) -> String {
        self.path_str_with_args(def_id, ty::GenericArgs::identity_for_item(self.tcx, def_id))
    }

    pub fn path_str_with_args(&self, def_id: DefId, args: ty::GenericArgsRef<'tcx>) -> String {
        // `{assoc_path}::{item_name}`
        if let Some((assoc_id, kind)) = self.tcx.assoc_parent(def_id) {
            rap_trace!("assoc item: {:?} => {:?}", assoc_id, kind);

            // the number of generic of assoc parent
            let num_generic = self.tcx.generics_of(assoc_id).own_params.len();

            let (parent_args, own_args) = args.split_at(num_generic);

            let parent_path_str = match kind {
                // Trait Impl
                DefKind::Impl { of_trait: true } => {
                    let trait_ref = self
                        .tcx
                        .impl_trait_ref(assoc_id)
                        .instantiate(self.tcx, parent_args);

                    let self_ty_str = self.ty_str(trait_ref.self_ty());
                    let trait_str = self.non_assoc_path_str(trait_ref.def_id);
                    if trait_ref.args.len() > 1 {
                        format!(
                            "<{} as {}{}>",
                            self_ty_str,
                            trait_str,
                            self.generic_args_str(&trait_ref.args[1..])
                        )
                    } else {
                        format!("<{} as {}>", self_ty_str, trait_str)
                    }
                }
                // inherent impl
                DefKind::Impl { of_trait: false } => {
                    let self_ty = self
                        .tcx
                        .type_of(assoc_id)
                        .instantiate(self.tcx, parent_args);
                    self.ty_str(self_ty)
                }
                // Trait
                DefKind::Trait => {
                    let self_ty = parent_args[0].expect_ty();
                    let self_ty_str = self.ty_str(self_ty);
                    let trait_str = self.non_assoc_path_str(assoc_id);
                    if parent_args.len() > 1 {
                        format!(
                            "<{} as {}{}>",
                            self_ty_str,
                            trait_str,
                            self.generic_args_str(&parent_args[1..])
                        )
                    } else {
                        format!("<{} as {}>", self_ty_str, trait_str)
                    }
                }
                _ => {
                    unreachable!(
                        "unexpected assoc parent: {:?} => {:?}, def_id: {:?}, path: {:?}",
                        assoc_id,
                        kind,
                        def_id,
                        self.tcx.def_path_str_with_args(def_id, args)
                    );
                }
            };

            let args_str = self.non_syn_generic_args_str(def_id, own_args);

            join_path_with_double_colon(&[
                &parent_path_str,
                self.tcx.item_name(def_id).as_str(),
                &args_str,
            ])
        } else {
            // non assoc item
            let path_str = self.non_assoc_path_str(def_id);
            let args_str = self.non_syn_generic_args_str(def_id, args);
            join_path_with_double_colon(&[path_str.as_str(), args_str.as_str()])
        }
    }

    pub fn generic_arg_str(&self, arg: ty::GenericArg<'tcx>) -> String {
        match arg.kind() {
            ty::GenericArgKind::Lifetime(_) => "'_".to_string(),
            ty::GenericArgKind::Type(ty) => self.ty_str(ty),
            ty::GenericArgKind::Const(const_) => format!("{}", const_),
        }
    }

    fn generic_args_str(&self, generic_args: &[ty::GenericArg<'tcx>]) -> String {
        if generic_args.is_empty() {
            return String::new();
        }
        format!(
            "<{}>",
            generic_args
                .iter()
                .map(|arg| self.generic_arg_str(*arg))
                .join(", ")
        )
    }

    fn non_syn_generic_args_str(&self, def_id: DefId, args: &[ty::GenericArg<'tcx>]) -> String {
        let defs = self.tcx.generics_of(def_id).own_params.as_slice();

        assert!(defs.len() == args.len());

        self.generic_args_str(
            args.iter()
                .zip(defs.iter())
                .filter_map(|(arg, param)| {
                    if param.kind.is_synthetic() {
                        None
                    } else {
                        Some(*arg)
                    }
                })
                .collect_vec()
                .as_slice(),
        )
    }
}
