use std::collections::HashMap;

use itertools::Itertools;
use rustc_hir::def::DefKind;
use rustc_hir::def_id::{DefId, LocalDefId, LOCAL_CRATE};
use rustc_hir::GenericArgs;
use rustc_middle::ty::{self, GenericArgsRef, Ty, TyCtxt, TyKind};
use rustc_span::Ident;

pub struct PathResolver<'tcx> {
    tcx: TyCtxt<'tcx>,
    path_map: HashMap<DefId, String>,
}

pub fn get_path_resolver<'tcx>(tcx: TyCtxt<'tcx>) -> PathResolver<'tcx> {
    let mut resolver = PathResolver::new(tcx);
    resolver.build(LOCAL_CRATE.as_def_id(), String::new());
    resolver
}

fn path_str(current_path: &str, ident: Ident) -> String {
    if current_path.is_empty() {
        ident.as_str().to_owned()
    } else {
        (current_path.to_string() + "::" + ident.as_str()).to_owned()
    }
}

impl<'tcx> PathResolver<'tcx> {
    fn new(tcx: TyCtxt<'tcx>) -> Self {
        PathResolver {
            tcx,
            path_map: HashMap::new(),
        }
    }

    fn build(&mut self, mod_id: DefId, current_path: String) {
        let childs = if mod_id.is_local() {
            self.tcx.module_children_local(mod_id.expect_local())
        } else {
            self.tcx.module_children(mod_id)
        };

        for child in childs {
            if !child.vis.is_public() {
                continue;
            }
            if let Some(did) = child.res.opt_def_id() {
                let path = path_str(&current_path, child.ident);
                self.path_map.entry(did).or_insert(path.clone());
                if self.tcx.def_kind(did).is_module_like() {
                    self.build(did, path);
                }
            }
        }
    }

    pub fn path_str(&self, def_id: DefId) -> String {
        match self.path_map.get(&def_id) {
            Some(path) => path.clone(),
            None => {
                rap_debug!("[PathResolver] cannot find path for {:?}", def_id);
                self.tcx.def_path_str(def_id)
            }
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
            _ => ty.to_string(),
        }
    }

    pub fn path_str_with_args(&self, def_id: DefId, args: ty::GenericArgsRef<'tcx>) -> String {
        let mut iter = args.iter();
        self.path_str_with_iter(def_id, &mut iter)
    }

    fn generic_arg_iter_str(
        &self,
        iter: impl Iterator<Item = ty::GenericArg<'tcx>>,
    ) -> Option<String> {
        let mut args: Vec<String> = Vec::new();
        for arg in iter {
            args.push(match arg.kind() {
                ty::GenericArgKind::Lifetime(re) => re.to_string(),
                ty::GenericArgKind::Type(ty) => self.ty_str(ty),
                ty::GenericArgKind::Const(const_) => {
                    const_.try_to_target_usize(self.tcx).unwrap().to_string()
                }
            });
        }
        if !args.is_empty() {
            Some(format!("{}", args.join(", ")))
        } else {
            None
        }
    }

    fn path_str_with_iter(
        &self,
        def_id: DefId,
        iter: &mut impl Iterator<Item = ty::GenericArg<'tcx>>,
    ) -> String {
        let mut path_str = String::new();

        // `{assoc_path}::{item_name}`
        if let Some((assoc_id, kind)) = self.tcx.assoc_parent(def_id) {
            rap_debug!("assoc item: {:?} => {:?}", assoc_id, kind);
            // the number of generic of assoc parent
            let num_generic = self.tcx.generics_of(assoc_id).own_params.len();
            let parent_args: Vec<_> = iter.take(num_generic).collect();
            match kind {
                // Trait Impl
                DefKind::Impl { of_trait: true } => {
                    let trait_ref = self
                        .tcx
                        .impl_trait_ref(assoc_id)
                        .unwrap()
                        .instantiate(self.tcx, parent_args.as_slice());

                    let self_ty_str = self.ty_str(trait_ref.self_ty());
                    let trait_str = self.path_str(trait_ref.def_id);
                    path_str += match self.generic_arg_iter_str(trait_ref.args.iter().skip(1)) {
                        Some(args) => format!("<{} as {}<{}>>", self_ty_str, trait_str, args),
                        None => format!("<{} as {}>", self_ty_str, trait_str),
                    }
                    .as_str();
                }
                // inherent impl
                DefKind::Impl { of_trait: false } => {
                    // let num_generic = self.tcx.generics_of(did).own_params.len();
                    let self_ty = self
                        .tcx
                        .type_of(assoc_id)
                        .instantiate(self.tcx, parent_args.as_slice());
                    path_str += &self.ty_str(self_ty);
                }
                // other
                _ => {
                    unreachable!("unexpected assoc parent: {:?} => {:?}", assoc_id, kind);
                }
            }
            path_str += "::";
            path_str += self.tcx.item_name(def_id).as_str();
        } else {
            path_str = self.path_str(def_id);
        }

        let num_generic = self.tcx.generics_of(def_id).own_params.len();

        match self.generic_arg_iter_str(iter.take(num_generic)) {
            Some(arg_str) => format!("{}::<{}>", path_str, arg_str),
            None => path_str,
        }
    }
}
