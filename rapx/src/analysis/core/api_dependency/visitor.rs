use super::Config;
use super::graph::ApiDependencyGraph;
use super::graph::{DepEdge, DepNode};
use super::is_def_id_public;
use crate::analysis::core::api_dependency::mono;
use crate::{rap_debug, rap_trace};
use rustc_hir::LangItem;
use rustc_hir::{
    BodyId, BodyOwnerKind, FnDecl,
    def_id::{DefId, LocalDefId},
    intravisit::{FnKind, Visitor},
};
use rustc_middle::ty::{self, FnSig, ParamEnv, Ty, TyCtxt, TyKind};
use rustc_span::Span;
use std::io::Write;

pub struct FnVisitor<'tcx, 'a> {
    tcx: TyCtxt<'tcx>,
    apis: Vec<DefId>,
    config: Config,
    graph: &'a mut ApiDependencyGraph<'tcx>,
}

impl<'tcx, 'a> FnVisitor<'tcx, 'a> {
    pub fn new(
        graph: &'a mut ApiDependencyGraph<'tcx>,
        config: Config,
        tcx: TyCtxt<'tcx>,
    ) -> FnVisitor<'tcx, 'a> {
        let fn_cnt = 0;
        let funcs = Vec::new();
        FnVisitor {
            tcx,
            graph,
            apis: funcs,
            config,
        }
    }

    pub fn count_api(&self) -> usize {
        self.apis.len()
    }

    pub fn apis(self) -> Vec<DefId> {
        self.apis
    }

    pub fn write_funcs<T: Write>(&self, f: &mut T) {
        for id in &self.apis {
            write!(f, "{}\n", self.tcx.def_path_str(id)).expect("fail when write funcs");
        }
    }
}

pub fn has_const_generics(generics: &ty::Generics, tcx: TyCtxt<'_>) -> bool {
    if generics
        .own_params
        .iter()
        .any(|param| matches!(param.kind, ty::GenericParamDefKind::Const { .. }))
    {
        return true;
    }

    if let Some(parent_def_id) = generics.parent {
        let parent = tcx.generics_of(parent_def_id);
        has_const_generics(parent, tcx)
    } else {
        false
    }
}

fn is_drop_impl(tcx: TyCtxt<'_>, fn_did: DefId) -> bool {
    if let Some(impl_id) = tcx.trait_impl_of_assoc(fn_did) {
        let trait_did = tcx.impl_trait_id(impl_id);
        if tcx.is_lang_item(trait_did, LangItem::Drop) {
            return true;
        }
    }
    false
}

impl<'tcx, 'a> Visitor<'tcx> for FnVisitor<'tcx, 'a> {
    fn visit_fn<'v>(
        &mut self,
        fk: FnKind<'v>,
        _fd: &'v FnDecl<'v>,
        _b: BodyId,
        _span: Span,
        id: LocalDefId,
    ) -> Self::Result {
        let fn_did = id.to_def_id();
        let generics = self.tcx.generics_of(fn_did);

        let is_generic = generics.requires_monomorphization(self.tcx);
        if self.config.pub_only && !is_def_id_public(fn_did, self.tcx) {
            return;
        }

        if !self.config.include_drop && is_drop_impl(self.tcx, fn_did) {
            return;
        }

        // if config.resolve_generic is false,
        // skip all generic functions
        if !self.config.resolve_generic && is_generic {
            return;
        }

        // if config.ignore_const_generic is true,
        // skip functions with const generics
        if self.config.ignore_const_generic && has_const_generics(generics, self.tcx) {
            return;
        }

        if !self.config.include_unsafe && fk.header().unwrap().safety().is_unsafe() {
            rap_trace!("skip unsafe fn: {}", self.tcx.def_path_str(fn_did));
            return;
        }

        if !is_generic {
            let args = ty::GenericArgs::identity_for_item(self.tcx, fn_did);
            self.graph.add_api(fn_did, &args);
        }

        self.apis.push(fn_did);
    }
}
