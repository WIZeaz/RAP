use super::LlmAuditAnalysis;
use crate::{
    analysis::{core::callgraph::CallGraph, llm_audit::canonicalize_file_name},
    rap_debug,
};
use anyhow::Result;
use rustc_middle::ty::{self, Ty, TyCtxt, TyKind, TypeSuperVisitable, TypeVisitable};
use rustc_span::{def_id::DefId, FileName};
use std::{collections::HashMap, path::PathBuf};

#[derive(Debug, Clone)]
pub struct FileContext {
    inner: HashMap<FileName, HashMap<FileName, usize>>,
}

pub type ContextMap = HashMap<PathBuf, Vec<(PathBuf, usize)>>;

impl FileContext {
    pub fn new() -> Self {
        FileContext {
            inner: HashMap::default(),
        }
    }
    // collect HashMap<FileName, usize> to Vec<FileName> by usize value
    pub fn into_sorted_map(self) -> Result<ContextMap> {
        let mut map = HashMap::new();
        for (k, v) in self.inner {
            let abs_path = k.into_local_path().unwrap().canonicalize().unwrap();
            let mut vec: Vec<(PathBuf, usize)> = v
                .into_iter()
                .filter_map(|(filename, cnt)| Some((canonicalize_file_name(&filename)?, cnt)))
                .collect();

            vec.sort_by(|lhs, rhs| rhs.1.cmp(&lhs.1));
            map.insert(abs_path, vec);
        }
        Ok(map)
    }

    fn add<'tcx>(&mut self, source: DefId, dep: DefId, tcx: TyCtxt<'tcx>) {
        let source_map = tcx.sess.source_map();
        let source_file = source_map.span_to_filename(tcx.def_span(source));
        let dep_file = source_map.span_to_filename(tcx.def_span(dep));
        let dep_crate = tcx.crate_name(dep.krate);

        if matches!(dep_crate.as_str(), "std" | "core" | "alloc") {
            return;
        }

        if source_file == dep_file {
            return;
        }

        *self
            .inner
            .entry(source_file)
            .or_default()
            .entry(dep_file)
            .or_default() += 1;
    }
}

impl<'tcx> LlmAuditAnalysis<'tcx> {
    pub fn collect_fn(
        &self,
        fn_did: DefId,
        call_graph: &CallGraph,
        file_context: &mut FileContext,
    ) {
        let fn_span = self.tcx.def_span(fn_did);
        let fn_sig = self.tcx.fn_sig(fn_did);
        let fn_sig = fn_sig.instantiate_identity().skip_binder();

        rap_debug!("fn: {}", self.tcx.def_path_str(fn_did));
        rap_debug!("span: {:?}", fn_span);

        // add callee
        if let Some(callees) = call_graph.fn_calls.get(&fn_did) {
            callees.iter().for_each(|callee| {
                rap_debug!("callee: {}", self.tcx.def_path_str(callee));
                rap_debug!("span: {:?}", self.tcx.def_span(callee));
                file_context.add(fn_did, *callee, self.tcx);
            });
        }

        // add arg type
        for arg_ty in fn_sig.inputs_and_output.iter() {
            self.collect_ty(arg_ty, fn_did, file_context);
        }

        let predicates = self.tcx.predicates_of(fn_did);

        for (predicate, span) in predicates.predicates {
            rap_debug!("pred:{:?} ({:?})", predicate, span);
            if let ty::ClauseKind::Trait(trait_predicate) = predicate.kind().skip_binder() {
                let trait_ref = trait_predicate.trait_ref;
                file_context.add(fn_did, trait_ref.def_id, self.tcx);
                rap_debug!(
                    "trait span: {:?}",
                    self.tcx
                        .sess
                        .source_map()
                        .span_to_filename(self.tcx.def_span(trait_ref.def_id))
                );

                trait_ref.args.iter().for_each(|arg| {
                    if let Some(ty) = arg.as_type() {
                        rap_debug!("pred arg ty: {}", ty);
                        self.collect_ty(ty, fn_did, file_context);
                    }
                });
            }
        }
    }

    pub fn collect_ty(&self, ty: Ty<'tcx>, fn_did: DefId, file_context: &mut FileContext) {
        struct Visitor {
            inner: Vec<DefId>,
        }

        impl<'tcx> ty::TypeVisitor<TyCtxt<'tcx>> for Visitor {
            type Result = ();
            fn visit_ty(&mut self, t: Ty<'tcx>) -> Self::Result {
                if let TyKind::Adt(adt_def, _) = t.kind() {
                    let def_id = adt_def.did();
                    self.inner.push(def_id);
                }
                t.super_visit_with(self);
            }
        }

        let mut visitor = Visitor { inner: vec![] };

        ty.visit_with(&mut visitor);

        for did in visitor.inner {
            file_context.add(fn_did, did, self.tcx);
        }
    }
}
