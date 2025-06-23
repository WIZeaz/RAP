use crate::analysis::testgen::utils;
use crate::{rap_debug, rap_info, rap_trace, rap_warn};
use rustc_hir::def_id::DefId;
use rustc_infer::infer::canonical::ir::InferCtxtLike;
use rustc_infer::infer::TyCtxtInferExt;
use rustc_infer::infer::{DefineOpaqueTypes, TyCtxtInferExt as _};
use rustc_infer::traits::{select, Obligation, ObligationCause};
use rustc_middle::ty::{self, Ty, TyCtxt, TyKind, TypeFoldable, TypeVisitableExt};
use rustc_span::DUMMY_SP;
use rustc_trait_selection::infer::InferCtxtExt;
use rustc_trait_selection::traits::query::evaluate_obligation::InferCtxtExt as _;
use rustc_trait_selection::traits::{FulfillmentContext, ObligationCtxt};
use std::cell::RefCell;
use std::collections::{HashMap, HashSet, VecDeque};
use std::io::Write;

use super::context::LtContext;

#[derive(Clone, Debug)]
pub struct MonoSet<'tcx> {
    pub value: Vec<Vec<ty::GenericArg<'tcx>>>,
}

impl<'tcx> MonoSet<'tcx> {
    pub fn all(args: &[ty::GenericArg<'tcx>]) -> MonoSet<'tcx> {
        MonoSet {
            value: vec![Vec::from(args)],
        }
    }

    pub fn count(&self) -> usize {
        self.value.len()
    }

    pub fn args_at(&self, no: usize) -> &[ty::GenericArg<'tcx>] {
        &self.value[no]
    }

    pub fn is_empty(&self) -> bool {
        self.value.is_empty()
    }

    pub fn empty() -> MonoSet<'tcx> {
        MonoSet { value: Vec::new() }
    }

    pub fn add_from_iter(&mut self, iter: impl Iterator<Item = ty::GenericArg<'tcx>>) {
        let mut value = Vec::new();
        for arg in iter {
            value.push(arg);
        }
        self.value.push(value);
    }

    pub fn merge(&mut self, other: &MonoSet<'tcx>, tcx: TyCtxt<'tcx>) -> MonoSet<'tcx> {
        let mut res = MonoSet::empty();

        for args in self.value.iter() {
            for other_args in other.value.iter() {
                let merged = self.merge_args(args, other_args, tcx);
                rap_trace!("merged: {:?}", merged);
                if let Some(new_args) = merged {
                    res.value.push(new_args);
                }
            }
        }

        res
    }

    fn merge_args(
        &self,
        args: &[ty::GenericArg<'tcx>],
        other_args: &[ty::GenericArg<'tcx>],
        tcx: TyCtxt<'tcx>,
    ) -> Option<Vec<ty::GenericArg<'tcx>>> {
        rap_trace!(
            "[MonoSet::merge_args] args: {:?} other_args: {:?}",
            args,
            other_args
        );
        assert!(args.len() == other_args.len());
        let mut res = Vec::new();
        for i in 0..args.len() {
            let arg = args[i];
            let other_arg = other_args[i];
            let new_arg = if let Some(ty) = arg.as_type() {
                let other_ty = other_arg.expect_ty();
                if ty.is_ty_var() && other_ty.is_ty_var() {
                    arg
                } else if ty.is_ty_var() {
                    other_arg
                } else if other_ty.is_ty_var() {
                    arg
                } else if utils::is_ty_eq(ty, other_ty, tcx) {
                    arg
                } else {
                    return None;
                }
            } else {
                arg
            };
            res.push(new_arg);
        }
        Some(res)
    }

    fn filter_unbound_solution(mut self) -> Self {
        self.value.retain(|args| {
            args.iter().all(|arg| match arg.kind() {
                ty::GenericArgKind::Type(ty) => !ty.is_ty_var(),
                _ => true,
            })
        });
        self
    }

    fn filter_by_trait_bound(mut self, fn_did: DefId, tcx: TyCtxt<'tcx>) -> Self {
        let early_fn_sig = tcx.fn_sig(fn_did);
        self.value.retain(|args| {
            let args = tcx.mk_args(args);
            // let fn_sig = early_fn_sig.instantiate(tcx, args);
            let infcx = tcx.infer_ctxt().build(ty::TypingMode::PostAnalysis);
            let pred = tcx.predicates_of(fn_did);
            let inst_pred = pred.instantiate(tcx, args);
            let param_env = tcx.param_env(fn_did);
            rap_trace!("[trait bound] {fn_did:?} {args:?} {param_env:?} {inst_pred:?}");

            for pred in inst_pred.predicates.iter() {
                let obligation = Obligation::new(
                    tcx,
                    ObligationCause::dummy(),
                    param_env,
                    pred.as_predicate(),
                );

                let res = infcx.evaluate_obligation(&obligation);
                rap_trace!("{obligation:?}");
                rap_trace!("{res:?}");
                match res {
                    Ok(eva) => {
                        if !eva.may_apply() {
                            return false;
                        }
                    }
                    Err(_) => {
                        rap_trace!("[trait bound] check fail");
                        return false;
                    }
                }
            }
            rap_trace!("[trait bound] check succ");
            true
        });
        self
    }
}

fn get_mono_set<'tcx>(
    fn_did: DefId,
    available_ty: &HashSet<Ty<'tcx>>,
    tcx: TyCtxt<'tcx>,
) -> MonoSet<'tcx> {
    let fn_sig = tcx.fn_sig(fn_did);
    let infcx = tcx
        .infer_ctxt()
        .ignoring_regions()
        .build(ty::TypingMode::PostAnalysis);
    let param_env = tcx.param_env(fn_did);
    let fresh_args = infcx.fresh_args_for_item(DUMMY_SP, fn_did);
    let fn_sig = fn_sig.instantiate(tcx, fresh_args);
    let fn_sig = tcx.liberate_late_bound_regions(fn_did, fn_sig);
    let generics = tcx.generics_of(fn_did);
    for i in 0..fresh_args.len() {
        rap_trace!(
            "arg#{}: {:?} -> {:?}",
            i,
            generics.param_at(i, tcx).name,
            fresh_args[i]
        );
    }
    let dummy_cause = ObligationCause::dummy();

    rap_trace!("param_env: {:?}", param_env);
    // let mut ret = MonoSet::all(fresh_args);
    // for input_ty in fn_sig.inputs().iter() {}

    fn_sig
        .inputs()
        .iter()
        .fold(MonoSet::all(&fresh_args), |mut acc, input_ty| {
            let reachable_set =
                available_ty
                    .iter()
                    .fold(MonoSet::empty(), |mut reachable_set, ty| {
                        infcx.probe(|_| {
                            match infcx.at(&dummy_cause, param_env).eq(
                                DefineOpaqueTypes::Yes,
                                *input_ty,
                                *ty,
                            ) {
                                Ok(infer_ok) => {
                                    rap_trace!("{} can eq to {}: {:?}", ty, input_ty, infer_ok);
                                }
                                Err(e) => {
                                    rap_trace!("{} cannot eq to {}: {:?}", ty, input_ty, e);
                                    return;
                                }
                            }

                            reachable_set.add_from_iter(fresh_args.iter().map(
                                |arg| match arg.kind() {
                                    ty::GenericArgKind::Lifetime(region) => {
                                        infcx.resolve_vars_if_possible(region).into()
                                    }
                                    ty::GenericArgKind::Type(ty) => {
                                        infcx.resolve_vars_if_possible(ty).into()
                                    }
                                    ty::GenericArgKind::Const(ct) => {
                                        infcx.resolve_vars_if_possible(ct).into()
                                    }
                                },
                            ));
                        });
                        reachable_set
                    });

            acc.merge(&reachable_set, tcx)
        })
}

pub fn get_all_concrete_mono_solution<'tcx>(
    fn_did: DefId,
    mut available_ty: HashSet<Ty<'tcx>>,
    tcx: TyCtxt<'tcx>,
) -> MonoSet<'tcx> {
    rap_trace!("enter get_all_concrete_mono_solution for {fn_did:?}");

    add_prelude_tys(&mut available_ty, tcx);
    add_transform_tys(&mut available_ty, tcx);
    rap_debug!("[mono] input => {fn_did:?}: {available_ty:?}");
    let ret = get_mono_set(fn_did, &available_ty, tcx)
        .filter_unbound_solution()
        .filter_by_trait_bound(fn_did, tcx);
    rap_debug!("possible mono solution for {fn_did:?}: {ret:?}");
    ret
}

pub fn add_transform_tys<'tcx>(available_ty: &mut HashSet<Ty<'tcx>>, tcx: TyCtxt<'tcx>) {
    let mut new_tys = Vec::new();
    available_ty.iter().for_each(|ty| {
        new_tys.push(Ty::new_ref(
            tcx,
            tcx.lifetimes.re_erased,
            *ty,
            ty::Mutability::Not,
        ));
        new_tys.push(Ty::new_ref(
            tcx,
            tcx.lifetimes.re_erased,
            *ty,
            ty::Mutability::Mut,
        ));
    });
    new_tys.into_iter().for_each(|ty| {
        available_ty.insert(ty);
    });
}

pub fn add_prelude_tys<'tcx>(available_ty: &mut HashSet<Ty<'tcx>>, tcx: TyCtxt<'tcx>) {
    let prelude_tys = [
        tcx.types.bool,
        tcx.types.char,
        tcx.types.f32,
        tcx.types.f64,
        tcx.types.i8,
        tcx.types.i32,
        tcx.types.u8,
        tcx.types.u32,
        tcx.types.usize,
        tcx.types.isize,
    ];
    prelude_tys.iter().for_each(|ty| {
        available_ty.insert(*ty);
    });
}
