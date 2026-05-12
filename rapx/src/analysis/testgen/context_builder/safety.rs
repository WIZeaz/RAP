use super::super::utils;
use super::ContextBuilder;
use super::lifetime::{Rid, extract_rids};
use crate::analysis::core::alias_analysis::AliasPair;
use crate::analysis::testgen::context::{Stmt, Var};
use rand::seq::IndexedRandom;
use rustc_middle::ty::{self, Ty, TyCtxt, TyKind};
use std::collections::{HashMap, HashSet};

fn ty_project_to<'tcx>(mut ty: Ty<'tcx>, proj: &[usize], tcx: TyCtxt<'tcx>) -> Ty<'tcx> {
    for field_no in proj {
        ty = match ty.peel_refs().kind() {
            TyKind::Adt(adt_def, args) => {
                let did = adt_def
                    .all_fields()
                    .nth(*field_no)
                    .expect("field not found")
                    .did;
                tcx.type_of(did).instantiate(tcx, args)
            }
            _ => {
                panic!("unexpected type: {:?}", ty);
            }
        }
    }
    ty
}

fn get_fn_arg_ty_at<'tcx>(no: usize, fn_sig: ty::FnSig<'tcx>) -> Ty<'tcx> {
    if no == 0 {
        fn_sig.output()
    } else {
        fn_sig.inputs()[no - 1]
    }
}

fn destruct_ret_alias<'tcx>(
    fn_sig: ty::FnSig<'tcx>,
    fact: &AliasPair,
    tcx: TyCtxt<'tcx>,
) -> (Ty<'tcx>, Ty<'tcx>) {
    let left_local = fact.left_local();
    let right_local = fact.right_local();

    (
        ty_project_to(
            get_fn_arg_ty_at(left_local, fn_sig),
            &fact.lhs_fields(),
            tcx,
        ),
        ty_project_to(
            get_fn_arg_ty_at(right_local, fn_sig),
            &fact.rhs_fields(),
            tcx,
        ),
    )
}

/// check whether it is possible that lhs point to rhs.
///
/// if lhs contain any pointer to `T` (`&T`/`*T`) while rhs contain `T`,
/// [check_possibility] return `true`
pub fn check_possibility<'tcx>(lhs_ty: Ty<'tcx>, rhs_ty: Ty<'tcx>, tcx: TyCtxt<'tcx>) -> bool {
    let mut set = HashSet::new();
    let mut ret = false;
    utils::visit_ty_fields_while(rhs_ty, tcx, &mut |ty| {
        rap_trace!("[check_possibility] add {ty}");
        set.insert(tcx.erase_and_anonymize_regions(ty));
        true
    });
    utils::visit_ty_fields_while(lhs_ty, tcx, &mut |ty| {
        if ret {
            return false;
        }
        match ty.kind() {
            TyKind::RawPtr(inner_ty, _) | TyKind::Ref(_, inner_ty, _) => {
                rap_trace!("[check_possibility] check {ty}");
                if set.contains(inner_ty) {
                    rap_trace!("[check_possibility] find {ty} -> {inner_ty}");
                    ret = true;
                    return false;
                }
            }
            _ => {}
        }
        true
    });
    rap_trace!("[check_possibility] ret = {ret}");
    ret
}

/// check if underlied data of ty is stored inside the struct.
/// If ty is any pointer type (&T, *T or Fn), this function return false
fn ty_can_be_owned<'tcx>(ty: Ty<'tcx>) -> bool {
    if ty.is_any_ptr() {
        return false;
    }
    true
}

impl<'tcx, 'a> ContextBuilder<'tcx, 'a> {
    /// return a map from variable to the set of vulnerable regions that variable should be contrainted with
    pub fn detect_vulnerable_paths(&self, stmt: &Stmt<'tcx>) -> Option<HashMap<Var, HashSet<Rid>>> {
        let mut ret = HashMap::new();
        let _tcx = self.tcx;

        let call = stmt.as_apicall();

        let fn_sig = stmt.mk_fn_sig_with_var_tys(&self.cx);

        rap_debug!("analysis alias for: {:?} {:?}", call.fn_did, fn_sig);

        let mut add_potential_paths = |lhs_var, lhs_ty, rhs_var, rhs_ty| {
            rap_debug!(
                "[add_potential_paths] ({}) lhs_var = {}: {}, ({}) rhs_var = {}: {}",
                self.rid_of(lhs_var),
                lhs_var,
                lhs_ty,
                self.rid_of(rhs_var),
                rhs_var,
                rhs_ty
            );

            let mut rhs_ty_rids = extract_rids(rhs_ty);
            rap_debug!("rhs rids: {:?}", rhs_ty_rids);

            // if rhs_ty does not bind with any lifetime,
            // this maybe imply that lhs is a reference of rhs (e.g., lhs=&rhs.f)
            // the coresponding lifetime binding 'lhs->'rhs should be added
            // FIXME: the field-sensitive alias analysis is not exactly accurate,
            // so we may miss some 'lhs -> 'rhs lifetime bindings
            if rhs_ty_rids.is_empty() && ty_can_be_owned(rhs_ty) {
                rhs_ty_rids.push(self.rid_of(rhs_var));
            }
            let entry: &mut HashSet<Rid> = ret.entry(lhs_var).or_default();

            // add all unsafe regions into entry
            rhs_ty_rids.into_iter().for_each(|rid| {
                entry.insert(rid);
            });
        };

        // make facts symmetric
        let facts = self
            .alias_map
            .get(&call.fn_did())
            .expect(&format!("{:?} do not have alias infomation", call.fn_did()))
            .aliases()
            .iter()
            .filter(|fact| fact.left_local() <= fact.right_local())
            .cloned()
            .flat_map(|fact| {
                let mut rfact = fact.clone();
                rfact.swap();
                [fact, rfact]
            });

        for fact in facts {
            rap_trace!("alias fact: {}", fact);
            if fact.right_local() == 0 {
                rap_trace!("filter this fact (rhs is return value)");
                continue;
            }

            let (lhs_ty, rhs_ty) = destruct_ret_alias(fn_sig, &fact, self.tcx);

            // if fact.left_local() != 0 && !check_possibility(lhs_ty, rhs_ty, tcx) {
            //     rap_debug!("filter this fact (lhs is not mutable reference)");
            //     continue;
            // }

            let lhs_var = stmt.call_inputs_and_output_var_at(fact.left_local());
            let rhs_var = stmt.call_inputs_and_output_var_at(fact.right_local());
            add_potential_paths(lhs_var, lhs_ty, rhs_var, rhs_ty);
        }
        if ret.is_empty() {
            return None;
        }
        Some(ret)
    }

    pub fn try_inject_drop(&mut self) -> bool {
        let stmt = self.cx.stmts().last().unwrap();

        if !stmt.kind().is_call() {
            return false;
        }

        let call = stmt.as_apicall();
        let fn_did = call.fn_did();

        rap_info!(
            "try to inject drop for {}",
            self.tcx.def_path_str_with_args(fn_did, call.generic_args())
        );

        // if the function do not exist alias relationship, we assume it is safe
        if !self.alias_map.contains_key(&fn_did) {
            self.lack_of_alias.push(fn_did);
            return false;
        }

        // reborrow stmt here, since we need borrow mutable reference for lack_of_alias
        let stmt = self.cx.stmts().last().unwrap();

        let mut success = false;

        if !utils::is_env_var_exist("TESTGEN_DISABLE_ALIAS") {
            if let Some(vec) = self.detect_vulnerable_paths(&stmt) {
                for (var, rids) in vec {
                    // we should prove `rid_of(var) -> rid` in the region graph for each rid
                    let unproved = rids
                        .iter()
                        .filter(|rid| !self.region_graph.prove(self.rid_of(var), **rid))
                        .copied()
                        .collect::<Vec<_>>();

                    if unproved.is_empty() {
                        continue;
                    }

                    rap_debug!("[unsafe] variable {} lack of binding with {:?}", var, rids);

                    unproved.iter().for_each(|rid| {
                        success |= self.drop_source_from_rids(*rid);
                    });
                }
            }
        } else {
            let region_graph = self.region_graph.inner();
            let rid_nodes: Vec<_> = region_graph.node_indices().collect();
            let mut rng = rand::rng();

            if let Some(index) = rid_nodes.choose(&mut rng) {
                success |= self.drop_source_from_rids((*index).into());
            }
        }

        success
    }

    fn drop_source_from_rids(&mut self, rid: Rid) -> bool {
        let mut dropped_var = Vec::new();

        rap_debug!("drop source from: {rid:?}");

        self.region_graph.for_each_sink_from(rid, &mut |rid| {
            if let Some(var) = self.region_graph.get_node(rid).as_var() {
                if !self.var_state(var).is_dead() {
                    dropped_var.push(var);
                }
            }
        });

        for var in dropped_var.iter() {
            self.drop_var(*var);
        }

        !dropped_var.is_empty()
    }
}
