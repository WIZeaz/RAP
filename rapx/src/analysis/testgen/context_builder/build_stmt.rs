use super::lifetime::{RegionNode, Rid, extract_rids};
use crate::analysis::testgen::context::{
    ApiCall, DUMMY_INPUT_VAR, DUMMY_UNIT_VAR, ExploitKind, StmtKind,
};
use crate::analysis::testgen::context::{Stmt, Var};
use crate::analysis::testgen::context_builder::var_state::VarState;
use crate::analysis::testgen::context_builder::{ContextBuilder, is_ty_moved_on_call};
use crate::analysis::testgen::utils;
use itertools::Itertools;
use rustc_hir::LangItem;
use rustc_middle::ty::{self, Ty, TyCtxt, TyKind};
use rustc_span::sym::{self};
use std::collections::VecDeque;

fn str_ref<'tcx>(region: ty::Region<'tcx>, tcx: TyCtxt<'tcx>) -> Ty<'tcx> {
    Ty::new_ref(tcx, region, tcx.types.str_, ty::Mutability::Not)
}

impl<'tcx, 'a> ContextBuilder<'tcx, 'a> {
    pub fn add_stmt(&mut self, stmt: Stmt<'tcx>) {
        let place = stmt.place();

        if place != DUMMY_UNIT_VAR {
            // update step_of(var)
            let num_steps = match stmt.kind() {
                StmtKind::Input => 0,
                StmtKind::Tuple(vars) | StmtKind::Array(vars) | StmtKind::SpecialCall(_, vars) => {
                    vars.iter().fold(0, |acc, &var| acc + self.step_of(var))
                }
                StmtKind::Ref(var, _) | StmtKind::AsRef(var) | StmtKind::AsMut(var) => {
                    self.step_of(*var)
                }
                StmtKind::Call(api_call) => {
                    api_call
                        .args()
                        .iter()
                        .fold(0, |acc, &arg| acc + self.step_of(arg))
                        + 1
                }
                StmtKind::Comment(_) | StmtKind::Exploit(..) => unreachable!(),
                StmtKind::Ctor(_ctor_dict) => todo!(),
            };
            self.set_step_of(place, num_steps);
        }

        self.cx.add_stmt(stmt);
    }

    pub fn comment_current_state(&mut self) {
        let comment: String = self
            .cx
            .vars()
            .filter_map(|var| {
                let state = self.var_state(var);
                if !state.is_dead() {
                    Some(format!(
                        "{}: {} ({})",
                        var,
                        self.var_state(var),
                        self.step_of(var)
                    ))
                } else {
                    None
                }
            })
            .join(", ");
        self.add_comment_stmt(comment);
    }

    pub fn add_exploit_stmt(&mut self, var: Var, use_kind: ExploitKind) -> Var {
        let retvar = self.mk_var(self.tcx.types.unit, false);
        self.add_stmt(Stmt::exploit(retvar, var, use_kind));
        retvar
    }

    pub fn add_comment_stmt(&mut self, comment: String) {
        self.add_stmt(Stmt::comment(comment));
    }

    pub fn add_box_stmt(&mut self, boxed: Var) -> Var {
        self.move_var(boxed);
        let ty = self.cx.type_of(boxed);
        // NOTE: we use ty instead of Box<ty> because we cannot
        // get DefId of `Box` on no-std environment.
        // this is sound for building lifetime contraints.
        let var = self.mk_var(ty, false);
        self.add_stmt(Stmt::box_(var, boxed));
        var
    }

    pub fn try_add_input_stmts_for_std_item(&mut self, ty: Ty<'tcx>) -> Option<Var> {
        let TyKind::Adt(adt_def, args) = ty.kind() else {
            return None;
        };
        let item_did = adt_def.did();

        if self.tcx.is_lang_item(item_did, LangItem::String) {
            let inner_var =
                self.try_add_input_stmts(str_ref(self.tcx.lifetimes.re_static, self.tcx), true);
            let var = self.mk_var(ty, false);
            self.move_var(inner_var);
            self.add_stmt(Stmt::special_call(
                "String::from".to_owned(),
                vec![inner_var],
                var,
            ));
            Some(var)
        } else if self.tcx.is_diagnostic_item(sym::Vec, item_did) {
            let inner_ty = args.type_at(0);
            let inner_var = self.try_add_input_stmts(Ty::new_array(self.tcx, inner_ty, 3), true); // FIXME: vec length is fixed to 3
            let var = self.mk_var(ty, false);
            self.move_var(inner_var);
            self.add_stmt(Stmt::special_call(
                "Vec::from".to_owned(),
                vec![inner_var],
                var,
            ));
            Some(var)
        } else if self.tcx.is_diagnostic_item(sym::Arc, item_did) {
            let inner_ty = args.type_at(0);
            let inner_var = self.try_add_input_stmts(inner_ty, true);
            let var = self.mk_var(ty, false);
            self.move_var(inner_var);
            self.add_stmt(Stmt::special_call(
                "std::sync::Arc::new".to_owned(),
                vec![inner_var],
                var,
            ));
            Some(var)
        } else {
            None
        }
    }

    /// try directly add input stmt to generate an instance of ty.
    /// This could fail since some types cannot be directly obtained from input,
    /// e.g., `[&i32]`. This function minimizes the number of input statements
    /// by making the types generated by the input statements as complex as possible.
    ///
    /// output: if ty can be directly generated, retrun DUMMY_INPUT_VAR,
    /// otherwise return a var representing the instance of ty.
    /// if must_instantiate is true, this function will always return a var
    /// representing the instance of ty.
    pub fn try_add_input_stmts(&mut self, ty: Ty<'tcx>, must_instantiate: bool) -> Var {
        if ty.is_unit() {
            return DUMMY_UNIT_VAR;
        }

        if let Some(var) = self.try_add_input_stmts_for_std_item(ty) {
            return var;
        }

        let var;
        match ty.kind() {
            ty::Adt(..) => {
                // TODO: Add Ctor Support
                var = DUMMY_INPUT_VAR;
            }
            ty::Ref(region, inner_ty, mutability) => {
                match (region.kind(), inner_ty.kind(), mutability) {
                    // Handle 'static
                    (ty::ReStatic, _, ty::Mutability::Mut) => {
                        panic!("&'static mut T is not supported");
                    }
                    (ty::ReStatic, _, ty::Mutability::Not) => {
                        var = DUMMY_INPUT_VAR;
                    }
                    // Handle &str/&mut str
                    (_, TyKind::Str, mutability) => {
                        match Ty::new_lang_item(self.tcx, self.tcx.types.unit, LangItem::String) {
                            Some(string_ty) => {
                                let inner_var = self.try_add_input_stmts(string_ty, true);
                                var = self.add_as_ref_stmt(
                                    inner_var,
                                    *mutability,
                                    Some(self.tcx.types.str_),
                                );
                            }
                            None => {
                                assert!(
                                    mutability.is_not(),
                                    "String is required to generate &mut str"
                                );
                                // if String is not available, we cannot generate &str by making string,
                                // so we fallback to the default implementation which generates &str from input
                                var = DUMMY_INPUT_VAR;
                            }
                        }
                    }
                    // handle &[T]/&mut [T]
                    (_, TyKind::Slice(slice_ty), _) => {
                        //TODO: the length of array is fixed to 3, but should be determined when generated
                        let inner_var =
                            self.try_add_input_stmts(Ty::new_array(self.tcx, *slice_ty, 3), true);
                        let box_var = self.add_box_stmt(inner_var);
                        var = self.add_slice_ref_stmt(box_var, *mutability, *slice_ty);
                    }

                    _ => {
                        let inner_var = self.try_add_input_stmts(*inner_ty, true);
                        let box_var = self.add_box_stmt(inner_var);
                        var = self.add_as_ref_stmt(
                            box_var,
                            *mutability,
                            Some(self.cx.type_of(inner_var)),
                        );
                    }
                }
            }
            ty::Tuple(tys) => {
                let mut vars = Vec::new();
                let mut should_instantiate = false;
                for inner_ty in tys.iter() {
                    let var = self.try_add_input_stmts(inner_ty, false);
                    vars.push(var);
                    if var != DUMMY_INPUT_VAR {
                        should_instantiate = true;
                    }
                }
                if !should_instantiate {
                    var = DUMMY_INPUT_VAR;
                } else {
                    for (inner_ty, inner_var) in tys.iter().zip(vars.iter_mut()) {
                        if *inner_var == DUMMY_INPUT_VAR {
                            *inner_var = self.try_add_input_stmts(inner_ty, true);
                        }
                        self.move_var(*inner_var);
                    }
                    var = self.mk_var(ty, false);
                    self.add_stmt(Stmt::tuple(var, vars));
                }
            }
            ty::Array(array_ty, array_len) => {
                let inner_var = self.try_add_input_stmts(*array_ty, false);
                if inner_var == DUMMY_INPUT_VAR {
                    var = DUMMY_INPUT_VAR;
                } else {
                    let len = array_len.try_to_target_usize(self.tcx).unwrap();
                    let mut vars = Vec::new();
                    for _ in 0..len {
                        let inner_var = self.try_add_input_stmts(*array_ty, true);
                        self.move_var(inner_var);
                        vars.push(inner_var);
                    }
                    var = self.mk_var(ty, false);
                    self.add_stmt(Stmt::array(var, vars));
                }
            }
            _ => {
                var = DUMMY_INPUT_VAR;
            }
        }

        if var == DUMMY_INPUT_VAR && must_instantiate {
            let input_var = self.mk_var(ty, true);
            self.add_stmt(Stmt::input(input_var));
            input_var
        } else {
            var
        }
    }

    pub fn add_input_stmts(&mut self, ty: Ty<'tcx>) -> Var {
        self.try_add_input_stmts(ty, true)
    }

    pub fn add_call_stmt(&mut self, mut call: ApiCall<'tcx>) -> Var {
        let tcx = self.tcx;
        let fn_did = call.fn_did;
        let fn_sig = utils::fn_sig_with_generic_args(fn_did, call.generic_args(), tcx);

        let output_ty = fn_sig.output();
        for idx in 0..fn_sig.inputs().len() {
            let input_ty = fn_sig.inputs()[idx];
            let arg = call.args[idx];
            if arg == DUMMY_INPUT_VAR {
                let var = self.add_input_stmts(input_ty);
                call.args[idx] = var;
            }
            let arg = call.args[idx];

            if is_ty_moved_on_call(input_ty, tcx) || arg.is_from_input() {
                rap_trace!("var {}:{} is moved on call", arg, input_ty);
                self.move_var(arg);
            }
        }

        let var = self.mk_var(output_ty, false);
        let stmt = Stmt::call(call, var);

        // build call lifetime constraints
        let real_fn_sig = stmt.mk_fn_sig_with_var_tys(&self.cx);
        rap_trace!("stmt: {:?}", stmt);
        rap_trace!("real_fn_sig: {:?}", real_fn_sig);

        let rids = extract_rids(real_fn_sig);

        // handling call subtyping and lifetime bounds
        self.pat_provider
            .get_patterns_with(fn_did, &stmt.as_apicall().generic_args, |patterns| {
                rap_debug!("patterns: {:?}", patterns);
                rap_debug!("regions: {:?}", rids);

                self.region_graph.add_edges_by_patterns(patterns, &rids);
            });

        // maintain context
        self.add_stmt(stmt);
        var
    }

    pub fn get_or_borrow(&mut self, var: Var, mutability: ty::Mutability) -> Var {
        if let VarState::Borrowed(mutbl, borrower) = self.var_state(var) {
            if mutbl == mutability && mutability.is_not() {
                return borrower;
            }
            // if the mutability does not match, or it is the exclusive mutability,
            // we need to borrow from the original var again with the desired mutability
            self.drop_var_from(var, true);
        }

        self.cx.lift_mutability(var, mutability);
        let ref_ty = Ty::new_ref(
            self.tcx,
            self.region_of(var),
            self.cx.type_of(var),
            mutability,
        );
        let new_var = self.mk_var(ref_ty, false);
        self.set_var_state(var, VarState::borrowed(mutability, new_var));
        rap_trace!(
            "var {} is borrowed as {} with mutability {:?}",
            var,
            new_var,
            mutability
        );
        self.add_stmt(Stmt::ref_(new_var, var, mutability));
        new_var
    }

    pub fn add_as_ref_stmt(
        &mut self,
        var: Var,
        mutability: ty::Mutability,
        as_ref_ty: Option<Ty<'tcx>>, // None represent the type of var
    ) -> Var {
        let ref_var = self.get_or_borrow(var, mutability);

        if as_ref_ty.is_none() {
            return ref_var;
        }

        let ref_ty = Ty::new_ref(
            self.tcx,
            self.region_of(var),
            as_ref_ty.unwrap_or(self.cx.type_of(var)),
            mutability,
        );

        let new_var = self.mk_var(ref_ty, false);
        if mutability.is_not() {
            self.add_stmt(Stmt::as_ref_(new_var, ref_var));
        } else {
            self.add_stmt(Stmt::as_mut_(new_var, ref_var));
        }
        new_var
    }

    pub fn add_slice_ref_stmt(
        &mut self,
        var: Var,
        mutability: ty::Mutability,
        slice_ty: Ty<'tcx>,
    ) -> Var {
        self.add_as_ref_stmt(var, mutability, Some(Ty::new_slice(self.tcx, slice_ty)))
    }
}

/// VarState maintain implementation
///
impl<'tcx, 'a> ContextBuilder<'tcx, 'a> {
    /// drop all vars depended on `source` and `source` itself if `exclude_source` is false.
    fn drop_var_from(&mut self, source: Var, exclude_source: bool) {
        let from_rid = self.rid_of(source).into();
        let mut visited = vec![false; self.region_graph.total_node_count()];
        let mut q: VecDeque<Rid> = VecDeque::from([from_rid]);
        visited[from_rid.index()] = true;

        let mut drop_vars = Vec::new();

        while let Some(rid) = q.pop_front() {
            if let RegionNode::Named(var) = self.region_graph.get_node(rid) {
                if self.var_state(var).is_dead() {
                    continue;
                }
                drop_vars.push(var);
            }
            for next_idx in self
                .region_graph
                .inner()
                .neighbors_directed(rid.into(), petgraph::Direction::Incoming)
            {
                if !visited[next_idx.index()] {
                    visited[next_idx.index()] = true;
                    q.push_back(next_idx.into());
                }
            }
        }

        let drop_vars = if exclude_source {
            drop_vars.into_iter().filter(|&var| var != source).collect()
        } else {
            drop_vars
        };

        rap_debug!(
            "drop vars: {}",
            drop_vars
                .iter()
                .rev()
                .map(|var| var.to_string())
                .collect::<Vec<_>>()
                .join(", ")
        );
        for var in drop_vars.into_iter().rev() {
            self.move_var(var);
            // if the type of var is not reference,
            // we need to add an explicit drop stmt to make it dropped immediately,
            // which is important for later statement generation.
            if !self.cx.type_of(var).is_ref() {
                self.add_drop_stmt(var);
            }
        }
    }

    pub fn add_drop_stmt(&mut self, var: Var) {
        self.add_stmt(Stmt::drop_(DUMMY_UNIT_VAR, var));
        self.explicit_droped_cnt += 1;
    }

    // pub fn drop_var(&mut self, dropped: Var) {
    //     rap_debug!("drop from: {dropped}");
    //     if !self.var_state(dropped).is_dropped() {
    //         self.drop_var_from(dropped);
    //         self.explicit_droped_cnt += 1;
    //     }
    // }

    pub fn move_var(&mut self, var: Var) {
        self.set_var_state(var, VarState::moved());
    }
}
