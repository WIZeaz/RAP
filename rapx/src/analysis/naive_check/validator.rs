use itertools::Itertools;
use rustc_ast::{BindingMode, Mutability, UnOp};
use rustc_hir::{Expr, ExprKind, HirId, QPath, def_id::LocalDefId};
use rustc_hir::{LetStmt, Pat, PatKind, Stmt, StmtKind};
use rustc_infer::infer::TyCtxtInferExt;
use rustc_middle::ty::ParamEnv;
use rustc_middle::ty::{self, Ty, TyCtxt};
use rustc_span::{Ident, Span};
use rustc_trait_selection::infer::InferCtxtExt as _;
use std::collections::HashMap;

pub fn is_ty_impl_copy<'tcx>(ty: Ty<'tcx>, tcx: TyCtxt<'tcx>) -> bool {
    let infcx = tcx.infer_ctxt().build(ty::TypingMode::PostAnalysis);
    let param_env = ParamEnv::empty();
    let ret = infcx.type_is_copy_modulo_regions(param_env, ty);
    rap_trace!("[is_ty_impl_copy] ty: {}, is_copy: {}", ty, ret);
    ret
}

fn ty_contain_lifetime<'tcx>(ty: Ty<'tcx>) -> bool {
    ty.walk().any(|arg| arg.as_region().is_some())
}

#[derive(Debug, Copy, Clone)]
pub enum VarState {
    Live,
    Borrowed(Mutability, usize),
    Moved,
}

impl VarState {
    fn as_mutability(&self) -> Option<Mutability> {
        match self {
            VarState::Borrowed(mutability, _) => Some(*mutability),
            _ => None,
        }
    }
    fn is_moved(&self) -> bool {
        matches!(self, VarState::Moved)
    }
    fn is_live(&self) -> bool {
        matches!(self, VarState::Live)
    }
}

#[derive(Debug, Copy, Clone)]
pub struct ValidateError {
    pub span: Span,
    pub kind: ValidateErrorKind,
}

#[derive(Debug, Copy, Clone)]
pub enum ValidateErrorKind {
    ValidateFail(ValidateFailReason),
    InvalidLetBinding,
    InvalidStmtKind,
    InvalidExprKind,
    InvalidPathRes,
    InvalidVarStateTrans(VarState, VarState),
}

impl ValidateErrorKind {
    pub fn is_validate_fail(&self) -> bool {
        matches!(self, ValidateErrorKind::ValidateFail(_))
    }

    pub fn error_dianostic_message(&self) -> String {
        match self {
            ValidateErrorKind::ValidateFail(reason) => match reason {
                ValidateFailReason::MutBorrowAfterMut => {
                    "Mutable borrow after mutable borrow".to_owned()
                }
                ValidateFailReason::MutBorrowAfterImmut => {
                    "Mutable borrow after immutable borrow".to_owned()
                }
                ValidateFailReason::ImmutBorrowAfterMut => {
                    "Immutable borrow after mutable borrow".to_owned()
                }
            },

            ValidateErrorKind::InvalidVarStateTrans(prev_state, curr_state) => {
                format!(
                    "Invalid variable state transition from {:?} to {:?}",
                    prev_state, curr_state
                )
            }
            ValidateErrorKind::InvalidLetBinding => "Invalid let binding pattern".to_owned(),
            ValidateErrorKind::InvalidStmtKind => "Invalid statement kind".to_owned(),
            ValidateErrorKind::InvalidExprKind => "Invalid expression kind".to_owned(),
            ValidateErrorKind::InvalidPathRes => "Invalid path resolution".to_owned(),
        }
    }
}

#[derive(Debug, Copy, Clone)]
pub enum ValidateFailReason {
    MutBorrowAfterMut,
    MutBorrowAfterImmut,
    ImmutBorrowAfterMut,
}
pub type ValidateResult<T = ()> = Result<T, ValidateError>;

pub struct SynValidator<'tcx> {
    tcx: TyCtxt<'tcx>,
    state_map: HashMap<HirId, VarState>,
    ident_map: HashMap<HirId, Ident>,
    borrow_map: HashMap<HirId, Vec<HirId>>,
    fn_did: LocalDefId,
}

impl<'tcx> SynValidator<'tcx> {
    pub fn new(tcx: TyCtxt<'tcx>, fn_did: LocalDefId) -> Self {
        SynValidator {
            tcx,
            state_map: HashMap::new(),
            ident_map: HashMap::new(),
            borrow_map: HashMap::new(),
            fn_did,
        }
    }

    fn hir_type(&self, hid: HirId) -> Ty<'tcx> {
        self.tcx.typeck(self.fn_did).node_type(hid)
    }

    fn hir_ident(&self, hid: HirId) -> String {
        self.ident_map
            .get(&hid)
            .map(|i| i.to_string())
            .unwrap_or("UNKNOWN".to_string())
    }

    fn hir_debug_str(&self, hid: HirId) -> String {
        let ident = self.hir_ident(hid);
        format!("{}({:?})", ident, hid)
    }

    pub fn add_stmt(&mut self, stmt: &Stmt<'tcx>) -> ValidateResult {
        let span = stmt.span;
        match stmt.kind {
            StmtKind::Let(LetStmt { pat, init, .. }) => {
                let (_, hid, ident) = self.as_let_binding(*pat)?;
                if let Some(expr) = init {
                    let hids = self.validate_expr(expr)?;
                    let ret_ty = self.hir_type(hid);

                    if ty_contain_lifetime(ret_ty) {
                        self.borrow_map.insert(hid, hids);
                    } else {
                        for hid in hids {
                            self.return_var(hid);
                        }
                    }
                }

                self.ident_map.insert(hid, ident);
                self.state_map.insert(hid, VarState::Live);

                rap_info!(
                    "Let binding: {}({}):{:?} at {:?}",
                    ident,
                    hid,
                    self.hir_type(hid),
                    span
                );
            }
            StmtKind::Semi(expr) | StmtKind::Expr(expr) => {
                let hids = self.validate_expr(expr)?;
                hids.into_iter().for_each(|hid| self.return_var(hid));
            }
            _ => {
                return Err(ValidateError {
                    span,
                    kind: ValidateErrorKind::InvalidStmtKind,
                });
            }
        }
        self.log_state();
        Ok(())
    }

    pub fn as_let_binding(&self, pat: &Pat<'tcx>) -> ValidateResult<(BindingMode, HirId, Ident)> {
        match pat.kind {
            PatKind::Binding(mode, hid, ident, pat) => Ok((mode, hid, ident)),
            _ => Err(ValidateError {
                span: pat.span,
                kind: ValidateErrorKind::InvalidLetBinding,
            }),
        }
    }

    pub fn expect_path(&mut self, expr: &Expr<'tcx>) -> ValidateResult<HirId> {
        match expr.kind {
            ExprKind::Path(QPath::Resolved(_, path)) => match path.res {
                rustc_hir::def::Res::Local(hid) => Ok(hid),
                _ => Err(ValidateError {
                    span: expr.span,
                    kind: ValidateErrorKind::InvalidPathRes,
                }),
            },
            ExprKind::Index(expr, _, _) => self.expect_path(expr),
            ExprKind::Unary(UnOp::Deref, expr) => {
                // reborrow
                let hid = self.expect_path(expr)?;

                let borrowed_hid = self.reborrow_var(hid, expr.span)?;

                return Ok(borrowed_hid);
            }
            ExprKind::Array(_) => {
                // temporary array, create a new variable for it
                self.state_map.insert(expr.hir_id, VarState::Live);
                self.ident_map
                    .insert(expr.hir_id, Ident::from_str("temp_array"));
                Ok(expr.hir_id)
            }
            _ => {
                rap_error!("Unexpected Expr Kind: {:?}", expr.kind);
                Err(ValidateError {
                    span: expr.span,
                    kind: ValidateErrorKind::InvalidExprKind,
                })
            }
        }
    }

    fn log_state(&self) {
        rap_info!("Current variable states:");
        for (hid, state) in &self.state_map {
            rap_info!("  {}: {:?}", self.hir_debug_str(*hid), state);
            rap_info!(
                "    borrow: {}",
                self.borrow_map
                    .get(hid)
                    .map(|hids| { hids.iter().map(|hid| self.hir_debug_str(*hid)).join(", ") })
                    .unwrap_or("None".to_string())
            );
        }
    }

    pub fn return_var(&mut self, hid: HirId) {
        let node_str = self.hir_debug_str(hid);
        rap_info!("Returning variable {}", node_str);
        let Some(state) = self.state_map.get_mut(&hid) else {
            panic!("variable {} is not in state map", node_str);
        };
        match state {
            VarState::Borrowed(mutability, count) => {
                if *count == 1 {
                    *state = VarState::Live;
                } else {
                    *state = VarState::Borrowed(*mutability, *count - 1);
                }
            }
            VarState::Moved => {
                panic!("variable {} is not borrowed, cannot be returned", node_str);
            }
            VarState::Live => {}
        }
    }

    fn borrow_inc(&mut self, hid: HirId) {
        let node_str = self.hir_debug_str(hid);
        rap_info!("Increasing borrow count of variable {}", node_str);
        let Some(state) = self.state_map.get_mut(&hid) else {
            panic!("variable {} is not in state map", node_str);
        };
        match state {
            VarState::Borrowed(mutability, count) => {
                *count += 1;
                if mutability.is_mut() && *count > 1 {
                    panic!("variable {} is mutably borrowed more than once", node_str);
                }
                rap_info!("Variable {} borrow count increased to {}", node_str, count);
            }
            VarState::Moved | VarState::Live => {
                panic!("variable {} is not borrowed, cannot be increased", node_str);
            }
        }
    }

    pub fn borrow_var(&mut self, hid: HirId, mutability: Mutability, span: Span) -> ValidateResult {
        rap_info!(
            "Borrowing variable {} with mutability {:?} at {:?}",
            self.hir_debug_str(hid),
            mutability,
            span
        );
        let Some(prev_state) = self.state_map.get(&hid) else {
            panic!("variable {} is not in state map", self.hir_debug_str(hid));
        };

        match prev_state {
            VarState::Moved => {
                return Err(ValidateError {
                    span,
                    kind: ValidateErrorKind::InvalidVarStateTrans(
                        *prev_state,
                        VarState::Borrowed(mutability, 1),
                    ),
                });
            }
            VarState::Live => {
                self.state_map
                    .insert(hid, VarState::Borrowed(mutability, 1));
                return Ok(());
            }
            VarState::Borrowed(prev_mut, count) => {
                let reason = match (prev_mut, mutability) {
                    (Mutability::Mut, Mutability::Mut) => ValidateFailReason::MutBorrowAfterMut,
                    (Mutability::Not, Mutability::Mut) => ValidateFailReason::MutBorrowAfterImmut,
                    (Mutability::Mut, Mutability::Not) => ValidateFailReason::ImmutBorrowAfterMut,
                    (Mutability::Not, Mutability::Not) => {
                        self.state_map
                            .insert(hid, VarState::Borrowed(mutability, count + 1));
                        return Ok(());
                    }
                };
                return Err(ValidateError {
                    span: span,
                    kind: ValidateErrorKind::ValidateFail(reason),
                });
            }
        }
    }

    // move_var does not return var, we just mark the variable as moved.
    // The caller stmt is responsible for returning the variable if needed.
    fn move_var(&mut self, hid: HirId, span: Span) -> ValidateResult {
        rap_info!("Moving variable {} at {:?}", self.hir_debug_str(hid), span);
        if let Some(prev_state) = self.state_map.insert(hid, VarState::Moved) {
            if prev_state.is_moved() {
                return Err(ValidateError {
                    span,
                    kind: ValidateErrorKind::InvalidVarStateTrans(prev_state, VarState::Moved),
                });
            }
        }
        Ok(())
    }

    fn reborrow_var(&mut self, hid: HirId, span: Span) -> ValidateResult<HirId> {
        rap_info!(
            "Reborrowing variable {} at {:?}",
            self.hir_debug_str(hid),
            span
        );

        let borrowed_hids = self.borrow_map.get(&hid).cloned().unwrap_or_default();
        if borrowed_hids.len() != 1 {
            panic!(
                "Dereferencing a variable with multiple borrows: {}",
                self.hir_debug_str(hid)
            );
        }
        let borrowed_hid = borrowed_hids[0];

        let Some(hir_state) = self.state_map.get(&hid) else {
            panic!("variable {} is not in state map", self.hir_debug_str(hid));
        };

        // This is first time hir be reborrwed,
        // we return the borrower and move this variable
        if hir_state.is_live() {
            self.move_var(hid, span)?;
            self.return_var(borrowed_hid);
        }

        Ok(borrowed_hid)
    }

    pub fn validate_call_arg_expr(&mut self, expr: &Expr<'tcx>) -> ValidateResult<Vec<HirId>> {
        let mut hids = Vec::new();
        match expr.kind {
            ExprKind::AddrOf(_, mutability, this_expr) => {
                let hid = self.expect_path(this_expr)?;
                hids.push(hid);
                self.borrow_var(hid, mutability, expr.span)?;
                rap_info!(
                    "Borrowing variable with {} at {:?}",
                    self.hir_debug_str(hid),
                    expr.span
                );
            }

            // hid moved after function call
            ExprKind::Path(QPath::Resolved(_, path)) => match path.res {
                rustc_hir::def::Res::Local(hid) => {
                    let ty = self.hir_type(hid);
                    if let Some(borrowers) = self.borrow_map.get(&hid) {
                        hids.extend(borrowers);
                    }
                    if !is_ty_impl_copy(ty, self.tcx) {
                        self.move_var(hid, expr.span)?;
                    } else {
                        rap_info!("Variable {} is Copy", self.hir_debug_str(hid));
                    }
                }
                _ => {
                    return Err(ValidateError {
                        span: expr.span,
                        kind: ValidateErrorKind::InvalidPathRes,
                    });
                }
            },
            ExprKind::Call(_, exprs) => {
                if exprs.len() != 1 {
                    rap_error!(
                        "Unexpected number of arguments in call expression: {}",
                        exprs.len()
                    );
                    return Err(ValidateError {
                        span: expr.span,
                        kind: ValidateErrorKind::InvalidExprKind,
                    });
                }
                self.validate_call_arg_expr(&exprs[0])?;
            }
            ExprKind::Lit(..) => {} // nothing happens for literal expressions
            _ => {
                rap_error!("Other expression: {:?}", expr.kind);
                return Err(ValidateError {
                    span: expr.span,
                    kind: ValidateErrorKind::InvalidExprKind,
                });
            }
        }
        Ok(hids)
    }

    /// validate the expression and return the variables (HirId) that are borrowed in the expression.
    pub fn validate_expr(&mut self, expr: &Expr<'tcx>) -> ValidateResult<Vec<HirId>> {
        let mut hids = Vec::new();
        match expr.kind {
            ExprKind::AddrOf(_, mutability, this_expr) => {
                let hid = self.expect_path(this_expr)?;
                hids.push(hid);
                self.borrow_var(hid, mutability, expr.span)?;
                rap_info!(
                    "Borrowing variable with {} at {:?}",
                    self.hir_debug_str(hid),
                    expr.span
                );
            }
            // `ExprKind::If` happens in `let x = if Some(x) = f(..) {x} else {return;} ;`
            // We currently only validate the condition expression, this should not threat validity
            // of our validator because this kind of expr only occurs in certain circumstances.
            ExprKind::If(cond_expr, ..) => match cond_expr.kind {
                ExprKind::Let(let_expr) => {
                    let cond_hids = self.validate_expr(let_expr.init)?;
                    hids.extend(cond_hids);
                }
                _ => {
                    rap_error!("Invalid if condition expression: {:?}", cond_expr.kind);
                    return Err(ValidateError {
                        span: cond_expr.span,
                        kind: ValidateErrorKind::InvalidExprKind,
                    });
                }
            },
            ExprKind::Call(_, exprs) => {
                for (i, expr) in exprs.iter().enumerate() {
                    rap_debug!("call expr #{}: {:?}", i, expr.kind);
                    let expr_hids = self.validate_call_arg_expr(expr)?;
                    hids.extend(expr_hids);
                }
            }
            ExprKind::MethodCall(_, receiver, exprs, _) => {
                rap_debug!("method call receiver: {:?}", receiver.kind);
                let receiver_hid = self.expect_path(receiver)?;

                let method_did = self
                    .tcx
                    .typeck(self.fn_did)
                    .type_dependent_def_id(expr.hir_id)
                    .unwrap();

                let fn_sig = self.tcx.fn_sig(method_did).skip_binder().skip_binder();

                let self_ty = fn_sig.inputs().first().unwrap();
                rap_info!("method call self arg type: {}", self_ty);

                // adhoc for FRIES's `fr`
                if self_ty.is_ref() && self.hir_ident(receiver_hid) != "fr" {
                    self.borrow_var(
                        receiver_hid,
                        self_ty.ref_mutability().unwrap(),
                        receiver.span,
                    )?;
                    hids.push(receiver_hid);
                }

                for (i, expr) in exprs.iter().enumerate() {
                    rap_debug!("method call arg #{}: {:?}", i, expr.kind);
                    let expr_hids = self.validate_call_arg_expr(expr)?;
                    hids.extend(expr_hids);
                }
            }
            ExprKind::Array(exprs) | ExprKind::Tup(exprs) => {
                for (i, expr) in exprs.iter().enumerate() {
                    let expr_hids = self.validate_expr(expr)?;
                    hids.extend(expr_hids);
                }
            }
            ExprKind::Lit(_) => {} // nothing happens for literal expressions
            ExprKind::Block(..) => {} // block is println!
            ExprKind::Struct(_, fields, _) => {
                for field in fields {
                    let expr_hids = self.validate_expr(field.expr)?;
                    hids.extend(expr_hids);
                }
            }
            ExprKind::Unary(_, expr) => {
                let expr_hids = self.validate_expr(expr)?;
                hids.extend(expr_hids);
            }

            ExprKind::Path(_) => {}
            _ => {
                rap_error!("Other expression: {:?}", expr.kind);
                return Err(ValidateError {
                    span: expr.span,
                    kind: ValidateErrorKind::InvalidExprKind,
                });
            }
        }
        Ok(hids)
    }
}
