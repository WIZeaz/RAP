mod validator;

use crate::{
    analysis::Analysis,
    utils::log::{relative_pos_range, span_to_filename, span_to_line_number, span_to_source_code},
};
use annotate_snippets::{Annotation, Level, Renderer, Snippet};
use glob::Pattern;
use rustc_ast::{BindingMode, Mutability};
use rustc_hir::{
    BodyId, Expr, ExprKind, FnDecl, HirId, Path, QPath,
    def_id::{DefId, LOCAL_CRATE, LocalDefId},
    intravisit::FnKind,
};
use rustc_hir::{LetStmt, Pat, PatKind, Stmt, StmtKind};
use rustc_middle::query::Key;
use rustc_middle::ty::{Ty, TyCtxt};
use rustc_span::{Ident, Span};
use validator::{
    SynValidator, ValidateError, ValidateErrorKind, ValidateFailReason, ValidateResult,
};

pub struct NaiveSynAnalysis<'tcx> {
    tcx: TyCtxt<'tcx>,
    validate: bool,
    glob: Option<Pattern>,
}

impl<'tcx> Analysis for NaiveSynAnalysis<'tcx> {
    fn name(&self) -> &'static str {
        "Naive Synthesis Checker"
    }

    fn run(&mut self) {
        struct Visitor<'a, 'tcx> {
            analyzer: &'a mut NaiveSynAnalysis<'tcx>,
        }

        impl<'a, 'tcx> rustc_hir::intravisit::Visitor<'tcx> for Visitor<'a, 'tcx> {
            fn visit_fn(
                &mut self,
                fk: FnKind<'tcx>,
                fd: &'tcx FnDecl<'tcx>,
                b: BodyId,
                span: Span,
                id: LocalDefId,
            ) -> Self::Result {
                self.analyzer.check_fn(id);

                rustc_hir::intravisit::walk_fn(self, fk, fd, b, id);
            }
        }

        self.tcx
            .hir_visit_all_item_likes_in_crate(&mut Visitor { analyzer: self });
    }

    fn reset(&mut self) {}
}

/// Naive Checker check whether a Rust program can be synthesized with a non-lifetime aware synthesis.
/// It checks the program with following rules:
/// 1. A variable can be borrowed mutably only once at a time.
/// 2. A variable without reference type will be regarded as removed after it is used in a function call.
/// 3. If a function call does not have a non-unit return type, the variables used in the function call will be regarded as borrowed.
/// 4. If a function call have a unit return type, the variables borrowed in the funciton call will be returnted.
/// Naive Checker work on programs' HIR.
impl<'tcx> NaiveSynAnalysis<'tcx> {
    pub fn new(tcx: TyCtxt<'tcx>, glob: Option<String>) -> Self {
        let glob = glob.map(|pattern| {
            Pattern::new(&pattern)
                .unwrap_or_else(|err| panic!("invalid glob pattern `{pattern}`: {err}"))
        });
        NaiveSynAnalysis {
            tcx,
            validate: true,
            glob,
        }
    }

    pub fn is_valid(&self) -> bool {
        self.validate
    }

    fn check_fn(&mut self, local_id: LocalDefId) {
        let fn_name = self.tcx.def_path_str(local_id);
        if !matches_fn_path(&fn_name, self.glob.as_ref()) {
            return;
        }
        rap_info!("Checking function: {}", fn_name);
        let tcx = self.tcx;
        let body = tcx.hir_body_owned_by(local_id);
        let mut validator = SynValidator::new(tcx, local_id);
        let expr = body.value;
        let ExprKind::Block(block, _) = expr.kind else {
            unreachable!("Function {} does not have a block expression", fn_name);
        };

        let renderer = Renderer::styled();
        let body_span = tcx.hir_span(body.id().hir_id);
        let source = span_to_source_code(body_span);
        let filename = span_to_filename(body_span);
        let line_start = span_to_line_number(body_span);
        for stmt in block.stmts {
            if let Err(e) = validator.add_stmt(stmt) {
                self.validate = false;

                // print diagnostic

                let span = e.span;
                let diag = e.kind.error_dianostic_message();
                let snippet = Snippet::source(&source)
                    .line_start(line_start)
                    .origin(&filename)
                    .annotation(
                        Level::Error
                            .span(relative_pos_range(body_span, span))
                            .label(&diag),
                    );
                let title = format!("{:?}, span={:?}", e.kind, span);
                let message = Level::Error.title(&title).snippet(snippet);
                let rendered_message = renderer.render(message);
                rap_error!("{}", rendered_message);

                if e.kind.is_validate_fail() {
                    std::fs::write("naive-check.txt", format!("INVALID: {}", diag)).unwrap();
                } else {
                    std::fs::write("naive-check.txt", format!("UNSUPPORT: {}", diag)).unwrap();
                }
                return;
            }
        }
    }
}

fn matches_fn_path(fn_name: &str, glob: Option<&Pattern>) -> bool {
    glob.is_none_or(|pattern| pattern.matches(fn_name))
}

#[cfg(test)]
mod tests {
    use super::matches_fn_path;
    use glob::Pattern;

    #[test]
    fn glob_matches_full_function_path() {
        let glob = Pattern::new("crate::module::target*").unwrap();

        assert!(matches_fn_path("crate::module::target_fn", Some(&glob)));
        assert!(!matches_fn_path("crate::module::other_fn", Some(&glob)));
    }

    #[test]
    fn empty_glob_matches_everything() {
        assert!(matches_fn_path("crate::module::anything", None));
    }
}
