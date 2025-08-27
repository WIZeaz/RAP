use super::super::context::{Context, Stmt, StmtKind, Var};
use super::input::InputGen;
use super::{SynOption, Synthesizer};
use crate::analysis::testgen::context::UseKind;
use crate::rap_debug;
use rustc_middle::ty::{self, Ty, TyCtxt};

pub struct FuzzDriverSynImpl<I: InputGen> {
    input_gen: I,
    option: SynOption,
}

impl<I: InputGen> FuzzDriverSynImpl<I> {
    pub fn new(input_gen: I, option: SynOption) -> Self {
        Self { input_gen, option }
    }

    fn stmt_kind_str<'tcx>(&mut self, stmt: &Stmt<'tcx>, cx: &Context<'tcx>) -> String {
        match stmt.kind() {
            StmtKind::Call(call) => {
                // let generics = cx.tcx().generics_of(call.fn_did());
                let tcx = cx.tcx();

                let args = call.generic_args().into_iter().map(|arg| match arg.kind() {
                    ty::GenericArgKind::Lifetime(_) => {
                        ty::GenericArg::from(tcx.lifetimes.re_erased)
                    }
                    _ => *arg,
                });

                format!(
                    "{}({})",
                    cx.tcx()
                        .def_path_str_with_args(call.fn_did(), tcx.mk_args_from_iter(args)),
                    call.args
                        .iter()
                        .map(|arg| arg.to_string())
                        .collect::<Vec<_>>()
                        .join(", ")
                )
            }
            StmtKind::SpecialCall(path, vars) => {
                format!(
                    "{}({})",
                    path,
                    vars.iter()
                        .map(|arg| arg.to_string())
                        .collect::<Vec<_>>()
                        .join(", ")
                )
            }
            StmtKind::Input => {
                let ty = cx.type_of(stmt.place());
                rap_debug!("{} -> {}", stmt.place(), ty);
                self.input_gen.gen(ty, cx.tcx()).to_string()
            }
            StmtKind::Ref(var, mutability) => {
                format!("{}{}", mutability.ref_prefix_str(), self.var_str(**var))
            }
            StmtKind::Deref(var, mutability) => {
                format!("{}*{}", mutability.ref_prefix_str(), self.var_str(**var))
            }
            StmtKind::Drop(var) => {
                format!("drop({})", self.var_str(**var))
            }
            StmtKind::Box(var) => {
                format!("Box::new({})", self.var_str(**var))
            }
            StmtKind::Use(var, kind) => match kind {
                UseKind::Debug => {
                    format!(
                        "println!(\"{}: {{:?}}\",{})",
                        self.var_str(*var),
                        self.var_str(*var)
                    )
                }
            },
        }
    }

    fn var_str(&self, var: Var) -> String {
        format!("{}", var)
    }

    fn ty_str<'tcx>(&self, ty: Ty<'tcx>) -> String {
        format!("{}", ty)
        // format!(
        //     "{}",
        //     FmtPrinter::print_string(tcx, Namespace::TypeNS, |fmt| fmt.pretty_print_type(ty))
        //         .unwrap()
        // )
    }

    fn need_explicit_type_annotation(&self, stmt: &Stmt<'_>) -> bool {
        match stmt.kind() {
            StmtKind::Deref(..) => true,
            _ => false,
        }
    }

    fn place_str<'tcx>(&self, stmt: &Stmt<'tcx>, cx: &Context<'tcx>) -> String {
        let var = stmt.place;
        if self.need_explicit_type_annotation(stmt) {
            format!(
                "{}{}: {}",
                cx.var_mutability(var).prefix_str(),
                self.var_str(var),
                self.ty_str(cx.type_of(var))
            )
        } else {
            format!(
                "{}{}",
                cx.var_mutability(var).prefix_str(),
                self.var_str(var)
            )
        }
    }

    fn stmt_str<'tcx>(&mut self, stmt: Stmt<'tcx>, cx: &Context<'tcx>) -> String {
        let var = stmt.place;
        let var_ty = cx.type_of(var);
        let stmt_str = self.stmt_kind_str(&stmt, cx);
        if !var_ty.is_unit() || (var_ty.is_unit() && var.is_from_input()) {
            format!("let {} = {};", self.place_str(&stmt, cx), stmt_str)
        } else {
            format!("{};", stmt_str)
        }
    }

    fn header_str(&self) -> String {
        format!("use {}::*;", self.option.crate_name)
    }

    fn main_str<'tcx>(&mut self, cx: &Context<'tcx>) -> String {
        let mut ret = String::new();
        ret.push_str("fn main() {\n");
        let indent = "    ";
        for stmt in cx.stmts() {
            ret.push_str(indent);
            ret.push_str(&self.stmt_str(stmt.clone(), cx));
            ret.push_str("\n");
        }
        ret.push_str("}\n");
        ret
    }
}

impl<'tcx, I: InputGen> Synthesizer<'tcx> for FuzzDriverSynImpl<I> {
    fn syn(&mut self, cx: &Context<'tcx>, tcx: TyCtxt<'tcx>) -> String {
        format!("{}\n{}", self.header_str(), self.main_str(cx))
    }
}
