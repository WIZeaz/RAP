use crate::rap_debug;

use super::super::context::{Context, Stmt, StmtKind, Var};
use super::input::InputGen;
use super::{SynOption, Synthesizer};
use rustc_middle::ty::{self, Ty, TyCtxt};

fn debug_state() -> bool {
    false
    // true
}

pub struct FuzzDriverSynImpl<I: InputGen> {
    input_gen: I,
    option: SynOption,
}

impl<I: InputGen> FuzzDriverSynImpl<I> {
    pub fn new(input_gen: I, option: SynOption) -> Self {
        Self { input_gen, option }
    }

    fn stmt_kind_str<'tcx>(&mut self, stmt: &Stmt<'tcx>, cx: &impl Context<'tcx>) -> String {
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
            StmtKind::Input => {
                let ty = cx.type_of(stmt.place()).peel_refs();
                rap_debug!("{} -> {}", stmt.place(), ty);
                self.input_gen.gen(ty, cx.tcx()).to_string()
            }
            StmtKind::Ref(var, mutability) => {
                format!("{}{}", mutability.ref_prefix_str(), self.var_str(**var))
            }
            StmtKind::Deref(var) => {
                format!("*{}", self.var_str(**var))
            }
            StmtKind::Drop(var) => {
                format!("drop({})", self.var_str(**var))
            }
            _ => todo!(),
        }
    }

    fn var_str(&self, var: Var) -> String {
        format!("{}", var)
    }

    fn ty_str<'tcx>(&self, ty: Ty<'tcx>, tcx: TyCtxt<'tcx>) -> String {
        if debug_state() {
            return format!("{:?}", ty);
        }
        format!("{}", ty)
        // format!(
        //     "{}",
        //     FmtPrinter::print_string(tcx, Namespace::TypeNS, |fmt| fmt.pretty_print_type(ty))
        //         .unwrap()
        // )
    }

    fn stmt_str<'tcx>(&mut self, stmt: Stmt<'tcx>, cx: &impl Context<'tcx>) -> String {
        let var = stmt.place;
        let var_ty = cx.type_of(var);
        let stmt_str = self.stmt_kind_str(&stmt, cx);
        if !var_ty.is_unit() || (var_ty.is_unit() && var.is_input()) {
            format!(
                "let {}{}: {} = {};",
                cx.var_mutability(var).prefix_str(),
                self.var_str(var),
                self.ty_str(
                    if !debug_state() {
                        cx.tcx().erase_regions(var_ty)
                    } else {
                        var_ty
                    },
                    cx.tcx()
                ),
                stmt_str
            )
        } else {
            format!("{};", stmt_str)
        }
    }

    fn header_str(&self) -> String {
        format!("use {}::*;", self.option.crate_name)
    }

    fn main_str<'tcx>(&mut self, cx: &impl Context<'tcx>) -> String {
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
    fn syn<C: Context<'tcx>>(&mut self, cx: C, tcx: TyCtxt<'tcx>) -> String {
        format!("{}\n{}", self.header_str(), self.main_str(&cx))
    }
}
