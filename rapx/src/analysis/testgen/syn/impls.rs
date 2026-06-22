use super::super::context::{Context, Stmt, StmtKind, Var};
use super::input::InputGen;
use super::{SynOption, Synthesizer};
use crate::analysis::testgen::context::{DUMMY_INPUT_VAR, DUMMY_UNIT_VAR, ExploitKind};
use crate::analysis::utils::path::PathResolver;
use rustc_middle::ty::{self, TyCtxt};

pub struct FuzzDriverSynImpl<'a, 'tcx, I: InputGen> {
    input_gen: I,
    option: SynOption,
    tcx: TyCtxt<'tcx>,
    resolver: &'a PathResolver<'tcx>,
}

impl<'a, 'tcx, I: InputGen> FuzzDriverSynImpl<'a, 'tcx, I> {
    pub fn new(
        input_gen: I,
        option: SynOption,
        tcx: TyCtxt<'tcx>,
        resolver: &'a PathResolver<'tcx>,
    ) -> Self {
        resolver.reset_non_local_def_ids();
        Self {
            input_gen,
            option,
            tcx,
            resolver,
        }
    }

    fn stmt_kind_str(&mut self, stmt: &Stmt<'tcx>, cx: &Context<'tcx>) -> String {
        match stmt.kind() {
            StmtKind::Call(call) => {
                // let generics = cx.tcx().generics_of(call.fn_did());
                let tcx = cx.tcx();

                let args = call.generic_args().into_iter().map(|arg| match arg.kind() {
                    ty::GenericArgKind::Lifetime(_) => {
                        ty::GenericArg::from(tcx.lifetimes.re_erased)
                    }
                    _ => arg,
                });
                let args = tcx.mk_args_from_iter(args);
                format!(
                    "{}({})",
                    self.resolver.path_str_with_args(call.fn_did(), args),
                    call.args
                        .iter()
                        .map(|arg| self.call_arg_str(*arg))
                        .collect::<Vec<_>>()
                        .join(", ")
                )
            }
            StmtKind::SpecialCall(path, vars) => {
                format!(
                    "{}({})",
                    path,
                    vars.iter()
                        .map(|arg| self.call_arg_str(*arg))
                        .collect::<Vec<_>>()
                        .join(", ")
                )
            }
            StmtKind::Input => {
                let ty = cx.type_of(stmt.place());
                rap_debug!("{} -> {}", stmt.place(), ty);
                self.input_gen.syn(ty, cx.tcx(), self.resolver)
            }
            StmtKind::Ref(var, mutability) => {
                format!("{}{}", mutability.ref_prefix_str(), self.var_str(*var))
            }
            StmtKind::AsRef(var) => {
                format!("{}.as_ref()", self.var_str(*var))
            }
            StmtKind::AsMut(var) => {
                format!("{}.as_mut()", self.var_str(*var))
            }
            // StmtKind::Deref(var, mutability) => {
            //     format!("{}*{}", mutability.ref_prefix_str(), self.var_str(**var))
            // }
            StmtKind::Exploit(var, kind) => match kind {
                ExploitKind::Debug => {
                    format!(
                        "println!(\"{}: {{:?}}\",{})",
                        self.var_str(*var),
                        self.var_str(*var)
                    )
                }
            },
            StmtKind::Array(vars) => {
                format!(
                    "[{}]",
                    vars.iter()
                        .map(|arg| self.var_str(*arg))
                        .collect::<Vec<_>>()
                        .join(", ")
                )
            }
            StmtKind::Tuple(vars) => {
                format!(
                    "({})",
                    vars.iter()
                        .map(|arg| self.var_str(*arg))
                        .collect::<Vec<_>>()
                        .join(", ")
                )
            }
            StmtKind::Comment(comment) => {
                format!("// {}", comment)
            }

            StmtKind::Ctor(dict) => {
                let adt_def = dict.adt_def;
                let adt_path = self.resolver.path_str(adt_def.did());
                let variant = adt_def.variant(dict.variant_idx);
                let variant_name = variant.name;
                let mut fields = Vec::new();
                for (field_name, field_var) in dict.field_vars.iter() {
                    fields.push(format!("{field_name}: {field_var}"));
                }

                if adt_def.is_struct() {
                    return format!("{adt_path} {{ {} }}", fields.join(", "));
                }

                // must be enum here
                if fields.is_empty() {
                    return format!("{adt_path}::{variant_name}");
                }
                return format!("{adt_path}::{variant_name} {{ {} }}", fields.join(", "));
            }
        }
    }

    fn call_arg_str(&self, arg: Var) -> String {
        if arg == DUMMY_UNIT_VAR {
            "()".to_string()
        } else {
            self.var_str(arg)
        }
    }

    fn var_str(&self, var: Var) -> String {
        assert!(
            var != DUMMY_UNIT_VAR && var != DUMMY_INPUT_VAR,
            "DUMMY_UNIT_VAR and DUMMY_INPUT_VAR should not be used in var_str"
        );
        format!("{}", var)
    }

    fn need_explicit_type_annotation(&self, stmt: &Stmt<'_>) -> bool {
        match stmt.kind() {
            StmtKind::AsRef(_) => true,
            StmtKind::AsMut(_) => true,
            _ => false,
        }
    }

    fn place_str(&self, stmt: &Stmt<'tcx>, cx: &Context<'tcx>) -> String {
        let var = stmt.place;
        if self.need_explicit_type_annotation(stmt) {
            format!(
                "{}{}: {}",
                cx.var_mutability(var).prefix_str(),
                self.var_str(var),
                self.resolver.ty_str(cx.type_of(var))
            )
        } else {
            format!(
                "{}{}",
                cx.var_mutability(var).prefix_str(),
                self.var_str(var)
            )
        }
    }

    fn stmt_str(&mut self, stmt: Stmt<'tcx>, cx: &Context<'tcx>) -> String {
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
        format!(
            "#![feature(allocator_api)]\nextern crate alloc;\nuse {}::*;",
            self.option.crate_name
        )
    }

    fn comment_var_tys(&mut self, cx: &Context<'tcx>, indent: &str) -> String {
        let mut ret = String::new();
        cx.vars().for_each(|var| {
            let ty = cx.type_of(var);
            ret.push_str(&format!(
                "{}// {}: {}\n",
                indent,
                var,
                self.resolver.ty_str(ty)
            ));
        });
        ret
    }

    fn main_str(&mut self, cx: &Context<'tcx>) -> String {
        let mut ret = String::new();
        ret.push_str("fn main() {\n");
        let indent = "    ";
        for stmt in cx.stmts() {
            ret.push_str(indent);
            ret.push_str(&self.stmt_str(stmt.clone(), cx));
            ret.push_str("\n");
        }
        ret.push_str(&self.comment_var_tys(cx, indent));
        ret.push_str("}\n");

        ret
    }
}

impl<'a, 'tcx, I: InputGen> Synthesizer<'tcx> for FuzzDriverSynImpl<'a, 'tcx, I> {
    fn syn(&mut self, cx: &Context<'tcx>, _tcx: TyCtxt<'tcx>) -> String {
        format!("{}\n{}", self.header_str(), self.main_str(cx))
    }
}
