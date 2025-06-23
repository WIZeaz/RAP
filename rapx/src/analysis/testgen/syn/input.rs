use crate::rap_debug;
use rand::{rng, Rng};
use rustc_abi::FIRST_VARIANT;
use rustc_hir::def::Namespace;
use rustc_middle::ty::cast::IntTy;
use rustc_middle::ty::print::{PrettyPrinter, Printer};
use rustc_middle::ty::{self, print, Ty, TyCtxt, TyKind};
use rustc_span::def_id::DefId;
pub trait InputGen {
    fn gen<'tcx>(&mut self, ty: Ty<'tcx>, tcx: TyCtxt<'tcx>) -> impl ToString;
}

pub struct SillyInputGen;

impl InputGen for SillyInputGen {
    fn gen<'tcx>(&mut self, ty: Ty<'tcx>, tcx: TyCtxt<'tcx>) -> impl ToString {
        let ty = ty.peel_refs();
        match ty.kind() {
            TyKind::Bool => "false".to_owned(),
            TyKind::Int(_) => "42".to_owned(),
            TyKind::Uint(_) => "42".to_owned(),
            TyKind::Float(_) => "42.0".to_owned(),
            TyKind::Str => "\"don't panic\"".to_owned(),
            TyKind::Char => "'a'".to_owned(),
            TyKind::Array(inner_ty, const_) => {
                let len = const_
                    .to_value()
                    .try_to_target_usize(tcx)
                    .expect("Failed to get array length");
                let mut arr: Vec<String> = Vec::new();
                for _ in 0..len {
                    arr.push(self.gen(*inner_ty, tcx).to_string());
                }
                format!("[{}]", arr.join(", "))
            }
            TyKind::Tuple(tys) => {
                let mut fields = Vec::new();
                for ty in tys.iter() {
                    fields.push(self.gen(ty, tcx).to_string());
                }
                format!("({})", fields.join(", "))
            }
            TyKind::Adt(adt_def, generic_arg) => {
                let name = get_trimmed_path(adt_def.did(), tcx, Namespace::TypeNS);
                if adt_def.is_struct() {
                    // generate input for each field
                    let mut fields = Vec::new();
                    for field in adt_def.all_fields() {
                        let field_name = field.name.to_string();
                        let field_type = field.ty(tcx, generic_arg);
                        let field_input = self.gen(field_type, tcx).to_string();
                        fields.push(format!("{field_name}: {field_input}"));
                    }
                    return format!("{name} {{ {} }}", fields.join(", "));
                }
                if adt_def.is_enum() {
                    let mut fields = Vec::new();
                    // Always generate the first variant

                    let variant_def = adt_def.variant(FIRST_VARIANT);
                    let variant_name = variant_def.name.to_string();
                    for field in variant_def.fields.iter() {
                        let field_name = field.name.to_string();
                        let field_type = field.ty(tcx, generic_arg);
                        let field_input = self.gen(field_type, tcx).to_string();
                        fields.push(format!("{field_name}: {field_input}"));
                    }
                    if fields.is_empty() {
                        return format!("{name}::{variant_name}");
                    }
                    return format!("{name}::{variant_name} {{ {} }}", fields.join(", "));
                }
                panic!("Unsupported ADT: {:?}", ty)
            }
            TyKind::Slice(inner_ty) => {
                let len = 3; // Fixed length for simplicity
                let element = self.gen(*inner_ty, tcx).to_string();
                format!("[{}; {}]", element, len)
            }
            _ => panic!("Unsupported type: {:?}", ty),
        }
    }
}

fn get_trimmed_path<'tcx>(def_id: DefId, tcx: TyCtxt<'tcx>, namespace: Namespace) -> String {
    let mut printer = print::FmtPrinter::new(tcx, namespace);
    let result = printer.force_print_trimmed_def_path(def_id);
    let mut ret: String;
    match result {
        Ok(val) => {
            if val {
            } else {
                let _ = printer.print_def_path(def_id, &[]);
            }
            ret = printer.into_buffer();
        }
        Err(e) => {
            rap_debug!("Error printing trimmed path: {:?}", e);
            ret = tcx.def_path_str(def_id);
        }
    };
    rap_debug!("trimmed_path: {}", ret);
    ret
}
