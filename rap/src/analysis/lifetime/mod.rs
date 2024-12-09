use std::io::Write;

use crate::{rap_info, utils::fs};

use super::core::alias::{mop::MopAlias, FnRetAlias, RetAlias};
use rustc_hir::{def_id::DefId, intravisit::{self, Visitor}};
use rustc_middle::ty::TyCtxt;
use serde::{Deserialize, Serialize};

pub struct Lifetime<'tcx> {
    pub tcx: TyCtxt<'tcx>,
}

impl<'tcx> Lifetime<'tcx> {
    pub fn new(tcx: TyCtxt<'tcx>) -> Lifetime<'tcx> {
        Lifetime { tcx }
    }
}

pub trait AnalysisQuery {
    fn start(&self);
}

#[derive(Serialize)]
struct AliasRecord {
    def_path: String,
    alias_str: String,
}

impl AliasRecord {
    fn new(def_id: DefId, ret_alias: &FnRetAlias, tcx: TyCtxt) -> Self {
        AliasRecord {
            def_path: tcx.def_path_str(def_id),
            alias_str: format!("{}", ret_alias),
        }
    }
}

struct FnVisitor;
impl<'tcx> Visitor<'tcx> for FnVisitor {
    fn visit_fn_decl(&mut self, fd: &rustc_hir::FnDecl<'_>) -> Self::Result {
        println!("{:?}", fd);
    }
}

impl<'tcx> AnalysisQuery for Lifetime<'tcx> {
    fn start(&self) {
        rap_info!("Run Lifetime Analysis");
        let mut alias = MopAlias::new(self.tcx);
        let fn_map = alias.start();
        let records: Vec<_> = fn_map
            .iter()
            .map(|(def_id, ret_alias)| AliasRecord::new(*def_id, ret_alias, self.tcx))
            .collect();
        self.tcx
            .hir()
            .visit_all_item_likes_in_crate(&mut FnVisitor {});
        let file = fs::rap_create_file("lifetime.json", "create log file fail");
        serde_json::to_writer_pretty(file, &records).expect("dump json fail");
    }
}
