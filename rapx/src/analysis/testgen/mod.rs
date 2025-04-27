mod context;
mod generator;
mod syn;
mod utils;

use std::path::{Path, PathBuf};

use crate::analysis::core::{alias, api_dep};
use crate::{rap_debug, rap_info};
use context::ContextBase;
use generator::ltgen::context::LtContext;
use generator::ltgen::{initialize_subgraph_map, LtGenBuilder};
use generator::rulf;
use rustc_hir::def_id::LOCAL_CRATE;
use rustc_middle::ty::TyCtxt;
use stable_mir::local_crate;
use syn::input::SillyInputGen;
use syn::project::{CargoProjectBuilder, RsProjectOption};
use syn::Synthesizer;
use syn::{impls::FuzzDriverSynImpl, SynOption};
/// Automatic Test Generator for detecting lifetime-related bugs
pub struct Testgen<'tcx> {
    pub tcx: TyCtxt<'tcx>,
}

impl<'tcx> Testgen<'tcx> {
    pub fn new(tcx: TyCtxt<'tcx>) -> Testgen<'tcx> {
        Testgen { tcx }
    }

    pub fn tcx(&self) -> TyCtxt<'tcx> {
        self.tcx
    }

    pub fn start(&self) {
        let mut api_dep_graph = api_dep::ApiDep::new(self.tcx()).start(true);
        let mut alias_analysis = alias::mop::MopAlias::new(self.tcx());
        let alias_map = alias_analysis.start();

        let local_crate_name = self.tcx.crate_name(LOCAL_CRATE);
        let local_crate_type = self.tcx.crate_types()[0];
        rap_info!(
            "Generate testcase on {} ({})",
            local_crate_name.as_str(),
            local_crate_type
        );

        // rulf
        // let mut cx: ContextBase<'tcx> = ContextBase::new(self.tcx);
        // let mut rng = rand::rng();
        // let mut rulf = rulf::Rulf::new();
        // rulf.rulf_algorithm(self.tcx, &mut api_dep_graph, 3, &mut cx, &mut rng);
        // let max_coverage = rulf.max_coverage(&mut api_dep_graph, self.tcx);
        // match max_coverage {
        //     Some(max) => {
        //         rap_info!("Max coverage: {:?}", max);
        //     }
        //     None => {
        //         rap_info!("No coverage found");
        //     }
        // }
        // for stmt in cx.stmts(){
        //     rap_info!("stmt: {:?}", stmt);
        // }

        // run random program generator
        let mut lt_gen = LtGenBuilder::new(self.tcx, alias_map, &api_dep_graph)
            .max_complexity(20)
            .build();

        let cx = lt_gen.gen();

        // synthesize rust program
        let option = SynOption {
            crate_name: local_crate_name.to_string(),
        };
        let mut syn = FuzzDriverSynImpl::new(SillyInputGen, option);
        let rs_str = syn.syn(cx, self.tcx);

        // let output_path = Path::new("fuzz_driver.rs");
        // let mut file = File::create(output_path).unwrap();
        // file.write_all(rs_str.as_bytes()).unwrap();
        let fuzz_config = RsProjectOption {
            tested_crate_name: local_crate_name.to_string(),
            project_path: PathBuf::from(format!("../{}_fuzz_driver", local_crate_name)),
            verbose: true,
        };
        let project_builder = CargoProjectBuilder::new(fuzz_config);
        let project = match project_builder.build(&rs_str) {
            Ok(t) => t,
            Err(e) => {
                panic!("Failed to generate fuzz driver project: {}", e);
            }
        };
        match project.run() {
            Ok(_) => {
                rap_info!("Fuzz driver project run successfully");
            }
            Err(e) => {
                rap_info!("Failed to run fuzz driver project: {}", e);
            }
        }
        rap_debug!("{}", rs_str);
    }
}
