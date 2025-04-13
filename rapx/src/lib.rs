#![feature(rustc_private)]
#![feature(box_patterns)]

#[macro_use]
pub mod utils;
pub mod analysis;

extern crate rustc_data_structures;
extern crate rustc_driver;
extern crate rustc_errors;
extern crate rustc_hir;
extern crate rustc_index;
extern crate rustc_infer;
extern crate rustc_interface;
extern crate rustc_metadata;
extern crate rustc_middle;
extern crate rustc_session;
extern crate rustc_span;
extern crate rustc_target;
extern crate rustc_trait_selection;
extern crate rustc_traits;
extern crate rustc_type_ir;

extern crate stable_mir;
use crate::analysis::core::heap_item::TypeAnalysis;
use analysis::core::alias::mop::MopAlias;
use analysis::core::api_dep::ApiDep;
use analysis::core::call_graph::CallGraph;
use analysis::core::dataflow::DataFlow;
use analysis::core::range_analysis::SSATrans;
use analysis::opt::Opt;
use analysis::rcanary::rCanary;
use analysis::safedrop::SafeDrop;
use analysis::senryx::{CheckLevel, SenryxCheck};
use analysis::testgen::Testgen;
use analysis::unsafety_isolation::{UigInstruction, UnsafetyIsolationCheck};
use analysis::utils::show_mir::ShowMir;
use rustc_data_structures::sync::Lrc;
use rustc_driver::{Callbacks, Compilation};
use rustc_interface::interface::Compiler;
use rustc_interface::{Config, Queries};
use rustc_middle::ty::TyCtxt;
use rustc_middle::util::Providers;
use rustc_session::search_paths::PathKind;
use std::path::PathBuf;

// Insert rustc arguments at the beginning of the argument list that RAP wants to be
// set per default, for maximal validation power.
pub static RAP_DEFAULT_ARGS: &[&str] = &["-Zalways-encode-mir", "-Zmir-opt-level=0"];

pub type Elapsed = (i64, i64);

#[derive(Debug, Copy, Clone, Hash)]
pub struct RapCallback {
    rcanary: bool,
    safedrop: bool,
    verify: bool,
    infer: bool,
    unsafety_isolation: usize,
    mop: bool,
    callgraph: bool,
    api_dep: bool,
    testgen: bool,
    show_mir: bool,
    dataflow: usize,
    opt: bool,
    heap_item: bool,
    ssa: bool,
}

#[allow(clippy::derivable_impls)]
impl Default for RapCallback {
    fn default() -> Self {
        Self {
            rcanary: false,
            safedrop: false,
            verify: false,
            infer: false,
            unsafety_isolation: 0,
            mop: false,
            callgraph: false,
            api_dep: false,
            testgen: false,
            show_mir: false,
            dataflow: 0,
            opt: false,
            heap_item: false,
            ssa: false,
        }
    }
}

impl Callbacks for RapCallback {
    fn config(&mut self, config: &mut Config) {
        config.override_queries = Some(|_, providers| {
            providers.extern_queries.used_crate_source = |tcx, cnum| {
                let mut providers = Providers::default();
                rustc_metadata::provide(&mut providers);
                let mut crate_source = (providers.extern_queries.used_crate_source)(tcx, cnum);
                // HACK: rustc will emit "crate ... required to be available in rlib format, but
                // was not found in this form" errors once we use `tcx.dependency_formats()` if
                // there's no rlib provided, so setting a dummy path here to workaround those errors.
                Lrc::make_mut(&mut crate_source).rlib = Some((PathBuf::new(), PathKind::All));
                crate_source
            };
        });
    }

    fn after_analysis<'tcx>(
        &mut self,
        _compiler: &Compiler,
        queries: &'tcx Queries<'tcx>,
    ) -> Compilation {
        rap_trace!("Execute after_analysis() of compiler callbacks");
        queries
            .global_ctxt()
            .unwrap()
            .enter(|tcx| start_analyzer(tcx, *self));
        rap_trace!("analysis done");
        Compilation::Continue
    }
}

impl RapCallback {
    pub fn enable_rcanary(&mut self) {
        self.rcanary = true;
    }

    pub fn is_rcanary_enabled(&self) -> bool {
        self.rcanary
    }

    pub fn enable_mop(&mut self) {
        self.mop = true;
    }

    pub fn is_mop_enabled(&self) -> bool {
        self.mop
    }

    pub fn enable_safedrop(&mut self) {
        self.safedrop = true;
    }

    pub fn is_safedrop_enabled(&self) -> bool {
        self.safedrop
    }

    pub fn enable_unsafety_isolation(&mut self, x: usize) {
        self.unsafety_isolation = x;
    }

    pub fn is_unsafety_isolation_enabled(&self) -> usize {
        self.unsafety_isolation
    }

    pub fn enable_api_dep(&mut self) {
        self.api_dep = true;
    }

    pub fn enable_testgen(&mut self) {
        self.testgen = true;
    }

    pub fn is_api_dep_enabled(&self) -> bool {
        self.api_dep
    }

    pub fn is_testgen_enabled(&self) -> bool {
        self.testgen
    }

    pub fn enable_verify(&mut self) {
        self.verify = true;
    }

    pub fn is_verify_enabled(&self) -> bool {
        self.verify
    }

    pub fn enable_infer(&mut self) {
        self.infer = true;
    }

    pub fn is_infer_enabled(&self) -> bool {
        self.infer
    }

    pub fn enable_callgraph(&mut self) {
        self.callgraph = true;
    }

    pub fn is_callgraph_enabled(&self) -> bool {
        self.callgraph
    }

    pub fn enable_show_mir(&mut self) {
        self.show_mir = true;
    }

    pub fn is_show_mir_enabled(&self) -> bool {
        self.show_mir
    }

    pub fn enable_dataflow(&mut self, x: usize) {
        self.dataflow = x;
    }

    pub fn is_dataflow_enabled(self) -> usize {
        self.dataflow
    }

    pub fn enable_opt(&mut self) {
        self.opt = true;
    }

    pub fn is_opt_enabled(self) -> bool {
        self.opt
    }

    pub fn enable_heap_item(&mut self) {
        self.heap_item = true;
    }

    pub fn is_heap_item_enabled(self) -> bool {
        self.heap_item
    }
    pub fn enable_ssa_transform(&mut self) {
        self.ssa = true;
    }
    pub fn is_ssa_transform_enabled(self) -> bool {
        self.ssa
    }
}

#[derive(Debug, Copy, Clone, Hash, Eq, PartialEq, Ord, PartialOrd)]
pub enum RapPhase {
    Cleanup,
    Cargo,
    Rustc,
    LLVM, // unimplemented yet
}

pub fn start_analyzer(tcx: TyCtxt, callback: RapCallback) {
    let _rcanary: Option<rCanary> = if callback.is_rcanary_enabled() {
        let mut rcx = rCanary::new(tcx);
        rcx.start();
        Some(rcx)
    } else {
        None
    };

    if callback.is_mop_enabled() {
        MopAlias::new(tcx).start();
    }

    if callback.is_safedrop_enabled() {
        SafeDrop::new(tcx).start();
    }

    if callback.is_heap_item_enabled() {
        let rcx_boxed = Box::new(rCanary::new(tcx));
        let rcx = Box::leak(rcx_boxed);
        let mut type_analysis = TypeAnalysis::new(rcx);
        type_analysis.start();
        type_analysis.output();
    }

    let x = callback.is_unsafety_isolation_enabled();
    match x {
        1 => UnsafetyIsolationCheck::new(tcx).start(UigInstruction::StdSp),
        2 => UnsafetyIsolationCheck::new(tcx).start(UigInstruction::Doc),
        3 => UnsafetyIsolationCheck::new(tcx).start(UigInstruction::Upg),
        4 => UnsafetyIsolationCheck::new(tcx).start(UigInstruction::Ucons),
        _ => {}
    }

    if callback.is_verify_enabled() {
        let check_level = CheckLevel::High;
        SenryxCheck::new(tcx, 2).start(check_level, true);
    }

    if callback.is_infer_enabled() {
        let check_level = CheckLevel::High;
        SenryxCheck::new(tcx, 2).start(check_level, false);
    }

    if callback.is_show_mir_enabled() {
        ShowMir::new(tcx).start();
    }

    if callback.is_api_dep_enabled() {
        ApiDep::new(tcx).start(true);
    }

    if callback.is_testgen_enabled() {
        Testgen::new(tcx).start();
    }

    match callback.is_dataflow_enabled() {
        1 => DataFlow::new(tcx, false).start(),
        2 => DataFlow::new(tcx, true).start(),
        _ => {}
    }

    if callback.is_callgraph_enabled() {
        CallGraph::new(tcx).start();
    }

    if callback.is_opt_enabled() {
        Opt::new(tcx).start();
    }
    if callback.is_ssa_transform_enabled() {
        SSATrans::new(tcx, false).start();
    }
}
