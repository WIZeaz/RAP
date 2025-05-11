#![feature(rustc_private)]

extern crate rustc_driver;
extern crate rustc_session;

use rapx::{rap_info, rap_trace, utils::log::init_log, RapCallback, RAP_DEFAULT_ARGS};
use rustc_session::config::ErrorOutputType;
use rustc_session::EarlyDiagCtxt;
use std::env;

fn run_complier(args: &mut Vec<String>, callback: &mut RapCallback) -> i32 {
    // Finally, add the default flags all the way in the beginning, but after the binary name.
    args.splice(1..1, RAP_DEFAULT_ARGS.iter().map(ToString::to_string));

    let handler = EarlyDiagCtxt::new(ErrorOutputType::default());
    rustc_driver::init_rustc_env_logger(&handler);
    rustc_driver::install_ice_hook("bug_report_url", |_| ());

    let run_compiler = rustc_driver::RunCompiler::new(args, callback);
    let exit_code = rustc_driver::catch_with_exit_code(move || run_compiler.run());
    rap_trace!("The arg for compilation is {:?}", args);

    exit_code
}

fn main() {
    // Parse the arguments from env.
    let mut args = vec![];
    let mut compiler = RapCallback::default();
    for arg in env::args() {
        match arg.as_str() {
            "-F" | "-uaf" => compiler.enable_safedrop(),
            "-M" | "-mleak" => compiler.enable_rcanary(),
            "-I" | "-infer" => compiler.enable_infer(),
            "-V" | "-verify" => compiler.enable_verify(),
            "-O" | "-opt" => compiler.enable_opt(1),
            "-opt=all" => compiler.enable_opt(2),
            "-alias" => compiler.enable_mop(),
            "-heap" => compiler.enable_heap_item(),
            "-adg" => compiler.enable_api_dep(), // api dependency graph
            "-callgraph" => compiler.enable_callgraph(),
            "-dataflow" => compiler.enable_dataflow(1),
            "-ssa" => compiler.enable_ssa_transform(),
            "-dataflow=debug" => compiler.enable_dataflow(2),
            "-audit" => compiler.enable_unsafety_isolation(1),
            "-doc" => compiler.enable_unsafety_isolation(2),
            "-upg" => compiler.enable_unsafety_isolation(3),
            "-ucons" => compiler.enable_unsafety_isolation(4),
            "-mir" => compiler.enable_show_mir(),
            "-testgen" => compiler.enable_testgen(),
            _ => args.push(arg),
        }
    }
    _ = init_log().inspect_err(|err| eprintln!("Failed to init log: {err}"));
    rap_info!("Start analysis with RAP.");
    rap_trace!("rap received arguments: {:#?}", env::args());
    rap_trace!("arguments to rustc: {:?}", &args);

    let exit_code = run_complier(&mut args, &mut compiler);
    std::process::exit(exit_code)
}
