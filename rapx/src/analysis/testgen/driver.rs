use crate::analysis::Analysis;
use crate::analysis::core::alias_analysis::{AliasAnalysis, FnAliasMap};
use crate::analysis::core::api_dependency::ApiDependencyAnalysis;
use crate::analysis::core::{alias_analysis, api_dependency};
use crate::analysis::testgen::ltgen::LtGenBuilder;
use crate::analysis::testgen::syn::impls::FuzzDriverSynImpl;
use crate::analysis::testgen::syn::input::RandomGen;
use crate::analysis::testgen::syn::project::{CargoProjectBuilder, PocProject, RsProjectOption};
use crate::analysis::testgen::syn::{SynOption, Synthesizer};
use crate::analysis::utils::path::get_path_resolver;
use anyhow::Result;
use core::slice::SlicePattern;
use rustc_hir::def_id::{DefId, LOCAL_CRATE};
use rustc_middle::ty::TyCtxt;
use serde::{Deserialize, Serialize};
use std::collections::HashMap;
use std::io::Write;
use std::path::Path;
use std::{fs, io};
use toml;

#[derive(Deserialize, Debug)]
struct Config {
    pub max_complexity: usize,
    pub max_iteration: usize,
    pub max_run: usize,
    #[serde(default = "default_mode")]
    pub mode: Mode,
    #[serde(rename = "override")]
    pub override_: bool,
    #[serde(default = "default_timeout")]
    pub timeout: usize,
    #[serde(default)]
    pub terminate_on_ub: bool,
    #[serde(default = "default_skip_thresh")]
    pub skip_thresh: usize,
}

#[derive(Copy, Clone, Debug, Deserialize)]
#[serde(rename_all = "lowercase")]
enum Mode {
    Normal,
    Dryrun,
}

impl Mode {
    pub fn is_normal(&self) -> bool {
        matches!(self, Mode::Normal)
    }
    pub fn is_dryrun(&self) -> bool {
        matches!(self, Mode::Dryrun)
    }
}

fn default_timeout() -> usize {
    10
}

fn default_mode() -> Mode {
    Mode::Normal
}

fn default_skip_thresh() -> usize {
    5
}

pub fn disable_alias() -> bool {
    true
}

#[derive(Clone, Serialize, Deserialize, Default, Debug)]
#[serde(rename_all = "snake_case")]
struct Stats {
    results: HashMap<EvalResult, usize>,
    num_total: usize,
    num_estimated: usize,
    num_covered: usize,
}

impl Config {
    pub fn load() -> io::Result<Self> {
        let mut current_dir = std::env::current_dir()?;

        loop {
            let config_path = current_dir.join(".ltgenconfig");
            if config_path.exists() {
                rap_info!("load config file from: {}", config_path.display());
                return Self::load_from(config_path);
            }

            if !current_dir.pop() {
                return Err(io::Error::new(
                    io::ErrorKind::NotFound,
                    "Could not find .ltgenconfig in any parent directory",
                ));
            }
        }
    }

    pub fn load_from<P: AsRef<Path>>(path: P) -> io::Result<Self> {
        let path = path.as_ref();
        let contents = fs::read_to_string(&path)?;
        let config: Config = toml::from_str(&contents)
            .expect(&format!("cannot parse the content of {}", path.display()));
        Ok(config)
    }

    pub fn can_override(&self) -> bool {
        self.override_
    }
}

pub fn dump_alias_map(alias_map: &FnAliasMap, mut os: impl Write, tcx: TyCtxt<'_>) -> Result<()> {
    for (did, aliases) in alias_map {
        if tcx.is_closure_like(*did) {
            continue;
        }
        writeln!(
            os,
            "{} : {} = {}",
            tcx.def_path_str(did),
            tcx.fn_sig(did).instantiate_identity().skip_binder(),
            aliases
        )?;
    }
    Ok(())
}

pub fn miri_env_vars() -> &'static [(&'static str, &'static str)] {
    &[
        ("MIRIFLAGS", "-Zmiri-ignore-leaks -Zmiri-tree-borrows"),
        ("RUSTFLAGS", "-Awarnings"),
        ("RUST_BACKTRACE", "1"),
    ]
}

fn asan_env_vars() -> &'static [(&'static str, &'static str)] {
    &[("RUSTFLAGS", "-Awarnings -Zsanitizer=address")]
}

fn dep_crates_for_synthesis(def_ids: &[DefId], tcx: TyCtxt) -> Vec<String> {
    let mut deps = Vec::new();

    for def_id in def_ids {
        if !deps.contains(&def_id.krate) {
            let crate_name = tcx.crate_name(def_id.krate);
            deps.push(def_id.krate);
            rap_warn!(
                "crate {} is used in synthesis, adding it to dependencies",
                crate_name
            );
        }
    }
    deps.into_iter()
        .map(|krate| tcx.crate_name(krate).to_string())
        .collect()
}

pub fn driver_main(tcx: TyCtxt<'_>) -> Result<()> {
    let config = Config::load()?;
    let local_crate_name = tcx.crate_name(LOCAL_CRATE);
    rap_info!("run on crate: {}", local_crate_name);

    let workspace_dir = std::env::current_dir()?.join("testgen");
    let poc_path = workspace_dir.join("poc");

    if config.can_override() && fs::exists(&workspace_dir)? {
        rap_info!(
            "removing existing workspace directory: {}",
            workspace_dir.display()
        );
        fs::remove_dir_all(&workspace_dir)?;
    }

    // create workspace structure
    fs::create_dir_all(&workspace_dir)?;
    fs::create_dir_all(&poc_path)?;

    let mut run_count = 0;

    let mut api_analyzer = api_dependency::ApiDependencyAnalyzer::new(
        tcx,
        api_dependency::Config {
            resolve_generic: true,
            visit_config: api_dependency::VisitConfig {
                pub_only: true,
                include_generic: true,
                ignore_const_generic: true,
                include_unsafe: false,
                include_drop: false,
            },
            max_generic_search_iteration: 10,
            dump: None,
        },
    );
    api_analyzer.run();
    let api_dep_graph = api_analyzer.get_api_dependency_graph();

    api_dep_graph.dump_to_file(workspace_dir.join("api_graph.dot"))?;

    let (num_estimated, _) = api_dep_graph.estimate_coverage();

    if num_estimated <= config.skip_thresh {
        rap_warn!(
            "estimated covered API is {}, which is smaller than the skip_threshold {}. Skipping testgen",
            num_estimated,
            config.skip_thresh
        );
        return Ok(());
    }

    let mut alias_analyzer = alias_analysis::default::AliasAnalyzer::new(tcx);
    if disable_alias() {
        rap_info!("alias analysis is disabled, all functions will be treated as non-alias");
    } else {
        alias_analyzer.run();
    }
    let alias_map = alias_analyzer.get_all_fn_alias();

    let alias_file = std::fs::OpenOptions::new()
        .create(true)
        .read(true)
        .write(true)
        .open(workspace_dir.join("alias_file.txt"))?;

    dump_alias_map(&alias_map, alias_file, tcx)?;

    let mut ltgen = LtGenBuilder::new(tcx, &alias_map, api_dep_graph)
        .max_complexity(config.max_complexity)
        .max_iteration(config.max_iteration)
        .build();

    ltgen.log_depth_map();

    let report_path = workspace_dir.join("miri_report.txt");
    let stats_path = workspace_dir.join("stats.yaml");

    let mut report_file = std::fs::OpenOptions::new()
        .create(true)
        .read(true)
        .write(true)
        .open(&report_path)?;

    let package_name = std::env::var("CARGO_PKG_NAME")?;
    let package_dir = std::env::var("CARGO_MANIFEST_DIR")?;

    let resolver = get_path_resolver(tcx);
    let mut global_stats = Stats::default();

    while config.max_run == 0 || run_count < config.max_run {
        // 1. generate context
        let cx = ltgen.generate();

        // 2. synthesize Rust program
        let option = SynOption {
            crate_name: local_crate_name.to_string(),
        };
        let mut syn = FuzzDriverSynImpl::new(RandomGen::new(), option, tcx, &resolver);
        let rs_str = syn.syn(cx.cx(), tcx);

        let non_local_def_ids = resolver.non_local_def_ids();
        let deps = dep_crates_for_synthesis(non_local_def_ids.as_slice(), tcx);

        // 3. Build cargo project
        let project_name = format!("case{}", run_count);
        let project_path = workspace_dir.join("tests").join(&project_name);
        let debug_path = project_path.as_path().join("region_graph.dot");

        let project_option = RsProjectOption {
            tested_crate_name: (&package_name).into(),
            tested_crate_path: (&package_dir).into(),
            project_name: project_name.clone(),
            project_path: project_path.clone(),
        };

        let project_builder = CargoProjectBuilder::new(project_option).deps(deps);
        let project = project_builder.build()?;
        project.create_src_file("main.rs", &rs_str)?;
        // output debug file
        let mut file = std::fs::File::create(debug_path)?;
        cx.region_graph().dump(&mut file).unwrap();

        let delimeter = "=".repeat(40);
        writeln!(&mut report_file, "{}", delimeter)?;

        // 4. exec `cargo check` and `cargo miri run` to evaluate the generated program
        match check_and_evaluate(&project, &mut report_file, &config) {
            Ok(eval_result) => {
                *global_stats.results.entry(eval_result).or_default() += 1;
                if let EvalResult::UbDetected = eval_result {
                    let new_project = project.copy_to(&poc_path)?;
                    rap_warn!(
                        "copy project to {} and reduce",
                        new_project.option().project_path.display()
                    );
                    new_project.reduce()?;
                }
            }
            Err(err) => {
                rap_error!("evaluate project {} fail: {}", project_path.display(), err);
                writeln!(
                    &mut report_file,
                    "[Evaluate Fail] project {}: {}",
                    project_path.display(),
                    err
                )?;
            }
        }

        global_stats.num_total = ltgen.state().num_total_api();
        global_stats.num_estimated = ltgen.state().num_estimate_covered_api();
        global_stats.num_covered = ltgen.state().num_global_covered_api();

        rap_info!("current stats: {:?}", global_stats);
        serde_yaml::to_writer(&mut std::fs::File::create(&stats_path)?, &global_stats)?;

        writeln!(&mut report_file, "{}", delimeter)?;

        // 6. clear artifact to avoid space waste
        match project.clear_artifact() {
            Ok(_) => {}
            Err(e) => {
                rap_warn!(
                    "Fail to clear artifact for {}: {}",
                    project_path.display(),
                    e
                );
            }
        }

        run_count += 1;

        if config.terminate_on_ub
            && global_stats
                .results
                .get(&EvalResult::UbDetected)
                .copied()
                .unwrap_or_default()
                > 0
        {
            rap_info!("terminate on first UB detection");
            break;
        }
    }

    writeln!(&mut report_file, "{}", ltgen.statistic_str())?;
    rap_info!("report saved to: {}", report_path.display());

    Ok(())
}

#[derive(Debug, PartialEq, Eq, Hash, Clone, Copy, Serialize, Deserialize)]
#[serde(rename_all = "snake_case")]
pub enum EvalResult {
    Success,
    UbDetected,
    Timeout,
    CompileFailed,
    Other,
}

fn check_and_evaluate(
    project: &PocProject,
    log: &mut impl Write,
    config: &Config,
) -> io::Result<EvalResult> {
    let project_path = &project.option().project_path;

    // run `cargo check`
    let result = project.run_cargo_cmd(&["check"], &[("RUSTFLAGS", "-Awarnings")], 0)?;
    if !result.success() {
        rap_error!("running `cargo check` fail: {:?}", result.retcode);
        rap_error!("project {} compile fail", project_path.display());
        writeln!(log, "{}", result.brief())?;
        return Ok(EvalResult::CompileFailed);
    } else {
        rap_info!("`cargo check` success");
    }

    // if this is dryrun, skip evaluataion
    if config.mode.is_dryrun() {
        return Ok(EvalResult::Success);
    }

    let mut eval_result = EvalResult::Success;

    // run `cargo miri run`
    let result = project.run_cargo_cmd(&["miri", "run"], miri_env_vars(), config.timeout)?;
    writeln!(log, "{}", result.brief())?;
    if result.success() {
        rap_info!("`cargo miri run` success, nothing interested happen");
    } else {
        rap_warn!("miri return {:?}", result.retcode);
        let stderr_str = String::from_utf8_lossy(&result.stderr);
        match result.retcode {
            Some(1) if stderr_str.contains("error: Undefined Behavior:") => {
                eval_result = EvalResult::UbDetected;
                rap_warn!("this may indicate a UB bug detected");
            }
            Some(_) => {
                eval_result = EvalResult::Other;
            }
            None => {
                eval_result = EvalResult::Timeout;
                rap_warn!("this may indicate the program is timeout");
            }
        }
    }

    // run `cargo run`, with sanitizer flag (currenly only ASAN)
    // let result = project.run_cargo_cmd(&["run"], asan_env_vars(), config.timeout)?;
    // writeln!(log, "{}", result.brief())?;
    // if result.success() {
    //     rap_info!("`cargo run` with sanitizer success, nothing interested happen");
    // } else {
    //     rap_warn!("`cargo run` with sanitizer return {:?}", result.retcode);
    //     match result.retcode {
    //         Some(1) => rap_warn!("this may indicate a UB bug detected"),
    //         None => rap_warn!("this may indicate the program is timeout"),
    //         _ => {}
    //     }
    // }

    Ok(eval_result)
}
