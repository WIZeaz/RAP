use super::path::get_path_resolver;
use crate::analysis::core::alias_analysis::{AAResultMap, AliasAnalysis};
use crate::analysis::core::api_dependency::ApiDependencyAnalysis;
use crate::analysis::core::{alias_analysis, api_dependency};
use crate::analysis::testgen::generator::ltgen::LtGenBuilder;
use crate::analysis::testgen::syn::impls::FuzzDriverSynImpl;
use crate::analysis::testgen::syn::input::RandomGen;
use crate::analysis::testgen::syn::project::{CargoProjectBuilder, PocProject, RsProjectOption};
use crate::analysis::testgen::syn::{SynOption, Synthesizer};
use crate::analysis::Analysis;
use crate::{rap_error, rap_info, rap_warn};
use rustc_hir::def_id::LOCAL_CRATE;
use rustc_middle::ty::TyCtxt;
use serde::Deserialize;
use std::io::Write;
use std::path::Path;
use std::{fs, io};
use toml;

#[derive(Deserialize, Debug)]
pub struct LtGenConfig {
    pub max_complexity: usize,
    pub max_iteration: usize,
    pub max_run: usize,
    #[serde(default = "default_mode")]
    pub mode: String,
    #[serde(rename = "override")]
    pub override_: bool,
}

fn default_mode() -> String {
    "nodebug".into()
}

impl LtGenConfig {
    pub fn load() -> io::Result<Self> {
        let mut current_dir = std::env::current_dir()?;

        loop {
            let config_path = current_dir.join(".ltgenconfig");
            if config_path.exists() {
                rap_debug!("load config file from: {}", config_path.display());
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
        let config: LtGenConfig = toml::from_str(&contents)
            .expect(&format!("cannot parse the content of {}", path.display()));
        Ok(config)
    }

    pub fn is_debug_mode(&self) -> bool {
        self.mode == "debug"
    }
    pub fn can_override(&self) -> bool {
        self.override_
    }
}

pub fn dump_alias_map(
    alias_map: &AAResultMap,
    mut os: impl Write,
    tcx: TyCtxt<'_>,
) -> Result<(), Box<dyn std::error::Error>> {
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

fn miri_env_vars() -> &'static [(&'static str, &'static str)] {
    &[
        (
            "MIRIFLAGS",
            "-Zmiri-ignore-leaks -Zmiri-disable-stacked-borrows",
        ),
        ("RUSTFLAGS", "-Awarnings"),
        ("RUST_BACKTRACE", "1"),
    ]
}

fn asan_env_vars() -> &'static [(&'static str, &'static str)] {
    &[("RUSTFLAGS", "-Awarnings -Zsanitizer=address")]
}

pub fn driver_main(tcx: TyCtxt<'_>) -> Result<(), Box<dyn std::error::Error>> {
    let mut config = LtGenConfig::load()?;
    let local_crate_name = tcx.crate_name(LOCAL_CRATE);
    rap_info!("run on crate: {}", local_crate_name);

    let workspace_dir = std::env::current_dir()?.join("testgen");

    if config.is_debug_mode() {
        config.max_run = 1;
    }

    if (config.is_debug_mode() || config.can_override()) && fs::exists(&workspace_dir)? {
        rap_info!(
            "removing existing workspace directory: {}",
            workspace_dir.display()
        );
        fs::remove_dir_all(&workspace_dir)?;
    }

    fs::create_dir_all(&workspace_dir)?;

    let mut run_count = 0;

    let mut api_analyzer = api_dependency::ApiDependencyAnalyzer::new(
        tcx,
        api_dependency::Config {
            pub_only: true,
            resolve_generic: true,
            ignore_const_generic: true,
            include_unsafe: false,
            include_drop: false,
        },
    );
    api_analyzer.run();
    let api_dep_graph = api_analyzer.get_api_dependency_graph();

    api_dep_graph.dump_to_dot(workspace_dir.join("api_graph.dot"));

    let mut alias_analyzer = alias_analysis::default::AliasAnalyzer::new(tcx);
    alias_analyzer.run();
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

    let report_path = workspace_dir.join("miri_report.txt");

    let mut report_file = std::fs::OpenOptions::new()
        .create(true)
        .read(true)
        .write(true)
        .open(&report_path)?;

    let package_name = std::env::var("CARGO_PKG_NAME")?;
    let package_dir = std::env::var("CARGO_MANIFEST_DIR")?;

    let resolver = get_path_resolver(tcx);

    while config.max_run == 0 || run_count < config.max_run {
        // 1. generate context
        let cx = ltgen.gen();

        // 2. synthesize Rust program
        let option = SynOption {
            crate_name: local_crate_name.to_string(),
        };
        let mut syn = FuzzDriverSynImpl::new(RandomGen::new(), option, tcx, &resolver);
        let rs_str = syn.syn(cx.cx(), tcx);

        // 3. Build cargo project
        let project_name = format!("case{}", run_count);
        let project_path = workspace_dir.join(&project_name);
        let debug_path = project_path.as_path().join("region_graph.dot");

        let fuzz_config = RsProjectOption {
            tested_crate_name: (&package_name).into(),
            tested_crate_path: (&package_dir).into(),
            project_name: project_name.clone(),
            project_path: project_path.clone(),
        };

        let project_builder = CargoProjectBuilder::new(fuzz_config);
        let project = project_builder.build()?;
        project.create_src_file("main.rs", &rs_str)?;
        // output debug file
        let mut file = std::fs::File::create(debug_path)?;
        cx.region_graph().dump(&mut file).unwrap();

        // 4. run cargo check
        // 5. evaluate with miri & asan
        let delimeter = "=".repeat(40);
        writeln!(&mut report_file, "{}", delimeter)?;

        if let Err(err) = check_and_evaluate(&project, &mut report_file) {
            rap_error!("evaluate project {} fail: {}", project_path.display(), err);
            writeln!(
                &mut report_file,
                "evaluate project {} fail: {}",
                project_path.display(),
                err
            )?;
        }

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
    }

    writeln!(&mut report_file, "{}", ltgen.statistic_str())?;
    rap_info!("report saved to: {}", report_path.display());

    Ok(())
}

pub fn check_and_evaluate(project: &PocProject, log: &mut impl Write) -> io::Result<()> {
    let project_path = &project.option().project_path;

    // run `cargo check`
    let result = project.run_cargo_cmd(&["check"], &[])?;
    if !result.success() {
        rap_error!("running `cargo check` fail: {:?}", result.retcode);
        rap_error!("project {} compile fail", project_path.display());
        writeln!(log, "{}", result.brief())?;
        return Ok(());
    }

    // run `cargo miri run`
    let result = project.run_cargo_cmd(&["miri", "run"], miri_env_vars())?;
    writeln!(log, "{}", result.brief())?;
    if result.success() {
        rap_info!("`cargo miri run` success, nothing interested happen");
    } else {
        rap_warn!("miri return {:?}", result.retcode);
        match result.retcode {
            Some(1) => rap_warn!("this may indicate a UB bug detected"),
            None => rap_warn!("this may indicate the program is timeout"),
            _ => {}
        }
    }

    // run `cargo run`, with sanitizer flag (currenly only ASAN)
    let result = project.run_cargo_cmd(&["run"], asan_env_vars())?;
    writeln!(log, "{}", result.brief())?;
    if result.success() {
        rap_info!("`cargo run` with sanitizer success, nothing interested happen");
    } else {
        rap_warn!("`cargo run` with sanitizer return {:?}", result.retcode);
        match result.retcode {
            Some(1) => rap_warn!("this may indicate a UB bug detected"),
            None => rap_warn!("this may indicate the program is timeout"),
            _ => {}
        }
    }

    Ok(())
}
