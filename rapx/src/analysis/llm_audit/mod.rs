/// NOTE: This analysis module is currently under development and is highly unstable.
/// The #[allow(unused)] attribute is applied to suppress excessive lint warnings.
/// Once the analysis stabilizes, this marker should be removed.
#[allow(unused)]
mod llm;
mod source;
use crate::analysis::Analysis;
use crate::analysis::core::callgraph::CallGraphAnalysis;
use crate::analysis::core::callgraph::default::CallGraphAnalyzer;
use crate::analysis::llm_audit::source::{ContextMap, FileContext};
use crate::{rap_debug, rap_error, rap_info};
use anyhow::Result;
use futures::{StreamExt, stream};
use minijinja::render;
use rustc_hir::def::DefKind;
use rustc_middle::ty::TyCtxt;
use rustc_span::FileName;
use serde::Deserialize;
use std::ffi::OsStr;
use std::fs;
use std::path::{Path, PathBuf};
use std::sync::Arc;
use tokio;

#[derive(Debug, Clone, Deserialize)]
#[serde(rename_all = "kebab-case")]
pub struct Config {
    llm: llm::Config,
    #[serde(default = "default_target_dirname")]
    target_dirname: String,
    #[serde(default = "default_dryrun")]
    dryrun: bool,
    #[serde(default = "default_num_context_file")]
    num_context_file: usize,
}

fn default_target_dirname() -> String {
    "audit_reports".to_owned()
}

fn default_dryrun() -> bool {
    false
}

fn default_num_context_file() -> usize {
    3
}

impl Config {
    pub fn find_and_load(filename: &str) -> Result<Self> {
        let mut current_dir = std::env::current_dir()?;

        loop {
            let config_path = current_dir.join(filename);
            if config_path.exists() {
                return Self::from_file(config_path);
            }

            if !current_dir.pop() {
                return Err(anyhow::anyhow!(
                    "Configuration file '{}' not found in any parent directory.",
                    filename
                ));
            }
        }
    }

    pub fn from_file<P: AsRef<Path>>(path: P) -> Result<Self> {
        let path = path.as_ref();
        let contents = std::fs::read_to_string(&path)?;
        Ok(toml::from_str(&contents)?)
    }
}

/// LLM Audit Analysis - obtain basic information for crate
pub struct LlmAuditAnalysis<'tcx> {
    tcx: TyCtxt<'tcx>,
}

impl<'tcx> Analysis for LlmAuditAnalysis<'tcx> {
    fn name(&self) -> &'static str {
        "LLM Audit Analysis"
    }

    fn run(&mut self) {
        match self.run_analysis() {
            Ok(()) => rap_info!("LLM Audit Analysis completed successfully."),
            Err(e) => rap_info!("LLM Audit Analysis encountered an error: {}", e),
        }
    }

    fn reset(&mut self) {}
}

fn canonicalize_file_name(file_name: &FileName) -> Option<PathBuf> {
    match file_name.clone().into_local_path() {
        Some(pb) => pb.canonicalize().ok(),
        _ => None,
    }
}

impl<'tcx> LlmAuditAnalysis<'tcx> {
    pub fn new(tcx: TyCtxt<'tcx>) -> Self {
        LlmAuditAnalysis { tcx }
    }

    pub fn collect_context(&mut self) -> Result<ContextMap> {
        // preprocess context
        // let context_prefix =
        // std::env::var("LLM_CONTEXT_PREFIX").unwrap_or_else(|_| ".".to_string());

        let mut call_analyzer = CallGraphAnalyzer::new(self.tcx);
        call_analyzer.run();
        let call_graph = call_analyzer.get_callgraph();
        let mut file_context = FileContext::new();

        for local_def_id in self.tcx.iter_local_def_id() {
            let def_id = local_def_id.to_def_id();
            let def_kind = self.tcx.def_kind(def_id);

            if matches!(def_kind, DefKind::Fn | DefKind::AssocFn) {
                self.collect_fn(def_id, &call_graph, &mut file_context);
            }
        }

        Ok(file_context.into_sorted_map()?)
    }

    pub fn run_analysis(&mut self) -> Result<()> {
        let rt = tokio::runtime::Builder::new_current_thread()
            .enable_all()
            .build()?;

        rt.block_on(self.run_async())?;
        Ok(())
    }

    async fn run_async(&mut self) -> Result<()> {
        // read config
        let config = Config::find_and_load(".llmconfig.toml")?;
        rap_debug!("Config = {:?}", config);
        let Config {
            llm,
            target_dirname,
            dryrun,
            num_context_file,
        } = config;

        let project_dir = std::env::var("CARGO_MANIFEST_DIR")?;
        let project_path = fs::canonicalize(project_dir)?;
        let target_path = project_path.join(target_dirname);

        rap_info!("Project path: {}", project_path.display());
        rap_info!("Target path: {}", target_path.display());

        fs::create_dir_all(&target_path)?;

        let context_map = self.collect_context()?;

        rap_debug!("context_map: {:?}", context_map);

        let session = llm::Session::new(llm);

        let project_path = fs::canonicalize(project_path)?;
        let audit_ctx = Arc::new(AuditContext {
            project_path: project_path.clone(),
            target_path,
            session,
            context_map,
            num_context_file,
        });

        let source_map = self.tcx.sess.source_map();

        let mut tasks = vec![];

        for file in source_map.files().iter() {
            if let Some(file_path) = canonicalize_file_name(&file.name) {
                if !file_path.starts_with(&project_path) {
                    continue;
                }

                rap_info!("source file: {}", file_path.display());
                rap_info!("Analyzing source file: {}", file_path.display());
                tasks.push(audit_one_file(audit_ctx.clone(), file_path, dryrun));
            }
        }

        let results: Vec<_> = futures::stream::iter(tasks)
            .buffer_unordered(10)
            .collect()
            .await;

        for result in results {
            match result {
                Err(e) => {
                    rap_error!("Error auditing file: {}", e);
                }
                _ => {}
            }
        }

        Ok(())
    }
}

#[derive(Clone)]
struct AuditContext {
    project_path: PathBuf,
    target_path: PathBuf, // directoty to store audit reports
    session: llm::Session,
    context_map: ContextMap,
    num_context_file: usize,
}

fn get_file_context(audit_ctx: Arc<AuditContext>, file_path: &Path) -> Result<String> {
    if !audit_ctx.context_map.contains_key(file_path) {
        return Ok(String::new());
    }

    let context_vec = audit_ctx.context_map.get(file_path).unwrap();

    let mut context_prompt = String::new();

    let mut ctx_count = audit_ctx.num_context_file;
    for (context_file_path, _) in context_vec {
        // only add context file
        if context_file_path.extension().unwrap_or(OsStr::new("notrs")) != "rs" {
            continue;
        }
        let path_text = match context_file_path.strip_prefix(&audit_ctx.project_path) {
            Ok(relative) => relative.display().to_string(),
            Err(_) => {
                format!("(第三方依赖) {}", context_file_path.display())
            }
        };

        let content = fs::read_to_string(context_file_path)?;
        context_prompt.push_str(&format!(
            "- 文件路径: {}\n- 文件内容：\n\n```rust\n{}\n```\n\n",
            path_text, content
        ));

        ctx_count -= 1;
        if ctx_count <= 0 {
            break;
        }
    }
    Ok(context_prompt)
}

async fn audit_one_file(
    audit_ctx: Arc<AuditContext>,
    file_path: PathBuf,
    dryrun: bool,
) -> Result<()> {
    let content = fs::read_to_string(&file_path)?;
    let manifest_dir = Path::new(env!("CARGO_MANIFEST_DIR"));
    let prompt_path = manifest_dir.join("prompt.md");
    let prompt_template = fs::read_to_string(&prompt_path)?;

    let relative_path = file_path.strip_prefix(audit_ctx.project_path.as_path())?;
    let report_file_name = relative_path
        .with_extension("md")
        .display()
        .to_string()
        .replace("/", "-");

    let report_path = audit_ctx.target_path.join(report_file_name);
    rap_info!("Report Path: {}", report_path.display());

    let prompt = render!(
        &prompt_template,
        relative_path => relative_path,
        context => get_file_context(audit_ctx.clone(), &file_path)?,
        content => content
    );

    let ctx = llm::MessageContext {
        messages: vec![llm::Message::user(prompt.to_string())],
    };

    if dryrun {
        let content = format!("# Prompt\n{}\n", prompt);
        fs::write(&report_path, content)?;
        rap_info!("save report to {}", report_path.display());
        return Ok(());
    }

    let response = audit_ctx.session.call(&ctx).await?;

    let content = format!("{}\n---\n# Prompt\n{}\n", response.message.content, prompt);
    fs::write(&report_path, content)?;
    rap_info!("save report to {}", report_path.display());

    Ok(())
}
