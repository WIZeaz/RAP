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
use anyhow::Result;
use minijinja::render;
use rustc_hir::def::DefKind;
use rustc_middle::ty::TyCtxt;
use serde::Deserialize;
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
}

fn default_target_dirname() -> String {
    "audit_reports".to_owned()
}

fn default_dryrun() -> bool {
    false
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
        } = config;

        let project_dir = std::env::var("CARGO_MANIFEST_DIR")?;
        let project_path = fs::canonicalize(project_dir)?;
        let target_path = project_path.join(target_dirname);

        fs::create_dir_all(&target_path)?;

        let context_map = self.collect_context()?;

        rap_info!("context_map: {:?}", context_map);

        let session = llm::Session::new(llm);

        let audit_ctx = Arc::new(AuditContext::new(
            project_path.clone(),
            target_path,
            session,
            context_map,
        )?);

        let source_map = self.tcx.sess.source_map();
        rap_info!("Project path: {}", project_path.display());

        let mut handles = vec![];

        for file in source_map.files().iter() {
            let file_path = fs::canonicalize(Path::new(&file.name.prefer_local().to_string()))?;
            if !file_path.starts_with(&project_path) {
                continue;
            }

            rap_info!("source file: {}", file_path.display());

            rap_info!("Analyzing source file: {}", file_path.display());
            let handle = tokio::spawn(audit_one_file(audit_ctx.clone(), file_path, dryrun));
            handles.push(handle);
        }

        for handle in handles {
            match handle.await? {
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
}

impl AuditContext {
    pub fn new(
        project_path: PathBuf,
        target_path: PathBuf,
        session: llm::Session,
        context_map: ContextMap,
    ) -> Result<Self> {
        let project_path = fs::canonicalize(project_path)?;
        Ok(Self {
            project_path,
            target_path,
            session,
            context_map,
        })
    }
}

fn get_file_context(audit_ctx: Arc<AuditContext>, file_path: &Path) -> Result<String> {
    if !audit_ctx.context_map.contains_key(file_path) {
        return Ok(String::new());
    }

    let context_vec = audit_ctx.context_map.get(file_path).unwrap();

    let mut context_prompt = String::new();
    // choose Top 3

    let ctx_num = 3.min(context_vec.len());
    for i in 0..ctx_num {
        let context_file_path = context_vec[i].0.as_path();
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
    }
    Ok(context_prompt)
}

async fn audit_one_file(
    audit_ctx: Arc<AuditContext>,
    file_path: PathBuf,
    dryrun: bool,
) -> Result<()> {
    let content = fs::read_to_string(&file_path)?;
    let prompt_template = fs::read_to_string("/app/RAPx-main/prompt.md")?;
    let relative_path = file_path.strip_prefix(audit_ctx.project_path.as_path())?;
    let report_file_name = relative_path
        .with_extension("md")
        .display()
        .to_string()
        .replace("/", "-");

    let report_path = audit_ctx.target_path.join(report_file_name);

    let prompt = render!(
        &prompt_template,
        relative_path => relative_path,
        context => get_file_context(audit_ctx.clone(), &file_path)?,
        content => content
    );

    let ctx = llm::MessageContext {
        messages: vec![llm::Message::system(prompt.to_string())],
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
