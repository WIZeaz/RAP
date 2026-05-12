use itertools::Itertools;
use std::fs::{self, File};
use std::io::{self, Write};
use std::path::{Path, PathBuf};
use std::process::{Command, Stdio};
use std::time::Duration;
use wait_timeout::ChildExt;

#[derive(Clone, Debug)]
pub struct RsProjectOption {
    pub tested_crate_path: PathBuf,
    pub tested_crate_name: String,
    pub project_path: PathBuf,
    pub project_name: String,
}

/// Generator for fuzz driver projects.
pub struct CargoProjectBuilder {
    option: RsProjectOption,
    deps: Vec<String>,
}

pub struct PocProject {
    option: RsProjectOption,
}

impl CargoProjectBuilder {
    pub fn new(option: RsProjectOption) -> Self {
        Self {
            option,
            deps: Vec::new(),
        }
    }

    pub fn deps(mut self, deps: Vec<String>) -> Self {
        self.deps = deps;
        self
    }

    pub fn build(self) -> io::Result<PocProject> {
        let project_path = self.option.project_path.as_path();

        // create the new project
        rap_info!("Creating new project at {}", project_path.display());

        fs::create_dir_all(&project_path)?;
        fs::create_dir_all(project_path.join("src"))?;

        // add dependencies to Cargo.toml
        self.update_cargo_toml()?;

        rap_info!(
            "Successfully created fuzz driver project at: {}",
            project_path.display()
        );
        Ok(PocProject {
            option: self.option,
        })
    }

    fn dependencies_str(&self) -> String {
        let this_dep = format!(
            "{} = {{ path = \"{}\" }}",
            self.option.tested_crate_name,
            pathdiff::diff_paths(&self.option.tested_crate_path, &self.option.project_path)
                .unwrap()
                .display()
        );
        self.deps
            .iter()
            .map(|dep| format!("{} = \"*\"", dep))
            .chain(std::iter::once(this_dep))
            .join("\n")
    }

    fn update_cargo_toml(&self) -> io::Result<()> {
        let project_path = self.option.project_path.as_path();
        let cargo_toml_path = project_path.join("Cargo.toml");
        let mut file = fs::OpenOptions::new()
            .create(true)
            .write(true)
            .append(true)
            .open(cargo_toml_path)?;

        writeln!(
            file,
            "[package]\nname = \"{}\"\nedition = \"2024\"",
            self.option.project_name
        )?;

        writeln!(file, "[dependencies]")?;
        writeln!(file, "{}", self.dependencies_str())?;
        writeln!(file, "\n[workspace]")?; // add workspace to avoid cargo warning about multiple packages in the same directory

        Ok(())
    }
}

#[derive(Debug, Clone)]
pub struct CmdRecord {
    pub reproduce: String,
    pub elapsed: Duration,
    pub retcode: Option<i32>,
    pub stdout: Vec<u8>,
    pub stderr: Vec<u8>,
}

impl CmdRecord {
    pub fn success(&self) -> bool {
        match self.retcode {
            Some(0) => true,
            _ => false,
        }
    }

    pub fn brief(&self) -> String {
        let mut s = String::new();
        s.push_str(&format!("Reproduce Line:\n{}\n", self.reproduce));
        s.push_str(&format!("retcode = {:?}\n", self.retcode));
        s.push_str(&format!("elapsed = {}ms\n", self.elapsed.as_millis()));
        if !self.success() {
            s.push_str(&format!(
                "stdout:{}\n",
                String::from_utf8_lossy(self.stdout.as_slice())
            ));
            s.push_str(&format!(
                "stderr:{}\n",
                String::from_utf8_lossy(self.stderr.as_slice())
            ));
        }
        s
    }
}

pub fn env_vars_str(vars: &[(&str, &str)]) -> String {
    vars.iter()
        .fold(String::new(), |s, (k, v)| {
            if v.contains(" ") {
                format!("{s} {k}=\"{v}\"")
            } else {
                format!("{s} {k}={v}")
            }
        })
        .trim()
        .to_owned()
}
impl PocProject {
    pub fn option(&self) -> &RsProjectOption {
        &self.option
    }

    pub fn copy_to<P: AsRef<Path>>(&self, path: P) -> io::Result<PocProject> {
        let path = path.as_ref();
        let options = fs_extra::dir::CopyOptions::new();
        // fs::create_dir_all(path)?;
        match fs_extra::dir::copy(&self.option.project_path, path, &options) {
            Err(err) => return Err(io::Error::new(io::ErrorKind::Other, err.to_string())),
            Ok(_) => {}
        }

        let mut new_project = PocProject {
            option: self.option.clone(),
        };
        new_project.option.project_path = path.join(&self.option.project_name).to_path_buf();
        Ok(new_project)
    }

    pub fn create_src_file(&self, file_name: &str, content: &str) -> io::Result<()> {
        let src_path = self.option.project_path.join("src").join(file_name);
        let mut file = File::create(src_path)?;
        file.write_all(content.as_bytes())?;
        Ok(())
    }

    pub fn clear_artifact(&self) -> io::Result<()> {
        let project_path = self.option.project_path.as_path();
        let mut command = Command::new("cargo");
        command
            .current_dir(&project_path)
            .arg("clean")
            .env_remove("RUSTC_WRAPPER") // rapx set RUSTC_WRAPPER to rapx executable to hijack the compilation, however we just want to use official rustc here
            .stdout(Stdio::piped())
            .stderr(Stdio::piped())
            .output()?;
        Ok(())
    }

    pub fn run_cargo_cmd(
        &self,
        args: &[&str],
        env_vars: &[(&str, &str)],
        timeout: usize,
    ) -> io::Result<CmdRecord> {
        let project_path = self.option.project_path.as_path();

        let stdout_path = self.option.project_path.join("stdout.log");
        let stderr_path = self.option.project_path.join("stderr.log");

        let stdout_file = File::create(&stdout_path)?;
        let stderr_file = File::create(&stderr_path)?;

        let mut command = Command::new("cargo");
        command
            .current_dir(&project_path)
            .args(args)
            .env_remove("RUSTC_WRAPPER") // rapx set RUSTC_WRAPPER to rapx executable to hijack the compilation, however we just want to use official rustc here
            .envs(env_vars.to_owned())
            // it is critical to redirect stdout/stderr to files,
            // otherwise the output buffer may be full and block the process
            .stdout(Stdio::from(stdout_file))
            .stderr(Stdio::from(stderr_file));

        rap_debug!("Running command: {:?}", command);

        let timer = std::time::Instant::now();
        let mut child = command.spawn()?;

        let opt_status = if timeout == 0 {
            Some(child.wait()?)
        } else {
            child.wait_timeout(Duration::from_secs(timeout as u64))?
        };

        match opt_status {
            Some(_) => {
                let output = child.wait_with_output()?;
                let elapsed = timer.elapsed();
                Ok(CmdRecord {
                    reproduce: format!(
                        "cd {} && {} cargo {}",
                        project_path.display(),
                        env_vars_str(env_vars),
                        args.join(" ")
                    ),
                    elapsed,
                    retcode: output.status.code(),
                    stdout: fs::read(&stdout_path)?,
                    stderr: fs::read(&stderr_path)?,
                })
            }
            // the child is timeout, we need to kill the child
            None => {
                child.kill()?;
                let elapsed = timer.elapsed();
                Ok(CmdRecord {
                    reproduce: format!(
                        "cd {} && {} cargo {}",
                        project_path.display(),
                        env_vars_str(env_vars),
                        args.join(" ")
                    ),
                    elapsed,
                    retcode: None,
                    stdout: vec![],
                    stderr: vec![],
                })
            }
        }
    }
}
