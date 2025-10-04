use wait_timeout::ChildExt;

use crate::rap_info;
use std::fs::{self, File};
use std::io::{self, Write};
use std::path::{Path, PathBuf};
use std::process::{Command, Stdio};
use std::time::Duration;

pub struct RsProjectOption {
    pub tested_crate_path: PathBuf,
    pub tested_crate_name: String,
    pub project_path: PathBuf,
    pub project_name: String,
}

/// Generator for fuzz driver projects.
pub struct CargoProjectBuilder {
    option: RsProjectOption,
}

pub struct PocProject {
    option: RsProjectOption,
}

impl CargoProjectBuilder {
    pub fn new(option: RsProjectOption) -> Self {
        Self { option }
    }

    pub fn build(self) -> io::Result<PocProject> {
        let project_path = self.option.project_path.as_path();

        // remove project path if it exists
        // if self.option.project_path.exists() {
        //     fs::remove_dir_all(self.option.project_path)?;
        // }

        // create the new project
        rap_info!("Creating new project at {}", project_path.display());

        let mut command = Command::new("cargo");
        command
            .arg("new")
            .arg(project_path)
            .arg("--vcs")
            .arg("none")
            .stdout(Stdio::piped())
            .stderr(Stdio::piped());

        let process = command.spawn()?;
        let output = process.wait_with_output()?;

        if !output.status.success() {
            let error = String::from_utf8_lossy(&output.stderr);
            return Err(io::Error::new(
                io::ErrorKind::Other,
                format!("Failed to create cargo project: {}", error),
            ));
        }

        // add dependencies to Cargo.toml
        self.update_cargo_toml(&project_path)?;

        rap_info!(
            "Successfully created fuzz driver project at: {}",
            project_path.display()
        );
        Ok(PocProject {
            option: self.option,
        })
    }

    fn update_cargo_toml(&self, project_path: &Path) -> io::Result<()> {
        let cargo_toml_path = project_path.join("Cargo.toml");
        let mut file = fs::OpenOptions::new()
            .write(true)
            .append(true)
            .open(cargo_toml_path)?;
        writeln!(
            file,
            "{} = {{ path = \"{}\" }}",
            self.option.tested_crate_name,
            self.option.tested_crate_path.display(),
        )?;
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

    pub fn run_cargo_cmd(&self, args: &[&str], env_vars: &[(&str, &str)]) -> io::Result<CmdRecord> {
        let project_path = self.option.project_path.as_path();
        rap_info!("Running `cargo {}`", args.join(" "));

        // first run `cargo check` to ensure the code can be compiled
        let mut command = Command::new("cargo");
        command
            .current_dir(&project_path)
            .args(args)
            .env_remove("RUSTC_WRAPPER") // rapx set RUSTC_WRAPPER to rapx executable to hijack the compilation, however we just want to use official rustc here
            .envs(env_vars.to_owned())
            .stdout(Stdio::piped())
            .stderr(Stdio::piped());

        let timer = std::time::Instant::now();
        let mut child = command.spawn()?;
        // 10s timeout

        match child.wait_timeout(Duration::from_secs(10))? {
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
                    stdout: output.stdout,
                    stderr: output.stderr,
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
