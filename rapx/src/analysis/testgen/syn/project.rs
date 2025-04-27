use crate::analysis::opt::Opt;
use crate::rap_info;
use std::fs::{self, File};
use std::io::{self, Write};
use std::path::{Path, PathBuf};
use std::process::{Command, Stdio};
use std::thread;

pub struct RsProjectOption {
    pub tested_crate_name: String,
    pub project_path: PathBuf,
    pub verbose: bool,
}

impl RsProjectOption {
    pub fn tested_crate_name(&self) -> &str {
        &self.tested_crate_name
    }
    pub fn project_path(&self) -> &Path {
        &self.project_path.as_path()
    }
    pub fn verbose(&self) -> bool {
        self.verbose
    }
}

/// Generator for fuzz driver projects.
pub struct CargoProjectBuilder {
    option: RsProjectOption,
}

pub struct RsProject {
    option: RsProjectOption,
}

impl CargoProjectBuilder {
    /// 创建新的项目生成器
    pub fn new(option: RsProjectOption) -> Self {
        Self { option }
    }

    pub fn build(self, rs_str: &str) -> io::Result<RsProject> {
        // remove project path if it exists
        if self.option.project_path().exists() {
            fs::remove_dir_all(self.option.project_path())?;
        }

        let project_path = self.option.project_path();

        // create the new project
        rap_info!("Creating new project at {}", project_path.display());

        let mut command = Command::new("cargo");
        command
            .arg("new")
            .arg(self.option.project_path())
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

        // write the Rust code to main.rs
        let main_path = project_path.join("src").join("main.rs");
        let mut main_file = File::create(main_path)?;
        main_file.write_all(rs_str.as_bytes())?;

        // add dependencies to Cargo.toml
        self.update_cargo_toml(&project_path)?;

        rap_info!(
            "Successfully created fuzz driver project at: {}",
            project_path.display()
        );
        Ok(RsProject {
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
            "{} = {{ path = \"../{}\" }}",
            self.option.tested_crate_name(),
            self.option.tested_crate_name(),
        )?;
        Ok(())
    }
}

impl RsProject {
    pub fn run(&self) -> io::Result<()> {
        let project_path = self.option.project_path().to_owned();
        rap_info!("Running fuzz driver project at: {}", project_path.display());
        let verbose = self.option.verbose();

        thread::spawn(move || {
            let mut command = Command::new("cargo");
            command
                .arg("run")
                .current_dir(&project_path)
                .stdout(Stdio::piped())
                .stderr(Stdio::piped());

            if verbose {
                command.arg("--verbose");
                rap_info!(
                    "Executing: cargo run --verbose (in {})",
                    project_path.display()
                );
            } else {
                rap_info!("Executing: cargo run (in {})", project_path.display());
            }

            match command.spawn() {
                Ok(process) => match process.wait_with_output() {
                    Ok(output) => {
                        let status = output.status;
                        let stdout = String::from_utf8_lossy(&output.stdout);
                        let stderr = String::from_utf8_lossy(&output.stderr);

                        if status.success() {
                            rap_info!("Project executed successfully");
                            if !stdout.is_empty() {
                                rap_info!("Standard output:\n{}", stdout);
                            }
                        } else {
                            rap_info!("Project execution failed with status: {}", status);
                            if !stderr.is_empty() {
                                rap_info!("Error output:\n{}", stderr);
                            }
                            if !stdout.is_empty() && verbose {
                                rap_info!("Standard output:\n{}", stdout);
                            }
                        }
                    }
                    Err(e) => {
                        rap_info!("Failed to get command output: {}", e);
                    }
                },
                Err(e) => {
                    rap_info!("Failed to execute command: {}", e);
                }
            }
        });

        Ok(())
    }
}
