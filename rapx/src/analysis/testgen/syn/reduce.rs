use super::super::driver;
use super::project::PocProject;
use std::{
    fs,
    io::{self},
};

fn join_lines_if(lines: &[&str], reserved: &[bool]) -> String {
    lines
        .iter()
        .zip(reserved.iter())
        .filter_map(|(line, reserved)| if *reserved { Some(*line) } else { None })
        .collect::<Vec<_>>()
        .join("\n")
}

impl PocProject {
    fn is_project_still_interesting(&self) -> io::Result<bool> {
        let record = self.run_cargo_cmd(&["miri", "run"], driver::miri_env_vars(), 0)?;
        // rap_info!("Poc Stdout: {}", String::from_utf8_lossy(&record.stdout));
        // rap_info!("Poc Stderr: {}", String::from_utf8_lossy(&record.stderr));
        if !matches!(record.retcode, Some(1)) {
            return Ok(false);
        }

        Ok(String::from_utf8_lossy(&record.stderr).contains("Undefined Behavior"))
    }

    pub fn reduce(&self) -> std::io::Result<()> {
        let source_path = self.option().project_path.join("src/main.rs");
        rap_info!("reduce {}", source_path.display());

        // backup the source file
        fs::copy(&source_path, source_path.with_file_name("main.rs.orig"))?;
        let content = fs::read_to_string(&source_path)?;
        // analyze source
        let lines = content.split('\n').collect::<Vec<&str>>();
        let mut start = 0;
        let mut end = 0;
        lines.iter().enumerate().for_each(|(no, line)| {
            if line.starts_with("fn main() {") {
                start = no;
            }
            if line.starts_with("}") {
                end = no;
            }
        });

        end -= 1;
        let mut reserved = vec![true; lines.len()];

        rap_info!(
            "start reducing file (start = {}, end = {})",
            start + 1,
            end + 1
        );

        // from end to start, try remove one line each
        while end != start {
            let mut msg = format!("try reducing line {}...", end + 1);
            reserved[end] = false;
            // if it is comment line, skip directly
            if lines[end].trim().starts_with("//") {
                msg += "success!";
            } else {
                // write file to new content
                fs::write(&source_path, join_lines_if(&lines, &reserved))?;
                self.clear_artifact()?;
                if !self.is_project_still_interesting()? {
                    reserved[end] = true;
                    msg += "fail :(";
                } else {
                    msg += "success!";
                }
            }

            rap_info!("{}", msg);
            end -= 1;
        }
        self.clear_artifact()?;

        // write final source file back
        fs::write(&source_path, join_lines_if(&lines, &reserved))?;

        Ok(())
    }
}
