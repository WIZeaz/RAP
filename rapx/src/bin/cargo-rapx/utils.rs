use crate::args;
use std::path::Path;
use std::process::{self, Command};

pub fn run_cmd(mut cmd: Command) {
    rap_trace!("Command is: {:?}.", cmd);
    match cmd.status() {
        Ok(status) => {
            if !status.success() {
                // 254 is an arbitrary non-zero magic number that
                // indicates the program is terminated by signals
                process::exit(status.code().unwrap_or(254));
            }
        }
        Err(err) => panic!("Error in running {:?} {}.", cmd, err),
    }
}

pub fn run_rustc() {
    let mut cmd = Command::new("rustc");
    cmd.args(args::skip2());
    run_cmd(cmd);
}

pub fn run_rap() {
    // This is for integration test, which runs cargo-rapx with `RAP_EXE_PATH`
    // set to the path of the rapx binary built by cargo, since the rapx binary
    // built by cargo is not installed to the system.
    let mut cmd = if let Ok(rap_path) = std::env::var("RAP_EXE_PATH") {
        let path = Path::new(&rap_path);
        assert!(
            path.exists(),
            "RAP_EXE_PATH is set to {}, but the file does not exist.",
            path.display()
        );
        Command::new(path)
    } else {
        Command::new("rapx")
    };
    cmd.args(args::skip2());
    run_cmd(cmd);
}
