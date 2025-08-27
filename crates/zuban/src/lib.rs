use std::env;
use std::process::{exit, Command};

pub fn execute_zuban_executable_with_subcommand(subcommand: &str) {
    // Collect args except the binary name
    let args: Vec<String> = env::args().skip(1).collect();

    let mut zuban_path = env::current_exe().expect("failed to get current exe path");
    // replace "zubanls"/"zmypy" with "zuban"
    zuban_path.set_file_name("zuban");

    // Run "./zuban server <args...>"
    let status = Command::new(zuban_path)
        .arg(subcommand)
        .args(args)
        .status()
        .expect("failed to execute zuban");
    exit(status.code().unwrap_or(1));
}
