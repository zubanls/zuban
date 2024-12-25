use std::{io::Read, path::Path};

use zuban_python::{DiagnosticConfig, ProjectOptions};

const CONFIG_PATHS: [&str; 6] = [
    "mypy.ini",
    ".mypy.ini",
    "pyproject.toml",
    "setup.cfg",
    "~/.config/mypy/config",
    "~/.mypy.ini",
];

pub fn find_config_or_default(config_file: Option<&Path>) -> (ProjectOptions, DiagnosticConfig) {
    let mut diagnostic_config = DiagnosticConfig::default();
    let options = if let Some((name, content)) = find_mypy_config_file(config_file) {
        if name.ends_with(".toml") {
            ProjectOptions::from_pyproject_toml(&content, &mut diagnostic_config)
        } else {
            ProjectOptions::from_mypy_ini(&content, &mut diagnostic_config)
        }
        .unwrap_or_else(|err| panic!("Problem parsing Mypy config {name}: {err}"))
    } else {
        ProjectOptions::default()
    };
    (options, diagnostic_config)
}

fn find_mypy_config_file(config_file: Option<&Path>) -> Option<(&str, String)> {
    const CONFIG_FILE_READ_ISSUE: &'static str = "Issue while reading the config file";
    if let Some(config_file) = config_file.as_ref() {
        let config_path = config_file
            .as_os_str()
            .to_str()
            .expect("Expected a valid UTF-8 encoded config path");
        let s = std::fs::read_to_string(config_path).expect(CONFIG_FILE_READ_ISSUE);
        return Some((config_path, s));
    }
    for config_path in CONFIG_PATHS {
        if let Ok(mut file) = std::fs::File::open(config_path) {
            let mut content = String::new();
            file.read_to_string(&mut content)
                .expect(CONFIG_FILE_READ_ISSUE);
            return Some((config_path, content));
        }
    }
    None
}
