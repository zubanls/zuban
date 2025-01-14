use std::{io::Read, path::Path};

use config::{DiagnosticConfig, ProjectOptions};

const CONFIG_PATHS: [&str; 6] = [
    "mypy.ini",
    ".mypy.ini",
    "pyproject.toml",
    "setup.cfg",
    "~/.config/mypy/config",
    "~/.mypy.ini",
];

pub fn find_workspace_config(
    workspace_dir: &str,
    on_check_path: impl FnMut(&Path),
) -> anyhow::Result<ProjectOptions> {
    let maybe_found = find_mypy_config_file_in_dir(Some(Path::new(workspace_dir)), on_check_path);
    let mut project_options = initialize_config(maybe_found)?.0;
    project_options.settings.mypy_path = vec![];
    Ok(project_options)
}

pub fn find_cli_config(
    config_file: Option<&Path>,
) -> anyhow::Result<(ProjectOptions, DiagnosticConfig)> {
    let maybe_found = if let Some(config_file) = config_file.as_ref() {
        let Some(config_path) = config_file.as_os_str().to_str() else {
            anyhow::bail!("Expected a valid UTF-8 encoded config path")
        };
        let s = std::fs::read_to_string(config_path);
        Some((config_path, s))
    } else {
        find_mypy_config_file_in_dir(None, |_| ())
    };
    initialize_config(maybe_found)
}

fn initialize_config(
    found_file_with_content: Option<(&str, std::io::Result<String>)>,
) -> anyhow::Result<(ProjectOptions, DiagnosticConfig)> {
    let _p = tracing::info_span!("config_finder").entered();
    let mut diagnostic_config = DiagnosticConfig::default();
    let options = if let Some((path, content)) = found_file_with_content {
        tracing::info!("Config found: {path}");
        let content =
            content.map_err(|err| anyhow::anyhow!("Issue while reading {path}: {err}"))?;
        if path.ends_with(".toml") {
            ProjectOptions::from_pyproject_toml(&content, &mut diagnostic_config)?
        } else {
            ProjectOptions::from_mypy_ini(&content, &mut diagnostic_config)?
        }
    } else {
        tracing::info!("No config found");
        ProjectOptions::default()
    };
    Ok((options, diagnostic_config))
}

fn find_mypy_config_file_in_dir(
    dir: Option<&Path>,
    mut on_check_path: impl FnMut(&Path),
) -> Option<(&'static str, std::io::Result<String>)> {
    CONFIG_PATHS.iter().find_map(|config_path| {
        let mut check = |path: &Path| {
            on_check_path(path);
            if let Ok(mut file) = std::fs::File::open(path) {
                let mut content = String::new();
                let result = file.read_to_string(&mut content);
                return Some((*config_path, result.map(|_| content)));
            }
            None
        };
        if let Some(dir) = dir {
            check(&dir.join(config_path))
        } else {
            check(Path::new(config_path))
        }
    })
}
