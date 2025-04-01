use std::{io::Read, path::Path};

use crate::{DiagnosticConfig, ProjectOptions};
use vfs::{AbsPath, VfsHandler};

const CONFIG_PATHS: [&str; 4] = [
    "mypy.ini",
    ".mypy.ini",
    "pyproject.toml",
    "setup.cfg",
    // TODO this is currently not implemented
    //"~/.config/mypy/config",
    //"~/.mypy.ini",
];

pub fn find_workspace_config(
    vfs: &dyn VfsHandler,
    workspace_dir: &AbsPath,
    on_check_path: impl FnMut(&AbsPath),
) -> anyhow::Result<ProjectOptions> {
    let mut project_options = find_mypy_config_file_in_dir(vfs, workspace_dir, on_check_path)?.0;
    project_options.settings.mypy_path = vec![];
    Ok(project_options)
}

pub fn find_cli_config(
    vfs: &dyn VfsHandler,
    current_dir: &AbsPath,
    config_file: Option<&Path>,
) -> anyhow::Result<(ProjectOptions, DiagnosticConfig)> {
    if let Some(config_file) = config_file.as_ref() {
        let Some(config_path) = config_file.as_os_str().to_str() else {
            anyhow::bail!("Expected a valid UTF-8 encoded config path")
        };
        let s = std::fs::read_to_string(config_path)
            .map_err(|err| anyhow::anyhow!("Issue while reading {config_path}: {err}"))?;

        let result = initialize_config(vfs, current_dir, config_path, s)?;
        Ok((result.0.unwrap_or_else(ProjectOptions::default), result.1))
    } else {
        find_mypy_config_file_in_dir(vfs, current_dir, |_| ())
    }
}

fn initialize_config(
    vfs: &dyn VfsHandler,
    current_dir: &AbsPath,
    path: &str,
    content: String,
) -> anyhow::Result<(Option<ProjectOptions>, DiagnosticConfig)> {
    let _p = tracing::info_span!("config_finder").entered();
    let mut diagnostic_config = DiagnosticConfig::default();
    let options = if path.ends_with(".toml") {
        ProjectOptions::from_pyproject_toml(vfs, current_dir, &content, &mut diagnostic_config)?
    } else {
        ProjectOptions::from_mypy_ini(vfs, current_dir, &content, &mut diagnostic_config)?
    };
    Ok((options, diagnostic_config))
}

fn find_mypy_config_file_in_dir(
    vfs: &dyn VfsHandler,
    dir: &AbsPath,
    mut on_check_path: impl FnMut(&AbsPath),
) -> anyhow::Result<(ProjectOptions, DiagnosticConfig)> {
    for config_path in CONFIG_PATHS.iter() {
        let path = vfs.join(dir, config_path);
        on_check_path(&path);
        if let Ok(mut file) = std::fs::File::open(path.as_ref()) {
            let mut content = String::new();
            if let Err(err) = file.read_to_string(&mut content) {
                anyhow::bail!("Issue while reading {path}: {err}");
            }
            tracing::info!("Potential config found: {config_path}");
            let mut result = initialize_config(vfs, dir, config_path, content)?;
            if result.0.is_none() && ["mypy.ini", ".mypy.ini"].contains(config_path) {
                // Both mypy.ini and .mypy.ini always take precedent, even if there is no [mypy]
                // section. See also https://mypy.readthedocs.io/en/stable/config_file.html
                result.0 = Some(ProjectOptions::default())
            }
            if let Some(project_options) = result.0 {
                return Ok((project_options, result.1));
            }
        }
    }
    tracing::info!("No relevant config found");
    Ok((ProjectOptions::default(), DiagnosticConfig::default()))
}
