use std::{io::Read, path::Path, sync::Arc};

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

pub struct FoundConfig {
    pub project_options: ProjectOptions,
    pub diagnostic_config: DiagnosticConfig,
    pub config_path: Option<Arc<AbsPath>>,
}

pub fn find_workspace_config(
    vfs: &dyn VfsHandler,
    workspace_dir: &AbsPath,
    on_check_path: impl FnMut(&AbsPath),
) -> anyhow::Result<ProjectOptions> {
    Ok(find_mypy_config_file_in_dir(vfs, workspace_dir, false, on_check_path)?.project_options)
}

pub fn find_cli_config(
    vfs: &dyn VfsHandler,
    current_dir: &AbsPath,
    config_file: Option<&Path>,
    mypy_compatible_default: bool,
) -> anyhow::Result<FoundConfig> {
    if let Some(config_file) = config_file.as_ref() {
        let Some(config_path) = config_file.as_os_str().to_str() else {
            anyhow::bail!("Expected a valid UTF-8 encoded config path")
        };
        let s = std::fs::read_to_string(config_path)
            .map_err(|err| anyhow::anyhow!("Issue while reading {config_path}: {err}"))?;

        let result = initialize_config(vfs, current_dir, config_path, s)?;
        Ok(FoundConfig {
            project_options: result.0.unwrap_or_else(ProjectOptions::mypy_default),
            diagnostic_config: result.1,
            config_path: Some(vfs.absolute_path(current_dir, config_path)),
        })
    } else {
        find_mypy_config_file_in_dir(vfs, current_dir, mypy_compatible_default, |_| ())
    }
}

fn initialize_config(
    vfs: &dyn VfsHandler,
    current_dir: &AbsPath,
    path: &str,
    content: String,
) -> anyhow::Result<(Option<ProjectOptions>, DiagnosticConfig, Arc<AbsPath>)> {
    let _p = tracing::info_span!("config_finder").entered();
    let mut diagnostic_config = DiagnosticConfig::default();
    let config_path = vfs.absolute_path(current_dir, path);
    let options = if path.ends_with(".toml") {
        ProjectOptions::from_pyproject_toml(
            vfs,
            current_dir,
            &config_path,
            &content,
            &mut diagnostic_config,
        )?
    } else {
        ProjectOptions::from_mypy_ini(
            vfs,
            current_dir,
            &config_path,
            &content,
            &mut diagnostic_config,
        )?
    };
    Ok((options, diagnostic_config, config_path))
}

fn find_mypy_config_file_in_dir(
    vfs: &dyn VfsHandler,
    dir: &AbsPath,
    mypy_compatible_default: bool,
    mut on_check_path: impl FnMut(&AbsPath),
) -> anyhow::Result<FoundConfig> {
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
                result.0 = Some(ProjectOptions::mypy_default())
            }
            if let Some(project_options) = result.0 {
                return Ok(FoundConfig {
                    project_options,
                    diagnostic_config: result.1,
                    config_path: Some(result.2),
                });
            }
        }
    }
    tracing::info!("No relevant config found");
    Ok(FoundConfig {
        project_options: if mypy_compatible_default {
            ProjectOptions::mypy_default()
        } else {
            ProjectOptions::default()
        },
        diagnostic_config: DiagnosticConfig::default(),
        config_path: None,
    })
}
