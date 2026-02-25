use std::{io::Read, path::Path, sync::Arc};

use crate::{DiagnosticConfig, Mode, ProjectOptions};
use toml_edit::DocumentMut;
use vfs::{AbsPath, VfsHandler};

const PYPROJECT_TOML_NAME: &str = "pyproject.toml";
const CONFIG_NAMES: [&str; 4] = [
    // Mypy prioritizes mypy.ini. But since we allow [tool.zuban] entries as well it makes sense
    // to check that first. I doubt many people have both mypy.ini and pyproject.toml configs for
    // Mypy.
    PYPROJECT_TOML_NAME,
    "mypy.ini",
    ".mypy.ini",
    "setup.cfg",
    // TODO this is currently not implemented
    //"~/.config/mypy/config",
    //"~/.mypy.ini",
];

pub struct FoundConfig {
    pub project_options: ProjectOptions,
    pub diagnostic_config: DiagnosticConfig,
    pub config_path: Option<Arc<AbsPath>>,
    pub most_probable_base: Arc<AbsPath>,
}

pub fn find_workspace_config(
    vfs: &dyn VfsHandler,
    workspace_dir: Arc<AbsPath>,
    on_check_path: impl FnMut(&AbsPath),
) -> anyhow::Result<ProjectOptions> {
    let config = find_mypy_config_file_in_dir(vfs, workspace_dir, None, on_check_path)?;

    Ok(match config {
        Some(config) => config.project_options,
        None => {
            tracing::info!("No relevant config found");
            ProjectOptions::default_for_mode(Mode::Default)
        }
    })
}

pub fn find_cli_config(
    vfs: &dyn VfsHandler,
    current_dir: Arc<AbsPath>,
    config_file: Option<&Path>,
    mode: Option<Mode>,
) -> anyhow::Result<FoundConfig> {
    if let Some(config_file) = config_file.as_ref() {
        let Some(config_path) = config_file.as_os_str().to_str() else {
            anyhow::bail!("Expected a valid UTF-8 encoded config path")
        };
        let config_path = vfs.absolute_path(&current_dir, config_path);
        let s = std::fs::read_to_string(config_path.as_ref())
            .map_err(|err| anyhow::anyhow!("Issue while reading {config_path}: {err}"))?;

        let most_probable_base = Arc::from(vfs.parent_of_absolute_path(&config_path).unwrap());
        let result = initialize_config(vfs, &current_dir, config_path, s, mode)?;
        let project_options = result.0.unwrap_or_else(ProjectOptions::mypy_default);
        Ok(FoundConfig {
            project_options,
            diagnostic_config: result.1,
            config_path: Some(result.2),
            most_probable_base,
        })
    } else {
        let mut current = current_dir.clone();
        loop {
            if let Some(found) = find_mypy_config_file_in_dir(vfs, current.clone(), mode, |_| ())? {
                return Ok(found);
            }
            if let Some(outer) = vfs.parent_of_absolute_path(&current) {
                current = Arc::from(outer);
            } else {
                break;
            }
        }
        tracing::info!("No relevant config found");
        Ok(default_config(mode, None, current_dir))
    }
}

fn initialize_config(
    vfs: &dyn VfsHandler,
    in_dir: &AbsPath,
    config_path: Arc<AbsPath>,
    content: String,
    mode: Option<Mode>,
) -> anyhow::Result<(Option<ProjectOptions>, DiagnosticConfig, Arc<AbsPath>)> {
    let _p = tracing::info_span!("config_finder").entered();
    let mut diagnostic_config = DiagnosticConfig::default();
    let options = if config_path.ends_with(".toml") {
        ProjectOptions::from_pyproject_toml_only(
            vfs,
            in_dir,
            &config_path,
            &content,
            &mut diagnostic_config,
            mode,
        )?
    } else {
        ProjectOptions::from_mypy_ini(vfs, in_dir, &config_path, &content, &mut diagnostic_config)?
    };
    Ok((options, diagnostic_config, config_path))
}

fn find_mypy_config_file_in_dir(
    vfs: &dyn VfsHandler,
    dir: Arc<AbsPath>,
    mode: Option<Mode>,
    mut on_check_path: impl FnMut(&AbsPath),
) -> anyhow::Result<Option<FoundConfig>> {
    let mut end_result = None;
    let mut pyproject_toml: Option<DocumentMut> = None;
    for config_name in CONFIG_NAMES.iter() {
        let path = vfs.join(&dir, config_name);
        on_check_path(&path);
        if let Ok(mut file) = std::fs::File::open(path.as_ref()) {
            let mut content = String::new();
            if let Err(err) = file.read_to_string(&mut content) {
                anyhow::bail!("Issue while reading {path}: {err}");
            }
            let config_path = vfs.absolute_path(&dir, config_name);
            tracing::info!("Potential config found: {config_path}");
            if *config_name == PYPROJECT_TOML_NAME {
                let mut diagnostic_config = DiagnosticConfig::default();
                pyproject_toml = Some(content.parse()?);
                let project_options = ProjectOptions::apply_pyproject_toml_mypy_part(
                    vfs,
                    &dir,
                    &config_path,
                    pyproject_toml.as_ref().unwrap(),
                    &mut diagnostic_config,
                    mode,
                )?;
                if let Some(project_options) = project_options {
                    end_result = Some(FoundConfig {
                        project_options,
                        diagnostic_config,
                        config_path: Some(config_path),
                        most_probable_base: dir.clone(),
                    });
                    break;
                }
            } else {
                let result = initialize_config(vfs, &dir, config_path, content, mode)?;
                if let Some(project_options) = result.0.or_else(|| {
                    ["mypy.ini", ".mypy.ini"].contains(config_name).then(|| {
                        // Both mypy.ini and .mypy.ini always take precedent, even if there is no [mypy]
                        // section. See also https://mypy.readthedocs.io/en/stable/config_file.html
                        ProjectOptions::mypy_default()
                    })
                }) {
                    end_result = Some(FoundConfig {
                        project_options,
                        diagnostic_config: result.1,
                        config_path: Some(result.2),
                        most_probable_base: dir.clone(),
                    });
                    break;
                }
            };
        }
    }
    if let Some(pyproject_toml) = pyproject_toml
        && let Some(config) = pyproject_toml
            .get("tool")
            .and_then(|item| item.get("zuban"))
    {
        if end_result.is_none() {
            end_result = Some(default_config(
                mode,
                Some(vfs.absolute_path(&dir, PYPROJECT_TOML_NAME)),
                dir.clone(),
            ));
        }
        let found = end_result.as_mut().unwrap();
        found.project_options.apply_pyproject_table(
            vfs,
            &dir,
            found.config_path.as_ref().unwrap(),
            &mut found.diagnostic_config,
            config,
            true,
        )?
    }
    Ok(end_result)
}

fn default_config(
    mode: Option<Mode>,
    config_path: Option<Arc<AbsPath>>,
    dir: Arc<AbsPath>,
) -> FoundConfig {
    FoundConfig {
        project_options: ProjectOptions::default_for_mode(mode.unwrap_or(Mode::Default)),
        diagnostic_config: DiagnosticConfig::default(),
        config_path,
        most_probable_base: dir,
    }
}
