use std::{io::Read, path::Path, sync::Arc};

use crate::{DiagnosticConfig, Mode, ModeChoice, ProjectOptions, get_zuban_config_and_apply_mode};
use toml_edit::{DocumentMut, Item, Value};
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

#[derive(Debug)]
pub struct FoundConfig {
    pub project_options: ProjectOptions,
    pub diagnostic_config: DiagnosticConfig,
    pub config_path: Option<Arc<AbsPath>>,
    pub most_probable_base: Arc<AbsPath>,
}

pub fn find_config(
    vfs: &dyn VfsHandler,
    current_dir: Arc<AbsPath>,
    config_file: Option<&Path>,
    mut mode: ModeChoice,
    mut on_check_path: impl FnMut(&AbsPath),
) -> anyhow::Result<FoundConfig> {
    if let Some(config_file) = config_file.as_ref() {
        let Some(config_path) = config_file.as_os_str().to_str() else {
            anyhow::bail!("Expected a valid UTF-8 encoded config path")
        };
        let config_path = vfs.absolute_path(&current_dir, config_path);
        let s = std::fs::read_to_string(config_path.as_ref())
            .map_err(|err| anyhow::anyhow!("Issue while reading {config_path}: {err}"))?;

        let most_probable_base = Arc::from(vfs.parent_of_absolute_path(&config_path).unwrap());
        if matches!(mode, ModeChoice::Auto) && config_path.ends_with(".ini") {
            mode = ModeChoice::Explicit(Mode::Mypy)
        }
        let result = initialize_config(vfs, &current_dir, config_path, s, mode)?;
        let project_options = result
            .0
            .unwrap_or_else(|| ProjectOptions::default_for_mode(mode.into()));
        Ok(FoundConfig {
            project_options,
            diagnostic_config: result.1,
            config_path: Some(result.2),
            most_probable_base,
        })
    } else {
        let mut current = current_dir.clone();
        loop {
            if let Some(found) =
                find_mypy_config_file_in_dir(vfs, current.clone(), mode, &mut on_check_path)?
            {
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
    mode: ModeChoice,
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
        ProjectOptions::from_mypy_ini(
            vfs,
            in_dir,
            &config_path,
            &content,
            &mut diagnostic_config,
            mode,
        )?
    };
    Ok((options, diagnostic_config, config_path))
}

fn find_mypy_config_file_in_dir(
    vfs: &dyn VfsHandler,
    dir: Arc<AbsPath>,
    mut mode: ModeChoice,
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
            // In the case of pyproject.toml we first check for Mypy specific parts, because the
            // general zuban parts just overwrite all Mypy specific config (other files such as
            // mypy.ini included). However mypy.ini still needs to be loaded first.
            if *config_name == PYPROJECT_TOML_NAME {
                let mut diagnostic_config = DiagnosticConfig::default();
                pyproject_toml = Some(content.parse()?);
                let document = pyproject_toml.as_ref().unwrap();
                get_zuban_config_and_apply_mode(document, &mut mode)?;
                let project_options = ProjectOptions::apply_pyproject_toml_mypy_part(
                    vfs,
                    &dir,
                    &config_path,
                    document,
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
                if matches!(mode, ModeChoice::Auto) {
                    mode = ModeChoice::Implicit(Mode::Mypy);
                }
                let result = initialize_config(vfs, &dir, config_path, content, mode)?;
                if let Some(project_options) = result.0.or_else(|| {
                    ["mypy.ini", ".mypy.ini"].contains(config_name).then(|| {
                        // Both mypy.ini and .mypy.ini always take precedent, even if there is no [mypy]
                        // section. See also https://mypy.readthedocs.io/en/stable/config_file.html
                        ProjectOptions::default_for_mode(mode.into())
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
    if let Some(pyproject_toml) = pyproject_toml {
        let end_result = end_result.get_or_insert_with(|| {
            default_config(
                mode,
                Some(vfs.absolute_path(&dir, PYPROJECT_TOML_NAME)),
                dir.clone(),
            )
        });
        if let Some(config) = pyproject_toml
            .get("tool")
            .and_then(|item| item.get("zuban"))
        {
            end_result.project_options.apply_pyproject_table(
                vfs,
                &dir,
                end_result.config_path.as_ref().unwrap(),
                &mut end_result.diagnostic_config,
                config,
                true,
            )?
        }
        // Try to figure out the Python version from other project.requires-python
        // Documented at https://packaging.python.org/en/latest/specifications/pyproject-toml/#requires-python
        if end_result.project_options.settings.python_version.is_none()
            && let Some(item) = pyproject_toml
                .get("project")
                .and_then(|item| item.get("requires-python"))
            && let Item::Value(Value::String(string)) = item
        {
            let s = string.value();
            if let Some(suffix) = s
                .strip_prefix("===")
                .or_else(|| s.strip_prefix("=="))
                .or_else(|| {
                    if s.split(".").count() < 3 {
                        return None;
                    }
                    s.strip_prefix("~=")
                })
            {
                end_result.project_options.settings.python_version = suffix.parse().ok()
            }
        }
    }
    Ok(end_result)
}

fn default_config(
    mode: ModeChoice,
    config_path: Option<Arc<AbsPath>>,
    dir: Arc<AbsPath>,
) -> FoundConfig {
    FoundConfig {
        project_options: ProjectOptions::default_for_mode(mode.into()),
        diagnostic_config: DiagnosticConfig::default(),
        config_path,
        most_probable_base: dir,
    }
}

#[cfg(test)]
mod tests {
    use vfs::LocalFS;

    use crate::PythonVersion;

    use super::*;

    const ZUBAN_WITH_VERSION: &str = "[tool.zuban]\npython_version = 3.13\n";

    fn project_version(version: &str) -> String {
        format!("[project]\nrequires-python = \"{version}\"\n")
    }

    fn search_fixture(fixture: impl AsRef<str>) -> FoundConfig {
        let test_dir = test_utils::write_files_from_fixture(fixture.as_ref(), false);

        let fs = LocalFS::without_watcher();
        find_config(
            &fs,
            fs.unchecked_abs_path(test_dir.path()),
            None,
            ModeChoice::Auto,
            |_| (),
        )
        .unwrap()
    }

    #[test]
    fn test_requires_python_from_pyproject_toml() {
        let run = |pyproject_toml: &str| {
            let fixture = format!("[file pyproject.toml]\n{pyproject_toml}");
            search_fixture(fixture)
                .project_options
                .settings
                .python_version
        };

        assert_eq!(
            run(&project_version("==3.32.3")),
            Some(PythonVersion::new(3, 32))
        );
        assert_eq!(
            run(&project_version("===3.10.1")),
            Some(PythonVersion::new(3, 10))
        );
        assert_eq!(
            run(&project_version("~=3.33.3")),
            Some(PythonVersion::new(3, 33))
        );
        assert_eq!(run(&project_version(">=3.11")), None);
        assert_eq!(run(&project_version(">3.11")), None);
        assert_eq!(run(&project_version("<3.15")), None);
        assert_eq!(run(&project_version("<=3.15")), None);
        assert_eq!(run(&project_version("==3")), None);
        assert_eq!(run(&project_version("~=3")), None);
        assert_eq!(run(&project_version("~=3.2")), None);
        assert_eq!(run(&project_version("3.12")), None);

        assert_eq!(run(ZUBAN_WITH_VERSION), Some(PythonVersion::new(3, 13)));
        assert_eq!(
            run(&format!(
                "{ZUBAN_WITH_VERSION}\n{}",
                project_version("==3.12")
            )),
            Some(PythonVersion::new(3, 13))
        );
        assert_eq!(
            run(&format!(
                "{}\n{ZUBAN_WITH_VERSION}",
                project_version("==3.12")
            )),
            Some(PythonVersion::new(3, 13))
        );
    }

    #[test]
    fn test_requires_python_from_pyproject_toml_and_mypy_ini() {
        let run = |pyproject_toml: &str| {
            let fixture = format!(
                "[file pyproject.toml]\n{pyproject_toml}\n\
                 [file mypy.ini]\n\
                 [mypy]\n\
                 python_version = 3.42"
            );
            search_fixture(fixture)
                .project_options
                .settings
                .python_version
        };

        assert_eq!(
            run(&project_version("==3.32.3")),
            Some(PythonVersion::new(3, 42))
        );
        assert_eq!(
            run(&format!(
                "{}\n{ZUBAN_WITH_VERSION}",
                project_version("==3.12")
            )),
            Some(PythonVersion::new(3, 13))
        );

        assert_eq!(
            run(&format!(
                "[tool.mypy]\npython_version = 3.3\n{}",
                project_version("==3.12")
            )),
            Some(PythonVersion::new(3, 3))
        );
        assert_eq!(
            run(&format!("[tool.mypy]\npython_version = 3.3\n",)),
            Some(PythonVersion::new(3, 3))
        );
    }
}
