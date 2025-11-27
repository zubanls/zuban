use std::{str::FromStr, sync::Arc};

use vfs::{AbsPath, NormalizedPath, VfsHandler};

use crate::{PythonVersion, Settings, parse_python_ini};

type EnvResult = Result<String, std::env::VarError>;

impl Settings {
    pub fn try_to_apply_environment_variables(
        &mut self,
        vfs_handler: &dyn VfsHandler,
        base_directory: &AbsPath,
        lookup_env_var: impl Fn(&str) -> EnvResult,
    ) {
        let mut add_to_mypy_path = |lookup: EnvResult| {
            if let Ok(found_path) = lookup {
                self.mypy_path.extend(found_path.split(':').map(|p| {
                    vfs_handler.normalize_rc_path(vfs_handler.absolute_path(base_directory, p))
                }))
            }
        };
        add_to_mypy_path(lookup_env_var("PYTHONPATH"));
        add_to_mypy_path(lookup_env_var("MYPYPATH"));
        self.try_to_find_environment_if_not_defined(vfs_handler, base_directory, lookup_env_var);
    }

    pub fn try_to_find_environment_if_not_defined(
        &mut self,
        vfs_handler: &dyn VfsHandler,
        base_directory: &AbsPath,
        lookup_env_var: impl Fn(&str) -> EnvResult,
    ) {
        if self.environment.is_some() {
            return;
        }
        match lookup_env_var("VIRTUAL_ENV").or_else(|_| lookup_env_var("CONDA_PREFIX")) {
            Ok(path) => {
                self.environment = Some(
                    vfs_handler.normalize_rc_path(vfs_handler.absolute_path(base_directory, &path)),
                )
            }
            Err(err) => {
                tracing::info!("Tried to access $VIRTUAL_ENV, but got: {err}");
                if try_to_find_env_in_dir(
                    &mut self.environment,
                    &mut self.python_version,
                    vfs_handler,
                    base_directory,
                ) {
                    return;
                }
                for path in &self.mypy_path {
                    if **path.as_ref() != *base_directory
                        && try_to_find_env_in_dir(
                            &mut self.environment,
                            &mut self.python_version,
                            vfs_handler,
                            path,
                        )
                    {
                        return;
                    }
                }
            }
        }
    }
}

fn try_to_find_env_in_dir(
    environment: &mut Option<Arc<NormalizedPath>>,
    py_version: &mut Option<PythonVersion>,
    vfs_handler: &dyn VfsHandler,
    base_directory: &AbsPath,
) -> bool {
    let _span = tracing::info_span!("try find venv").entered();
    let read_dir = match std::fs::read_dir(base_directory) {
        Ok(read_dir) => read_dir,
        Err(err) => {
            tracing::debug!("The base directory cannot be listed: {err}");
            return false;
        }
    };
    for entry in read_dir {
        let entry = match entry {
            Ok(entry) => entry,
            Err(err) => {
                tracing::debug!("Error while listing base directory: {err}");
                return false;
            }
        };
        if entry.file_type().is_ok_and(|t| t.is_dir()) {
            let venv_path = entry.path();
            let pyvenv_cfg_path = venv_path.join("pyvenv.cfg");
            let Some(venv_path_str) = venv_path.to_str() else {
                tracing::debug!("{venv_path:?} must be utf8 if wants to be a venv -> ignored");
                continue;
            };
            let code = match std::fs::read_to_string(&pyvenv_cfg_path) {
                Ok(string) => string,
                Err(err) => {
                    tracing::debug!("Error while reading {pyvenv_cfg_path:?}: {err}");
                    continue;
                }
            };
            if let Ok(ini) = parse_python_ini(&code) {
                // TODO use include-system-site-packages = false
                *environment = Some(
                    vfs_handler.normalize_rc_path(vfs_handler.unchecked_abs_path(venv_path_str)),
                );

                if py_version.is_none() {
                    if let Some(version_str) = ini.get_from(None::<String>, "version") {
                        match PythonVersion::from_str(version_str) {
                            Ok(v) => *py_version = Some(v),
                            Err(err) => {
                                tracing::warn!(
                                    "Parsing Python version in {pyvenv_cfg_path:?} failed: {err}"
                                );
                            }
                        }
                    } else {
                        tracing::warn!(
                            "Found {pyvenv_cfg_path:?}, but it has no \"version\" field"
                        );
                    }
                }
                tracing::info!("Found venv in {venv_path_str:?}");
                return true;
            }
        }
    }
    false
}
