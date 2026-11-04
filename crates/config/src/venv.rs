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

    fn try_to_find_environment_if_not_defined(
        &mut self,
        vfs_handler: &dyn VfsHandler,
        base_directory: &AbsPath,
        lookup_env_var: impl Fn(&str) -> EnvResult,
    ) {
        if self.environment.is_some() {
            return;
        }
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
        // The environment variable has an intentionally lower priority than looking for venvs.
        // This appears to happen in a lot of cases where Zuban is run as a tool from e.g. uv, but
        // probably also happens with pipx, where virtual environments are used to isolate Zuban
        // (see also GitHub #21). This might also happen in VSCode when multiple projects are
        // opened in a different order where the first and initial $VIRTUAL_ENV is different than
        // the actual virtual envs of the later opened projects.
        match lookup_env_var("VIRTUAL_ENV").or_else(|_| lookup_env_var("CONDA_PREFIX")) {
            Ok(path) => {
                self.environment = Some(
                    vfs_handler.normalize_rc_path(vfs_handler.absolute_path(base_directory, &path)),
                )
            }
            Err(err) => {
                tracing::info!("Tried to access $VIRTUAL_ENV, but got: {err}");
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
    let mut dir_entries = vec![];
    for entry in read_dir {
        let entry = match entry {
            Ok(entry) => entry,
            Err(err) => {
                tracing::debug!("Error while listing base directory: {err}");
                return false;
            }
        };
        if entry.file_type().is_ok_and(|t| t.is_dir()) {
            dir_entries.push(entry)
        }
    }
    // Sort venvs in a more deterministic way.
    dir_entries.sort_by_key(|e| {
        let f = e.file_name();
        let file_name = f.as_encoded_bytes();
        let contains_bytes = |sought: &[u8]| file_name.windows(sought.len()).any(|w| w == sought);
        match file_name {
            b"venv" => 0,
            b".venv" => 1,
            _ if contains_bytes(b"venv") => 2,
            _ if contains_bytes(b"virtualenv") => 3,
            _ => 4,
        }
    });
    for entry in dir_entries {
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
            *environment =
                Some(vfs_handler.normalize_rc_path(vfs_handler.unchecked_abs_path(venv_path_str)));

            if py_version.is_none() {
                if let Some(version_str) = ini
                    .get_from(None::<String>, "version")
                    .or_else(|| ini.get_from(None::<String>, "version_info"))
                {
                    match PythonVersion::from_str(version_str) {
                        Ok(v) => *py_version = Some(v),
                        Err(err) => {
                            tracing::warn!(
                                "Parsing Python version in {pyvenv_cfg_path:?} failed: {err}"
                            );
                        }
                    }
                } else {
                    tracing::warn!("Found {pyvenv_cfg_path:?}, but it has no \"version\" field");
                }
            }
            tracing::info!("Found venv in {venv_path_str:?}");
            return true;
        }
    }
    false
}

#[cfg(test)]
mod tests {
    use vfs::LocalFS;

    use crate::PythonVersion;

    use super::*;

    #[test]
    fn test_requires_python_from_pyproject_toml() {
        let run = |version_string: &str| {
            let fixture = format!("[file venv/pyvenv.cfg]\n{version_string}");
            let test_dir = test_utils::write_files_from_fixture(fixture.as_ref(), false);

            let fs = LocalFS::without_watcher();
            let mut settings = Settings::default();
            settings.try_to_apply_environment_variables(
                &fs,
                &fs.unchecked_abs_path(test_dir.path()),
                |_| Err(std::env::VarError::NotPresent),
            );
            settings.python_version
        };

        assert_eq!(run("version = 3.4.1"), Some(PythonVersion::new(3, 4)));
        assert_eq!(run("version_info = 3.5.1"), Some(PythonVersion::new(3, 5)));
        assert_eq!(
            run("version_info = 3.6.1\nversion=3.7"),
            Some(PythonVersion::new(3, 7))
        );
        assert_eq!(run(""), None);
    }
}
