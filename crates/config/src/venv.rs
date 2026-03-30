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

pub fn extract_version_from_pyvenv_cfg(env_path: &NormalizedPath) -> Option<PythonVersion> {
    let pyvenv_cfg_path = env_path.as_ref().join("pyvenv.cfg");
    let code = match std::fs::read_to_string(&pyvenv_cfg_path) {
        Ok(string) => string,
        Err(err) => {
            // pyvenv.cfg doesn't exist - this is normal for system Python installations
            tracing::debug!("Error while reading {pyvenv_cfg_path:?}: {err}");
            return None;
        }
    };

    match parse_python_ini(&code) {
        Ok(ini) => {
            // Try "version" field first (stdlib venv format)
            if let Some(version_str) = ini.get_from(None::<String>, "version") {
                match PythonVersion::from_str(version_str) {
                    Ok(v) => return Some(v),
                    Err(err) => {
                        tracing::warn!(
                            "Parsing Python version in {pyvenv_cfg_path:?} failed: {err}"
                        );
                        return None;
                    }
                }
            }
            // Fallback to "version_info" field (uv format)
            if let Some(version_str) = ini.get_from(None::<String>, "version_info") {
                match PythonVersion::from_str(version_str) {
                    Ok(v) => return Some(v),
                    Err(err) => {
                        tracing::warn!(
                            "Parsing Python version in {pyvenv_cfg_path:?} failed: {err}"
                        );
                        return None;
                    }
                }
            }
            tracing::warn!("Found {pyvenv_cfg_path:?}, but it has no \"version\" field");
            None
        }
        Err(err) => {
            tracing::warn!("Parsing Python version in {pyvenv_cfg_path:?} failed: {err}");
            None
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
        let Some(venv_path_str) = venv_path.to_str() else {
            tracing::debug!("{venv_path:?} must be utf8 if wants to be a venv -> ignored");
            continue;
        };
        let pyvenv_cfg_path = venv_path.join("pyvenv.cfg");
        let code = match std::fs::read_to_string(&pyvenv_cfg_path) {
            Ok(string) => string,
            Err(err) => {
                tracing::debug!("Error while reading {pyvenv_cfg_path:?}: {err}");
                continue;
            }
        };

        if parse_python_ini(&code).is_err() {
            continue;
        }

        // TODO use include-system-site-packages = false
        *environment =
            Some(vfs_handler.normalize_rc_path(vfs_handler.unchecked_abs_path(venv_path_str)));

        if py_version.is_none() {
            let env_path = environment.as_ref().unwrap();
            if let Some(version) = extract_version_from_pyvenv_cfg(env_path.as_ref()) {
                *py_version = Some(version);
            }
        }

        tracing::info!("Found venv in {venv_path_str:?}");
        return true;
    }
    false
}

#[cfg(test)]
mod tests {
    use std::io::Write;

    use super::*;
    use vfs::LocalFS;

    #[test]
    fn test_extract_version_from_pyvenv_cfg_version_field() {
        let temp_dir = tempfile::tempdir().unwrap();
        let pyvenv_cfg_path = temp_dir.path().join("pyvenv.cfg");
        let mut file = std::fs::File::create(&pyvenv_cfg_path).unwrap();
        writeln!(file, "version = 3.12").unwrap();

        let handler = LocalFS::without_watcher();
        let env_path = handler.unchecked_normalized_path(
            handler.unchecked_abs_path(temp_dir.path().to_str().unwrap()),
        );
        let version = extract_version_from_pyvenv_cfg(&env_path).unwrap();
        assert_eq!(version.major, 3);
        assert_eq!(version.minor, 12);
    }

    #[test]
    fn test_extract_version_from_pyvenv_cfg_version_info_field() {
        let temp_dir = tempfile::tempdir().unwrap();
        let pyvenv_cfg_path = temp_dir.path().join("pyvenv.cfg");
        let mut file = std::fs::File::create(&pyvenv_cfg_path).unwrap();
        writeln!(file, "version_info = 3.11.5").unwrap();

        let handler = LocalFS::without_watcher();
        let env_path = handler.unchecked_normalized_path(
            handler.unchecked_abs_path(temp_dir.path().to_str().unwrap()),
        );
        let version = extract_version_from_pyvenv_cfg(&env_path).unwrap();
        assert_eq!(version.major, 3);
        assert_eq!(version.minor, 11);
    }

    #[test]
    fn test_extract_version_from_pyvenv_cfg_version_takes_priority() {
        let temp_dir = tempfile::tempdir().unwrap();
        let pyvenv_cfg_path = temp_dir.path().join("pyvenv.cfg");
        let mut file = std::fs::File::create(&pyvenv_cfg_path).unwrap();
        writeln!(file, "version = 3.12").unwrap();
        writeln!(file, "version_info = 3.11.5").unwrap();

        let handler = LocalFS::without_watcher();
        let env_path = handler.unchecked_normalized_path(
            handler.unchecked_abs_path(temp_dir.path().to_str().unwrap()),
        );
        let version = extract_version_from_pyvenv_cfg(&env_path).unwrap();

        assert_eq!(version.major, 3);
        assert_eq!(version.minor, 12);
    }

    #[test]
    fn test_extract_version_from_pyvenv_cfg_missing_file() {
        let temp_dir = tempfile::tempdir().unwrap();

        let handler = LocalFS::without_watcher();
        let env_path = handler.unchecked_normalized_path(
            handler.unchecked_abs_path(temp_dir.path().to_str().unwrap()),
        );
        let version = extract_version_from_pyvenv_cfg(&env_path);
        assert!(version.is_none());
    }

    #[test]
    fn test_extract_version_from_pyvenv_cfg_missing_version_fields() {
        let temp_dir = tempfile::tempdir().unwrap();
        let pyvenv_cfg_path = temp_dir.path().join("pyvenv.cfg");
        let mut file = std::fs::File::create(&pyvenv_cfg_path).unwrap();
        writeln!(file, "home = /usr/bin/python3").unwrap();
        writeln!(file, "include-system-site-packages = false").unwrap();

        let handler = LocalFS::without_watcher();
        let env_path = handler.unchecked_normalized_path(
            handler.unchecked_abs_path(temp_dir.path().to_str().unwrap()),
        );
        let version = extract_version_from_pyvenv_cfg(&env_path);
        assert!(version.is_none());
    }

    #[test]
    fn test_apply_python_executable_extracts_version() {
        let temp_dir = tempfile::tempdir().unwrap();
        let venv_path = temp_dir.path().join("test_venv");
        std::fs::create_dir(&venv_path).unwrap();
        let bin_path = venv_path.join("bin");
        std::fs::create_dir(&bin_path).unwrap();
        let python_path = bin_path.join("python");
        std::fs::write(&python_path, "").unwrap();

        let pyvenv_cfg_path = venv_path.join("pyvenv.cfg");
        let mut file = std::fs::File::create(&pyvenv_cfg_path).unwrap();
        writeln!(file, "version = 3.12").unwrap();

        let mut settings = Settings::default();
        let handler = LocalFS::without_watcher();
        let project_dir = handler.unchecked_abs_path(temp_dir.path().to_str().unwrap());

        settings
            .apply_python_executable(&handler, &project_dir, None, python_path.to_str().unwrap())
            .unwrap();

        let version = settings.python_version.unwrap();
        assert_eq!(version.major, 3);
        assert_eq!(version.minor, 12);
    }

    #[test]
    fn test_apply_python_executable_respects_explicit_version() {
        let temp_dir = tempfile::tempdir().unwrap();
        let venv_path = temp_dir.path().join("test_venv");
        std::fs::create_dir(&venv_path).unwrap();
        let bin_path = venv_path.join("bin");
        std::fs::create_dir(&bin_path).unwrap();
        let python_path = bin_path.join("python");
        std::fs::write(&python_path, "").unwrap();

        let pyvenv_cfg_path = venv_path.join("pyvenv.cfg");
        let mut file = std::fs::File::create(&pyvenv_cfg_path).unwrap();
        writeln!(file, "version = 3.12").unwrap();

        let mut settings = Settings::default();
        settings.python_version = Some(PythonVersion::new(3, 10));

        let handler = LocalFS::without_watcher();
        let project_dir = handler.unchecked_abs_path(temp_dir.path().to_str().unwrap());

        settings
            .apply_python_executable(&handler, &project_dir, None, python_path.to_str().unwrap())
            .unwrap();

        let version = settings.python_version.unwrap();
        assert_eq!(version.major, 3);
        assert_eq!(version.minor, 10);
    }
}
