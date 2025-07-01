use std::{
    path::{Path, PathBuf},
    rc::Rc,
};

use vfs::{AbsPath, LocalFS, NormalizedPath, VfsHandler};

use crate::{PythonVersion, Settings};

pub(crate) fn create_sys_path(
    handler: &dyn VfsHandler,
    settings: &Settings,
) -> Vec<Rc<NormalizedPath>> {
    let mut sys_path = vec![];

    sys_path.extend(settings.prepended_site_packages.iter().cloned());

    if let Some(env) = &settings.environment {
        // We cannot use cannonicalize here, because the path of the exe is often a venv path
        // that is a symlink to the actual exectuable. We however want the relative paths to
        // the symlink. Therefore cannonicalize only after getting the first dir
        let p = site_packages_path_from_venv(env, settings.python_version);
        sys_path.push(handler.unchecked_normalized_path(
            handler.unchecked_abs_path(
                p.to_str().expect(
                    "Should never happen, because we only put together valid unicode paths",
                ),
            ),
        ));
        add_editable_src_packages(handler, &mut sys_path, env);
    } else {
        // TODO use a real sys path
        //"../typeshed/stubs".into(),
        //"/usr/lib/python3/dist-packages".into(),
        //"/usr/local/lib/python3.8/dist-packages/pip-20.0.2-py3.8.egg".into(),
        //"/usr/lib/python3.8".into(),
        //"/home/<user>/.local/lib/python3.8/site-packages".into(),
        //"/usr/local/lib/python3.8/dist-packages".into(),
    }
    sys_path
}

fn site_packages_path_from_venv(environment: &AbsPath, version: PythonVersion) -> PathBuf {
    if cfg!(windows) {
        let direct_site_packages = environment.as_ref().join("site-packages");
        if direct_site_packages.exists() {
            return direct_site_packages;
        }
        // This is the more typical case, see also comments in finding typeshed path for Windows.
        environment.as_ref().join("Lib").join("site-packages")
    } else {
        let lib = environment.as_ref().join("lib");

        let expected_path = lib
            .join(format!("python{}.{}", version.major, version.minor))
            .join("site-packages");

        if expected_path.exists() {
            return expected_path;
        }
        // Since the path we wanted doesn't exist, we fall back to trying to find a folder in the lib,
        // because we are probably not always using the correct PythonVersion.
        match lib.read_dir() {
            Ok(dir) => {
                for path_in_dir in dir.flatten() {
                    let n = path_in_dir.file_name();
                    if n.as_encoded_bytes().starts_with(b"python") {
                        return lib.join(n).join("site-packages");
                    }
                }
            }
            Err(err) => {
                tracing::error!("Expected {lib:?} to be a directory: {err}");
            }
        }
        expected_path
    }
}

fn add_editable_src_packages(
    handler: &dyn VfsHandler,
    sys_path: &mut Vec<Rc<NormalizedPath>>,
    env: &NormalizedPath,
) {
    let Ok(entries) = env.as_ref().join("src").read_dir() else {
        return;
    };
    for entry in entries {
        if let Ok(entry) = entry {
            if let Some(path) = entry.path().to_str() {
                sys_path.push(handler.normalize_rc_path(handler.unchecked_abs_path(path)))
            }
        }
    }
}

pub(crate) fn typeshed_path_from_executable() -> Rc<NormalizedPath> {
    let mut executable = std::env::current_exe().expect(
        "Cannot access the path of the current executable, you need to provide \
                 a typeshed path in that case.",
    );

    // It seems on Mac the paths are not canonicalized, see https://github.com/zubanls/zubanls/issues/2
    if let Ok(canonicalized) = std::fs::canonicalize(&executable) {
        executable = canonicalized;
    }
    const NEEDS_PARENTS: &str = "The executable is expected to be relative to the typeshed path";
    let env_folder = executable
        .parent()
        .expect(NEEDS_PARENTS)
        .parent()
        .expect(NEEDS_PARENTS);

    let maybe_has_zuban = |lib_path: &Path| {
        let typeshed_path = lib_path
            .join("site-packages")
            .join("zuban")
            .join("typeshed");
        typeshed_path.exists().then(|| {
            LocalFS::without_watcher().normalized_path_from_current_dir(
                typeshed_path
                    .to_str()
                    .expect("Expected the typeshed path to be UTF-8"),
            )
        })
    };
    if cfg!(windows) {
        // Windows has two different formats. The first one is the "normal" one that is typically
        // encountered in venvs and system packages. The second one is encountered for example in
        // when installing the Windows app (and maybe with pip install --user?)
        if let Some(p) = maybe_has_zuban(&env_folder.join("Lib")) {
            return p;
        }
        if let Some(p) = maybe_has_zuban(&env_folder) {
            return p;
        }
    } else {
        let lib_folder = env_folder.join("lib");
        // The lib folder typically contains a Python specific folder called "python3.8" or
        // python3.13", corresponding to the Python version. Here we try to find the package.
        for folder in lib_folder.read_dir().unwrap_or_else(|err| {
            panic!(
                "The Python environment lib folder {lib_folder:?} should be readable ({err}).
                    You might want to set ZUBAN_TYPESHED."
            )
        }) {
            let folder = folder.unwrap_or_else(|err| {
                panic!("The lib folder {lib_folder:?} should be readable ({err})")
            });
            let p = folder.path();
            if let Some(found) = maybe_has_zuban(&p) {
                return found;
            }
        }
    }
    panic!("Did not find a typeshed folder in {env_folder:?}")
}
