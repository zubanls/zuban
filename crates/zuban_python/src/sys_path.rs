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

    let new_unchecked = |p: &str| handler.unchecked_normalized_path(handler.unchecked_abs_path(p));
    if let Some(path) = lib_path(settings) {
        tracing::info!("Decided to use {path} as the Python lib folder");
        sys_path.push(new_unchecked(&path));
    } else {
        tracing::warn!("Did not find a Python lib folder (on Linux e.g. /usr/lib/python3.12)");
    }

    if let Some(env) = &settings.environment {
        // We cannot use cannonicalize here, because the path of the exe is often a venv path
        // that is a symlink to the actual exectuable. We however want the relative paths to
        // the symlink. Therefore cannonicalize only after getting the first dir
        let p = site_packages_path_from_venv(env, settings.python_version_or_default());
        sys_path.push(new_unchecked(p.to_str().expect(
            "Should never happen, because we only put together valid unicode paths",
        )));
        add_editable_src_packages(handler, &mut sys_path, env);
    } else {
        // TODO use a real sys path
        //"../typeshed/stubs".into(),
        //"/home/<user>/.local/lib/python3.8/site-packages".into(),
    }
    // TODO maybe add these paths for Windows/Mac as well
    if cfg!(target_os = "linux") && settings.add_global_packages_default {
        // TODO maybe add /usr/local/lib/python3.12/dist-packages
        let p = "/usr/lib/python3/dist-packages";
        if std::fs::exists(p).is_ok_and(|found| found) {
            sys_path.push(new_unchecked(p));
        }
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

fn lib_path(settings: &Settings) -> Option<String> {
    let check = |path: String| {
        let os_path = Path::new(&path).join("os.py");
        match std::fs::exists(&path) {
            Ok(true) => {
                tracing::debug!("Found {os_path:?} -> choosing {path} as the library path");
                Some(path)
            }
            Ok(false) => {
                tracing::debug!(
                    "Tried to lookup {os_path:?} to find the library path but it does not exist"
                );
                None
            }
            Err(err) => {
                tracing::warn!(
                    "Got error while trying to find the library path {os_path:?}: {err:?}"
                );
                None
            }
        }
    };
    let check_path_buf = |path_buf: PathBuf| match path_buf.into_os_string().into_string() {
        Ok(s) => check(s),
        Err(err) => {
            tracing::error!("Python seems to be installed in a non-utf8 path: {err:?}");
            None
        }
    };
    let with_which = |executable_name| {
        let path_of_exe = match which::which(executable_name) {
            Ok(path_of_exe) => match path_of_exe.canonicalize() {
                Ok(p) => p,
                Err(err) => {
                    tracing::warn!("Wanted to canonicalize {path_of_exe:?} but got error: {err:?}");
                    /*
                    fn iter_dir_paths_that_start_with<'a>(dir: &'a Path, starts_with: &'a str) -> impl Iterator<Item=PathBuf> + 'a {
                        dbg!(dir.read_dir());
                        dir.read_dir().ok().map(|iterator| {
                            iterator.filter_map(move |e| {
                                dbg!(&e);
                                match e {
                                    Ok(entry) if entry.file_name().to_str()?.starts_with(starts_with) => {
                                        Some(entry.path().to_path_buf())
                                    }
                                    _ => None
                                }
                            })
                        }).into_iter().flatten()
                    }
                    // We currently check for these weird Python Apps on Windows, because it seems to be
                    // very hard to resolve the reparse points. Note that this feels extremely buggy and
                    // incomplete and should likely be replaced with a better solution.
                    // If you want to check the file details, use `fsutil reparsepoint`
                    for p in iter_dir_paths_that_start_with(&Path::new(r"C:\\Program Files\WindowsApps"), "PythonSoftwareFoundation.Python") {
                        tracing::debug!("Checking potential path {p:?}");
                        match p.join("Lib").into_os_string().into_string() {
                            Ok(s) => {
                                if let result @ Some(_) = check(s) {
                                    return result
                                }
                            }
                            Err(err) => {
                                tracing::error!("Python seems to be installed in a non-utf8 path: {err:?}");
                            }
                        }
                    }
                    */
                    path_of_exe
                }
            },
            Err(err) => {
                tracing::warn!(
                    "Got error while trying to run which on {executable_name:?}: {err:?}"
                );
                return None;
            }
        };
        // Python itself uses an algorithm where they check all parents for the lib folder.
        // Skip the first entry, because that's the executable itself.
        for parent in path_of_exe.ancestors().skip(1) {
            if cfg!(windows) {
                if let result @ Some(_) = check_path_buf(parent.join("Lib")) {
                    return result;
                }
            } else {
                let lib_path = parent.join("lib");
                let mut found = vec![];
                match std::fs::read_dir(&lib_path) {
                    Ok(list) => {
                        for entry in list {
                            match entry {
                                Ok(entry) => {
                                    if let Some(version) = entry
                                        .file_name()
                                        .to_str()
                                        .and_then(|s| s.strip_prefix("python3."))
                                        .and_then(|s| s.parse::<usize>().ok())
                                    {
                                        found.push((version, entry.path()));
                                    }
                                }
                                Err(err) => {
                                    tracing::warn!(
                                        "Wanted to list lib dir {lib_path:?}, but got: {err:?}",
                                    );
                                }
                            }
                        }
                    }
                    Err(err) => {
                        tracing::debug!("Wanted to list lib dir {lib_path:?}, but got: {err:?}");
                    }
                }
                found.sort();
                for (_version, in_path) in found.into_iter().rev() {
                    if let result @ Some(_) = check_path_buf(in_path) {
                        return result;
                    }
                }
            }
        }
        tracing::info!("Did not find a parent in {path_of_exe:?} that contains a lib folder");
        None
    };
    if cfg!(windows) {
        // Typically paths like: C:\Users\<you>\AppData\Local\Programs\Python\Python312\Lib\
        with_which("python3.exe").or_else(|| with_which("python.exe"))
    } else if cfg!(any(target_os = "macos", target_os = "ios")) {
        with_which("python3")
        // Mac depends on whether it's from python.org or Homebrew or other sources, e.g.:
        // /Library/Frameworks/Python.framework/Versions/3.12/lib/python3.12/
        //    or /usr/local/Cellar/python@3.12/.../Frameworks/.../lib/python3.12/
    } else {
        if let Some(version) = settings.python_version {
            let path = format!("/usr/lib/python{}.{}", version.major, version.minor);
            if let result @ Some(_) = check(path) {
                return result;
            } else {
                tracing::warn!("Got python version {:?}, but could not find", version);
            }
        }
        with_which("python3")
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
