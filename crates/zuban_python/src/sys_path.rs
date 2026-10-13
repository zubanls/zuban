use std::{
    path::{Path, PathBuf},
    sync::Arc,
};

use vfs::{AbsPath, LocalFS, NormalizedPath, VfsHandler, WorkspaceKind};

use crate::{PythonVersion, Settings};

pub(crate) fn create_sys_path(
    handler: &dyn VfsHandler,
    settings: &Settings,
) -> Vec<(WorkspaceKind, Arc<NormalizedPath>)> {
    create_sys_path_with_file_access(FileAccess, handler, settings)
}

fn create_sys_path_with_file_access(
    file_access: impl TestableFileAccess,
    handler: &dyn VfsHandler,
    settings: &Settings,
) -> Vec<(WorkspaceKind, Arc<NormalizedPath>)> {
    let mut sys_path = vec![];

    sys_path.extend(
        settings
            .prepended_site_packages
            .iter()
            .map(|p| (WorkspaceKind::SitePackages, p.clone())),
    );

    let new_unchecked = |p: &str| handler.unchecked_normalized_path(handler.unchecked_abs_path(p));
    let lib_path = lib_path(file_access, settings);
    if let Some(path) = &lib_path {
        tracing::info!("Decided to use {path} as the Python lib folder");
        sys_path.push((WorkspaceKind::PythonStdLib, new_unchecked(&path)));
    } else {
        tracing::warn!("Did not find a Python lib folder (on Linux e.g. /usr/lib/python3.12)");
    }

    let version = settings.python_version_or_default();
    let mut add_site =
        |p: PathBuf| {
            sys_path.push((
                WorkspaceKind::SitePackages,
                new_unchecked(p.to_str().expect(
                    "Should never happen, because we only put together valid unicode paths",
                )),
            ))
        };
    let check_global_site_packages = if let Some(env) = &settings.environment {
        // We cannot use cannonicalize here, because the path of the exe is often a venv path
        // that is a symlink to the actual exectuable. We however want the relative paths to
        // the symlink. Therefore cannonicalize only after getting the first dir
        add_site(site_packages_path_from_env(file_access, env, version));
        add_editable_src_packages(file_access, handler, &mut sys_path, env);
        include_system_site_packages_in_pyvenv_cfg(file_access, env)
    } else {
        if let Some(lib_path) = &lib_path
            && settings.add_global_packages_default
        {
            let p = Path::new(lib_path).join("site-packages");
            if file_access.exists(&p).unwrap_or(false) {
                // This is not necessary on Ubuntu (and probably Debian), but the default in
                // site.py is that site-packages are added. Ubuntu probably patches this.
                tracing::info!("Looked up site-packages for {p:?} and added it to the sys path");
                add_site(p);
            } else {
                tracing::info!("Looked up site-packages for {p:?} but it doesn't exist");
            }
        }
        settings.add_global_packages_default
    };
    if check_global_site_packages {
        add_user_site_packages(file_access, version, |p| {
            sys_path.push((WorkspaceKind::SitePackages, new_unchecked(p)))
        });
        add_global_site_packages(file_access, lib_path, version, |p| {
            sys_path.push((WorkspaceKind::SitePackages, new_unchecked(p)))
        });
    }
    sys_path
}

fn site_packages_path_from_env(
    file_access: impl TestableFileAccess,
    environment: &AbsPath,
    version: PythonVersion,
) -> PathBuf {
    if cfg!(windows) {
        let direct_site_packages = environment.as_ref().join("site-packages");
        if file_access.exists(&direct_site_packages).unwrap_or(false) {
            return direct_site_packages;
        }
        // This is the more typical case, see also comments in finding typeshed path for Windows.
        environment.as_ref().join("Lib").join("site-packages")
    } else {
        let lib = environment.as_ref().join("lib");
        lookup_site_packages_with_version(file_access, &lib, version)
    }
}

fn lookup_site_packages_with_version(
    file_access: impl TestableFileAccess,
    lib: impl AsRef<Path>,
    version: PythonVersion,
) -> PathBuf {
    lookup_site_packages_with_version_detailed(
        file_access,
        lib.as_ref(),
        format!("python{}.{}", version.major, version.minor),
        "python",
        "site-packages",
    )
}

fn lookup_site_packages_with_version_detailed(
    file_access: impl TestableFileAccess,
    base: &Path,
    version_folder_name: String,
    starts_with: &str,
    end: &str,
) -> PathBuf {
    let expected_path = base.join(version_folder_name).join(end);

    if file_access.exists(&expected_path).unwrap_or(false) {
        return expected_path;
    }
    // Since the path we wanted doesn't exist, we fall back to trying to find a folder in the lib,
    // because we are probably not always using the correct PythonVersion.
    match file_access.read_dir(base) {
        Ok(dir) => {
            for path_in_dir in dir.flatten() {
                let n = path_in_dir.file_name();
                let b = n.as_encoded_bytes();
                if b.starts_with(starts_with.as_bytes()) {
                    return base.join(n).join(end);
                }
            }
        }
        Err(err) => {
            tracing::error!("Expected {base:?} to be a directory: {err}");
        }
    }
    expected_path
}

fn add_editable_src_packages(
    file_access: impl TestableFileAccess,
    handler: &dyn VfsHandler,
    sys_path: &mut Vec<(WorkspaceKind, Arc<NormalizedPath>)>,
    env: &NormalizedPath,
) {
    let Ok(entries) = file_access.read_dir(&env.as_ref().join("src")) else {
        return;
    };
    for entry in entries.flatten() {
        if let Some(path) = entry.path().to_str() {
            sys_path.push((
                WorkspaceKind::SitePackages,
                handler.normalize_rc_path(handler.unchecked_abs_path(path)),
            ))
        }
    }
}

fn lib_path(file_access: impl TestableFileAccess, settings: &Settings) -> Option<String> {
    let check = |path: String| {
        let os_path = Path::new(&path).join("os.py");
        match file_access.exists(&path) {
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
        let path_of_exe = match file_access.which(executable_name) {
            Ok(path_of_exe) => match file_access.canonicalize(&path_of_exe) {
                Ok(p) => {
                    tracing::debug!("which python3 (canonicalized): {p:?}");
                    p
                }
                Err(err) => {
                    tracing::warn!("Wanted to canonicalize {path_of_exe:?} but got error: {err:?}");
                    /*
                    fn iter_dir_paths_that_start_with<'a>(dir: &'a Path, starts_with: &'a str) -> impl Iterator<Item=PathBuf> + 'a {
                        dir.read_dir().ok().map(|iterator| {
                            iterator.filter_map(move |e| {
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
                match file_access.read_dir(&lib_path) {
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
                tracing::debug!("Found the following potential python base paths {found:?}");
                // Return the highest version path
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

pub(crate) fn typeshed_path_from_executable() -> Arc<NormalizedPath> {
    let mut executable = std::env::current_exe().expect(
        "Cannot access the path of the current executable, you need to provide \
                 a typeshed path in that case.",
    );

    // It seems on Mac the paths are not canonicalized, see https://github.com/zubanls/zubanls/issues/2
    if let Ok(canonicalized) = std::fs::canonicalize(&executable) {
        executable = canonicalized;
    }
    tracing::debug!("Trying to find typeshed path for executable {executable:?}");

    let result = typeshed_path_from_executable_part2(&executable);
    tracing::debug!("Found typeshed path: {:?}", &result);
    result
}

fn typeshed_path_from_executable_part2(executable: &Path) -> Arc<NormalizedPath> {
    const NEEDS_PARENTS: &str = "The executable is expected to be relative to the typeshed path";
    let env_folder = executable
        .parent()
        .expect(NEEDS_PARENTS)
        .parent()
        .expect(NEEDS_PARENTS);

    let maybe_has_zuban_in_path = |path: &Path| {
        let typeshed_path = path.join("zuban").join("third_party").join("typeshed");
        typeshed_path.exists().then(|| {
            LocalFS::without_watcher().normalized_path_from_current_dir(
                typeshed_path
                    .to_str()
                    .expect("Expected the typeshed path to be UTF-8"),
            )
        })
    };
    let maybe_has_zuban_detailed = |lib_path: &Path, site_packages_name: &str| {
        let typeshed_path = lib_path
            .join(site_packages_name)
            .join("zuban")
            .join("third_party")
            .join("typeshed");
        typeshed_path.exists().then(|| {
            LocalFS::without_watcher().normalized_path_from_current_dir(
                typeshed_path
                    .to_str()
                    .expect("Expected the typeshed path to be UTF-8"),
            )
        })
    };
    let maybe_has_zuban = |lib_path: &Path| maybe_has_zuban_detailed(lib_path, "site-packages");
    if cfg!(windows) {
        // Windows has two different formats. The first one is the "normal" one that is typically
        // encountered in venvs and system packages. The second one is encountered for example in
        // when installing the Windows app (and maybe with pip install --user?)
        if let Some(p) = maybe_has_zuban(&env_folder.join("Lib")) {
            return p;
        }
        if let Some(p) = maybe_has_zuban(env_folder) {
            return p;
        }
        // TODO uv simply copies the executable to ~/.local/bin/ and we do not know the actual venv
        // path anymore. I'm not sure what to do here other than hardcoding it.
        if let Some(user_home) =
            std::env::var_os("HOME").or_else(|| std::env::var_os("USERPROFILE"))
            && let Some(p) =
                maybe_has_zuban(&Path::new(&user_home).join("AppData/Roaming/uv/tools/zuban/Lib/"))
        {
            return p;
        }
    } else {
        // The lib folder typically contains a Python specific folder called "python3.8" or
        // python3.13", corresponding to the Python version. Here we try to find the package.
        let result = search_typeshed_dir_in_unix(env_folder.join("lib"), maybe_has_zuban);
        if let Ok(Some(result)) = result {
            return result;
        }
        if cfg!(target_os = "linux") {
            // On Fedora / Redhat based systems with 64-bit architectures, Zuban is installed
            // in the lib64 directory. We should look there as well.
            if let Ok(Some(found)) =
                search_typeshed_dir_in_unix(env_folder.join("lib64"), maybe_has_zuban)
            {
                return found;
            }
            // Debian uses dist-packages for globally installed packages.
            let result = search_typeshed_dir_in_unix(env_folder.join("lib"), |lib| {
                maybe_has_zuban_detailed(lib, "dist-packages")
            });
            if let Ok(Some(found)) = result {
                return found;
            }
        }
        if let Err(err) = result {
            // This can happen when you for example pip install -t ...
            if let Some(p) = maybe_has_zuban_in_path(env_folder) {
                return p;
            }
            panic!("{err}")
        }
    }
    // See comment above
    if let Some(p) = maybe_has_zuban_in_path(env_folder) {
        return p;
    }
    panic!("Did not find a typeshed folder in {env_folder:?}")
}

fn search_typeshed_dir_in_unix(
    lib_folder: PathBuf,
    maybe_has_zuban: impl Fn(&Path) -> Option<Arc<NormalizedPath>>,
) -> anyhow::Result<Option<Arc<NormalizedPath>>> {
    for folder in lib_folder.read_dir().map_err(|err| {
        anyhow::anyhow!(
            "The Python environment lib folder {lib_folder:?} should be readable ({err}).
                You might want to set ZUBAN_TYPESHED."
        )
    })? {
        let folder = folder.map_err(|err| {
            anyhow::anyhow!("The lib folder {lib_folder:?} should be readable ({err})")
        })?;
        let p = folder.path();
        if let Some(found) = maybe_has_zuban(&p) {
            return Ok(Some(found));
        }
    }
    Ok(None)
}

fn include_system_site_packages_in_pyvenv_cfg(
    file_access: impl TestableFileAccess,
    env: &NormalizedPath,
) -> bool {
    let path = env.as_ref().join("pyvenv.cfg");
    match file_access.read_to_string(&path) {
        Ok(content) => {
            for line in content.lines() {
                if let Some((key, value)) = line.split_once('=')
                    && key.trim() == "include-system-site-packages"
                {
                    return value.to_lowercase() == "true";
                }
            }
            tracing::warn!("Did not find an include-system-site-packages definition in {path:?}");
            true
        }
        Err(err) => {
            tracing::info!("Error while looking up {path:?}: {err}");
            false
        }
    }
}

fn add_user_site_packages(
    file_access: impl TestableFileAccess,
    version: PythonVersion,
    mut add: impl FnMut(&str),
) {
    if cfg!(windows) {
        if let Some(app_data) = std::env::var_os("APPDATA") {
            if let Some(app_data) = app_data.to_str() {
                let new = lookup_site_packages_with_version_detailed(
                    file_access,
                    &Path::new(app_data).join("Python"),
                    format!("Python{}{}", version.major, version.minor),
                    "Python",
                    "site-packages",
                );
                if let Some(new) = new.to_str() {
                    add(new)
                } else {
                    tracing::warn!("site-packages path not unicode: {new:?}");
                }
            } else {
                tracing::warn!("app_data not unicode: {app_data:?}");
            }
        } else {
            tracing::warn!("Did not find the environment variable APPDATA");
        }
    } else if let Some(home) = file_access.home_dir() {
        if cfg!(any(target_os = "macos", target_os = "ios")) {
            let base = home.join("Library").join("Python");
            let new = lookup_site_packages_with_version_detailed(
                file_access,
                &base,
                format!("{}.{}", version.major, version.minor),
                "python",
                "lib/python/site-packages",
            );
            if let Some(new) = new.to_str() {
                add(new)
            } else {
                tracing::warn!("site-packages path not unicode: {new:?}");
            }
        }
        if let Some(pkg) = lookup_site_packages_with_version(
            file_access,
            &home.join(".local").join("lib"),
            version,
        )
        .to_str()
        {
            add(pkg)
        }
    }
}

fn add_global_site_packages(
    file_access: impl TestableFileAccess,
    lib_path: Option<String>,
    version: PythonVersion,
    mut add: impl FnMut(&str),
) {
    if let Some(lib) = lib_path {
        let site_packages = if cfg!(windows) {
            // Windows has site-packages directly on
            Path::new(&lib).join("site-packages")
        } else {
            lookup_site_packages_with_version(file_access, lib, version)
        };
        match file_access.exists(&site_packages) {
            Ok(true) => {
                if let Some(site_packages) = site_packages.to_str() {
                    add(site_packages)
                } else {
                    tracing::info!("site-packages are not unicode: {site_packages:?}")
                }
            }
            Ok(false) => {}
            Err(err) => {
                tracing::info!("Failed while looking for global site packages: {err}")
            }
        }
    }

    if cfg!(target_os = "linux") {
        // This adds the paths for Debian-likes.
        let p = "/usr/lib/python3/dist-packages";
        if file_access.exists(&p).is_ok_and(|found| found) {
            add(p);
        }
        // TODO maybe add /usr/local/lib/python3.12/dist-packages, but it seems Ubuntu doesn't
        // really use it (at least for me).
    }
}

trait TestableFileAccess: Copy {
    fn exists(&self, path: &dyn AsRef<Path>) -> std::io::Result<bool>;
    fn home_dir(&self) -> Option<PathBuf>;
    fn which(&self, executable_name: &str) -> Result<PathBuf, which::Error>;
    fn read_to_string(&self, path: &dyn AsRef<Path>) -> std::io::Result<String>;
    fn canonicalize(&self, path: &PathBuf) -> std::io::Result<PathBuf>;
    fn read_dir(&self, path: &Path) -> std::io::Result<std::fs::ReadDir>;
}

#[derive(Copy, Clone)]
struct FileAccess;

impl TestableFileAccess for FileAccess {
    fn exists(&self, path: &dyn AsRef<Path>) -> std::io::Result<bool> {
        std::fs::exists(path)
    }

    fn home_dir(&self) -> Option<PathBuf> {
        dirs::home_dir()
    }

    fn which(&self, executable_name: &str) -> Result<PathBuf, which::Error> {
        which::which(executable_name)
    }

    fn read_to_string(&self, path: &dyn AsRef<Path>) -> std::io::Result<String> {
        std::fs::read_to_string(&path)
    }

    fn canonicalize(&self, path: &PathBuf) -> std::io::Result<PathBuf> {
        path.canonicalize()
    }

    fn read_dir(&self, path: &Path) -> std::io::Result<std::fs::ReadDir> {
        std::fs::read_dir(path)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[derive(Copy, Clone)]
    struct KnownFiles<'x> {
        files: &'x [&'x str],
        home_dir: bool,
    }

    impl TestableFileAccess for KnownFiles<'_> {
        fn exists(&self, path: &dyn AsRef<Path>) -> std::io::Result<bool> {
            Ok(self.files.iter().any(|p| Path::new(p) == path.as_ref()))
        }

        fn which(&self, executable_name: &str) -> Result<PathBuf, which::Error> {
            match executable_name {
                "python3" => Ok("/usr/bin/python3".into()),
                _ => unimplemented!("{executable_name}"),
            }
        }

        fn home_dir(&self) -> Option<PathBuf> {
            self.home_dir.then(|| "/home/myuser".into())
        }

        fn read_to_string(&self, _path: &dyn AsRef<Path>) -> std::io::Result<String> {
            unimplemented!()
        }

        fn canonicalize(&self, path: &PathBuf) -> std::io::Result<PathBuf> {
            Ok(path.clone())
        }

        fn read_dir(&self, path: &Path) -> std::io::Result<std::fs::ReadDir> {
            // TODO
            std::fs::read_dir(path)
        }
    }

    fn sys_path(files: &[&str], home_dir: bool) -> Vec<String> {
        create_sys_path_with_file_access(
            KnownFiles { files, home_dir },
            &LocalFS::without_watcher(),
            &Settings::default(),
        )
        .into_iter()
        .map(|(_, p)| p.to_string())
        .collect()
    }

    #[test]
    #[cfg(target_os = "linux")]
    fn test_sys_path_for_linux() {
        assert_eq!(
            sys_path(&[], false), // No homedir
            [] as [&str; 0]
        );
        assert_eq!(
            sys_path(&[], true), // homedir
            ["/home/myuser/.local/lib/python3.14/site-packages"]
        );

        assert_eq!(
            sys_path(&["/usr/lib/python3/dist-packages/"], false),
            ["/usr/lib/python3/dist-packages"]
        );
    }
}
