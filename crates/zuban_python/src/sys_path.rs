use std::{
    ffi::OsString,
    path::{Path, PathBuf},
    sync::Arc,
};

use vfs::{AbsPath, NormalizedPath, VfsHandler, WorkspaceKind};

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

    let mut version = settings.python_version;
    let check_global_site_packages = if let Some(env) = &settings.environment {
        let infos = pyvenv_cfg_infos(file_access, env);
        if version.is_none() {
            version = infos.version
        }
        infos.include_system_site_packages
    } else {
        settings.add_global_packages_default
    };

    let lib_path = lib_path(file_access, version);
    if let Some(path) = &lib_path {
        tracing::info!("Decided to use {path} as the Python lib folder");
        sys_path.push((WorkspaceKind::PythonStdLib, new_unchecked(&path)));
    } else {
        tracing::warn!("Did not find a Python lib folder (on Linux e.g. /usr/lib/python3.12)");
    }

    let version = version.unwrap_or_else(|| settings.python_version_or_default());
    let mut add_site =
        |p: PathBuf| {
            sys_path.push((
                WorkspaceKind::SitePackages,
                new_unchecked(p.to_str().expect(
                    "Should never happen, because we only put together valid unicode paths",
                )),
            ))
        };
    if let Some(env) = &settings.environment {
        // We cannot use cannonicalize here, because the path of the exe is often a venv path
        // that is a symlink to the actual exectuable. We however want the relative paths to
        // the symlink. Therefore cannonicalize only after getting the first dir
        add_site(site_packages_path_from_env(file_access, env, version));
        add_editable_src_packages(file_access, handler, &mut sys_path, env);
    }
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

fn lib_path(
    file_access: impl TestableFileAccess,
    version: Option<PythonVersion>,
) -> Option<String> {
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
        if let Some(version) = version {
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

#[derive(Default)]
struct PyvenvInfos {
    include_system_site_packages: bool,
    version: Option<PythonVersion>,
}

fn pyvenv_cfg_infos(file_access: impl TestableFileAccess, env: &NormalizedPath) -> PyvenvInfos {
    let path = env.as_ref().join("pyvenv.cfg");
    match file_access.read_to_string(&path) {
        Ok(content) => {
            let mut infos = PyvenvInfos::default();
            let mut had_include_system_site_packages = false;
            for line in content.lines() {
                if let Some((key, value)) = line.split_once('=') {
                    match key.trim() {
                        "include-system-site-packages" => {
                            had_include_system_site_packages = true;
                            infos.include_system_site_packages =
                                value.to_lowercase().trim() == "true";
                        }
                        "version" => {
                            infos.version = value.trim().parse().ok();
                        }
                        _ => (),
                    }
                }
            }
            if !had_include_system_site_packages {
                tracing::warn!(
                    "Did not find an include-system-site-packages definition in {path:?}"
                );
                // Since this should always be available we fall back to the more comfortable
                // setting for users.
                infos.include_system_site_packages = true;
            }
            infos
        }
        Err(err) => {
            tracing::info!("Error while looking up {path:?}: {err}");
            PyvenvInfos::default()
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
    _version: PythonVersion,
    mut add: impl FnMut(&str),
) {
    let mut maybe_add = |site_packages: &Path| match file_access.exists(&site_packages) {
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
    };
    if let Some(lib) = lib_path {
        let site_packages = Path::new(&lib).join("site-packages");
        if cfg!(target_os = "linux")
            && let Some(suffix) = site_packages.strip_prefix("/usr/lib/").ok()
            && let Some(suffix) = suffix.to_str()
        {
            // Fedora patches site.py and adds /usr/local as an additional prefix:
            // https://src.fedoraproject.org/rpms/python3.13/blob/a93ec22eafc24bef97cc352b2be90bf7d3c136e6/f/00251-change-user-install-location.patch
            let usr_local = PathBuf::from(format!("/usr/local/lib/{suffix}"));
            maybe_add(&usr_local);
            // Ubuntu uses the dist-packages name instead of site-packages
            maybe_add(&usr_local.parent().unwrap().join("dist-packages"));
        }

        maybe_add(&site_packages)
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

enum ReadDir {
    Std(std::fs::ReadDir),
    #[allow(dead_code)] //  This is not actually dead code, it's just used in testing
    Testable(std::vec::IntoIter<DirEntry>),
}

impl Iterator for ReadDir {
    type Item = std::io::Result<DirEntry>;

    fn next(&mut self) -> Option<Self::Item> {
        match self {
            ReadDir::Std(read_dir) => Some(read_dir.next()?.map(|d| DirEntry::Std(d))),
            ReadDir::Testable(entries) => entries.next().map(|e| Ok(e)),
        }
    }
}

enum DirEntry {
    Std(std::fs::DirEntry),
    #[allow(dead_code)] //  This is not actually dead code, it's just used in testing
    Testable {
        name: String,
        path: String,
    },
}

impl DirEntry {
    fn file_name(&self) -> OsString {
        match self {
            Self::Std(entry) => entry.file_name(),
            Self::Testable { name, .. } => name.into(),
        }
    }

    fn path(&self) -> PathBuf {
        match self {
            Self::Std(entry) => entry.path(),
            Self::Testable { path, .. } => path.into(),
        }
    }
}

trait TestableFileAccess: Copy {
    fn exists(&self, path: &dyn AsRef<Path>) -> std::io::Result<bool>;
    fn home_dir(&self) -> Option<PathBuf>;
    fn which(&self, executable_name: &str) -> Result<PathBuf, which::Error>;
    fn read_to_string(&self, path: &dyn AsRef<Path>) -> std::io::Result<String>;
    fn canonicalize(&self, path: &PathBuf) -> std::io::Result<PathBuf>;
    fn read_dir(&self, path: &Path) -> std::io::Result<ReadDir>;
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

    fn read_dir(&self, path: &Path) -> std::io::Result<ReadDir> {
        std::fs::read_dir(path).map(|r| ReadDir::Std(r))
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    struct DirOrFile<'x> {
        path: &'x str,
        kind: DirOrFileKind<'x>,
    }
    enum DirOrFileKind<'x> {
        Dir,
        File(&'x str),
    }

    #[derive(Copy, Clone)]
    struct KnownFiles<'x> {
        // Files are a list of dirs/files that exist. Files also imply that the directories below
        // them exist.
        files_or_dirs: &'x [DirOrFile<'x>],
        home_dir: bool,
    }

    impl TestableFileAccess for KnownFiles<'_> {
        fn exists(&self, path: &dyn AsRef<Path>) -> std::io::Result<bool> {
            Ok(self
                .files_or_dirs
                .iter()
                .any(|p| Path::new(p.path).starts_with(path.as_ref())))
        }

        fn which(&self, executable_name: &str) -> Result<PathBuf, which::Error> {
            Ok(match executable_name {
                "python3.exe" => r"C:\Program Files\Python312\python.exe",
                "python3" => "/usr/bin/python3",
                _ => unimplemented!("{executable_name}"),
            }
            .into())
        }

        fn home_dir(&self) -> Option<PathBuf> {
            self.home_dir.then(|| "/home/myuser".into())
        }

        fn read_to_string(&self, path: &dyn AsRef<Path>) -> std::io::Result<String> {
            if let Some(content) = self.files_or_dirs.iter().find_map(|f| {
                if f.path != path.as_ref() {
                    return None;
                }
                match &f.kind {
                    DirOrFileKind::Dir => None,
                    DirOrFileKind::File(content) => Some(content),
                }
            }) {
                Ok(content.to_string())
            } else {
                Err(std::io::Error::new(
                    std::io::ErrorKind::NotFound,
                    "not found file (from tests)",
                ))
            }
        }

        fn canonicalize(&self, path: &PathBuf) -> std::io::Result<PathBuf> {
            Ok(path.clone())
        }

        fn read_dir(&self, path: &Path) -> std::io::Result<ReadDir> {
            let mut had_entries = false;
            let found: Vec<DirEntry> = self
                .files_or_dirs
                .iter()
                .filter_map(|file_or_dir| {
                    let potential_entry = Path::new(file_or_dir.path);
                    let found = potential_entry.strip_prefix(path).ok()?;
                    had_entries = true;

                    let name = found.iter().next()?;
                    Some(DirEntry::Testable {
                        path: path.join(name).to_str().unwrap().to_string(),
                        name: name.to_str().unwrap().to_string(),
                    })
                })
                .collect();
            if had_entries {
                Ok(ReadDir::Testable(found.into_iter()))
            } else {
                Err(std::io::Error::new(
                    std::io::ErrorKind::NotFound,
                    "not found dir (from tests)",
                ))
            }
        }
    }

    fn sys_path_for_dirs(dirs: &[&str], home_dir: bool) -> Vec<String> {
        sys_path(None, dirs, &[], home_dir)
    }

    fn sys_path(
        environment: Option<&str>,
        dirs: &[&str],
        files: &[(&str, &str)],
        home_dir: bool,
    ) -> Vec<String> {
        let files_or_dirs: Vec<_> = dirs
            .iter()
            .map(|path| DirOrFile {
                path,
                kind: DirOrFileKind::Dir,
            })
            .chain(files.iter().map(|(path, content)| DirOrFile {
                path,
                kind: DirOrFileKind::File(content),
            }))
            .collect();
        let local_fs = vfs::LocalFS::without_watcher();
        create_sys_path_with_file_access(
            KnownFiles {
                files_or_dirs: &files_or_dirs,
                home_dir,
            },
            &local_fs,
            &Settings {
                environment: environment.map(|env| local_fs.normalize_unchecked_abs_path(env)),
                ..Settings::default()
            },
        )
        .into_iter()
        .map(|(_, p)| p.to_string())
        .collect()
    }

    #[test]
    #[cfg(target_os = "linux")]
    fn test_homedir_sys_path_for_linux() {
        assert_eq!(
            sys_path_for_dirs(&[], false), // No homedir
            [] as [&str; 0]
        );
        assert_eq!(
            sys_path_for_dirs(&[], true), // homedir
            ["/home/myuser/.local/lib/python3.14/site-packages"]
        );
    }

    #[test]
    #[cfg(target_os = "linux")]
    fn test_different_versions_for_linux() {
        assert_eq!(
            sys_path_for_dirs(&["/usr/lib/python3.14/site-packages/"], false),
            ["/usr/lib/python3.14", "/usr/lib/python3.14/site-packages"]
        );
        assert_eq!(
            sys_path_for_dirs(&["/usr/lib/python3.12/site-packages/"], false),
            ["/usr/lib/python3.12", "/usr/lib/python3.12/site-packages"]
        );
        assert_eq!(
            sys_path_for_dirs(&["/usr/lib/python3.12/", "/usr/lib/python3.14/"], false),
            ["/usr/lib/python3.14"]
        );
        assert_eq!(
            sys_path_for_dirs(
                &[
                    "/usr/lib/python3.14/site-packages",
                    "/usr/lib/python3.13/site-packages"
                ],
                false
            ),
            ["/usr/lib/python3.14", "/usr/lib/python3.14/site-packages",]
        );
    }

    #[test]
    #[cfg(target_os = "linux")]
    fn test_debian_like() {
        assert_eq!(
            sys_path_for_dirs(
                &[
                    "/usr/lib/python3.14/",
                    "/usr/lib/python3/dist-packages/",
                    "/usr/local/lib/python3.12/dist-packages/",
                ],
                true
            ),
            [
                "/usr/lib/python3.14",
                "/home/myuser/.local/lib/python3.14/site-packages",
                "/usr/lib/python3/dist-packages",
            ]
        );
        assert_eq!(
            sys_path_for_dirs(
                &[
                    "/usr/lib/python3.13/",
                    "/usr/lib/python3/dist-packages/",
                    "/usr/local/lib/python3.13/dist-packages/",
                    "/usr/local/lib/python3.14/dist-packages/",
                ],
                false,
            ),
            [
                "/usr/lib/python3.13",
                "/usr/local/lib/python3.13/dist-packages",
                "/usr/lib/python3/dist-packages",
            ]
        );
    }

    #[test]
    #[cfg(target_os = "linux")]
    fn test_fedora_like() {
        // From GH #612
        assert_eq!(
            sys_path_for_dirs(
                &[
                    "/usr/lib/python3.14/site-packages/",
                    "/usr/local/lib/python3.14/site-packages/"
                ],
                false
            ),
            [
                "/usr/lib/python3.14",
                "/usr/local/lib/python3.14/site-packages",
                "/usr/lib/python3.14/site-packages",
            ]
        );
        assert_eq!(
            sys_path_for_dirs(
                &[
                    "/usr/lib/python3.13/site-packages/",
                    "/usr/local/lib/python3.13/site-packages/",
                    "/usr/local/lib/python3.14/site-packages/",
                ],
                false
            ),
            [
                "/usr/lib/python3.13",
                "/usr/local/lib/python3.13/site-packages",
                "/usr/lib/python3.13/site-packages",
            ]
        );
        assert_eq!(
            sys_path_for_dirs(
                &[
                    "/usr/lib/python3.13/site-packages/",
                    "/usr/local/lib/python3.14/site-packages/",
                ],
                false
            ),
            ["/usr/lib/python3.13", "/usr/lib/python3.13/site-packages"]
        );
    }

    #[test]
    #[cfg(target_os = "linux")]
    fn test_venv_path_on_linux() {
        assert_eq!(
            sys_path(
                Some("/home/proj/venv"),
                &["/usr/lib/python3.13/site-packages"],
                &[("/home/proj/venv/pyvenv.cfg", "")],
                false
            ),
            [
                // It feels weird that the version mismatches here, but I kind of like this,
                // because the venv doesn't have a version so we have to guess. And if the version
                // is not available, it should fall back to whatever version there is around.
                "/usr/lib/python3.13",
                "/home/proj/venv/lib/python3.14/site-packages",
                // This is in here because include-system-site-packages is missing
                "/usr/lib/python3.13/site-packages",
            ]
        );

        assert_eq!(
            sys_path(
                Some("/home/proj/venv"),
                &[
                    "/usr/lib/python3.13/site-packages/",
                    "/usr/lib/python3.12/site-packages/",
                    "/home/proj/venv/lib/python3.13/site-packages/",
                ],
                &[(
                    "/home/proj/venv/pyvenv.cfg",
                    "include-system-site-packages = true"
                )],
                false
            ),
            [
                "/usr/lib/python3.13",
                "/home/proj/venv/lib/python3.13/site-packages",
                "/usr/lib/python3.13/site-packages",
            ]
        );

        assert_eq!(
            sys_path(
                Some("/home/proj/venv"),
                &[
                    "/usr/lib/python3.13/",
                    "/usr/lib/python3.12/",
                    "/home/proj/venv/lib/python3.13/site-packages/"
                ],
                &[(
                    "/home/proj/venv/pyvenv.cfg",
                    "include-system-site-packages = false\nversion_info = 3.13.0"
                )],
                false
            ),
            [
                "/usr/lib/python3.13",
                "/home/proj/venv/lib/python3.13/site-packages",
            ]
        );

        assert_eq!(
            sys_path(
                Some("/home/proj/venv"),
                &["/usr/lib/python3.13/", "/usr/lib/python3.12/"],
                &[(
                    "/home/proj/venv/pyvenv.cfg",
                    "include-system-site-packages = true\nversion_info = 3.12.3"
                )],
                false
            ),
            [
                "/usr/lib/python3.13",
                "/home/proj/venv/lib/python3.14/site-packages",
            ]
        );
    }

    #[test]
    #[cfg(windows)]
    fn test_venv_path_on_windows() {
        assert_eq!(
            sys_path(
                Some(r"C:\Users\myuser\proj\venv"),
                &[r"C:\Program Files\Python312\Lib\site-packages\"],
                &[(
                    r"C:\Users\myuser\proj\venv\pyvenv.cfg",
                    "include-system-site-packages = true\nversion_info = 3.12.3"
                )],
                false
            ),
            [
                r"C:\Program Files\Python312\Lib",
                r"C:\Users\myuser\proj\venv\Lib\site-packages",
                r"C:\Program Files\Python312\Lib\site-packages",
            ]
        );
    }
}
