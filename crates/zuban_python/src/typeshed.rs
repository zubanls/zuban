use std::{
    path::{Path, PathBuf},
    sync::Arc,
};

use vfs::{LocalFS, NormalizedPath};

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
