use std::path::{Path, PathBuf};

use crate::{PythonVersion, Settings};

pub(crate) fn create_sys_path(settings: &Settings) -> Vec<Box<str>> {
    let mut sys_path = vec![];

    // Theoretically according to PEP 561 (Distributing and Packaging Type Information), this
    // should be last, but for now this should be good enough.
    sys_path.push("/home/dave/source/rust/zuban/typeshed/stdlib".into());
    sys_path.push("/home/dave/source/rust/zuban/typeshed/stubs/mypy-extensions".into());

    if let Some(exe) = &settings.python_executable {
        // We cannot use cannonicalize here, because the path of the exe is often a venv path
        // that is a symlink to the actual exectuable. We however want the relative paths to
        // the symlink. Therefore cannonicalize only after getting the first dir
        let p = site_packages_path_from_venv(exe, settings.python_version);
        sys_path.push(
            p.into_os_string()
                .into_string()
                .expect("Should never happen, because we only put together valid unicode paths")
                .into(),
        );
    } else {
        // TODO use a real sys path
        //"../typeshed/stubs".into(),
        //"/usr/lib/python3/dist-packages".into(),
        //"/usr/local/lib/python3.8/dist-packages/pip-20.0.2-py3.8.egg".into(),
        //"/usr/lib/python3.8".into(),
        //"/home/dave/.local/lib/python3.8/site-packages".into(),
        //"/usr/local/lib/python3.8/dist-packages".into(),
    }
    sys_path
}

fn site_packages_path_from_venv(executable: &str, version: PythonVersion) -> PathBuf {
    const ERR: &str = "Expected a custom executable to be at least two directories deep";
    let lib = Path::new(executable)
        .parent()
        .expect(ERR)
        .canonicalize()
        .expect("Expected chdir to be possible with a custom python executable")
        .parent()
        .expect(ERR)
        .join("lib");

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
        Err(err) => panic!("Expected {lib:?} to be a directory: {err}"),
    }
    expected_path
}
