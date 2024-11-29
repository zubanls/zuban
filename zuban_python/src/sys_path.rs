use std::path::{Path, PathBuf};

pub(crate) fn create_sys_path(python_executable: Option<&str>) -> Vec<Box<str>> {
    let mut sys_path = vec![];
    if let Some(exe) = python_executable {
        // We cannot use cannonicalize here, because the path of the exe is often a venv path
        // that is a symlink to the actual exectuable. We however want the relative paths to
        // the symlink. Therefore cannonicalize only after getting the first dir
        let p = site_packages_path_from_venv(exe);
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
    sys_path.push("/home/dave/source/rust/zuban/typeshed/stdlib".into());
    sys_path.push("/home/dave/source/rust/zuban/typeshed/stubs/mypy-extensions".into());
    sys_path
}

fn site_packages_path_from_venv(executable: &str) -> PathBuf {
    const ERR: &str = "Expected a custom executable to be at least two directories deep";
    Path::new(executable)
        .parent()
        .expect(ERR)
        .canonicalize()
        .expect("Expected chdir to be possible with a custom python executable")
        .parent()
        .expect(ERR)
        .join("lib")
        .join("python3.12")
        .join("site-packages")
}
