use std::{fmt::Display, path::Path};

use crate::VfsHandler;

#[derive(Clone, Hash, PartialEq, Eq, Debug)]
pub struct AbsPath {
    path: Box<str>,
}

impl AbsPath {
    pub fn new_unchecked(vfs: &dyn VfsHandler, mut path: String) -> Self {
        if let Some(new_root_path) = vfs.strip_separator_suffix(&path.as_str()) {
            path.truncate(new_root_path.len());
        }
        Self::new(path)
    }

    fn new(path: String) -> Self {
        Self { path: path.into() }
    }

    pub fn from_current_dir_and_path(
        vfs: &dyn VfsHandler,
        _current_dir: &Self,
        path: String,
    ) -> Self {
        Self::new_unchecked(vfs, path)
    }

    pub fn is_sub_file(&self, path: &str) -> bool {
        Path::new(&*self.path).starts_with(Path::new(path))
    }

    pub fn join(&self, name: &str) -> Self {
        Self::new(
            Path::new(&*self.path)
                .join(name)
                .into_os_string()
                .into_string()
                .unwrap(),
        )
    }

    pub fn as_str(&self) -> &str {
        &self.path
    }
}

impl AsRef<Path> for AbsPath {
    fn as_ref(&self) -> &Path {
        &Path::new(&*self.path)
    }
}

impl Display for AbsPath {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.path)
    }
}
