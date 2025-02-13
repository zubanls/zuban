use std::{fmt::Display, path::Path};

#[derive(Clone, Hash, PartialEq, Eq, Debug)]
pub struct AbsPath {
    path: Box<str>,
}

impl AbsPath {
    pub(crate) fn new(path: String) -> Self {
        Self { path: path.into() }
    }

    pub fn contains_sub_file(&self, path: &str) -> bool {
        Path::new(path).starts_with(Path::new(&*self.path))
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
