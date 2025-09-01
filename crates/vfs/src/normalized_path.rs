use std::{
    borrow::Cow,
    path::{Component, PathBuf},
    sync::Arc,
};

use crate::AbsPath;

#[derive(Debug, PartialEq, Eq, Hash)]
#[repr(transparent)]
pub struct NormalizedPath(AbsPath);

impl NormalizedPath {
    pub(crate) fn normalize(path: &AbsPath) -> Cow<'_, Self> {
        if cfg!(target_os = "windows") && path.contains("/") {
            let mut p = AbsPath::new_arc(path.replace('/', "\\").into());
            if let Some(result) = normalize(path) {
                p = result;
            }
            return Cow::Owned(Self::new_arc(p));
        }
        if let Some(result) = normalize(path) {
            Cow::Owned(Self::new_arc(result))
        } else {
            Cow::Borrowed(Self::new(path))
        }
    }

    fn new(x: &AbsPath) -> &Self {
        // SAFETY: `NormalizedPath` is repr(transparent) over `str`
        unsafe { std::mem::transmute(x) }
    }

    pub(crate) fn new_arc(x: Arc<AbsPath>) -> Arc<Self> {
        unsafe { std::mem::transmute(x) }
    }

    pub fn arc_to_abs_path(p: Arc<Self>) -> Arc<AbsPath> {
        unsafe { std::mem::transmute(p) }
    }
}

impl ToOwned for NormalizedPath {
    type Owned = Arc<Self>;

    fn to_owned(&self) -> Self::Owned {
        self.into()
    }
}

impl From<&NormalizedPath> for Arc<NormalizedPath> {
    #[inline]
    fn from(s: &NormalizedPath) -> Arc<NormalizedPath> {
        let x: Arc<AbsPath> = s.0.into();
        unsafe { std::mem::transmute(x) }
    }
}

impl std::ops::Deref for NormalizedPath {
    type Target = AbsPath;

    fn deref(&self) -> &Self::Target {
        &self.0
    }
}

impl std::fmt::Display for NormalizedPath {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        self.0.fmt(f)
    }
}

fn normalize(path: &AbsPath) -> Option<Arc<AbsPath>> {
    let mut normalized = PathBuf::with_capacity(path.len());
    for comp in path.as_ref().components() {
        match comp {
            Component::CurDir => {} // Skip
            Component::ParentDir => {
                normalized.pop();
            }
            other => normalized.push(other.as_os_str()),
        }
    }
    let s = normalized.to_str().unwrap();
    if s.len() == path.len() {
        return None;
    }
    Some(AbsPath::new_arc(s.into()))
}

#[cfg(test)]
mod tests {
    use super::*;
    #[test]
    fn test_normalization() {
        let n = |p: &str| normalize(&AbsPath::new_arc(p.into())).map(|p| p.to_string());
        assert_eq!(n("/foo/./bar/../baz"), Some("/foo/baz".into()));
        assert_eq!(n("/foo/./bar"), Some("/foo/bar".into()));
        assert_eq!(n("/foo/../bar"), Some("/bar".into()));
        assert_eq!(n("/foo/./bar"), Some("/foo/bar".into()));

        assert_eq!(n("/foo/bar/baz"), None);
    }
}
