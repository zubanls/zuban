use std::{path::Path, rc::Rc, sync::Arc};

#[derive(Debug, PartialEq, Eq, Hash)]
#[repr(transparent)]
pub struct AbsPath(str);

impl AbsPath {
    pub(crate) fn new(x: &str) -> &Self {
        // SAFETY: `AbsPath` is repr(transparent) over `str`
        unsafe { std::mem::transmute(x) }
    }

    pub(crate) fn new_arc(x: Arc<str>) -> Arc<Self> {
        // SAFETY: `AbsPath` is repr(transparent) over `str`
        unsafe { std::mem::transmute(x) }
    }

    pub fn contains_sub_file(&self, path: &Self) -> bool {
        let path: &Path = path.as_ref();
        let base: &Path = self.as_ref();
        path.starts_with(base)
    }
}

impl ToOwned for AbsPath {
    type Owned = Arc<AbsPath>;

    fn to_owned(&self) -> Self::Owned {
        self.into()
    }
}

impl From<&AbsPath> for Arc<AbsPath> {
    #[inline]
    fn from(s: &AbsPath) -> Arc<AbsPath> {
        let x: Rc<str> = s.0.into();
        unsafe { std::mem::transmute(x) }
    }
}

impl std::ops::Deref for AbsPath {
    type Target = str;

    fn deref(&self) -> &Self::Target {
        &self.0
    }
}

impl AsRef<Path> for AbsPath {
    fn as_ref(&self) -> &Path {
        Path::new(&self.0)
    }
}

impl std::fmt::Display for AbsPath {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        self.0.fmt(f)
    }
}
