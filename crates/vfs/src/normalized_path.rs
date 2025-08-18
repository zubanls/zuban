use std::sync::Arc;

use crate::AbsPath;

#[derive(Debug, PartialEq, Eq, Hash)]
#[repr(transparent)]
pub struct NormalizedPath(AbsPath);

impl NormalizedPath {
    pub(crate) fn new(x: &AbsPath) -> &Self {
        // SAFETY: `NormalizedPath` is repr(transparent) over `str`
        unsafe { std::mem::transmute(x) }
    }

    pub(crate) fn new_arc(x: Arc<AbsPath>) -> Arc<Self> {
        unsafe { std::mem::transmute(x) }
    }

    pub fn arc_to_abs_path(p: Arc<NormalizedPath>) -> Arc<AbsPath> {
        unsafe { std::mem::transmute(p) }
    }
}

impl ToOwned for NormalizedPath {
    type Owned = Arc<NormalizedPath>;

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
