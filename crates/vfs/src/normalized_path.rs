use std::rc::Rc;

use crate::AbsPath;

#[derive(Debug, PartialEq, Eq, Hash)]
#[repr(transparent)]
pub struct NormalizedPath(AbsPath);

impl NormalizedPath {
    pub(crate) fn new(x: &AbsPath) -> &Self {
        // SAFETY: `NormalizedPath` is repr(transparent) over `str`
        unsafe { std::mem::transmute(x) }
    }

    pub(crate) fn new_rc(x: Rc<AbsPath>) -> Rc<Self> {
        unsafe { std::mem::transmute(x) }
    }

    pub fn rc_to_abs_path(p: Rc<NormalizedPath>) -> Rc<AbsPath> {
        unsafe { std::mem::transmute(p) }
    }
}

impl ToOwned for NormalizedPath {
    type Owned = Rc<NormalizedPath>;

    fn to_owned(&self) -> Self::Owned {
        self.into()
    }
}

impl From<&NormalizedPath> for Rc<NormalizedPath> {
    #[inline]
    fn from(s: &NormalizedPath) -> Rc<NormalizedPath> {
        let x: Rc<AbsPath> = s.0.into();
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
