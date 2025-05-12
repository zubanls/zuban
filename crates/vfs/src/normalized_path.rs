use crate::AbsPath;

#[derive(Debug, PartialEq, Eq, Hash)]
#[repr(transparent)]
pub struct NormalizedPath(AbsPath);

impl NormalizedPath {
    pub(crate) fn new(x: &AbsPath) -> &Self {
        // SAFETY: `NormalizedPath` is repr(transparent) over `str`
        unsafe { std::mem::transmute(x) }
    }

    pub(crate) fn new_boxed(x: Box<AbsPath>) -> Box<Self> {
        unsafe { std::mem::transmute(x) }
    }
}

impl ToOwned for NormalizedPath {
    type Owned = Box<NormalizedPath>;

    fn to_owned(&self) -> Self::Owned {
        self.into()
    }
}

impl From<&NormalizedPath> for Box<NormalizedPath> {
    #[inline]
    fn from(s: &NormalizedPath) -> Box<NormalizedPath> {
        let x: Box<AbsPath> = s.0.into();
        unsafe { std::mem::transmute(x) }
    }
}

impl std::ops::Deref for NormalizedPath {
    type Target = AbsPath;

    fn deref(&self) -> &Self::Target {
        &self.0
    }
}

impl Clone for Box<NormalizedPath> {
    fn clone(&self) -> Self {
        NormalizedPath::new_boxed(self.0.cloned_box())
    }
}

impl std::fmt::Display for NormalizedPath {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        self.0.fmt(f)
    }
}
