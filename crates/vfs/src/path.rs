use std::{path::Path, rc::Rc};

#[derive(Debug, PartialEq, Eq, Hash)]
#[repr(transparent)]
pub struct AbsPath(str);

impl AbsPath {
    /*
    pub(crate) fn new(x: &str) -> &Self {
        // SAFETY: `AbsPath` is repr(transparent) over `str`
        unsafe { std::mem::transmute(x) }
    }
    */

    pub(crate) fn new_rc(x: Rc<str>) -> Rc<Self> {
        // SAFETY: `AbsPath` is repr(transparent) over `str`
        unsafe { std::mem::transmute(x) }
    }

    pub fn contains_sub_file(&self, path: &str) -> bool {
        Path::new(path).starts_with(Path::new(&self.0))
    }
}

impl ToOwned for AbsPath {
    type Owned = Rc<AbsPath>;

    fn to_owned(&self) -> Self::Owned {
        self.into()
    }
}

impl From<&AbsPath> for Rc<AbsPath> {
    #[inline]
    fn from(s: &AbsPath) -> Rc<AbsPath> {
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
