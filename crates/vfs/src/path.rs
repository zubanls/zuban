use std::path::Path;

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

    pub(crate) fn new_boxed(x: Box<str>) -> Box<Self> {
        // SAFETY: `AbsPath` is repr(transparent) over `str`
        unsafe { std::mem::transmute(x) }
    }

    pub fn contains_sub_file(&self, path: &str) -> bool {
        Path::new(path).starts_with(Path::new(&self.0))
    }

    pub fn cloned_box(&self) -> Box<Self> {
        Self::new_boxed(self.0.into())
    }

    pub fn into_string(self: Box<AbsPath>) -> String {
        // SAFETY: `AbsPath` is repr(transparent) over `str`
        let value: Box<str> = unsafe { std::mem::transmute(self) };
        value.into_string()
    }
}

impl ToOwned for AbsPath {
    type Owned = Box<AbsPath>;

    fn to_owned(&self) -> Self::Owned {
        self.into()
    }
}

impl From<&AbsPath> for Box<AbsPath> {
    #[inline]
    fn from(s: &AbsPath) -> Box<AbsPath> {
        let x: Box<str> = s.0.into();
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
        &Path::new(&self.0)
    }
}

impl Clone for Box<AbsPath> {
    fn clone(&self) -> Self {
        AbsPath::new_boxed(self.as_ref().to_string().into())
    }
}

impl std::fmt::Display for AbsPath {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        self.0.fmt(f)
    }
}
