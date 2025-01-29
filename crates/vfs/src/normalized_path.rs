use std::borrow::Cow;

#[derive(Debug, PartialEq, Eq, Hash)]
#[repr(transparent)]
pub struct NormalizedPath(str);

impl NormalizedPath {
    pub fn new(x: &str) -> Cow<Self> {
        // SAFETY: `NormalizedPath` is repr(transparent) over `str`
        Cow::Borrowed(unsafe { std::mem::transmute(x) })
    }

    pub fn new_boxed(x: Box<str>) -> Box<Self> {
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
        let x: Box<str> = s.0.into();
        unsafe { std::mem::transmute(x) }
    }
}

impl std::ops::Deref for NormalizedPath {
    type Target = str;

    fn deref(&self) -> &Self::Target {
        &self.0
    }
}

impl Clone for Box<NormalizedPath> {
    fn clone(&self) -> Self {
        NormalizedPath::new_boxed(self.as_ref().to_string().into())
    }
}

impl std::fmt::Display for NormalizedPath {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        self.0.fmt(f)
    }
}
