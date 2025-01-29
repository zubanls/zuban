use std::borrow::Cow;

#[derive(Debug, PartialEq, Eq, Hash)]
#[repr(transparent)]
pub struct NormalizedPath(str);

impl NormalizedPath {
    pub fn new(x: &str) -> Cow<Self> {
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
        // SAFETY: `NormalizedPath` is repr(transparent) over `str`
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
        todo!()
    }
}
