use std::borrow::Cow;

use parsa_python_cst::NodeIndex;
use vfs::FileIndex;

use crate::{
    database::{Database, Locality, Point, PointLink},
    file::PythonFile,
    inferred::Inferred,
    type_::AnyCause,
};

#[derive(Debug, Clone)]
pub(crate) enum LookupResult {
    // Locality is part of Inferred
    GotoName { name: PointLink, inf: Inferred },
    FileReference(FileIndex),
    UnknownName(Inferred),
    None,
}

impl LookupResult {
    pub fn any(cause: AnyCause) -> Self {
        Self::UnknownName(Inferred::new_any(cause))
    }

    pub fn is_some(&self) -> bool {
        !matches!(self, Self::None)
    }

    pub fn maybe_any(&self, db: &Database) -> Option<AnyCause> {
        self.maybe_inferred().and_then(|inf| inf.maybe_any(db))
    }

    pub fn into_maybe_inferred(self) -> Option<Inferred> {
        match self {
            Self::GotoName { inf, .. } | Self::UnknownName(inf) => Some(inf),
            Self::FileReference(f) => Some(Inferred::new_file_reference(f)),
            Self::None => None,
        }
    }

    pub fn maybe_inferred(&self) -> Option<Cow<'_, Inferred>> {
        match self {
            Self::GotoName { inf, .. } | Self::UnknownName(inf) => Some(Cow::Borrowed(inf)),
            Self::FileReference(f) => Some(Cow::Owned(Inferred::new_file_reference(*f))),
            Self::None => None,
        }
    }

    pub fn maybe_name(&self) -> Option<PointLink> {
        match self {
            Self::GotoName { name, .. } => Some(*name),
            _ => None,
        }
    }

    pub fn update_inferred(&mut self, new: Inferred) {
        match self {
            Self::GotoName { inf, .. } => *inf = new,
            _ => *self = Self::UnknownName(new),
        }
    }

    pub fn into_inferred(self) -> Inferred {
        self.into_maybe_inferred()
            .unwrap_or_else(|| Inferred::new_any(AnyCause::Todo))
    }

    pub fn save_name(self, file: &PythonFile, name_index: NodeIndex) -> Option<Inferred> {
        match &self {
            LookupResult::GotoName { name: link, .. } => {
                // TODO this is not correct, because there can be multiple runs, so setting
                // it here can be overwritten.
                file.points.set(
                    name_index,
                    Point::new_redirect(link.file, link.node_index, Locality::Todo),
                );
            }
            LookupResult::FileReference(file_index) => {
                file.points.set(
                    name_index,
                    Point::new_file_reference(*file_index, Locality::Todo),
                );
            }
            LookupResult::UnknownName(_) | LookupResult::None => (),
        };
        self.into_maybe_inferred()
    }

    pub fn and_then(self, c: impl FnOnce(Inferred) -> Option<Inferred>) -> Option<Self> {
        match self {
            Self::GotoName { name, inf } => c(inf).map(|inf| Self::GotoName { name, inf }),
            Self::UnknownName(inf) => c(inf).map(Self::UnknownName),
            // TODO is it ok that map does not include FileReference(_)?
            _ => Some(self),
        }
    }

    pub fn or_else(self, c: impl FnOnce() -> Self) -> Self {
        match self {
            Self::None => c(),
            _ => self,
        }
    }
}
