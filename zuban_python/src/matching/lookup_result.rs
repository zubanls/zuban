use parsa_python_ast::Name;

use crate::database::{FileIndex, Locality, Point, PointLink};
use crate::file::PythonFile;
use crate::inference_state::InferenceState;
use crate::inferred::Inferred;

#[derive(Debug, Clone)]
pub enum LookupResult {
    // Locality is part of Inferred
    GotoName(PointLink, Inferred),
    FileReference(FileIndex),
    UnknownName(Inferred),
    None,
}

impl LookupResult {
    pub fn any() -> Self {
        Self::UnknownName(Inferred::new_any())
    }

    pub fn into_maybe_inferred(self) -> Option<Inferred> {
        // TODO is it ok that map does not include FileReference(_)? (probably not)
        match self {
            Self::GotoName(_, inf) | Self::UnknownName(inf) => Some(inf),
            Self::FileReference(f) => Some(Inferred::new_file_reference(f)),
            Self::None => None,
        }
    }

    pub fn into_inferred(self) -> Inferred {
        self.into_maybe_inferred()
            .unwrap_or_else(Inferred::new_unknown)
    }

    pub fn union(self, i_s: &InferenceState, other: Self) -> Self {
        match self.into_maybe_inferred() {
            Some(self_) => match other.into_maybe_inferred() {
                Some(other) => LookupResult::UnknownName(self_.union(i_s, other)),
                None => LookupResult::UnknownName(self_),
            },
            None => other,
        }
    }

    pub fn save_name(
        self,
        i_s: &InferenceState,
        file: &PythonFile,
        name: Name,
    ) -> Option<Inferred> {
        match &self {
            LookupResult::GotoName(link, inferred) => {
                // TODO this is not correct, because there can be multiple runs, so setting
                // it here can be overwritten.
                file.points.set(
                    name.index(),
                    Point::new_redirect(link.file, link.node_index, Locality::Todo),
                );
            }
            LookupResult::FileReference(file_index) => {
                file.points.set(
                    name.index(),
                    Point::new_file_reference(*file_index, Locality::Todo),
                );
            }
            LookupResult::UnknownName(_) | LookupResult::None => (),
        };
        self.into_maybe_inferred()
    }

    /*
     * TODO remove?
    fn map(self, c: impl FnOnce(Inferred) -> Inferred) -> Self {
        match self {
            Self::GotoName(link, inf) => Self::GotoName(link, c(inf)),
            Self::UnknownName(inf) => Self::UnknownName(c(inf)),
            // TODO is it ok that map does not include FileReference(_)?
            _ => self,
        }
    }
    */

    pub fn and_then(self, c: impl FnOnce(Inferred) -> Option<Inferred>) -> Option<Self> {
        match self {
            Self::GotoName(link, inf) => c(inf).map(|inf| Self::GotoName(link, inf)),
            Self::UnknownName(inf) => c(inf).map(Self::UnknownName),
            // TODO is it ok that map does not include FileReference(_)?
            _ => Some(self),
        }
    }
}
