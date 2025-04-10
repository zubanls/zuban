use crate::{AbsPath, VfsHandler};

#[derive(Clone, Hash, PartialEq, Eq, Debug)]
pub struct GlobAbsPath {
    pattern: glob::Pattern,
}

impl GlobAbsPath {
    pub fn new(
        vfs: &dyn VfsHandler,
        current_dir: &AbsPath,
        mut path: String,
    ) -> anyhow::Result<Self> {
        if !path.ends_with(".py") {
            // TODO It feels very wrong to just add an arbitrary match for directories, but we have
            // no other solution for now, otherwise only a bare directory is matched and not the
            // file itself.
            if !path.ends_with(vfs.separator()) {
                path.push(vfs.separator());
            }
            path.push_str("**");
        }
        let abspath = vfs.absolute_path(current_dir, path);
        let pattern = glob::Pattern::new(&abspath)?;
        Ok(Self { pattern })
    }

    pub fn matches(&self, vfs: &dyn VfsHandler, path: &AbsPath) -> bool {
        // TODO this does not correctly use VFS's separator
        self.pattern.matches_with(
            &path,
            glob::MatchOptions {
                case_sensitive: vfs.is_case_sensitive(),
                require_literal_separator: true,
                ..Default::default()
            },
        )
    }

    pub fn as_str(&self) -> &str {
        self.pattern.as_str()
    }
}
