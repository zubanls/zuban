use crate::{AbsPath, VfsHandler};

#[derive(Clone, Hash, PartialEq, Eq, Debug)]
pub struct GlobAbsPath {
    pattern: glob::Pattern,
}

impl GlobAbsPath {
    pub fn new(vfs: &dyn VfsHandler, current_dir: &AbsPath, path: &str) -> anyhow::Result<Self> {
        let p = vfs.normalize_rc_path(vfs.absolute_path(current_dir, path));
        let pattern = glob::Pattern::new(&p)?;
        Ok(Self { pattern })
    }

    pub fn matches(&self, vfs: &dyn VfsHandler, path: &AbsPath) -> bool {
        // TODO this does not correctly use VFS's separator
        self.pattern.matches_with(
            path,
            glob::MatchOptions {
                case_sensitive: vfs.is_case_sensitive(),
                require_literal_separator: true,
                ..Default::default()
            },
        )
    }

    pub fn maybe_simple_path(&self) -> Option<&str> {
        let original = self.pattern.as_str();
        (!original.contains(['?', '[', ']', '*'])).then_some(original)
    }

    pub fn as_str(&self) -> &str {
        self.pattern.as_str()
    }
}
