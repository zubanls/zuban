use std::sync::Arc;
use vfs::{NormalizedPath, VfsHandler, WorkspaceKind};

pub(crate) fn create_sys_path(
    handler: &dyn VfsHandler,
    _settings: &crate::Settings,
) -> Vec<(WorkspaceKind, Arc<NormalizedPath>)> {
    vec![(
        WorkspaceKind::SitePackages,
        handler.normalize_unchecked_abs_path("/site-packages"),
    )]
}

pub(crate) fn typeshed_path_from_executable() -> Arc<NormalizedPath> {
    unimplemented!("not available in wasm")
}
