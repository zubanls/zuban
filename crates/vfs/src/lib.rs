// Some parts are copied from rust-analyzer

mod local_fs;

pub use local_fs::LocalFS;

/// Interface for reading and watching files.                                  
pub trait Vfs {
    /// Load the content of the given file, returning [`None`] if it does not  
    /// exists.                                                                
    fn read_and_watch_file(&mut self, path: &str) -> Option<String>;
}

/*
struct ZubanPart {
    initial_dir_walkers: Vec<WalkDir>,
    read_file: Box,
}

fn spawn(workspaces: &[&str]) -> (ZubanPart, NotifyPart) {}

enum WorkspaceChange {
    File(path),
}

enum Read {}

enum VFSUpdate {
    Vec<WorkspaceChange>,
    ProjectChanged,
}
*/
