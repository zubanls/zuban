// Some parts are copied from rust-analyzer

mod local_fs;

use crossbeam_channel::Receiver;
pub use local_fs::LocalFS;

pub type NotifyEvent = notify::Result<notify::Event>;

/// Interface for reading and watching files.                                  
pub trait Vfs {
    /// Load the content of the given file, returning [`None`] if it does not  
    /// exists.                                                                
    fn read_and_watch_file(&self, path: &str) -> Option<String>;
    fn notify_receiver(&self) -> Option<&Receiver<NotifyEvent>>;
    fn walk_and_watch_dirs(&self, path: &str);
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
