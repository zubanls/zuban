#![allow(clippy::nonminimal_bool)] // I don't like this rule
#![allow(clippy::too_many_arguments)] // TODO For now this is easier, but probably enable again

mod arguments;
mod completion;
mod database;
mod diagnostics;
mod file;
mod format_data;
mod getitem;
mod imports;
mod inference;
mod inference_state;
mod inferred;
mod lines;
mod matching;
mod name;
mod node_ref;
mod params;
mod python_state;
mod select_files;
mod sys_path;
mod type_;
mod type_helpers;
mod utils;

use std::cell::OnceCell;

use completion::CompletionResolver;
pub use completion::{Completion, CompletionKind};
use inference::{GotoResolver, PositionalDocument};
use parsa_python_cst::{CodeIndex, GotoNode, Tree};
use vfs::{AbsPath, DirOrFile, FileIndex, LocalFS, PathWithScheme, VfsHandler};

use config::{ProjectOptions, PythonVersion, Settings, TypeCheckerFlags};
pub use database::Mode;
use database::{Database, PythonProject};
pub use diagnostics::Severity;
use file::{File, PythonFile};
use inference_state::InferenceState;
use inferred::Inferred;
pub use lines::PositionInfos;
use matching::invalidate_protocol_cache;
pub use name::{Name, SymbolKind, ValueName};

pub struct Project {
    db: Database,
}

impl Project {
    pub fn new(vfs: Box<dyn VfsHandler>, options: ProjectOptions, mode: Mode) -> Self {
        let db = Database::new(vfs, options, mode);
        Self { db }
    }

    pub fn from_recovery(
        vfs: Box<dyn VfsHandler>,
        options: ProjectOptions,
        recovery: PanicRecovery,
    ) -> Self {
        let db = Database::from_recovery(vfs, options, recovery.mode, recovery.vfs);
        Self { db }
    }

    pub fn without_watcher(options: ProjectOptions, mode: Mode) -> Self {
        let db = Database::new(Box::new(LocalFS::without_watcher()), options, mode);
        Self { db }
    }

    pub fn invalidate_path(&mut self, path: &AbsPath) {
        self.db.invalidate_path(path)
    }

    pub fn into_panic_recovery(self) -> PanicRecovery {
        PanicRecovery {
            vfs: self.db.vfs.into_panic_recovery(),
            mode: self.db.mode,
        }
    }

    pub fn search(&self, _string: &str, _all_scopes: bool) {}

    pub fn complete_search(&self, _string: &str, _all_scopes: bool) {}

    pub fn store_in_memory_file(&mut self, path: PathWithScheme, code: Box<str>) {
        self.db.store_in_memory_file(path, code);
    }

    pub fn code_of_in_memory_file(&mut self, path: &PathWithScheme) -> Option<&str> {
        let file_index = self.db.vfs.in_memory_file(path)?;
        Some(self.db.loaded_python_file(file_index).code())
    }

    pub fn delete_directory_of_in_memory_files(
        &mut self,
        path: &PathWithScheme,
    ) -> Result<(), String> {
        self.db.delete_directory_of_in_memory_files(path)
    }

    pub fn close_in_memory_file(&mut self, path: &PathWithScheme) -> Result<(), &'static str> {
        self.db.close_in_memory_file(path)
    }

    pub fn diagnostics(&mut self) -> Diagnostics<'_> {
        if self.db.project.settings.mypy_path.len() > 1 {
            debug!(
                "Has complex mypy path: {:?}",
                &self.db.project.settings.mypy_path
            );
        }
        debug!(
            "Checking the following files: {:?}",
            self.db
                .project
                .settings
                .files_or_directories_to_check
                .iter()
                .map(|g| g.as_str())
                .collect::<Vec<_>>()
        );
        let mut all_diagnostics: Vec<diagnostics::Diagnostic> = vec![];
        let mut checked_files = 0;
        let mut files_with_errors = 0;

        select_files::with_relevant_files(&self.db, |file| {
            checked_files += 1;
            let mut issues = file.diagnostics(&self.db).into_vec();
            if !issues.is_empty() {
                files_with_errors += 1;
                all_diagnostics.append(&mut issues)
            }
        });
        tracing::info!("Checked {checked_files} files ({files_with_errors} files had errors)");
        invalidate_protocol_cache();
        Diagnostics {
            checked_files,
            files_with_errors,
            issues: all_diagnostics.into_boxed_slice(),
            error_count: Default::default(),
        }
    }

    /// This function is mostly for tests and should therefore not be used for something
    /// stable. We would have to ensure first it works everywhere.
    /// It currently is for example a big issue that HashableRawStr used in the name binder is very
    /// unsafe and will lead to SEGFAULTS if the original project is not kept.
    pub fn try_to_reuse_project_resources_for_tests(&mut self, options: ProjectOptions) -> Self {
        let db = self.db.try_to_reuse_project_resources_for_tests(options);
        Project { db }
    }

    pub fn document(&mut self, path: &PathWithScheme) -> Option<Document> {
        let DirOrFile::File(file_entry) = self
            .db
            .vfs
            .search_path(self.db.project.flags.case_sensitive, path)?
        else {
            return None;
        };

        let file_index = self.db.load_file_from_workspace(&file_entry, false)?;
        tracing::debug!("Looking at document #{file_index} for {}", path.as_uri());
        Some(Document {
            project: self,
            file_index,
        })
    }

    pub fn vfs_handler(&self) -> &dyn VfsHandler {
        self.db.vfs.handler.as_ref()
    }
}

impl std::fmt::Debug for Project {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("Project")
            .field("settings", &self.db.project.settings)
            .finish()
    }
}

pub struct Document<'project> {
    project: &'project mut Project,
    file_index: FileIndex,
}

impl<'project> Document<'project> {
    pub fn diagnostics(&mut self) -> Box<[diagnostics::Diagnostic]> {
        let python_file = self.project.db.loaded_python_file(self.file_index);
        python_file.diagnostics(&self.project.db)
    }

    fn positional_document(&self, position: InputPosition) -> PositionalDocument<GotoNode> {
        PositionalDocument::for_goto(
            &self.project.db,
            self.project.db.loaded_python_file(self.file_index),
            position,
        )
    }

    pub fn goto<T, R: FromIterator<T>>(
        &self,
        position: InputPosition,
        follow_imports: bool,
        on_name: impl for<'a> Fn(&dyn Name) -> T + Copy,
    ) -> R {
        GotoResolver::new(self.positional_document(position), on_name).goto(follow_imports)
    }

    pub fn infer_type_definition<'slf, T>(
        &'slf self,
        position: InputPosition,
        on_name: impl for<'a> Fn(ValueName) -> T + Copy + 'slf,
    ) -> impl Iterator<Item = T> + 'slf {
        GotoResolver::new(self.positional_document(position), on_name).infer_type_definition()
    }

    pub fn infer_implementation<'slf, T>(
        &'slf self,
        position: InputPosition,
        on_name: impl for<'a> Fn(ValueName) -> T + Copy + 'slf,
    ) -> impl Iterator<Item = T> + 'slf {
        GotoResolver::new(self.positional_document(position), on_name).infer_implementation()
    }

    pub fn complete<T>(
        &self,
        position: InputPosition,
        on_completion: impl Fn(&dyn Completion) -> T,
    ) -> Vec<T> {
        CompletionResolver::complete(
            &self.project.db,
            self.project.db.loaded_python_file(self.file_index),
            position,
            on_completion,
        )
    }
}

/// All positions are zero based
#[derive(Debug, Clone, Copy)]
pub enum InputPosition {
    NthByte(usize),
    Utf8Bytes { line: usize, column: usize },
    Utf16CodeUnits { line: usize, column: usize },
    CodePoints { line: usize, column: usize },
}

impl InputPosition {
    fn to_code_index(self, file: &PythonFile) -> CodeIndex {
        match self {
            InputPosition::NthByte(pos) => pos as u32,
            InputPosition::Utf8Bytes { line, column } => file.line_column_to_byte(line, column),
            InputPosition::Utf16CodeUnits { line: _, column: _ } => todo!(),
            InputPosition::CodePoints { line: _, column: _ } => todo!(),
        }
    }
}
/*
impl<'a> Script<'a> {
    fn leaf(&self, position: Position) -> Leaf {
        let pos = self.to_byte_position(position);
        let leaf = self.file().leaf(&self.project.db, pos);
        debug!("File {}", self.file().file_path(&self.project.db));
        debug!("Position {position:?} is on leaf {leaf:?}");
        leaf
    }

    pub fn search(&self, _text: String, _all_scopes: bool, _fuzzy: bool) {}
    pub fn complete_search(&self, _text: String, _all_scopes: bool, _fuzzy: bool) {}
    pub fn help(&self, _position: Position) {}
    pub fn references(&self, _position: Position /*, scope='project'*/) {}
    pub fn signatures(&self, _position: Position) {}
    pub fn context(&self, _position: Position) {}
    pub fn names(&self /*all_scopes=False, definitions=True, references=False*/) {}
    pub fn rename(&self, _position: Position, _new_name: &str) {}

    pub fn extract_variable(
        &self,
        _position: Position,
        _new_name: &str,
        _until_line: Option<usize>,
        _until_column: Option<usize>,
    ) {
    }
    pub fn extract_function(
        &self,
        _position: Position,
        _new_name: &str,
        _until_line: Option<usize>,
        _until_column: Option<usize>,
    ) {
    }
    pub fn inline(&self, _position: Position) {}

    pub fn selection_ranges() {
    }
}
*/

pub struct Diagnostics<'a> {
    pub checked_files: usize,
    pub files_with_errors: usize,
    pub issues: Box<[diagnostics::Diagnostic<'a>]>,
    error_count: OnceCell<usize>,
}

impl Diagnostics<'_> {
    pub fn summary(&self) -> String {
        let s_if_plural = |n| match n {
            1 => "",
            _ => "s",
        };
        let error_count = self.error_count();
        if error_count == 0 {
            format!(
                "Success: no issues found in {checked} source file{checked_s}",
                checked = self.checked_files,
                checked_s = s_if_plural(self.checked_files),
            )
        } else {
            format!(
                "Found {error_count} error{e_s} in {fwe} file{fwe_s} (checked {checked} source file{checked_s})",
                e_s = s_if_plural(self.issues.len()),
                fwe = self.files_with_errors,
                fwe_s = s_if_plural(self.files_with_errors),
                checked = self.checked_files,
                checked_s = s_if_plural(self.checked_files),
            )
        }
    }

    pub fn error_count(&self) -> usize {
        *self.error_count.get_or_init(|| {
            self.issues
                .iter()
                .filter(|issue| issue.severity() == Severity::Error)
                .count()
        })
    }

    pub fn sort_issues_by_kind(&mut self) {
        self.issues.sort_by_key(|issue| &issue.issue.kind)
    }
}

pub struct PanicRecovery {
    vfs: vfs::VfsPanicRecovery<Tree>,
    mode: Mode,
}
