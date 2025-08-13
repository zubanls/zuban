#![allow(clippy::nonminimal_bool)] // I don't like this rule
#![allow(clippy::too_many_arguments)] // TODO For now this is easier, but probably enable again

mod arguments;
mod completion;
mod database;
mod diagnostics;
mod file;
mod format_data;
mod getitem;
mod goto;
mod imports;
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

use std::{cell::OnceCell, path::Path};

use ::utils::FastHashMap;
use anyhow::bail;
use completion::CompletionResolver;
pub use completion::{Completion, CompletionItemKind};
pub use goto::{GotoGoal, ReferencesGoal};
use goto::{GotoResolver, PositionalDocument, ReferencesResolver};
use name::Range;
use parsa_python_cst::{GotoNode, Tree};
use vfs::{AbsPath, DirOrFile, FileIndex, LocalFS, PathWithScheme, VfsHandler};

use config::{ProjectOptions, PythonVersion, Settings, TypeCheckerFlags};
pub use database::Mode;
use database::{Database, PythonProject};
pub use diagnostics::Severity;
use file::File;
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
        Self::new_internal(db)
    }

    fn new_internal(db: Database) -> Self {
        tracing::debug!("Project settings: {:#?}", &db.project);
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
        Self::new_internal(db)
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
            issues.sort_by_key(|issue| issue.start_position().byte_position);
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
    project: &'project Project,
    file_index: FileIndex,
}

impl<'project> Document<'project> {
    pub fn diagnostics(&mut self) -> Box<[diagnostics::Diagnostic]> {
        let python_file = self.project.db.loaded_python_file(self.file_index);
        python_file.diagnostics(&self.project.db)
    }

    fn positional_document(
        &self,
        position: InputPosition,
    ) -> anyhow::Result<PositionalDocument<'project, GotoNode<'project>>> {
        let db = &self.project.db;
        PositionalDocument::for_goto(db, db.loaded_python_file(self.file_index), position)
    }

    pub fn goto<T>(
        &self,
        position: InputPosition,
        goal: GotoGoal,
        follow_imports: bool,
        on_name: impl for<'a> Fn(Name) -> T,
    ) -> anyhow::Result<Vec<T>> {
        Ok(
            GotoResolver::new(self.positional_document(position)?, goal, on_name)
                .goto(follow_imports),
        )
    }

    pub fn infer_definition<'slf, T>(
        &'slf self,
        position: InputPosition,
        goal: GotoGoal,
        on_name: impl for<'a> FnMut(ValueName) -> T,
    ) -> anyhow::Result<Vec<T>> {
        Ok(
            GotoResolver::new(self.positional_document(position)?, goal, on_name)
                .infer_definition(),
        )
    }

    pub fn references<'slf, T>(
        &'slf self,
        position: InputPosition,
        goal: ReferencesGoal,
        include_declarations: bool,
        on_name: impl for<'a> Fn(Name) -> T,
    ) -> anyhow::Result<Vec<T>> {
        Ok(
            ReferencesResolver::new(self.positional_document(position)?, on_name)
                .references(goal, include_declarations),
        )
    }

    pub fn references_for_rename<'x>(
        &self,
        position: InputPosition,
        new_name: &'x str,
    ) -> anyhow::Result<RenameChanges<'project, 'x>> {
        let document = self.positional_document(position)?;
        let Some(name) = document.node.on_name() else {
            bail!("Could not find a name under the cursor to rename");
        };

        let db = &self.project.db;
        if name.as_code() == new_name {
            // The rename doesn't change anything, because the names stay the same
            return Ok(RenameChanges {
                changes: vec![],
                file_renames: vec![],
                old_name: name.as_code(),
                new_name,
            });
        }

        let mut file_renames: Vec<&'project PathWithScheme> = vec![];
        let mut file_changes = FastHashMap::default();
        let references = ReferencesResolver::new(document, |name| match &name {
            Name::TreeName(tree_name) => {
                let file_index = tree_name.file.file_index;
                file_changes
                    .entry(file_index)
                    .or_insert_with(|| vec![])
                    .push(name.name_range());
            }
            Name::ModuleName(module_name) => {
                file_renames.push(module_name.file.file_path_with_scheme(db))
            }
            Name::NodeName(_) => recoverable_error!("Should never reach a node name in rename"),
        })
        .references(ReferencesGoal::OnlyTypeCheckedWorkspaces, true);
        if references.is_empty() {
            bail!(
                "Could not find the definition of {:?} under the cursor",
                name.as_code()
            );
        }
        let changes: Vec<SingleFileRenameChanges<'project>> = file_changes
            .into_iter()
            .map(|(file_index, changes)| {
                //
                SingleFileRenameChanges {
                    path: db.vfs.file_path(file_index),
                    ranges: changes,
                }
            })
            .collect();
        Ok(RenameChanges {
            changes,
            file_renames,
            old_name: name.as_code(),
            new_name,
        })
    }

    pub fn complete<T>(
        &self,
        position: InputPosition,
        filter_with_name_under_cursor: bool,
        on_completion: impl Fn(Range, &dyn Completion) -> T,
    ) -> anyhow::Result<Vec<T>> {
        CompletionResolver::complete(
            &self.project.db,
            self.project.db.loaded_python_file(self.file_index),
            position,
            filter_with_name_under_cursor,
            on_completion,
        )
    }

    pub fn documentation(
        &self,
        position: InputPosition,
        only_docstrings: bool,
    ) -> anyhow::Result<Option<DocumentationResult>> {
        let mut types = vec![];
        let mut resolver = GotoResolver::new(
            self.positional_document(position)?,
            GotoGoal::Indifferent,
            |n: ValueName| {
                if !only_docstrings {
                    types.push(
                        n.maybe_pretty_function_type()
                            .unwrap_or_else(|| n.type_description())
                            .into_string(),
                    );
                }
                n.name.documentation().to_string()
            },
        );
        let mut results = resolver.infer_definition();
        if results.is_empty() {
            return Ok(None);
        }
        let Some(on_symbol_range) = resolver.on_node_range() else {
            // This is probably not reachable
            return Ok(None);
        };

        let resolver = GotoResolver::new(resolver.infos, GotoGoal::Indifferent, |n: Name| {
            n.origin_kind()
        });
        let on_name = resolver.infos.node.on_name();
        let declaration_kinds = resolver.goto(true);
        results.retain(|doc| !doc.is_empty());

        let docs = results.join("\n\n");
        let documentation = if only_docstrings {
            docs
        } else {
            let mut out = String::default();
            if !declaration_kinds.is_empty() {
                out.push('(');
                out += &declaration_kinds.join(", ");
                out += ") ";
            }
            if let Some(name) = on_name {
                match declaration_kinds.as_slice() {
                    ["class"] => {
                        // Return the inner part in Type[A], because that makes more sense and
                        // looks nicer
                        for ty in &mut types {
                            if ty.starts_with("Type[") && ty.ends_with("]") {
                                ty.drain(..5);
                                ty.drain(ty.len() - 1..);
                            }
                        }
                    }
                    ["function"] => (),
                    ["type"] => {
                        out += name.as_code();
                        out += " = ";
                    }
                    _ => {
                        out += name.as_code();
                        out += ": ";
                    }
                }
            }
            out += &types.join(" | ");
            if !results.is_empty() {
                out += "\n---\n";
                out += &docs;
            }
            out
        };
        Ok(Some(DocumentationResult {
            documentation,
            on_symbol_range,
        }))
    }

    pub fn is_valid_rename_location(
        &self,
        position: InputPosition,
    ) -> anyhow::Result<Option<Range>> {
        let document = self.positional_document(position)?;
        let file = document.file;
        let Some(name) = document.node.on_name() else {
            return Ok(None);
        };
        let resolver = GotoResolver::new(document, GotoGoal::Indifferent, |_: Name| ());
        let is_valid = !resolver.goto(false).is_empty();
        if !is_valid {
            anyhow::bail!(
                "The reference {:?} cannot be resolved; rename is therefore not possible.",
                name.as_code()
            )
        }
        Ok(Some((
            file.byte_to_position_infos(&self.project.db, name.start()),
            file.byte_to_position_infos(&self.project.db, name.end()),
        )))
    }
}

pub struct DocumentationResult<'a> {
    pub documentation: String,
    pub on_symbol_range: Range<'a>,
}

#[derive(Debug)]
pub struct SingleFileRenameChanges<'db> {
    pub path: &'db PathWithScheme,
    pub ranges: Vec<Range<'db>>,
}

#[derive(Debug)]
pub struct RenameChanges<'db, 'a> {
    pub changes: Vec<SingleFileRenameChanges<'db>>,
    file_renames: Vec<&'db PathWithScheme>,
    pub old_name: &'db str,
    pub new_name: &'a str,
}

#[derive(Debug)]
pub struct FileRename<'db, 'a> {
    from: &'db PathWithScheme,
    new_name: &'a str,
}

impl<'db> FileRename<'db, '_> {
    pub fn from(&self) -> &'db PathWithScheme {
        self.from
    }

    pub fn from_uri(&self) -> String {
        self.from.as_uri()
    }

    pub fn to_uri(&self) -> String {
        let mut uri = self.from_uri();
        let path = Path::new(&uri);
        let mut parent = path.parent().unwrap();
        let old_name = path.file_stem().unwrap().to_str().unwrap();
        let extension = path.extension().unwrap().to_str().unwrap().to_string();
        let mut maybe_init = "".to_string();
        if old_name == "__init__" {
            if let Some(par_parent) = parent.parent() {
                parent = par_parent;
                maybe_init = format!("{old_name}/")
            }
        }
        uri.truncate(parent.as_os_str().len());
        uri.push('/');
        uri += self.new_name;
        uri += &maybe_init;
        uri.push('.');
        uri += &extension;
        uri
    }
}

impl<'db> RenameChanges<'db, '_> {
    pub fn has_changes(&self) -> bool {
        !self.changes.is_empty() || !self.file_renames.is_empty()
    }

    pub fn renames(&self) -> impl Iterator<Item = FileRename> {
        self.file_renames.iter().map(|from| FileRename {
            from,
            new_name: self.new_name,
        })
    }
}

/// All positions are zero based
#[derive(Debug, Clone, Copy)]
pub enum InputPosition {
    NthUTF8Byte(usize),
    Utf8Bytes { line: usize, column: usize },
    Utf16CodeUnits { line: usize, column: usize },
    CodePoints { line: usize, column: usize },
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
    pub fn signatures(&self, _position: Position) {}
    pub fn context(&self, _position: Position) {}

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
