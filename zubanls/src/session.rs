//! Data model, state management, and configuration resolution.

use std::borrow::Cow;
use std::collections::BTreeMap;
use std::ops::{Deref, DerefMut};
use std::path::{Path, PathBuf};
use std::sync::Arc;

use crate::{
    edit::DocumentVersion,
    system::{url_to_any_system_path, AnySystemPath, LSPSystem},
    PositionEncoding, TextDocument,
};

use super::ClientSettings;

use anyhow::anyhow;
use lsp_types::{ClientCapabilities, TextDocumentContentChangeEvent, Uri};
use rustc_hash::FxHashMap;
use serde::Deserialize;

use red_knot_workspace::db::RootDatabase;
use red_knot_workspace::workspace::WorkspaceMetadata;
use zuban_db::files::{system_path_to_file, File};
use zuban_db::system::SystemPath;
use zuban_db::Db;

/// The global state for the LSP
pub struct Session {
    /// Used to retrieve information about open documents and settings.
    ///
    /// This will be [`None`] when a mutable reference is held to the index via [`index_mut`]
    /// to prevent the index from being accessed while it is being modified. It will be restored
    /// when the mutable reference ([`MutIndexGuard`]) is dropped.
    ///
    /// [`index_mut`]: Session::index_mut
    index: Option<Arc<index::Index>>,

    /// Maps workspace root paths to their respective databases.
    workspaces: BTreeMap<PathBuf, RootDatabase>,
    /// The global position encoding, negotiated during LSP initialization.
    position_encoding: PositionEncoding,
    /// Tracks what LSP features the client supports and doesn't support.
    resolved_client_capabilities: Arc<ResolvedClientCapabilities>,
}

impl Session {
    pub fn new(
        client_capabilities: &ClientCapabilities,
        position_encoding: PositionEncoding,
        global_settings: ClientSettings,
        workspace_folders: &[(Uri, ClientSettings)],
    ) -> crate::ZResult<Self> {
        let mut workspaces = BTreeMap::new();
        let index = Arc::new(index::Index::new(global_settings));

        for (url, _) in workspace_folders {
            let path = url
                .to_file_path()
                .map_err(|()| anyhow!("Workspace URL is not a file or directory: {:?}", url))?;
            let system_path = SystemPath::from_std_path(&path)
                .ok_or_else(|| anyhow!("Workspace path is not a valid UTF-8 path: {:?}", path))?;
            let system = LSPSystem::new(index.clone());

            // TODO(dhruvmanila): Get the values from the client settings
            let metadata = WorkspaceMetadata::discover(system_path, &system, None)?;
            // TODO(micha): Handle the case where the program settings are incorrect more gracefully.
            workspaces.insert(path, RootDatabase::new(metadata, system)?);
        }

        Ok(Self {
            position_encoding,
            workspaces,
            index: Some(index),
            resolved_client_capabilities: Arc::new(ResolvedClientCapabilities::new(
                client_capabilities,
            )),
        })
    }

    // TODO: Ideally, we should have a single method for `workspace_db_for_path_mut`
    // and `default_workspace_db_mut` but the borrow checker doesn't allow that.
    /// Returns a reference to the workspace [`RootDatabase`] corresponding to the given path, if
    /// any.
    pub(crate) fn workspace_db_for_path(&self, path: impl AsRef<Path>) -> Option<&RootDatabase> {
        self.workspaces
            .range(..=path.as_ref().to_path_buf())
            .next_back()
            .map(|(_, db)| db)
    }

    /// Returns a mutable reference to the workspace [`RootDatabase`] corresponding to the given
    /// path, if any.
    pub(crate) fn workspace_db_for_path_mut(
        &mut self,
        path: impl AsRef<Path>,
    ) -> Option<&mut RootDatabase> {
        self.workspaces
            .range_mut(..=path.as_ref().to_path_buf())
            .next_back()
            .map(|(_, db)| db)
    }

    /// Returns a reference to the default workspace [`RootDatabase`]. The default workspace is the
    /// minimum root path in the workspace map.
    pub(crate) fn default_workspace_db(&self) -> &RootDatabase {
        // SAFETY: Currently, red knot only support a single workspace.
        self.workspaces.values().next().unwrap()
    }

    /// Returns a mutable reference to the default workspace [`RootDatabase`].
    pub(crate) fn default_workspace_db_mut(&mut self) -> &mut RootDatabase {
        // SAFETY: Currently, red knot only support a single workspace.
        self.workspaces.values_mut().next().unwrap()
    }

    /// Creates a document snapshot with the URL referencing the document to snapshot.
    pub fn take_snapshot(&self, uri: Uri) -> Option<DocumentSnapshot> {
        Some(DocumentSnapshot {
            resolved_client_capabilities: self.resolved_client_capabilities.clone(),
            document_ref: self.index().make_document_ref(uri)?,
            position_encoding: self.position_encoding,
        })
    }

    /// Registers a text document at the provided `url`.
    /// If a document is already open here, it will be overwritten.
    pub(crate) fn open_text_document(&mut self, url: Uri, document: TextDocument) {
        self.index_mut().open_text_document(url, document);
    }

    /// Updates a text document at the associated `key`.
    ///
    /// The document key must point to a text document, or this will throw an error.
    pub(crate) fn update_text_document(
        &mut self,
        key: &DocumentKey,
        content_changes: Vec<TextDocumentContentChangeEvent>,
        new_version: DocumentVersion,
    ) -> crate::ZResult<()> {
        let position_encoding = self.position_encoding;
        self.index_mut()
            .update_text_document(key, content_changes, new_version, position_encoding)
    }

    /// De-registers a document, specified by its key.
    /// Calling this multiple times for the same document is a logic error.
    pub(crate) fn close_document(&mut self, key: &DocumentKey) -> crate::ZResult<()> {
        self.index_mut().close_document(key)?;
        Ok(())
    }

    /// Returns a reference to the index.
    ///
    /// # Panics
    ///
    /// Panics if there's a mutable reference to the index via [`index_mut`].
    ///
    /// [`index_mut`]: Session::index_mut
    fn index(&self) -> &index::Index {
        self.index.as_ref().unwrap()
    }

    /// Returns a mutable reference to the index.
    ///
    /// This method drops all references to the index and returns a guard that will restore the
    /// references when dropped. This guard holds the only reference to the index and allows
    /// modifying it.
    fn index_mut(&mut self) -> MutIndexGuard {
        let index = self.index.take().unwrap();

        for db in self.workspaces.values_mut() {
            // Remove the `index` from each database. This drops the count of `Arc<Index>` down to 1
            db.system_mut()
                .as_any_mut()
                .downcast_mut::<LSPSystem>()
                .unwrap()
                .take_index();
        }

        // There should now be exactly one reference to index which is self.index.
        let index = Arc::into_inner(index);

        MutIndexGuard {
            session: self,
            index,
        }
    }
}

/// A guard that holds the only reference to the index and allows modifying it.
///
/// When dropped, this guard restores all references to the index.
struct MutIndexGuard<'a> {
    session: &'a mut Session,
    index: Option<index::Index>,
}

impl Deref for MutIndexGuard<'_> {
    type Target = index::Index;

    fn deref(&self) -> &Self::Target {
        self.index.as_ref().unwrap()
    }
}

impl DerefMut for MutIndexGuard<'_> {
    fn deref_mut(&mut self) -> &mut Self::Target {
        self.index.as_mut().unwrap()
    }
}

impl Drop for MutIndexGuard<'_> {
    fn drop(&mut self) {
        if let Some(index) = self.index.take() {
            let index = Arc::new(index);
            for db in self.session.workspaces.values_mut() {
                db.system_mut()
                    .as_any_mut()
                    .downcast_mut::<LSPSystem>()
                    .unwrap()
                    .set_index(index.clone());
            }

            self.session.index = Some(index);
        }
    }
}

/// An immutable snapshot of `Session` that references
/// a specific document.
#[derive(Debug)]
pub struct DocumentSnapshot {
    resolved_client_capabilities: Arc<ResolvedClientCapabilities>,
    document_ref: DocumentQuery,
    position_encoding: PositionEncoding,
}

impl DocumentSnapshot {
    pub(crate) fn resolved_client_capabilities(&self) -> &ResolvedClientCapabilities {
        &self.resolved_client_capabilities
    }

    pub fn query(&self) -> &DocumentQuery {
        &self.document_ref
    }

    pub(crate) fn encoding(&self) -> PositionEncoding {
        self.position_encoding
    }

    pub(crate) fn file(&self, db: &RootDatabase) -> Option<File> {
        match url_to_any_system_path(self.document_ref.file_url()).ok()? {
            AnySystemPath::System(path) => system_path_to_file(db, path).ok(),
            AnySystemPath::SystemVirtual(virtual_path) => db
                .files()
                .try_virtual_file(&virtual_path)
                .map(|virtual_file| virtual_file.file()),
        }
    }
}

/// Maps a workspace URI to its associated client settings. Used during server initialization.
pub(crate) type WorkspaceSettingsMap = FxHashMap<Uri, ClientSettings>;

/// This is a direct representation of the settings schema sent by the client.
#[derive(Debug, Deserialize, Default)]
#[cfg_attr(test, derive(PartialEq, Eq))]
#[serde(rename_all = "camelCase")]
pub struct ClientSettings {
    // These settings are only needed for tracing, and are only read from the global configuration.
    // These will not be in the resolved settings.
    #[serde(flatten)]
    pub(crate) tracing: TracingSettings,
}

/// Settings needed to initialize tracing. These will only be
/// read from the global configuration.
#[derive(Debug, Deserialize, Default)]
#[cfg_attr(test, derive(PartialEq, Eq))]
#[serde(rename_all = "camelCase")]
pub(crate) struct TracingSettings {
    pub(crate) log_level: Option<crate::trace::LogLevel>,
    /// Path to the log file - tildes and environment variables are supported.
    pub(crate) log_file: Option<PathBuf>,
}

/// This is a direct representation of the workspace settings schema,
/// which inherits the schema of [`ClientSettings`] and adds extra fields
/// to describe the workspace it applies to.
#[derive(Debug, Deserialize)]
#[cfg_attr(test, derive(PartialEq, Eq))]
#[serde(rename_all = "camelCase")]
struct WorkspaceSettings {
    #[serde(flatten)]
    settings: ClientSettings,
    workspace: Uri,
}

/// This is the exact schema for initialization options sent in by the client
/// during initialization.
#[derive(Debug, Deserialize)]
#[cfg_attr(test, derive(PartialEq, Eq))]
#[serde(untagged)]
enum InitializationOptions {
    #[serde(rename_all = "camelCase")]
    HasWorkspaces {
        global_settings: ClientSettings,
        #[serde(rename = "settings")]
        workspace_settings: Vec<WorkspaceSettings>,
    },
    GlobalOnly {
        #[serde(default)]
        settings: ClientSettings,
    },
}

/// Built from the initialization options provided by the client.
#[derive(Debug)]
pub(crate) struct AllSettings {
    pub(crate) global_settings: ClientSettings,
    /// If this is `None`, the client only passed in global settings.
    pub(crate) workspace_settings: Option<WorkspaceSettingsMap>,
}

impl AllSettings {
    /// Initializes the controller from the serialized initialization options.
    /// This fails if `options` are not valid initialization options.
    pub(crate) fn from_value(options: serde_json::Value) -> Self {
        Self::from_init_options(
            serde_json::from_value(options)
                .map_err(|err| {
                    tracing::error!("Failed to deserialize initialization options: {err}. Falling back to default client settings...");
                    show_err_msg!("ZubanLS received invalid client settings - falling back to default client settings.");
                })
                .unwrap_or_default(),
        )
    }

    fn from_init_options(options: InitializationOptions) -> Self {
        let (global_settings, workspace_settings) = match options {
            InitializationOptions::GlobalOnly { settings } => (settings, None),
            InitializationOptions::HasWorkspaces {
                global_settings,
                workspace_settings,
            } => (global_settings, Some(workspace_settings)),
        };

        Self {
            global_settings,
            workspace_settings: workspace_settings.map(|workspace_settings| {
                workspace_settings
                    .into_iter()
                    .map(|settings| (settings.workspace, settings.settings))
                    .collect()
            }),
        }
    }
}

impl Default for InitializationOptions {
    fn default() -> Self {
        Self::GlobalOnly {
            settings: ClientSettings::default(),
        }
    }
}

/// Stores and tracks all open documents in a session, along with their associated settings.
#[derive(Default, Debug)]
struct Index {
    /// Maps all document file URLs to the associated document controller
    documents: FxHashMap<Uri, DocumentController>,

    /// Global settings provided by the client.
    global_settings: ClientSettings,
}

impl Index {
    pub(super) fn new(global_settings: ClientSettings) -> Self {
        Self {
            documents: FxHashMap::default(),
            global_settings,
        }
    }

    pub(super) fn update_text_document(
        &mut self,
        key: &Uri,
        content_changes: Vec<lsp_types::TextDocumentContentChangeEvent>,
        new_version: DocumentVersion,
        encoding: PositionEncoding,
    ) -> crate::ZResult<()> {
        let controller = self.document_controller_for_key(key)?;
        let Some(document) = controller.as_text_mut() else {
            anyhow::bail!("Text document URI does not point to a text document");
        };

        if content_changes.is_empty() {
            document.update_version(new_version);
            return Ok(());
        }

        document.apply_changes(content_changes, new_version, encoding);

        Ok(())
    }

    pub(crate) fn make_document_ref(&self, uri: Uri) -> Option<DocumentQuery> {
        let controller = self.documents.get(&uri)?;
        Some(controller.make_ref(uri))
    }

    pub(super) fn open_text_document(&mut self, uri: Uri, document: TextDocument) {
        self.documents
            .insert(uri, DocumentController::new_text(document));
    }

    pub(super) fn close_document(&mut self, key: &Uri) -> crate::ZResult<()> {
        let Some(uri) = self.url_for_key(key).cloned() else {
            anyhow::bail!("Tried to close unavailable document `{key}`");
        };

        let Some(_) = self.documents.remove(&uri) else {
            anyhow::bail!("tried to close document that didn't exist at {}", uri)
        };
        Ok(())
    }

    fn document_controller_for_key(
        &mut self,
        uri: &Uri,
    ) -> crate::ZResult<&mut DocumentController> {
        let Some(controller) = self.documents.get_mut(&uri) else {
            anyhow::bail!("Document controller not available at `{}`", uri);
        };
        Ok(controller)
    }
}

/// A mutable handler to an underlying document.
#[derive(Debug)]
enum DocumentController {
    Text(Arc<TextDocument>),
}

impl DocumentController {
    fn new_text(document: TextDocument) -> Self {
        Self::Text(Arc::new(document))
    }

    fn make_ref(&self) -> DocumentQuery {
        match &self {
            Self::Text(document) => DocumentQuery::Text {
                file_url,
                document: document.clone(),
            },
        }
    }

    #[allow(dead_code)]
    pub(crate) fn as_text(&self) -> Option<&TextDocument> {
        match self {
            Self::Text(document) => Some(document),
        }
    }

    pub(crate) fn as_text_mut(&mut self) -> Option<&mut TextDocument> {
        Some(match self {
            Self::Text(document) => Arc::make_mut(document),
        })
    }
}

/// A read-only query to an open document.
/// It also includes document settings.
#[derive(Debug, Clone)]
pub enum DocumentQuery {
    Text {
        file_url: Uri,
        document: Arc<TextDocument>,
    },
}

impl DocumentQuery {
    /// Get the source type of the document associated with this query.
    pub(crate) fn source_type(&self) -> zuban_python_ast::PySourceType {
        match self {
            Self::Text { .. } => zuban_python_ast::PySourceType::from(self.virtual_file_path()),
        }
    }

    /// Get the version of document selected by this query.
    pub(crate) fn version(&self) -> DocumentVersion {
        match self {
            Self::Text { document, .. } => document.version(),
        }
    }

    /// Get the URL for the document selected by this query.
    pub(crate) fn file_url(&self) -> &Uri {
        match self {
            Self::Text { file_url, .. } => file_url,
        }
    }

    /// Get the path for the document selected by this query.
    ///
    /// Returns `None` if this is an unsaved (untitled) document.
    ///
    /// The path isn't guaranteed to point to a real path on the filesystem. This is the case
    /// for unsaved (untitled) documents.
    pub(crate) fn file_path(&self) -> Option<PathBuf> {
        self.file_url().to_file_path().ok()
    }

    /// Get the path for the document selected by this query, ignoring whether the file exists on disk.
    ///
    /// Returns the URL's path if this is an unsaved (untitled) document.
    pub(crate) fn virtual_file_path(&self) -> Cow<Path> {
        self.file_path()
            .map(Cow::Owned)
            .unwrap_or_else(|| Cow::Borrowed(Path::new(self.file_url().path())))
    }

    /// Attempt to access the single inner text document selected by the query.
    pub(crate) fn as_single_document(&self) -> Option<&TextDocument> {
        match self {
            Self::Text { document, .. } => Some(document),
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Default)]
#[allow(clippy::struct_excessive_bools)]
pub(crate) struct ResolvedClientCapabilities {
    pub(crate) code_action_deferred_edit_resolution: bool,
    pub(crate) apply_edit: bool,
    pub(crate) document_changes: bool,
    pub(crate) workspace_refresh: bool,
    pub(crate) pull_diagnostics: bool,
}

impl ResolvedClientCapabilities {
    pub(super) fn new(client_capabilities: &ClientCapabilities) -> Self {
        let code_action_settings = client_capabilities
            .text_document
            .as_ref()
            .and_then(|doc_settings| doc_settings.code_action.as_ref());
        let code_action_data_support = code_action_settings
            .and_then(|code_action_settings| code_action_settings.data_support)
            .unwrap_or_default();
        let code_action_edit_resolution = code_action_settings
            .and_then(|code_action_settings| code_action_settings.resolve_support.as_ref())
            .is_some_and(|resolve_support| resolve_support.properties.contains(&"edit".into()));

        let apply_edit = client_capabilities
            .workspace
            .as_ref()
            .and_then(|workspace| workspace.apply_edit)
            .unwrap_or_default();

        let document_changes = client_capabilities
            .workspace
            .as_ref()
            .and_then(|workspace| workspace.workspace_edit.as_ref())
            .and_then(|workspace_edit| workspace_edit.document_changes)
            .unwrap_or_default();

        let workspace_refresh = true;

        // TODO(jane): Once the bug involving workspace.diagnostic(s) deserialization has been fixed,
        // uncomment this.
        /*
        let workspace_refresh = client_capabilities
            .workspace
            .as_ref()
            .and_then(|workspace| workspace.diagnostic.as_ref())
            .and_then(|diagnostic| diagnostic.refresh_support)
            .unwrap_or_default();
        */

        let pull_diagnostics = client_capabilities
            .text_document
            .as_ref()
            .and_then(|text_document| text_document.diagnostic.as_ref())
            .is_some();

        Self {
            code_action_deferred_edit_resolution: code_action_data_support
                && code_action_edit_resolution,
            apply_edit,
            document_changes,
            workspace_refresh,
            pull_diagnostics,
        }
    }
}
