use std::borrow::Cow;
use std::path::{Path, PathBuf};
use std::sync::Arc;

use lsp_types::Uri;
use rustc_hash::FxHashMap;

use crate::{edit::DocumentVersion, PositionEncoding, TextDocument};

use super::ClientSettings;

/// Stores and tracks all open documents in a session, along with their associated settings.
#[derive(Default, Debug)]
pub(crate) struct Index {
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

    pub(super) fn text_document_urls(&self) -> impl Iterator<Item = &Uri> + '_ {
        self.documents
            .iter()
            .filter_map(|(url, doc)| doc.as_text().and(Some(url)))
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

    pub(super) fn num_documents(&self) -> usize {
        self.documents.len()
    }

    pub(crate) fn make_document_ref(&self, uri: Uri) -> Option<DocumentQuery> {
        let controller = self.documents.get(&uri)?;
        Some(controller.make_ref(url))
    }

    pub(super) fn open_text_document(&mut self, url: Uri, document: TextDocument) {
        self.documents
            .insert(url, DocumentController::new_text(document));
    }

    pub(super) fn close_document(&mut self, key: &Uri) -> crate::ZResult<()> {
        let Some(url) = self.url_for_key(key).cloned() else {
            anyhow::bail!("Tried to close unavailable document `{key}`");
        };

        let Some(_) = self.documents.remove(&url) else {
            anyhow::bail!("tried to close document that didn't exist at {}", url)
        };
        Ok(())
    }

    fn document_controller_for_key(
        &mut self,
        uri: &Uri,
    ) -> crate::ZResult<&mut DocumentController> {
        let Some(controller) = self.documents.get_mut(&uri) else {
            anyhow::bail!("Document controller not available at `{}`", url);
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
