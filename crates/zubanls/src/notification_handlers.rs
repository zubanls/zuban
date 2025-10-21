use anyhow::bail;
use lsp_types::{
    DidChangeNotebookDocumentParams, DidChangeTextDocumentParams, DidCloseNotebookDocumentParams,
    DidCloseTextDocumentParams, DidOpenNotebookDocumentParams, DidOpenTextDocumentParams,
    NotebookCell, NotebookCellKind, TextDocumentContentChangeEvent, TextDocumentIdentifier,
    TextDocumentItem, VersionedTextDocumentIdentifier,
};

use crate::server::GlobalState;

impl GlobalState<'_> {
    pub(crate) fn handle_did_open_text_document(
        &mut self,
        params: DidOpenTextDocumentParams,
    ) -> anyhow::Result<()> {
        let _p = tracing::info_span!("handle_did_open_text_document").entered();
        self.store_in_memory_file(params.text_document.uri, params.text_document.text.into())
    }

    pub(crate) fn handle_did_change_text_document(
        &mut self,
        params: DidChangeTextDocumentParams,
    ) -> anyhow::Result<()> {
        let _p = tracing::info_span!("handle_did_change_text_document").entered();
        self.change_document(params.text_document, params.content_changes)
    }

    fn change_document(
        &mut self,
        text_document: VersionedTextDocumentIdentifier,
        content_changes: Vec<TextDocumentContentChangeEvent>,
    ) -> anyhow::Result<()> {
        /*
         * TODO do something like this (check rust-analyzer as a reference)
        let Some(code) = self.project().code_of_in_memory_file(path) else {
            bail!("Should be an in memory file, because we have opened it before")
        };
        let code = apply_document_changes(encoding, code, params.content_changes);
        */
        let len = content_changes.len();
        let Some(change) = content_changes.into_iter().next() else {
            bail!("Expected there to be at least one config change")
        };
        if len != 1 || change.range.is_some() || change.range_length.is_some() {
            bail!(
                "Expected there to be exactly one content change, because we \
                   don't support TextDocumentSyncKind::INCREMENTAL yet"
            )
        }
        self.store_in_memory_file(text_document.uri, change.text.into())
    }

    fn store_in_memory_file(&mut self, uri: lsp_types::Uri, code: Box<str>) -> anyhow::Result<()> {
        let project = self.project();
        let path = Self::uri_to_path(project, uri)?;
        tracing::info!("Loading {}", path.as_uri());
        project.store_in_memory_file(path, code);
        Ok(())
    }

    pub(crate) fn handle_did_close_text_document(
        &mut self,
        params: DidCloseTextDocumentParams,
    ) -> anyhow::Result<()> {
        let _p = tracing::info_span!("handle_did_change_text_document").entered();
        let project = self.project();
        let path = Self::uri_to_path(project, params.text_document.uri)?;
        tracing::info!("Closing {}", path.as_uri());

        project
            .close_in_memory_file(&path)
            .map_err(|err| anyhow::anyhow!("{err}"))
    }

    pub(crate) fn handle_did_open_notebook(
        &mut self,
        params: DidOpenNotebookDocumentParams,
    ) -> anyhow::Result<()> {
        let _p = tracing::info_span!("handle_did_open_notebook").entered();
        self.new_cells(params.notebook_document.cells, params.cell_text_documents)
    }

    fn new_cells(
        &mut self,
        cells: Vec<NotebookCell>,
        mut text_documents: Vec<TextDocumentItem>,
    ) -> anyhow::Result<()> {
        for cell in cells {
            if cell.kind != NotebookCellKind::Code {
                continue;
            }
            let Some(pos) = text_documents.iter().position(|x| x.uri == cell.document) else {
                bail!(
                    "Did not find URI {:?} in cell_text_documents",
                    cell.document
                );
            };
            let doc_item = text_documents.swap_remove(pos);
            self.store_in_memory_file(cell.document, doc_item.text.into())?
        }
        Ok(())
    }

    fn close_cells(&mut self, text_documents: Vec<TextDocumentIdentifier>) -> anyhow::Result<()> {
        let project = self.project();
        let mut result = Ok(());
        for text_document in text_documents {
            let path = Self::uri_to_path(project, text_document.uri)?;
            tracing::info!("Closing {}", path.as_uri());
            if let err @ Err(_) = project
                .close_in_memory_file(&path)
                .map_err(|err| anyhow::anyhow!("{err}"))
            {
                result = err;
            }
        }
        result
    }

    pub(crate) fn handle_did_change_notebook(
        &mut self,
        params: DidChangeNotebookDocumentParams,
    ) -> anyhow::Result<()> {
        let _p = tracing::info_span!("handle_did_change_notebook").entered();
        let Some(cells) = params.change.cells else {
            // Only the meta data changed
            return Ok(());
        };
        let mut result = Ok(());
        if let Some(structure) = cells.structure {
            result = self.close_cells(structure.did_close.unwrap_or_default());
            if let Some(cells) = structure.array.cells {
                self.new_cells(cells, structure.did_open.unwrap_or_default())?
            }
        }
        if let Some(metadata_change) = cells.data {
            for _cell in metadata_change {
                // In VSCode the change of Markdown -> Python and vice versa just causes a change
                // in the structure (new/deleted), so this information seems irrelevant at the
                // moment, but maybe some people implement it in different ways.
            }
        }
        if let Some(text_content) = cells.text_content {
            for change in text_content {
                self.change_document(change.document, change.changes)?
            }
        }
        result
    }

    pub(crate) fn handle_did_close_notebook(
        &mut self,
        params: DidCloseNotebookDocumentParams,
    ) -> anyhow::Result<()> {
        let _p = tracing::info_span!("handle_did_close_notebook").entered();
        self.close_cells(params.cell_text_documents)
    }

    #[inline(never)]
    pub(crate) fn test_panic(&mut self, _: ()) -> anyhow::Result<()> {
        panic!("Test Panic in thread {:?}", std::thread::current().id())
    }
}

pub(crate) enum TestPanic {}

impl lsp_types::notification::Notification for TestPanic {
    type Params = ();
    const METHOD: &'static str = "test-panic";
}
