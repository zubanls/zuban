use anyhow::bail;
use lsp_types::{
    DidChangeNotebookDocumentParams, DidChangeTextDocumentParams, DidCloseNotebookDocumentParams,
    DidCloseTextDocumentParams, DidOpenNotebookDocumentParams, DidOpenTextDocumentParams,
    NotebookCell, NotebookCellKind, TextDocumentContentChangeEvent, TextDocumentIdentifier,
    TextDocumentItem, Uri, VersionedTextDocumentIdentifier,
};
use vfs::PathWithScheme;

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
        let encoding = self.client_capabilities.negotiated_encoding();
        let project = self.project();
        let path = Self::uri_to_path(project, text_document.uri)?;
        tracing::info!("Changing document {}", path.as_uri());
        project
            .store_file_with_lsp_changes(path, content_changes, |pos| encoding.input_position(pos))
    }

    fn store_in_memory_file(&mut self, uri: lsp_types::Uri, code: Box<str>) -> anyhow::Result<()> {
        let project = self.project();
        let path = Self::uri_to_path(project, uri)?;
        tracing::info!("Loading {}", path.as_uri());
        project.store_in_memory_file(path, code);
        Ok(())
    }

    fn store_in_memory_file_with_parent(
        &mut self,
        path: PathWithScheme,
        code: Box<str>,
        parent: Option<PathWithScheme>,
    ) -> anyhow::Result<()> {
        let project = self.project();
        tracing::info!("Loading {}", path.as_uri());
        if let Some(parent) = parent {
            project.store_in_memory_file_with_parent(path, code, &parent)
        } else {
            project.store_in_memory_file(path, code);
            Ok(())
        }
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
        self.notebooks
            .add_notebook(params.notebook_document.uri.clone());
        self.new_cells(
            &params.notebook_document.uri,
            params.notebook_document.cells,
            params.cell_text_documents,
            0,
        )?;
        Ok(())
    }

    fn new_cells(
        &mut self,
        notebook: &Uri,
        cells: Vec<NotebookCell>,
        mut text_documents: Vec<TextDocumentItem>,
        start_at_nth_cell: usize,
    ) -> anyhow::Result<()> {
        for (i, cell) in cells.into_iter().enumerate() {
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
            let project = self.project();
            let path = Self::uri_to_path(project, cell.document)?;
            let maybe_parent = self.notebooks.add_cell_and_return_parent(
                notebook,
                path.clone(),
                start_at_nth_cell + i,
            )?;
            self.store_in_memory_file_with_parent(path, doc_item.text.into(), maybe_parent)?;
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
            let start = structure.array.start as usize;
            let new_end = start
                + structure
                    .array
                    .cells
                    .as_ref()
                    .map(|v| v.len())
                    .unwrap_or_default();
            if let Some(closed) = structure.did_close {
                result = self.close_cells(closed);
                self.notebooks.remove_cells(
                    &params.notebook_document.uri,
                    start..start + structure.array.delete_count as usize,
                )?;
            }
            if let Some(cells) = structure.array.cells {
                self.new_cells(
                    &params.notebook_document.uri,
                    cells,
                    structure.did_open.unwrap_or_default(),
                    start,
                )?
            }
            if let Some(child) = self
                .notebooks
                .nth_cell(&params.notebook_document.uri, new_end)?
            {
                let Some(code) = self.project().code_of_in_memory_file(&child) else {
                    bail!("Expected to find code for the latest child {child:?}");
                };
                let code = code.into();
                let parent = self
                    .notebooks
                    .nth_cell(&params.notebook_document.uri, new_end)?
                    .unwrap();
                // TODO this is not optimal, we should probably not clone the code again for an
                // entry that is already there.
                self.store_in_memory_file_with_parent(child, code, Some(parent))?;
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
        let result = self.close_cells(params.cell_text_documents);
        self.notebooks.close_notebook(params.notebook_document.uri);
        result
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
