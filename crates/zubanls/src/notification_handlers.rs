use anyhow::bail;
use lsp_types::{
    DidChangeTextDocumentParams, DidCloseTextDocumentParams, DidOpenTextDocumentParams,
};

use crate::server::GlobalState;

impl GlobalState<'_> {
    pub(crate) fn handle_did_open_text_document(
        &mut self,
        params: DidOpenTextDocumentParams,
    ) -> anyhow::Result<()> {
        let _p = tracing::info_span!("handle_did_open_text_document").entered();
        let path = self.uri_to_path(&params.text_document.uri);
        tracing::info!("Opening {path}");
        self.project()
            .load_in_memory_file(path.into(), params.text_document.text.into());
        Ok(())
    }

    pub(crate) fn handle_did_change_text_document(
        &mut self,
        params: DidChangeTextDocumentParams,
    ) -> anyhow::Result<()> {
        let _p = tracing::info_span!("handle_did_change_text_document").entered();
        let path = self.uri_to_path(&params.text_document.uri);
        tracing::info!("Changing {path}");

        let len = params.content_changes.len();
        if len == 0 {
            bail!("Expected there to be at least one config change")
        }
        /*
         * TODO do something like this (check rust-analyzer as a reference)
        let Some(code) = self.project().code_of_in_memory_file(path) else {
            bail!("Should be an in memory file, because we have opened it before")
        };
        let code = apply_document_changes(encoding, code, params.content_changes);
        */
        let change = params.content_changes.into_iter().next().unwrap();
        if len != 1 || change.range.is_some() || change.range_length.is_some() {
            bail!(
                "Expected there to be exactly one content change, because we \
                   don't support TextDocumentSyncKind::INCREMENTAL yet"
            )
        }
        self.project()
            .load_in_memory_file(path.into(), change.text.into());
        Ok(())
    }

    pub(crate) fn handle_did_close_text_document(
        &mut self,
        params: DidCloseTextDocumentParams,
    ) -> anyhow::Result<()> {
        let _p = tracing::info_span!("handle_did_change_text_document").entered();
        let path = self.uri_to_path(&params.text_document.uri);
        tracing::info!("Closing {path}");
        let result = self
            .project()
            .unload_in_memory_file(path)
            .map_err(|err| anyhow::anyhow!("{err}"));
        result
    }

    pub(crate) fn test_panic(&mut self, _: ()) -> anyhow::Result<()> {
        panic!("Test Panic")
    }
}

pub(crate) enum TestPanic {}

impl lsp_types::notification::Notification for TestPanic {
    type Params = ();
    const METHOD: &'static str = "test-panic";
}
