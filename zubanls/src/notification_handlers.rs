use lsp_types::{
    DidChangeTextDocumentParams, DidCloseTextDocumentParams, DidOpenTextDocumentParams,
    DidSaveTextDocumentParams,
};

use crate::server::GlobalState;

impl GlobalState {
    pub(crate) fn handle_did_open_text_document(
        state: &mut GlobalState,
        params: DidOpenTextDocumentParams,
    ) -> anyhow::Result<()> {
        let _p = tracing::info_span!("handle_did_open_text_document").entered();
        /*

        if let Ok(path) = from_proto::vfs_path(&params.text_document.uri) {
            let already_exists = state
                .mem_docs
                .insert(
                    path.clone(),
                    DocumentData::new(
                        params.text_document.version,
                        params.text_document.text.clone().into_bytes(),
                    ),
                )
                .is_err();
            if already_exists {
                tracing::error!("duplicate DidOpenTextDocument: {}", path);
            }

            tracing::info!("New file content set {:?}", params.text_document.text);
            state.vfs.write().0.set_file_contents(path, Some(params.text_document.text.into_bytes()));
            /*
            if state.config.discover_workspace_config().is_some() {
                tracing::debug!("queuing task");
                let _ = state
                    .deferred_task_queue
                    .sender
                    .send(crate::main_loop::QueuedTask::CheckIfIndexed(params.text_document.uri));
            }
            */
        }
        */
        Ok(())
    }

    pub(crate) fn handle_did_change_text_document(
        state: &mut GlobalState,
        params: DidChangeTextDocumentParams,
    ) -> anyhow::Result<()> {
        todo!()
    }

    pub(crate) fn handle_did_close_text_document(
        state: &mut GlobalState,
        params: DidCloseTextDocumentParams,
    ) -> anyhow::Result<()> {
        todo!()
    }

    pub(crate) fn handle_did_save_text_document(
        state: &mut GlobalState,
        params: DidSaveTextDocumentParams,
    ) -> anyhow::Result<()> {
        todo!()
    }
}
