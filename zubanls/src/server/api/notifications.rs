use lsp_server::ErrorCode;
use lsp_types::{
    notification::{
        DidChangeTextDocument, DidCloseTextDocument, DidCloseTextDocumentParams, SetTrace,
    },
    DidChangeTextDocumentParams, SetTraceParams,
};
use red_knot_workspace::watch::ChangeEvent;
use zuban_db::Db;

use crate::server::api::diagnostics::clear_diagnostics;
use crate::server::api::traits::{NotificationHandler, SyncNotificationHandler};
use crate::server::api::LSPResult;
use crate::server::client::{Notifier, Requester};
use crate::server::Result;
use crate::session::Session;
use crate::system::{url_to_any_system_path, AnySystemPath};
use crate::TextDocument;

pub(crate) struct DidChangeTextDocumentHandler;

impl NotificationHandler for DidChangeTextDocumentHandler {
    type NotificationType = DidChangeTextDocument;
}

impl SyncNotificationHandler for DidChangeTextDocumentHandler {
    fn run(
        session: &mut Session,
        _notifier: Notifier,
        _requester: &mut Requester,
        params: DidChangeTextDocumentParams,
    ) -> Result<()> {
        let Ok(path) = url_to_any_system_path(&params.text_document.uri) else {
            return Ok(());
        };

        session
            .update_text_document(
                &params.text_document.uri,
                params.content_changes,
                params.text_document.version,
            )
            .with_failure_code(ErrorCode::InternalError)?;

        match path {
            AnySystemPath::System(path) => {
                let db = match session.workspace_db_for_path_mut(path.as_std_path()) {
                    Some(db) => db,
                    None => session.default_workspace_db_mut(),
                };
                db.apply_changes(vec![ChangeEvent::file_content_changed(path)], None);
            }
            AnySystemPath::SystemVirtual(virtual_path) => {
                let db = session.default_workspace_db_mut();
                db.apply_changes(vec![ChangeEvent::ChangedVirtual(virtual_path)], None);
            }
        }

        // TODO(dhruvmanila): Publish diagnostics if the client doesn't support pull diagnostics

        Ok(())
    }
}

pub(crate) struct DidCloseTextDocumentHandler;

impl NotificationHandler for DidCloseTextDocumentHandler {
    type NotificationType = DidCloseTextDocument;
}

impl SyncNotificationHandler for DidCloseTextDocumentHandler {
    fn run(
        session: &mut Session,
        notifier: Notifier,
        _requester: &mut Requester,
        params: DidCloseTextDocumentParams,
    ) -> Result<()> {
        let Ok(path) = url_to_any_system_path(&params.text_document.uri) else {
            return Ok(());
        };

        session
            .close_document(&params.text_document.uri)
            .with_failure_code(ErrorCode::InternalError)?;

        if let AnySystemPath::SystemVirtual(virtual_path) = path {
            let db = session.default_workspace_db_mut();
            db.apply_changes(vec![ChangeEvent::DeletedVirtual(virtual_path)], None);
        }

        clear_diagnostics(key.url(), &notifier)?;

        Ok(())
    }
}

pub(crate) struct DidOpenTextDocumentHandler;

impl NotificationHandler for DidOpenTextDocumentHandler {
    type NotificationType = DidOpenTextDocument;
}

impl SyncNotificationHandler for DidOpenTextDocumentHandler {
    fn run(
        session: &mut Session,
        _notifier: Notifier,
        _requester: &mut Requester,
        params: DidOpenTextDocumentParams,
    ) -> Result<()> {
        let Ok(path) = url_to_any_system_path(&params.text_document.uri) else {
            return Ok(());
        };

        let document = TextDocument::new(params.text_document.text, params.text_document.version);
        session.open_text_document(params.text_document.uri, document);

        match path {
            AnySystemPath::System(path) => {
                let db = match session.workspace_db_for_path_mut(path.as_std_path()) {
                    Some(db) => db,
                    None => session.default_workspace_db_mut(),
                };
                db.apply_changes(vec![ChangeEvent::Opened(path)], None);
            }
            AnySystemPath::SystemVirtual(virtual_path) => {
                let db = session.default_workspace_db_mut();
                db.files().virtual_file(db, &virtual_path);
            }
        }

        // TODO(dhruvmanila): Publish diagnostics if the client doesn't support pull diagnostics

        Ok(())
    }
}

pub(crate) struct SetTraceHandler;

impl NotificationHandler for SetTraceHandler {
    type NotificationType = SetTrace;
}

impl SyncNotificationHandler for SetTraceHandler {
    fn run(
        _session: &mut Session,
        _notifier: Notifier,
        _requester: &mut Requester,
        params: SetTraceParams,
    ) -> Result<()> {
        crate::trace::set_trace_value(params.value);
        Ok(())
    }
}
