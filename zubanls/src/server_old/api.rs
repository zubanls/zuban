use lsp_server as server;

use crate::server::schedule::Task;
use crate::session::Session;
use crate::system::{url_to_any_system_path, AnySystemPath};

mod diagnostics;
mod notifications;
mod requests;

use notifications as notification;
use requests as request;

use self::traits::{NotificationHandler, RequestHandler};

use super::{client::Responder, schedule::BackgroundSchedule, Result};

/// Sends back a response to the server using a [`Responder`].
fn respond<Req>(
    id: server::RequestId,
    result: crate::server::Result<
        <<Req as traits::RequestHandler>::RequestType as lsp_types::request::Request>::Result,
    >,
    responder: &Responder,
) where
    Req: traits::RequestHandler,
{
    if let Err(err) = &result {
        tracing::error!("An error occurred with result ID {id}: {err}");
        show_err_msg!("ZubanLS encountered a problem. Check the logs for more details.");
    }
    if let Err(err) = responder.respond(id, result) {
        tracing::error!("Failed to send response: {err}");
    }
}

/// Tries to cast a serialized request from the server into
/// a parameter type for a specific request handler.
fn cast_notification<N>(
    notification: server::Notification,
) -> super::Result<
    (
        &'static str,
        <<N as traits::NotificationHandler>::NotificationType as lsp_types::notification::Notification>::Params,
)> where N: traits::NotificationHandler{
    Ok((
        N::METHOD,
        notification
            .extract(N::METHOD)
            .map_err(|err| match err {
                json_err @ server::ExtractError::JsonError { .. } => {
                    anyhow::anyhow!("JSON parsing failure:\n{json_err}")
                }
                server::ExtractError::MethodMismatch(_) => {
                    unreachable!("A method mismatch should not be possible here unless you've used a different handler (`N`) \
                        than the one whose method name was matched against earlier.")
                }
            })
            .with_failure_code(server::ErrorCode::InternalError)?,
    ))
}
