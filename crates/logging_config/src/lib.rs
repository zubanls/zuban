//! Simple logger that logs either to stderr or to a file, using `tracing_subscriber`
//! filter syntax and `tracing_appender` for non blocking output.
//! This was initially copied from rust-analyzer's crate `rust-analyzer/tracing`.

mod hprof;

use std::{
    env, fs,
    path::PathBuf,
    sync::{Arc, Once},
};

use anyhow::Context;
use tracing::level_filters::LevelFilter;
use tracing_subscriber::{
    filter::Targets,
    fmt::{time, writer::BoxMakeWriter, MakeWriter, TestWriter},
    layer::SubscriberExt,
    Layer, Registry,
};

pub fn setup_logging(log_file_flag: Option<PathBuf>) -> anyhow::Result<()> {
    if cfg!(windows) {
        // This is required so that windows finds our pdb that is placed right beside the exe.
        // By default it doesn't look at the folder the exe resides in, only in the current working
        // directory which we set to the project workspace.
        // https://docs.microsoft.com/en-us/windows-hardware/drivers/debugger/general-environment-variables
        // https://docs.microsoft.com/en-us/windows/win32/api/dbghelp/nf-dbghelp-syminitialize
        if let Ok(path) = env::current_exe() {
            if let Some(path) = path.parent() {
                env::set_var("_NT_SYMBOL_PATH", path);
            }
        }
    }

    let log_file = env::var("ZUBAN_LOG_FILE")
        .ok()
        .map(PathBuf::from)
        .or(log_file_flag);
    let log_file = match log_file {
        Some(path) => {
            if let Some(parent) = path.parent() {
                let _ = fs::create_dir_all(parent);
            }
            Some(
                fs::File::create(&path)
                    .with_context(|| format!("can't create log file at {}", path.display()))?,
            )
        }
        None => None,
    };

    let writer = match log_file {
        Some(file) => BoxMakeWriter::new(Arc::new(file)),
        None => BoxMakeWriter::new(std::io::stderr),
    };

    Config {
        writer,
        // Deliberately enable all `error` logs if the user has not set ZUBAN_LOG, as there is
        // usually useful information in there for debugging.
        filter: env::var("ZUBAN_LOG")
            .ok()
            .unwrap_or_else(|| "error".to_owned()),
        profile_filter: env::var("ZUBAN_PROFILE").ok(),
    }
    .init()
}

pub fn setup_logging_for_tests() {
    static INIT: Once = Once::new();
    INIT.call_once(|| {
        Config {
            writer: TestWriter::default(),
            // Deliberately enable all `warning` logs if the user has not set ZUBAN_LOG, as there
            // is usually useful information in there for debugging.
            filter: std::env::var("ZUBAN_LOG")
                .ok()
                .unwrap_or_else(|| "warning".to_owned()),
            profile_filter: std::env::var("ZUBAN_PROFILE").ok(),
        }
        .init()
        .expect("Expect to be able to initialize logging for tests");
    });
}

#[derive(Debug)]
struct Config<T> {
    writer: T,
    filter: String,
    /// Filtering syntax, set in a shell:
    /// ```bash
    /// env ZUBAN_PROFILE=*             // dump everything
    /// env ZUBAN_PROFILE=foo|bar|baz   // enabled only selected entries
    /// env ZUBAN_PROFILE=*@3>10        // dump everything, up to depth 3, if it takes more than 10
    /// ```
    profile_filter: Option<String>,
}

impl<T> Config<T>
where
    T: for<'writer> MakeWriter<'writer> + Send + Sync + 'static,
{
    fn init(self) -> anyhow::Result<()> {
        let targets_filter: Targets = self
            .filter
            .parse()
            .with_context(|| format!("invalid log filter: `{}`", self.filter))?;

        let writer = self.writer;

        let ra_fmt_layer = tracing_subscriber::fmt::layer()
            .with_target(false)
            .with_ansi(false)
            .with_writer(writer);

        let ra_fmt_layer = match time::OffsetTime::local_rfc_3339() {
            Ok(timer) => {
                // If we can get the time offset, format logs with the timezone.
                ra_fmt_layer.with_timer(timer).boxed()
            }
            Err(_) => {
                // Use system time if we can't get the time offset. This should
                // never happen on Linux, but can happen on e.g. OpenBSD.
                ra_fmt_layer.boxed()
            }
        }
        .with_filter(targets_filter);

        // TODO: remove `.with_filter(LevelFilter::OFF)` on the `None` branch.
        let profiler_layer = match self.profile_filter {
            Some(spec) => Some(hprof::SpanTree::new(&spec)).with_filter(LevelFilter::INFO),
            None => None.with_filter(LevelFilter::OFF),
        };

        let subscriber = Registry::default().with(ra_fmt_layer).with(profiler_layer);

        tracing::subscriber::set_global_default(subscriber)?;

        Ok(())
    }
}
