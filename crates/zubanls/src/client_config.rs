use serde::Deserialize;

#[derive(Default, Deserialize, Debug)]
pub(crate) struct ClientConfig {
    pub zuban: ZubanClientConfig,
}

#[derive(Clone, Copy, Deserialize, Default, PartialEq, Eq, Debug)]
#[serde(rename_all = "kebab-case")]
pub(crate) enum TypeCheckingMode {
    #[default]
    Auto,
    Default,
    Mypy,
    Off,
}

impl TypeCheckingMode {
    pub fn is_enabled(self) -> bool {
        !matches!(self, Self::Off)
    }
}

#[derive(Clone, Copy, Deserialize, Default, PartialEq, Eq, Debug)]
pub(crate) enum DiagnosticMode {
    #[default]
    #[serde(rename = "openFilesOnly")]
    OpenFilesOnly,
    /// Compute and publish diagnostics for all files in the workspace, not just open files.
    #[serde(rename = "workspace")]
    Workspace,
}

#[derive(Default, Deserialize, Debug)]
#[serde(rename_all = "camelCase")]
pub(crate) struct ZubanClientConfig {
    /// Default mode to use if there is no explicit Zuban config in `pyproject.toml`.
    pub type_checking_mode: TypeCheckingMode,
    pub diagnostic_mode: DiagnosticMode,
    pub disable_language_services: bool,
}
