mod searcher;
mod venv;

use std::{borrow::Cow, sync::Arc};

use anyhow::{anyhow, bail};
use clap::ValueEnum as _;
use ini::{Ini, ParseOption};
use regex::Regex;
use toml_edit::{DocumentMut, Item, Table, Value};
use vfs::{AbsPath, Directory, GlobAbsPath, LocalFS, NormalizedPath, VfsHandler};

pub use searcher::{find_cli_config, find_workspace_config};

type ConfigResult = anyhow::Result<()>;

const OPTIONS_STARTING_WITH_ALLOW: [&str; 4] = [
    "allow_untyped_globals",
    "allow_redefinition",
    "allow_redefinition_new",
    "allow_empty_bodies",
];

pub struct DiagnosticConfig {
    pub show_error_codes: bool,
    pub show_error_end: bool,
    pub show_column_numbers: bool,
    pub pretty: bool,
    pub error_summary: bool,
}

impl Default for DiagnosticConfig {
    fn default() -> Self {
        Self {
            show_error_codes: true,
            show_error_end: false,
            show_column_numbers: false,
            pretty: false,
            error_summary: true,
        }
    }
}

#[derive(Clone, Default, Debug)]
pub struct ProjectOptions {
    pub settings: Settings,
    pub flags: TypeCheckerFlags,
    pub overrides: Vec<OverrideConfig>,
}

#[derive(Copy, Clone, Debug, PartialEq, Eq, Hash, clap::ValueEnum)]
pub enum Mode {
    Mypy,
    Default,
}

#[derive(Copy, Clone, Hash, PartialEq, Eq, Debug, clap::ValueEnum)]
pub enum UntypedFunctionReturnMode {
    Any,
    Inferred,
    Advanced,
}

#[derive(Clone, Hash, PartialEq, Eq, Debug)]
pub struct Settings {
    pub platform: Option<String>,
    pub python_version: Option<PythonVersion>,
    pub environment: Option<Arc<NormalizedPath>>,
    pub mypy_path: Vec<Arc<NormalizedPath>>,
    pub prepended_site_packages: Vec<Arc<NormalizedPath>>,
    /// Global packages are added by default (if we are not in a venv)
    pub add_global_packages_default: bool,
    pub mode: Mode,
    pub untyped_function_return_mode: UntypedFunctionReturnMode,
    pub exclude_gitignore: bool, // From Mypy's --exclude_gitignore
    // These are absolute paths.
    pub files_or_directories_to_check: Vec<GlobAbsPath>,
    pub typeshed_path: Option<Arc<NormalizedPath>>,
}

impl Default for Settings {
    fn default() -> Self {
        Self {
            platform: None,
            python_version: None,
            environment: None,
            typeshed_path: std::env::var("ZUBAN_TYPESHED")
                .ok()
                .map(|p| LocalFS::without_watcher().normalized_path_from_current_dir(&p)),
            mypy_path: vec![],
            add_global_packages_default: true,
            mode: Mode::Default,
            untyped_function_return_mode: UntypedFunctionReturnMode::Inferred,
            exclude_gitignore: true,
            files_or_directories_to_check: vec![],
            prepended_site_packages: vec![],
        }
    }
}

impl Settings {
    pub fn computed_platform(&self) -> &str {
        self.platform.as_deref().unwrap_or(if cfg!(windows) {
            "win32"
        } else if cfg!(any(target_os = "macos", target_os = "ios")) {
            "darwin"
        } else {
            "linux"
        })
    }

    #[inline]
    pub fn mypy_compatible(&self) -> bool {
        matches!(self.mode, Mode::Mypy)
    }

    pub fn python_version_or_default(&self) -> PythonVersion {
        self.python_version
            .unwrap_or_else(|| PythonVersion::new(3, 14))
    }

    pub fn apply_python_executable(
        &mut self,
        handler: &dyn VfsHandler,
        project_dir: &AbsPath,
        config_file_path: Option<&AbsPath>,
        python_executable: &str,
    ) -> anyhow::Result<()> {
        const ERR: &str = "Expected a python-executable to be at least two directories deep";
        let python_executable =
            to_normalized_path(handler, project_dir, config_file_path, python_executable);
        let Some(executable_dir) = python_executable.as_ref().as_ref().parent() else {
            bail!(ERR)
        };
        let environment = executable_dir.parent().map(|p| {
            let p = p
                .as_os_str()
                .to_str()
                .expect("Should never happen, because we only put together valid unicode paths");
            handler.unchecked_normalized_path(handler.unchecked_abs_path(p))
        });
        if environment.is_none() {
            bail!(ERR)
        }
        self.environment = environment;
        Ok(())
    }

    pub fn set_files_or_directories_to_check(
        &mut self,
        handler: &dyn VfsHandler,
        project_dir: &AbsPath,
        config_file_path: Option<&AbsPath>,
        items: impl IntoIterator<Item = String>,
    ) -> anyhow::Result<()> {
        self.files_or_directories_to_check = items
            .into_iter()
            .map(|s| {
                GlobAbsPath::new(
                    handler,
                    project_dir,
                    &replace_env_vars(config_file_path, &s),
                )
            })
            .collect::<anyhow::Result<Vec<_>>>()?;
        Ok(())
    }

    #[inline]
    pub fn should_infer_return_types(&self) -> bool {
        !matches!(
            self.untyped_function_return_mode,
            UntypedFunctionReturnMode::Any
        )
    }

    #[inline]
    pub fn should_infer_untyped_params(&self) -> bool {
        matches!(
            self.untyped_function_return_mode,
            UntypedFunctionReturnMode::Advanced
        )
    }
}

fn to_normalized_path(
    handler: &dyn VfsHandler,
    project_dir: &AbsPath,
    config_file_path: Option<&AbsPath>,
    s: &str,
) -> Arc<NormalizedPath> {
    // Replace only $MYPY_CONFIG_FILE_DIR for now.
    handler.normalize_rc_path(if s.contains('$') {
        handler.absolute_path(project_dir, &replace_env_vars(config_file_path, s))
    } else {
        handler.absolute_path(project_dir, s)
    })
}

fn replace_env_vars<'x>(config_file_path: Option<&AbsPath>, s: &'x str) -> Cow<'x, str> {
    // Replace only $MYPY_CONFIG_FILE_DIR for now.
    if s.contains('$')
        && let Some(config_file_path) = config_file_path
        && let Some(mypy_config_file_dir) = config_file_path.as_ref().parent()
    {
        return Cow::Owned(s.replace(
            "$MYPY_CONFIG_FILE_DIR",
            mypy_config_file_dir.to_str().unwrap(),
        ));
    }
    Cow::Borrowed(s)
}

impl ProjectOptions {
    pub fn new(settings: Settings, flags: TypeCheckerFlags) -> Self {
        Self {
            settings,
            flags,
            overrides: vec![],
        }
    }

    pub fn default_for_mode(mode: Mode) -> Self {
        if matches!(mode, Mode::Mypy) {
            ProjectOptions::mypy_default()
        } else {
            ProjectOptions::default()
        }
    }

    pub fn mypy_default() -> Self {
        Self {
            settings: Settings {
                mode: Mode::Mypy,
                untyped_function_return_mode: UntypedFunctionReturnMode::Any,
                exclude_gitignore: false,
                ..Default::default()
            },
            flags: TypeCheckerFlags::mypy_default(),
            overrides: Default::default(),
        }
    }

    pub fn from_mypy_ini(
        vfs: &dyn VfsHandler,
        project_dir: &AbsPath,
        config_file_path: &AbsPath,
        code: &str,
        diagnostic_config: &mut DiagnosticConfig,
    ) -> anyhow::Result<Option<Self>> {
        let ini = parse_python_ini(code)?;
        let mut result = Self::mypy_default();
        let mut had_relevant_section = false;
        for (name, section) in ini.iter() {
            let Some(name) = name else { continue };
            if name == "mypy" {
                had_relevant_section = true;
                for (key, value) in section.iter() {
                    apply_from_base_config(
                        vfs,
                        project_dir,
                        Some(config_file_path),
                        &mut result.settings,
                        &mut result.flags,
                        diagnostic_config,
                        key,
                        IniOrTomlValue::Ini(value),
                        false,
                    )?;
                }
            } else if let Some(rest) = name.strip_prefix("mypy-") {
                had_relevant_section = true;
                for rest in rest.split(',') {
                    result.overrides.push(OverrideConfig {
                        module: rest.into(),
                        config: section
                            .iter()
                            .map(|(x, y)| (x.into(), OverrideIniOrTomlValue::Ini(y.into())))
                            .collect(),
                    })
                }
            }
        }
        order_overrides_for_priority(&mut result.overrides);
        Ok(had_relevant_section.then_some(result))
    }

    pub fn from_pyproject_toml_only(
        vfs: &dyn VfsHandler,
        project_dir: &AbsPath,
        config_file_path: &AbsPath,
        code: &str,
        diagnostic_config: &mut DiagnosticConfig,
        mut mode: Option<Mode>,
    ) -> anyhow::Result<Option<Self>> {
        let document: DocumentMut = code.parse()?;
        let zuban_config = document.get("tool").and_then(|item| item.get("zuban"));
        if let Some(Item::Table(table)) = zuban_config
            && let Some(item) = table.get("mode")
            && let Some(value) = item.as_value()
        {
            mode = Some(
                Mode::from_str(IniOrTomlValue::Toml(value).as_str()?, false)
                    .map_err(|err| map_clap_error("mode", err))?,
            );
        }
        let result = Self::apply_pyproject_toml_mypy_part(
            vfs,
            project_dir,
            config_file_path,
            &document,
            diagnostic_config,
            mode,
        )?;
        Ok(if let Some(config) = zuban_config {
            let mut result =
                result.unwrap_or_else(|| Self::default_for_mode(mode.unwrap_or(Mode::Default)));
            result.apply_pyproject_table(
                vfs,
                project_dir,
                config_file_path,
                diagnostic_config,
                config,
                true,
            )?;
            Some(result)
        } else {
            result
        })
    }

    pub fn apply_pyproject_toml_mypy_part(
        vfs: &dyn VfsHandler,
        project_dir: &AbsPath,
        config_file_path: &AbsPath,
        document: &DocumentMut,
        diagnostic_config: &mut DiagnosticConfig,
        mode: Option<Mode>,
    ) -> anyhow::Result<Option<Self>> {
        if let Some(config) = document.get("tool").and_then(|item| item.get("mypy")) {
            // If an explicit mode is provided, use that, otherwise since we have an explicit Mypy
            // configuration we default to that.
            let mut result = ProjectOptions::default_for_mode(mode.unwrap_or(Mode::Mypy));
            result.apply_pyproject_table(
                vfs,
                project_dir,
                config_file_path,
                diagnostic_config,
                config,
                false,
            )?;
            Ok(Some(result))
        } else {
            Ok(None)
        }
    }

    fn apply_pyproject_table(
        &mut self,
        vfs: &dyn VfsHandler,
        project_dir: &AbsPath,
        config_file_path: &AbsPath,
        diagnostic_config: &mut DiagnosticConfig,
        config: &Item,
        from_zuban: bool,
    ) -> anyhow::Result<()> {
        let Item::Table(table) = config else {
            bail!(
                "Expected tool.{} to be a table in pyproject.toml",
                match from_zuban {
                    true => "zuban",
                    false => "mypy",
                }
            );
        };

        for (key, item) in table.iter() {
            match item {
                Item::Value(value) => {
                    apply_from_base_config(
                        vfs,
                        project_dir,
                        Some(config_file_path),
                        &mut self.settings,
                        &mut self.flags,
                        diagnostic_config,
                        key,
                        IniOrTomlValue::Toml(value),
                        from_zuban,
                    )?;
                }
                Item::ArrayOfTables(override_tables) if key == "overrides" => {
                    for override_table in override_tables.iter() {
                        for module in pyproject_toml_override_module_names(override_table)? {
                            let mut config = vec![];
                            for (key, part) in override_table.iter() {
                                if key != "module" {
                                    match part {
                                        Item::Value(v) => config.push((
                                            key.into(),
                                            OverrideIniOrTomlValue::Toml(v.clone()),
                                        )),
                                        _ => {
                                            bail!("Found unexpected value in override in pyproject.toml".to_string())
                                        }
                                    }
                                }
                            }
                            self.overrides.push(OverrideConfig { module, config })
                        }
                    }
                }
                Item::None | Item::Table(_) | Item::ArrayOfTables(_) => {
                    bail!(
                        "Expected tool.{} to be a simple table in pyproject.toml",
                        match from_zuban {
                            true => "zuban",
                            false => "mypy",
                        }
                    );
                }
            }
        }
        order_overrides_for_priority(&mut self.overrides);
        Ok(())
    }
}

fn parse_python_ini(code: &str) -> anyhow::Result<Ini> {
    let options = ParseOption {
        indented_multiline_values: true,
        ..Default::default()
    };
    Ok(Ini::load_from_str_opt(code, options)?)
}

fn order_overrides_for_priority(overrides: &mut [OverrideConfig]) {
    // The overrides with the highest priorities should be last, because they overwrite the flags
    // for a file at the end
    overrides.sort_by_key(|o| o.module.kind);
}

#[derive(Debug, Clone, Hash, PartialEq, Eq)]
pub struct TypeCheckerFlags {
    pub ignore_errors: bool,
    pub strict_optional: bool,
    pub strict_equality: bool,
    pub implicit_optional: bool,
    pub check_untyped_defs: bool,
    pub ignore_missing_imports: bool,
    pub follow_untyped_imports: bool,

    pub disallow_untyped_defs: bool,
    pub disallow_untyped_calls: bool,
    pub disallow_untyped_decorators: bool,
    pub disallow_any_generics: bool,
    pub disallow_any_decorated: bool,
    pub disallow_any_explicit: bool,
    pub disallow_any_unimported: bool,
    pub disallow_any_expr: bool,
    pub disallow_subclassing_any: bool,
    pub disallow_incomplete_defs: bool,
    pub allow_untyped_globals: bool,
    pub allow_redefinition: bool,
    pub allow_empty_bodies: bool,
    pub warn_unreachable: bool,
    pub warn_redundant_casts: bool,
    pub warn_return_any: bool,
    pub warn_no_return: bool,
    pub local_partial_types: bool,
    pub no_implicit_reexport: bool,
    pub disable_bytearray_promotion: bool,
    pub disable_memoryview_promotion: bool,

    pub enabled_error_codes: Vec<String>,
    pub disabled_error_codes: Vec<String>,
    pub always_true_symbols: Vec<String>,
    pub always_false_symbols: Vec<String>,
    pub excludes: Vec<ExcludeRegex>,

    pub extra_checks: bool,
    pub case_sensitive: bool,

    // Non-mypy settings
    pub use_joins: bool,
    pub disallow_deprecated: bool,
    pub allow_incomplete_generics: bool,
    pub check_untyped_overrides: bool,
    pub untyped_strict_optional: bool,
}

impl Default for TypeCheckerFlags {
    fn default() -> Self {
        Self {
            ignore_errors: false,
            strict_optional: true,
            strict_equality: false,
            implicit_optional: false,
            check_untyped_defs: true,
            ignore_missing_imports: false,
            follow_untyped_imports: true,
            disallow_untyped_defs: false,
            disallow_untyped_calls: false,
            disallow_untyped_decorators: false,
            disallow_any_generics: false,
            disallow_any_decorated: false,
            disallow_any_explicit: false,
            disallow_any_unimported: false,
            disallow_any_expr: false,
            disallow_subclassing_any: false,
            disallow_incomplete_defs: false,
            allow_untyped_globals: true,
            allow_empty_bodies: false,
            allow_redefinition: true,
            warn_unreachable: true,
            warn_redundant_casts: false,
            warn_return_any: false,
            warn_no_return: false,
            local_partial_types: true,
            no_implicit_reexport: false,
            disable_bytearray_promotion: false,
            disable_memoryview_promotion: false,
            excludes: vec![],
            always_true_symbols: vec![],
            always_false_symbols: vec![],
            enabled_error_codes: vec![],
            disabled_error_codes: vec![],
            extra_checks: false,
            case_sensitive: true,
            use_joins: false,
            disallow_deprecated: false,
            allow_incomplete_generics: false,
            check_untyped_overrides: false,
            untyped_strict_optional: false,
        }
    }
}

impl TypeCheckerFlags {
    pub fn enable_all_strict_flags(&mut self) {
        // Use for --strict
        // self.warn_unused_configs = true;
        self.disallow_any_generics = true;
        self.disallow_subclassing_any = true;
        self.disallow_untyped_calls = true;
        self.disallow_untyped_defs = true;
        self.disallow_incomplete_defs = true;
        self.check_untyped_defs = true;
        self.disallow_untyped_decorators = true;
        self.warn_redundant_casts = true;
        // self.warn_unused_ignores = true;
        self.warn_return_any = true;
        self.no_implicit_reexport = true;
        self.strict_equality = true;
        self.allow_untyped_globals = false; // This is mostly important for --mode default
        self.extra_checks = true;
        self.allow_incomplete_generics = false;
        self.untyped_strict_optional = true;
    }

    pub fn enable_strict_bytes(&mut self) {
        self.disable_bytearray_promotion = true;
        self.disable_memoryview_promotion = true;
    }

    pub fn mypy_default() -> Self {
        Self {
            check_untyped_defs: false,
            allow_redefinition: false,
            local_partial_types: false,
            allow_untyped_globals: false,
            use_joins: true,
            warn_unreachable: false,
            warn_no_return: true,
            follow_untyped_imports: false,
            untyped_strict_optional: true,
            ..Default::default()
        }
    }

    pub fn finalize(mut self) -> FinalizedTypeCheckerFlags {
        if !self.disallow_deprecated && self.enabled_error_codes.iter().any(|s| s == "deprecated") {
            self.disallow_deprecated = true;
        }
        FinalizedTypeCheckerFlags(self)
    }
}

#[derive(Copy, Clone, Hash, PartialEq, Eq, PartialOrd, Debug)]
pub struct PythonVersion {
    pub major: usize,
    pub minor: usize,
}

impl PythonVersion {
    pub fn new(major: usize, minor: usize) -> Self {
        Self { major, minor }
    }

    pub fn at_least_3_dot(&self, minor: usize) -> bool {
        self.major >= 3 && self.minor >= minor
    }
}

impl std::str::FromStr for PythonVersion {
    type Err = anyhow::Error;

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        let error = "Expected a dot separated python version like 3.13";
        let Some((major, mut minor)) = s.split_once(".") else {
            bail!(error);
        };
        if let Some((new_minor, _patch)) = minor.split_once(".") {
            minor = new_minor;
        };
        Ok(Self {
            major: major
                .parse()
                .map_err(|i| anyhow::anyhow!("{error} ({i})"))?,
            minor: minor
                .parse()
                .map_err(|i| anyhow::anyhow!("{error} ({i})"))?,
        })
    }
}

#[derive(Debug, Clone)]
pub struct ExcludeRegex {
    pub regex_str: String,
    pub regex: Regex,
}

impl ExcludeRegex {
    pub fn new(regex_str: String) -> Result<Self, regex::Error> {
        let regex = Regex::new(&regex_str)?;
        Ok(Self { regex_str, regex })
    }
}

impl std::cmp::PartialEq for ExcludeRegex {
    fn eq(&self, other: &Self) -> bool {
        self.regex_str == other.regex_str
    }
}
impl std::cmp::Eq for ExcludeRegex {}
impl std::hash::Hash for ExcludeRegex {
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
        self.regex_str.hash(state)
    }
}

// These are the overrides with the precedence order as described in https://mypy.readthedocs.io/en/stable/config_file.html#config-file-format
#[derive(PartialOrd, Ord, PartialEq, Eq, Copy, Clone, Debug)]
enum OverrideKind {
    WellStructured, // e.g. foo.bar.*
    Unstructured,   // e.g. foo.*.baz
    ModuleName,     // e.g. foo.bar (has the highest priority
}

#[derive(Clone, Debug)]
enum OverridePathPart {
    Part(Box<str>),
    Wildcard,
}

#[derive(Clone, Debug)]
pub struct OverridePath {
    path: Vec<OverridePathPart>,
    kind: OverrideKind,
}

impl From<&str> for OverridePath {
    fn from(value: &str) -> Self {
        let mut had_star = false;
        let mut had_name_after_star = false;
        let path = value
            .split('.')
            .map(|s| match s {
                "*" => {
                    had_star = true;
                    OverridePathPart::Wildcard
                }
                _ => {
                    had_name_after_star |= had_star;
                    OverridePathPart::Part(s.into())
                }
            })
            .collect();
        let kind = if had_name_after_star {
            OverrideKind::Unstructured
        } else if had_star {
            OverrideKind::WellStructured
        } else {
            OverrideKind::ModuleName
        };
        OverridePath { path, kind }
    }
}

impl OverridePath {
    pub fn matches_file_path(&self, name: &str, parent_dir: Option<&Directory>) -> bool {
        fn matches_file_path<'x>(
            mut reverse_path: impl Iterator<Item = &'x OverridePathPart> + Clone,
            name: &str,
            parent_dir: Option<&Directory>,
        ) -> bool {
            let Some(part) = reverse_path.next() else {
                return false;
            };
            match part {
                OverridePathPart::Part(part) => {
                    name == &**part && {
                        if let Some(dir) = parent_dir {
                            matches_file_path(
                                reverse_path,
                                &dir.name,
                                dir.parent.maybe_dir().ok().as_deref(),
                            )
                        } else {
                            reverse_path.next().is_none()
                        }
                    }
                }
                OverridePathPart::Wildcard => {
                    fn check_wildcard_parents<'x>(
                        mut reverse_path: impl Iterator<Item = &'x OverridePathPart> + Clone,
                        name: &str,
                        parent_dir: Option<&Directory>,
                    ) -> bool {
                        if matches_file_path(reverse_path.clone(), name, parent_dir) {
                            return true;
                        }
                        if let Some(dir) = parent_dir {
                            check_wildcard_parents(
                                reverse_path,
                                &dir.name,
                                dir.parent.maybe_dir().ok().as_deref(),
                            )
                        } else {
                            reverse_path.next().is_none()
                        }
                    }
                    check_wildcard_parents(reverse_path, name, parent_dir)
                }
            }
        }
        matches_file_path(self.path.iter().rev(), name, parent_dir)
    }
}

#[derive(Clone, Debug)]
enum OverrideIniOrTomlValue {
    Toml(Value),
    Ini(Box<str>),
}

#[derive(Clone, Debug)]
pub struct OverrideConfig {
    pub module: OverridePath, // Path like foo.bar or foo.bar.*
    // Key/Value mappings
    config: Vec<(Box<str>, OverrideIniOrTomlValue)>,
}

impl OverrideConfig {
    pub fn apply_to_flags(&self, flags: &mut TypeCheckerFlags) -> ConfigResult {
        for (key, value) in self.config.iter() {
            apply_from_config_part(
                flags,
                key,
                match value {
                    OverrideIniOrTomlValue::Toml(v) => IniOrTomlValue::Toml(v),
                    OverrideIniOrTomlValue::Ini(v) => IniOrTomlValue::Ini(v),
                },
                false,
            )?;
        }
        Ok(())
    }
}

fn pyproject_toml_override_module_names(table: &Table) -> anyhow::Result<Vec<OverridePath>> {
    match table.get("module") {
        Some(Item::Value(Value::String(s))) => Ok(vec![s.value().as_str().into()]),
        Some(Item::Value(Value::Array(list))) => {
            let mut result = vec![];
            for entry in list {
                match entry {
                    Value::String(s) => result.push(s.value().as_str().into()),
                    _ => bail!("Expected string in module list, but found {entry}"),
                }
            }
            Ok(result)
        }
        Some(_) => bail!("Unexpected value for module in override in pyproject.toml"),
        None => bail!("Expected a module entry for every override in pyproject.toml"),
    }
}

#[derive(Debug, Copy, Clone)]
pub enum IniOrTomlValue<'config> {
    Toml(&'config Value),
    Ini(&'config str),
    InlineConfigNoValue,
}

impl IniOrTomlValue<'_> {
    fn as_repr(&self) -> Cow<'_, str> {
        match self {
            Self::Toml(v) => Cow::from(v.to_string()),
            Self::Ini(v) => Cow::Borrowed(v),
            Self::InlineConfigNoValue => Cow::Borrowed("True"),
        }
    }

    fn as_bool(&self, invert: bool) -> anyhow::Result<bool> {
        let result = match self {
            Self::Toml(v) => v
                .as_bool()
                .ok_or_else(|| anyhow::anyhow!("Expected bool, got {}", v.to_string().trim()))?,
            Self::Ini(value) => match value.to_lowercase().as_str() {
                "true" | "1" | "yes" | "on" => true,
                "false" | "0" | "no" | "off" => false,
                _ => bail!("Expected bool, got \"{value}\""),
            },
            Self::InlineConfigNoValue => true,
        };
        Ok(result != invert)
    }

    fn as_str(&self) -> anyhow::Result<&str> {
        match self {
            Self::Toml(v) => v
                .as_str()
                .ok_or_else(|| anyhow::anyhow!("Expected str, got {}", v.to_string().trim())),
            Self::Ini(s) => Ok(s),
            Self::InlineConfigNoValue => unreachable!(),
        }
    }

    fn as_str_list(&self, key: &str, split_on: &[char]) -> anyhow::Result<Vec<String>> {
        let split_str = |s| split_and_trim(s, split_on).map(|x| x.to_string()).collect();
        match self {
            Self::Toml(v) => {
                if let Some(s) = v.as_str() {
                    return Ok(split_str(s));
                }
                v.as_array()
                    .ok_or_else(|| anyhow::anyhow!("Expected an array or string for {key}"))?
                    .iter()
                    .map(|v| {
                        v.as_str()
                            .map(|s| s.to_string())
                            .ok_or_else(|| anyhow::anyhow!("TODO error"))
                    })
                    .collect()
            }
            Self::Ini(s) => Ok(split_str(s)),
            Self::InlineConfigNoValue => unreachable!(),
        }
    }
}

fn maybe_invert(name: &str) -> (bool, Cow<'_, str>) {
    if let Some(after_no_prefix) = name.strip_prefix("no_") {
        return (true, Cow::Borrowed(after_no_prefix));
    } else if name.starts_with("allow") && !OPTIONS_STARTING_WITH_ALLOW.contains(&name) {
        return (true, Cow::Owned(format!("dis{name}")));
    } else if let Some(after_dis_prefix) = name.strip_prefix("dis")
        && OPTIONS_STARTING_WITH_ALLOW.contains(&after_dis_prefix)
    {
        return (true, Cow::Borrowed(after_dis_prefix));
    }
    (false, Cow::Borrowed(name))
}

pub fn set_flag(
    flags: &mut TypeCheckerFlags,
    name: &str,
    value: IniOrTomlValue,
    add_error_if_unrecognized_option: bool,
) -> ConfigResult {
    let (invert, option_name) = maybe_invert(name);
    let add_list_of_str = |target: &mut Vec<String>| {
        if invert {
            bail!("Can not invert non-boolean key {option_name}")
        } else {
            match &value {
                IniOrTomlValue::Toml(Value::Array(lst)) => {
                    for entry in lst.iter() {
                        match entry {
                            Value::String(s) => target.push(s.value().clone()),
                            _ => bail!("TODO expected string array for {name}"),
                        }
                    }
                    Ok(())
                }
                IniOrTomlValue::Toml(Value::String(s)) => {
                    // Apparently Mypy allows single strings for things like
                    //
                    //     enable_error_code = "ignore-without-code"
                    target.push(s.value().clone());
                    Ok(())
                }
                IniOrTomlValue::Ini(v) => {
                    target.extend(split_and_trim(v, &[',']).map(String::from));
                    Ok(())
                }
                _ => bail!("TODO expected string for {name}"),
            }
        }
    };
    match option_name.as_ref() {
        "exclude" => {
            if invert {
                bail!("Can not invert non-boolean key {option_name}")
            }
            add_excludes(&mut flags.excludes, value)
        }
        "always_true" => add_list_of_str(&mut flags.always_true_symbols),
        "always_false" => add_list_of_str(&mut flags.always_false_symbols),
        "enable_error_code" => add_list_of_str(&mut flags.enabled_error_codes),
        "disable_error_code" => add_list_of_str(&mut flags.disabled_error_codes),
        "strict" => bail!(concat!(
            r#"Setting "strict" not supported in inline configuration: "#,
            r#"specify it in a configuration file instead, or set individual "#,
            r#"inline flags (see "mypy -h" for the list of flags enabled in strict mode)"#
        )),
        _ => set_bool_init_flags(
            flags,
            name,
            &option_name,
            value,
            invert,
            add_error_if_unrecognized_option,
        ),
    }
}

fn set_bool_init_flags(
    flags: &mut TypeCheckerFlags,
    original_name: &str,
    name: &str,
    value: IniOrTomlValue,
    invert: bool,
    add_error_if_unrecognized_option: bool,
) -> ConfigResult {
    match name {
        "strict_optional" => flags.strict_optional = value.as_bool(invert)?,
        "strict_equality" => flags.strict_equality = value.as_bool(invert)?,
        "implicit_optional" => flags.implicit_optional = value.as_bool(invert)?,
        "check_untyped_defs" => flags.check_untyped_defs = value.as_bool(invert)?,
        "ignore_missing_imports" => flags.ignore_missing_imports = value.as_bool(invert)?,
        "follow_untyped_imports" => flags.follow_untyped_imports = value.as_bool(invert)?,

        "disallow_untyped_defs" => flags.disallow_untyped_defs = value.as_bool(invert)?,
        "disallow_untyped_calls" => flags.disallow_untyped_calls = value.as_bool(invert)?,
        "disallow_untyped_decorators" => {
            flags.disallow_untyped_decorators = value.as_bool(invert)?
        }
        "disallow_any_generics" => flags.disallow_any_generics = value.as_bool(invert)?,
        "disallow_any_decorated" => flags.disallow_any_decorated = value.as_bool(invert)?,
        "disallow_any_explicit" => flags.disallow_any_explicit = value.as_bool(invert)?,
        "disallow_any_unimported" => flags.disallow_any_unimported = value.as_bool(invert)?,
        "disallow_any_expr" => flags.disallow_any_expr = value.as_bool(invert)?,
        "disallow_subclassing_any" => flags.disallow_subclassing_any = value.as_bool(invert)?,
        "disallow_incomplete_defs" => flags.disallow_incomplete_defs = value.as_bool(invert)?,
        "allow_untyped_globals" => flags.allow_untyped_globals = value.as_bool(invert)?,
        "allow_empty_bodies" => flags.allow_empty_bodies = value.as_bool(invert)?,
        "warn_unreachable" => flags.warn_unreachable = value.as_bool(invert)?,
        "warn_return_any" => flags.warn_return_any = value.as_bool(invert)?,
        "warn_no_return" => flags.warn_no_return = value.as_bool(invert)?,
        "local_partial_types" => flags.local_partial_types = value.as_bool(invert)?,
        "implicit_reexport" => flags.no_implicit_reexport = !value.as_bool(invert)?,
        "allow_redefinition" | "allow_redefinition_new" => {
            flags.allow_redefinition = value.as_bool(invert)?
        }
        "disable_bytearray_promotion" => {
            flags.disable_bytearray_promotion = value.as_bool(invert)?
        }
        "disable_memoryview_promotion" => {
            flags.disable_memoryview_promotion = value.as_bool(invert)?
        }
        "warn_unused_ignores"
        | "strict_concatenate"
        | "strict_bytes"
        | "strict_equality_for_none" => {
            tracing::warn!("Ignored config value {name}, please contact support if you need them");
        }
        "sqlite_cache" | "incremental" => (), // This doesn't matter
        // Probably doesn't matter
        "force_uppercase_builtins" | "force_union_syntax" | "verbosity" | "color_output" => (),

        "extra_checks" => flags.extra_checks = value.as_bool(invert)?,
        // These are currently ignored
        "follow_imports" | "follow_imports_for_stubs" => (),
        // Will always be irrelevant
        "cache_fine_grained" => (),
        "ignore_errors" => {
            flags.ignore_errors = value.as_bool(invert)?;
        }
        "python_version" => bail!("python_version not supported in inline configuration"),

        // Our own
        "untyped_strict_optional" => flags.untyped_strict_optional = value.as_bool(invert)?,
        _ => {
            if add_error_if_unrecognized_option {
                bail!("Unrecognized option: {original_name} = {}", value.as_repr());
            } else {
                tracing::warn!(
                    "Unsupported option given in Mypy config: {original_name} = {}, contact support if you need it",
                    value.as_repr()
                );
            }
        }
    }
    Ok(())
}

fn split_and_trim<'a>(s: &'a str, pattern: &'a [char]) -> impl Iterator<Item = &'a str> {
    let mut s = s.trim();
    if let Some(new_s) = s.strip_suffix(pattern) {
        s = new_s
    }
    s.split(pattern).map(|s| s.trim())
}

fn map_clap_error(arg: &str, err: String) -> anyhow::Error {
    anyhow!("Error while parsing {arg}: {err}")
}

#[expect(clippy::too_many_arguments)]
fn apply_from_base_config(
    vfs: &dyn VfsHandler,
    project_dir: &AbsPath,
    config_file_path: Option<&AbsPath>,
    settings: &mut Settings,
    flags: &mut TypeCheckerFlags,
    diagnostic_config: &mut DiagnosticConfig,
    key: &str,
    value: IniOrTomlValue,
    from_zuban: bool,
) -> ConfigResult {
    match key {
        "show_error_codes" => {
            diagnostic_config.show_error_codes = value.as_bool(false)?;
        }
        "show_column_numbers" => {
            diagnostic_config.show_column_numbers = value.as_bool(false)?;
        }
        "show_error_end" => {
            diagnostic_config.show_error_end = value.as_bool(false)?;
        }
        "pretty" => {
            diagnostic_config.pretty = value.as_bool(false)?;
        }
        "exclude_gitignore" => {
            settings.exclude_gitignore = value.as_bool(false)?;
        }
        "no_error_summary" => {
            diagnostic_config.error_summary = value.as_bool(true)?;
        }
        "show_error_context"
        | "show_traceback"
        | "plugins"
        | "enable_incomplete_feature"
        | "show_error_code_links"
        | "cache_dir"
        | "warn_redundant_casts"
        | "warn_unused_configs" => {
            tracing::warn!("TODO ignored config value {key}");
        }
        "files" => settings.set_files_or_directories_to_check(
            vfs,
            project_dir,
            config_file_path,
            value.as_str_list(key, &[','])?,
        )?,
        "mypy_path" => settings.mypy_path.extend(
            value
                .as_str_list(key, &[',', ':'])?
                .into_iter()
                .map(|s| to_normalized_path(vfs, project_dir, config_file_path, &s)),
        ),
        "python_executable" => {
            settings.apply_python_executable(vfs, project_dir, config_file_path, value.as_str()?)?
        }
        "python_version" => {
            settings.python_version = Some(if let IniOrTomlValue::Toml(Value::Float(f)) = &value {
                f.display_repr().parse()?
            } else {
                value.as_str()?.parse()?
            })
        }
        "platform" => settings.platform = Some(value.as_str()?.to_string()),
        // Our own
        "mode" => (), // Already checked earlier
        "untyped_function_return_mode" => {
            settings.untyped_function_return_mode =
                UntypedFunctionReturnMode::from_str(value.as_str()?, false)
                    .map_err(|err| map_clap_error("untyped_function_return_mode", err))?;
        }
        _ => return apply_from_config_part(flags, key, value, from_zuban),
    };
    Ok(())
}

fn apply_from_config_part(
    flags: &mut TypeCheckerFlags,
    key: &str,
    value: IniOrTomlValue,
    from_zuban: bool,
) -> ConfigResult {
    if key == "strict" {
        if value.as_bool(false)? {
            flags.enable_all_strict_flags();
        }
        Ok(())
    } else {
        set_flag(flags, key, value, from_zuban)
    }
}

fn add_excludes(excludes: &mut Vec<ExcludeRegex>, value: IniOrTomlValue) -> ConfigResult {
    let mut compile_str = |s| match Regex::new(s) {
        Ok(regex) => {
            excludes.push(ExcludeRegex {
                regex_str: s.into(),
                regex,
            });
            Ok(())
        }
        Err(err) => bail!(err),
    };
    match &value {
        IniOrTomlValue::Toml(Value::Array(lst)) => {
            for entry in lst.iter() {
                match entry {
                    Value::String(s) => {
                        compile_str(s.value())?;
                    }
                    _ => bail!("TODO expected string array".to_string()),
                }
            }
            Ok(())
        }
        IniOrTomlValue::Toml(Value::String(s)) => compile_str(s.value()),
        IniOrTomlValue::Ini(v) => compile_str(v),
        _ => bail!("TODO expected string"),
    }
}

#[derive(Debug, Clone, Hash, PartialEq, Eq)]
pub struct FinalizedTypeCheckerFlags(TypeCheckerFlags);

impl FinalizedTypeCheckerFlags {
    pub fn into_unfinalized(self) -> TypeCheckerFlags {
        self.0
    }
}

impl std::ops::Deref for FinalizedTypeCheckerFlags {
    type Target = TypeCheckerFlags;

    fn deref(&self) -> &Self::Target {
        &self.0
    }
}

#[cfg(test)]
mod tests {
    use vfs::LocalFS;

    use super::*;

    fn project_options(code: &str, from_ini: bool) -> anyhow::Result<Option<ProjectOptions>> {
        let local_fs = LocalFS::without_watcher();
        let project_dir = local_fs.unchecked_abs_path("/foo");
        if from_ini {
            ProjectOptions::from_mypy_ini(
                &local_fs,
                &project_dir,
                &project_dir,
                code,
                &mut DiagnosticConfig::default(),
            )
        } else {
            ProjectOptions::from_pyproject_toml_only(
                &local_fs,
                &project_dir,
                &project_dir,
                code,
                &mut DiagnosticConfig::default(),
                None,
            )
        }
    }
    fn project_options_valid(code: &str, from_ini: bool) -> ProjectOptions {
        project_options(code, from_ini).unwrap().unwrap()
    }

    fn project_options_err(code: &str, from_ini: bool) -> anyhow::Error {
        let opts = project_options(code, from_ini);
        let Err(err) = opts else { unreachable!() };
        err
    }

    #[test]
    fn test_invalid_toml_bool() {
        let code = "\
            [tool.mypy]\n\
            disallow_any_generics = \"what\"
        ";
        let err = project_options_err(code, false);
        assert_eq!(err.to_string(), "Expected bool, got \"what\"");
    }

    #[test]
    fn test_invalid_ini_bool() {
        let code = "\
            [mypy]\n\
            disallow_any_generics = what
        ";
        let err = project_options_err(code, true);
        assert_eq!(err.to_string(), "Expected bool, got \"what\"");
    }

    #[test]
    fn test_invalid_toml_none() {
        let code = "[tool.mypy.foo]\nx=1";
        let err = project_options_err(code, false);
        assert_eq!(
            err.to_string(),
            "Expected tool.mypy to be a simple table in pyproject.toml"
        );
    }

    #[test]
    fn test_invalid_settings_type() {
        let code = "[tool.mypy]\npython_executable=1";
        let err = project_options_err(code, false);
        assert_eq!(err.to_string(), "Expected str, got 1");
    }

    #[test]
    fn test_python_executable_invalid() {
        let code = "[mypy]\npython_executable = /settings";
        let err = project_options_err(code, true);
        assert_eq!(
            err.to_string(),
            "Expected a python-executable to be at least two directories deep"
        );
    }

    #[test]
    fn test_python_executable_valid() {
        let code = "[mypy]\npython_executable = /some/path/bin/python";
        let opts = project_options_valid(code, true);
        let path = opts.settings.environment.as_ref().unwrap();
        if cfg!(target_os = "windows") {
            assert_eq!(****path, *"\\some\\path");
        } else {
            assert_eq!(****path, *"/some/path");
        }
    }

    #[test]
    fn test_python_version_valid_mypy_ini() {
        let code = "[mypy]\npython_version = 3.1";
        let opts = project_options_valid(code, true);
        let version = &opts.settings.python_version.unwrap();
        assert_eq!(version.major, 3);
        assert_eq!(version.minor, 1);
    }

    #[test]
    fn test_python_version_invalid_mypy_ini() {
        let code = "[mypy]\npython_version = hello";
        let err = project_options_err(code, true);
        assert_eq!(
            err.to_string(),
            "Expected a dot separated python version like 3.13"
        );
    }

    #[test]
    fn test_python_version_valid_pyproject_toml() {
        let code = "[tool.mypy]\npython_version = '3.1'";
        let opts = project_options_valid(code, false);
        let version = &opts.settings.python_version.unwrap();
        assert_eq!(version.major, 3);
        assert_eq!(version.minor, 1);
    }

    #[test]
    fn test_parse_python_version() {
        use std::str::FromStr;
        assert_eq!(
            PythonVersion::from_str("3.12").unwrap(),
            PythonVersion::new(3, 12)
        );
        assert_eq!(
            PythonVersion::from_str("3.12.42").unwrap(),
            PythonVersion::new(3, 12)
        );
    }

    #[test]
    fn test_python_version_valid_pyproject_toml_float() {
        let check = |major, minor| {
            let code = format!("[tool.mypy]\npython_version = {major}.{minor}");
            let opts = project_options_valid(&code, false);
            let version = &opts.settings.python_version.unwrap();
            assert_eq!(version.major, major);
            assert_eq!(version.minor, minor);
        };
        check(3, 0);
        check(3, 1);
        check(3, 10);
        check(3, 100);
        check(3, 101);
    }

    #[test]
    fn test_python_version_invalid_pyproject_toml() {
        let code = "[tool.mypy]\npython_version = false";
        let err = project_options_err(code, false);
        assert_eq!(err.to_string(), "Expected str, got false");
    }

    #[test]
    fn test_platform_valid() {
        let code = "[mypy]\nplatform = foo";
        let opts = project_options_valid(code, true);
        assert_eq!(opts.settings.platform.unwrap(), "foo");
    }

    #[test]
    fn test_platform_error() {
        let code = "[tool.mypy]\nplatform = false";
        let err = project_options_err(code, false);
        assert_eq!(err.to_string(), "Expected str, got false");
    }
}
