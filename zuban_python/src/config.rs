use std::borrow::Cow;

use ini::Ini;
use toml_edit::{DocumentMut, Item, Table, Value};

use crate::{workspaces::Directory, DiagnosticConfig};

type ConfigResult = Result<bool, String>;

const OPTIONS_STARTING_WITH_ALLOW: [&str; 3] = [
    "allow_untyped_globals",
    "allow_redefinition",
    "allow_empty_bodies",
];

#[derive(Clone)]
pub struct ProjectOptions {
    pub flags: TypeCheckerFlags,
    pub(crate) overrides: Vec<OverrideConfig>,
}

impl ProjectOptions {
    pub fn new(flags: TypeCheckerFlags) -> Self {
        Self {
            flags,
            overrides: vec![],
        }
    }

    pub fn from_mypy_ini(
        path: Box<str>,
        code: &str,
        diagnostic_config: &mut DiagnosticConfig,
    ) -> Result<Self, String> {
        let ini = Ini::load_from_str(code).map_err(|err| err.to_string())?;
        let mut flags = TypeCheckerFlags::default();
        let mut overrides = vec![];
        for (name, section) in ini.iter() {
            let Some(name) = name else { continue };
            if name == "mypy" {
                for (key, value) in section.iter() {
                    apply_from_base_config(
                        &mut flags,
                        diagnostic_config,
                        key,
                        IniOrTomlValue::Ini(value),
                    )?;
                }
            } else if let Some(rest) = name.strip_prefix("mypy-") {
                overrides.push(OverrideConfig {
                    module: rest.into(),
                    config: section
                        .iter()
                        .map(|(x, y)| (x.into(), OverrideIniOrTomlValue::Ini(y.into())))
                        .collect(),
                })
            }
        }
        Ok(ProjectOptions { flags, overrides })
    }

    pub fn from_pyproject_toml(
        path: Box<str>,
        code: &str,
        diagnostic_config: &mut DiagnosticConfig,
    ) -> Result<Self, String> {
        let document = code.parse::<DocumentMut>().map_err(|err| err.to_string())?;
        let mut flags = TypeCheckerFlags::default();
        if let Some(config) = document.get("tool").and_then(|item| item.get("mypy")) {
            let Item::Table(table) = config else {
                return Err("Expected tool.mypy to be a table in pyproject.toml".to_string());
            };

            let mut overrides = vec![];
            for (key, item) in table.iter() {
                match item {
                    Item::Value(value) => {
                        apply_from_base_config(
                            &mut flags,
                            diagnostic_config,
                            key,
                            IniOrTomlValue::Toml(value),
                        )?;
                    }
                    Item::ArrayOfTables(override_tables) if key == "overrides" => {
                        for override_table in override_tables.iter() {
                            for module in pyproject_toml_override_module_names(override_table)? {
                                let mut config = vec![];
                                for (key, part) in override_table.iter() {
                                    if key != "module" {
                                        match part {
                                            Item::Value(v) => {
                                                config.push((key.into(), OverrideIniOrTomlValue::Toml(v.clone())))
                                            }
                                            _ => {
                                                return Err("Found unexpected value in override in pyproject.toml".to_string())
                                            }
                                        }
                                    }
                                }
                                overrides.push(OverrideConfig { module, config })
                            }
                        }
                    }
                    _ => todo!("{item:?}"),
                }
            }
            Ok(ProjectOptions { flags, overrides })
        } else {
            Ok(ProjectOptions::new(TypeCheckerFlags::default()))
        }
    }
}

#[derive(Clone, Hash, PartialEq, Eq)]
pub struct TypeCheckerFlags {
    pub strict_optional: bool,
    pub strict_equality: bool,
    pub implicit_optional: bool,
    pub check_untyped_defs: bool,
    pub ignore_missing_imports: bool,

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
    pub allow_empty_bodies: bool,
    pub warn_unreachable: bool,
    pub warn_redundant_casts: bool,
    pub warn_return_any: bool,
    pub warn_no_return: bool,
    pub local_partial_types: bool,
    pub no_implicit_reexport: bool,
    pub disable_bytearray_promotion: bool,
    pub disable_memoryview_promotion: bool,

    pub platform: Option<String>,
    pub enabled_error_codes: Vec<String>,
    pub disabled_error_codes: Vec<String>,
    pub python_version: PythonVersion,
    pub always_true_symbols: Vec<String>,
    pub always_false_symbols: Vec<String>,
    pub mypy_path: Vec<String>,

    pub extra_checks: bool,
    pub mypy_compatible: bool,
    pub case_sensitive: bool,
}

impl Default for TypeCheckerFlags {
    fn default() -> Self {
        Self {
            strict_optional: true,
            strict_equality: false,
            implicit_optional: false,
            check_untyped_defs: false,
            ignore_missing_imports: false,
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
            allow_untyped_globals: false,
            allow_empty_bodies: false,
            warn_unreachable: false,
            warn_redundant_casts: false,
            warn_return_any: false,
            warn_no_return: true,
            local_partial_types: false,
            no_implicit_reexport: false,
            disable_bytearray_promotion: false,
            disable_memoryview_promotion: false,
            platform: None,
            python_version: PythonVersion::new(3, 12),
            always_true_symbols: vec![],
            always_false_symbols: vec![],
            enabled_error_codes: vec![],
            disabled_error_codes: vec![],
            mypy_path: vec![],
            extra_checks: false,
            mypy_compatible: false,
            case_sensitive: true,
        }
    }
}

impl TypeCheckerFlags {
    pub fn enable_all_strict_flags(&mut self) {
        // Use for --strict
        self.strict_equality = true;
        self.check_untyped_defs = true;
        self.disallow_untyped_defs = true;
        self.disallow_untyped_calls = true;
        self.disallow_any_generics = true;
        self.disallow_any_decorated = true;
        self.disallow_any_explicit = true;
        self.disallow_subclassing_any = true;
        self.disallow_incomplete_defs = true;
        self.warn_redundant_casts = true;
        self.warn_return_any = true;
    }

    pub(crate) fn computed_platform(&self) -> &str {
        self.platform.as_deref().unwrap_or("posix")
    }
}

#[derive(Clone, Hash, PartialEq, Eq, PartialOrd)]
pub struct PythonVersion {
    pub(crate) major: usize,
    pub(crate) minor: usize,
}

impl PythonVersion {
    pub fn new(major: usize, minor: usize) -> Self {
        Self { major, minor }
    }

    pub fn at_least_3_dot(&self, minor: usize) -> bool {
        self.major >= 3 && self.minor >= minor
    }
}

#[derive(Clone)]
struct OverridePath {
    path: Vec<Box<str>>,
    star: bool, // For things like foo.bar.*
}

impl From<&str> for OverridePath {
    fn from(mut value: &str) -> Self {
        let mut star = false;
        if let Some(new_s) = value.strip_suffix(".*") {
            value = new_s;
            star = true;
        }
        OverridePath {
            path: value.split('.').map(|s| s.into()).collect(),
            star,
        }
    }
}

#[derive(Clone)]
enum OverrideIniOrTomlValue {
    Toml(Value),
    Ini(Box<str>),
}

#[derive(Clone)]
pub(crate) struct OverrideConfig {
    module: OverridePath, // Path like foo.bar or foo.bar.*
    // Key/Value mappings
    config: Vec<(Box<str>, OverrideIniOrTomlValue)>,
}

impl OverrideConfig {
    pub fn matches_file_path(&self, name: &str, parent_dir: Option<&Directory>) -> bool {
        fn parent_count(dir: Option<&Directory>) -> usize {
            if let Some(dir) = dir {
                parent_count(dir.parent.maybe_dir().ok().as_deref()) + 1
            } else {
                0
            }
        }
        fn nth_parent<'x>(name: &'x str, dir: Option<&Directory>, n: usize) -> &'x str {
            if n == 0 {
                name
            } else {
                let dir = dir.unwrap();
                nth_parent(
                    // This transmute is fine, because we're only local and the parents will not
                    // change during the parent function.
                    unsafe { std::mem::transmute(dir.name.as_ref()) },
                    dir.parent.maybe_dir().ok().as_deref(),
                    n - 1,
                )
            }
        }
        let actual_path_count = parent_count(parent_dir) + 1;
        if actual_path_count != self.module.path.len() && !self.module.star
            || self.module.path.len() > actual_path_count
        {
            return false;
        }
        for (i, override_part) in self.module.path.iter().enumerate() {
            if override_part.as_ref() != nth_parent(name, parent_dir, actual_path_count - i - 1) {
                return false;
            }
        }
        true
    }

    pub fn apply_to_flags_and_return_ignore_errors(
        &self,
        flags: &mut TypeCheckerFlags,
    ) -> ConfigResult {
        let mut ignore_errors = false;
        for (key, value) in self.config.iter() {
            ignore_errors |= apply_from_config_part(
                flags,
                key,
                match value {
                    OverrideIniOrTomlValue::Toml(v) => IniOrTomlValue::Toml(v),
                    OverrideIniOrTomlValue::Ini(v) => IniOrTomlValue::Ini(v),
                },
            )?;
        }
        Ok(ignore_errors)
    }
}

fn pyproject_toml_override_module_names(table: &Table) -> Result<Vec<OverridePath>, String> {
    match table.get("module") {
        Some(Item::Value(Value::String(s))) => Ok(vec![s.value().as_str().into()]),
        Some(Item::Value(Value::Array(list))) => {
            let mut result = vec![];
            for entry in list {
                match entry {
                    Value::String(s) => result.push(s.value().as_str().into()),
                    _ => return Err("".to_string()),
                }
            }
            Ok(result)
        }
        Some(_) => Err("Unexpected value for module in override in pyproject.toml".to_string()),
        None => Err("Expected a module entry for every override in pyproject.toml".to_string()),
    }
}

#[derive(Debug, Copy, Clone)]
pub enum IniOrTomlValue<'config> {
    Toml(&'config Value),
    Ini(&'config str),
    InlineConfigNoValue,
}

impl IniOrTomlValue<'_> {
    fn as_repr(&self) -> Cow<str> {
        match self {
            Self::Toml(v) => Cow::from(v.to_string()),
            Self::Ini(v) => Cow::Borrowed(v),
            Self::InlineConfigNoValue => Cow::Borrowed("True"),
        }
    }

    fn to_bool(&self, invert: bool) -> Result<bool, String> {
        let result = match self {
            Self::Toml(v) => v.as_bool().unwrap_or_else(|| todo!()),
            Self::Ini(value) => match value.to_lowercase().as_str() {
                "true" | "1" | "yes" | "on" => true,
                "false" | "0" | "no" | "off" => false,
                _ => todo!(),
            },
            Self::InlineConfigNoValue => true,
        };
        Ok(result != invert)
    }

    fn as_mypy_path(&self) -> Result<Vec<String>, String> {
        let split_str = |s| {
            split_and_trim(s, &[',', ':'])
                .map(|x| x.to_string())
                .collect()
        };
        match self {
            Self::Toml(v) => {
                if let Some(s) = v.as_str() {
                    return Ok(split_str(s));
                }
                v.as_array()
                    .ok_or_else(|| "Expected an array or string for mypy_path".to_string())?
                    .iter()
                    .map(|v| {
                        v.as_str()
                            .map(|s| s.to_string())
                            .ok_or_else(|| "".to_string())
                    })
                    .collect()
            }
            Self::Ini(s) => Ok(split_str(s)),
            Self::InlineConfigNoValue => unreachable!(),
        }
    }
}

fn maybe_invert(name: &str) -> (bool, Cow<str>) {
    if let Some(after_no_prefix) = name.strip_prefix("no_") {
        return (true, Cow::Borrowed(after_no_prefix));
    } else if name.starts_with("allow") && !OPTIONS_STARTING_WITH_ALLOW.contains(&name) {
        return (true, Cow::Owned(format!("dis{name}")));
    } else if let Some(after_dis_prefix) = name.strip_prefix("dis") {
        if OPTIONS_STARTING_WITH_ALLOW.contains(&after_dis_prefix) {
            return (true, Cow::Borrowed(after_dis_prefix));
        }
    }
    (false, Cow::Borrowed(name))
}

pub fn set_flag_and_return_ignore_errors(
    flags: &mut TypeCheckerFlags,
    name: &str,
    value: IniOrTomlValue,
) -> ConfigResult {
    let (invert, option_name) = maybe_invert(name);
    let add_list_of_str = |target: &mut Vec<String>| {
        if invert {
            Err(format!("Can not invert non-boolean key {option_name}"))
        } else {
            match &value {
                IniOrTomlValue::Toml(Value::Array(lst)) => {
                    for entry in lst.iter() {
                        match entry {
                            Value::String(s) => target.push(s.value().clone()),
                            _ => return Err("TODO expected string array".to_string()),
                        }
                    }
                    Ok(false)
                }
                IniOrTomlValue::Ini(v) => {
                    target.extend(split_and_trim(v, &[',']).map(String::from));
                    Ok(false)
                }
                _ => Err("TODO expected string".to_string()),
            }
        }
    };
    match option_name.as_ref() {
        "always_true" => add_list_of_str(&mut flags.always_true_symbols),
        "always_false" => add_list_of_str(&mut flags.always_false_symbols),
        "enable_error_code" => add_list_of_str(&mut flags.enabled_error_codes),
        "disable_error_code" => add_list_of_str(&mut flags.disabled_error_codes),
        "strict" => Err(concat!(
            r#"Setting "strict" not supported in inline configuration: "#,
            r#"specify it in a configuration file instead, or set individual "#,
            r#"inline flags (see "mypy -h" for the list of flags enabled in strict mode)"#
        )
        .into()),
        _ => set_bool_init_flags(flags, name, &option_name, value, invert),
    }
}

fn set_bool_init_flags(
    flags: &mut TypeCheckerFlags,
    original_name: &str,
    name: &str,
    value: IniOrTomlValue,
    invert: bool,
) -> ConfigResult {
    match name {
        "strict_optional" => flags.strict_optional = value.to_bool(invert)?,
        "strict_equality" => flags.strict_equality = value.to_bool(invert)?,
        "implicit_optional" => flags.implicit_optional = value.to_bool(invert)?,
        "check_untyped_defs" => flags.check_untyped_defs = value.to_bool(invert)?,
        "ignore_missing_imports" => flags.ignore_missing_imports = value.to_bool(invert)?,

        "disallow_untyped_defs" => flags.disallow_untyped_defs = value.to_bool(invert)?,
        "disallow_untyped_calls" => flags.disallow_untyped_calls = value.to_bool(invert)?,
        "disallow_untyped_decorators" => {
            flags.disallow_untyped_decorators = value.to_bool(invert)?
        }
        "disallow_any_generics" => flags.disallow_any_generics = value.to_bool(invert)?,
        "disallow_any_decorated" => flags.disallow_any_decorated = value.to_bool(invert)?,
        "disallow_any_explicit" => flags.disallow_any_explicit = value.to_bool(invert)?,
        "disallow_any_unimported" => flags.disallow_any_unimported = value.to_bool(invert)?,
        "disallow_any_expr" => flags.disallow_any_expr = value.to_bool(invert)?,
        "disallow_subclassing_any" => flags.disallow_subclassing_any = value.to_bool(invert)?,
        "disallow_incomplete_defs" => flags.disallow_incomplete_defs = value.to_bool(invert)?,
        "allow_untyped_globals" => flags.allow_untyped_globals = value.to_bool(invert)?,
        "allow_empty_bodies" => flags.allow_empty_bodies = value.to_bool(invert)?,
        "warn_unreachable" => flags.warn_unreachable = value.to_bool(invert)?,
        "warn_return_any" => flags.warn_return_any = value.to_bool(invert)?,
        "warn_no_return" => flags.warn_no_return = value.to_bool(invert)?,
        "local_partial_types" => flags.local_partial_types = value.to_bool(invert)?,
        "implicit_reexport" => flags.no_implicit_reexport = !value.to_bool(invert)?,

        "extra_checks" => flags.extra_checks = value.to_bool(invert)?,
        // These are currently ignored
        "allow_redefinition" | "follow_imports" | "follow_imports_for_stubs" => (),
        // Will always be irrelevant
        "cache_fine_grained" => (),
        "ignore_errors" => return value.to_bool(invert),
        _ => {
            return Err(format!(
                "Unrecognized option: {} = {}",
                original_name,
                value.as_repr()
            ))
        }
    }
    Ok(false)
}

fn split_and_trim<'a>(s: &'a str, pattern: &'a [char]) -> impl Iterator<Item = &'a str> {
    let mut s = s.trim();
    if let Some(new_s) = s.strip_suffix(pattern) {
        s = new_s
    }
    s.split(pattern).map(|s| s.trim())
}

fn apply_from_base_config(
    flags: &mut TypeCheckerFlags,
    diagnostic_config: &mut DiagnosticConfig,
    key: &str,
    value: IniOrTomlValue,
) -> ConfigResult {
    match key {
        "show_error_codes" => {
            diagnostic_config.show_error_codes = value.to_bool(false)?;
            Ok(false)
        }
        "show_column_numbers" => {
            diagnostic_config.show_column_numbers = value.to_bool(false)?;
            Ok(false)
        }
        "show_error_end" => {
            diagnostic_config.show_error_end = value.to_bool(false)?;
            Ok(false)
        }
        // Currently ignored, but need to use in the future.
        "mypy_path" => {
            flags.mypy_path.extend(value.as_mypy_path()?);
            Ok(false)
        }
        _ => apply_from_config_part(flags, key, value),
    }
}

fn apply_from_config_part(
    flags: &mut TypeCheckerFlags,
    key: &str,
    value: IniOrTomlValue,
) -> ConfigResult {
    if key == "strict" {
        if value.to_bool(false).unwrap_or_else(|_| todo!()) {
            flags.enable_all_strict_flags();
        }
        Ok(false)
    } else {
        set_flag_and_return_ignore_errors(flags, key, value)
    }
}
