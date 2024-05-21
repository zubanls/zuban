use std::borrow::Cow;

use ini::Ini;
use toml_edit::{DocumentMut, Item, TomlError, Value};

const OPTIONS_STARTING_WITH_ALLOW: [&str; 3] = [
    "allow_untyped_globals",
    "allow_redefinition",
    "allow_empty_bodies",
];

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

    pub extra_checks: bool,
    pub mypy_compatible: bool,
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
            extra_checks: false,
            mypy_compatible: false,
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

    pub fn from_mypy_ini(code: &str) -> Result<Self, ini::ParseError> {
        let ini = Ini::load_from_str(code)?;
        let mut flags = Self::default();
        if let Some(section) = ini.section(Some("mypy")) {
            for (key, value) in section.iter() {
                apply_from_config(&mut flags, key, IniOrTomlValue::Ini(value));
            }
        }
        Ok(flags)
    }

    pub fn from_pyproject_toml(code: &str) -> Result<Self, TomlError> {
        let document = code.parse::<DocumentMut>()?;
        let mut flags = Self::default();
        if let Some(config) = document.get("tool").and_then(|item| item.get("mypy")) {
            let Item::Table(table) = config else {
                todo!();
            };
            for (key, item) in table.iter() {
                match item {
                    Item::Value(value) => {
                        apply_from_config(&mut flags, key, IniOrTomlValue::Toml(value))
                    }
                    Item::ArrayOfTables(_) => (), // Implement per file
                    _ => todo!("{item:?}"),
                }
            }
        }
        Ok(flags)
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

    pub fn to_bool(&self, invert: bool) -> Result<bool, Box<str>> {
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
}

pub fn set_flag(
    flags: &mut TypeCheckerFlags,
    name: &str,
    value: IniOrTomlValue,
) -> Result<(), Box<str>> {
    let (invert, option_name) = maybe_invert(name);
    let add_list_of_str = |target: &mut Vec<String>| {
        if invert {
            Err(format!("Can not invert non-boolean key {option_name}").into())
        } else {
            match &value {
                IniOrTomlValue::Toml(Value::Array(lst)) => {
                    for entry in lst.iter() {
                        match entry {
                            Value::String(s) => target.push(s.value().clone()),
                            _ => return Err(Box::from("TODO expected string array")),
                        }
                    }
                    Ok(())
                }
                IniOrTomlValue::Ini(v) => {
                    target.extend(split_commas(v).map(|s| String::from(s)));
                    Ok(())
                }
                _ => Err(Box::from("TODO expected string")),
            }
        }
    };
    match option_name.as_ref() {
        "always_true" => add_list_of_str(&mut flags.always_true_symbols),
        "always_false" => add_list_of_str(&mut flags.always_false_symbols),
        "enable_error_code" => add_list_of_str(&mut flags.enabled_error_codes),
        "disable_error_code" => add_list_of_str(&mut flags.disabled_error_codes),
        "ignore_errors" => Ok(()), // TODO
        "strict" => {
            return Err(concat!(
                r#"Setting "strict" not supported in inline configuration: "#,
                r#"specify it in a configuration file instead, or set individual "#,
                r#"inline flags (see "mypy -h" for the list of flags enabled in strict mode)"#
            )
            .into())
        }
        _ => {
            return set_bool_init_flags(flags, name, &option_name, value, invert);
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

fn set_bool_init_flags(
    flags: &mut TypeCheckerFlags,
    original_name: &str,
    name: &str,
    value: IniOrTomlValue,
    invert: bool,
) -> Result<(), Box<str>> {
    match name {
        "strict_equality" => flags.strict_equality = value.to_bool(invert)?,
        "strict_optional" => flags.strict_optional = value.to_bool(invert)?,
        "warn_no_return" => flags.warn_no_return = value.to_bool(invert)?,
        "disallow_any_generics" => flags.disallow_any_generics = value.to_bool(invert)?,
        "disallow_incomplete_defs" => flags.disallow_incomplete_defs = value.to_bool(invert)?,
        "disallow_subclassing_any" => flags.disallow_subclassing_any = value.to_bool(invert)?,
        "disallow_untyped_calls" => flags.disallow_untyped_calls = value.to_bool(invert)?,
        "allow_untyped_globals" => flags.allow_untyped_globals = value.to_bool(invert)?,
        "ignore_missing_imports" => flags.ignore_missing_imports = value.to_bool(invert)?,
        "local_partial_types" => flags.local_partial_types = value.to_bool(invert)?,
        "implicit_reexport" => flags.no_implicit_reexport = !value.to_bool(invert)?,
        "implicit_optional" => flags.implicit_optional = value.to_bool(invert)?,
        // These are currently ignored
        "follow_imports" | "follow_imports_for_stubs" => (),
        // Will always be irrelevant
        "cache_fine_grained" => (),
        _ => {
            return Err(format!(
                "Unrecognized option: {} = {}",
                original_name,
                value.as_repr()
            )
            .into())
        }
    }
    Ok(())
}

fn split_commas(s: &str) -> impl Iterator<Item = &str> {
    let mut s = s.trim();
    if let Some(new_s) = s.strip_suffix(',') {
        s = new_s
    }
    s.split(',').map(|s| s.trim())
}

fn apply_from_config(flags: &mut TypeCheckerFlags, key: &str, value: IniOrTomlValue) {
    if key == "show_error_codes" {
        // This is currently not handled here but in diagnostics config
        return;
    }
    if key == "strict" {
        if value.to_bool(false).unwrap_or_else(|_| todo!()) {
            flags.enable_all_strict_flags();
        }
    } else {
        set_flag(flags, key, value).unwrap_or_else(|_| todo!("key: {key:?}, value: {value:?}"))
    }
}
