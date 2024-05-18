use std::borrow::Cow;

use crate::TypeCheckerFlags;

const OPTIONS_STARTING_WITH_ALLOW: [&str; 3] = [
    "allow_untyped_globals",
    "allow_redefinition",
    "allow_empty_bodies",
];

pub fn set_flag<'x>(
    flags: &mut TypeCheckerFlags,
    name: &str,
    value: Option<&str>,
) -> Result<(), Box<str>> {
    let (invert, option_name) = maybe_invert(name);
    let expect_value = || {
        if invert {
            Err(format!("Can not invert non-boolean key {option_name}").into())
        } else {
            value.ok_or_else(|| Box::from("TODO string"))
        }
    };
    match option_name.as_ref() {
        "always_true" => flags
            .always_true_symbols
            .extend(split_commas(expect_value()?).map(|s| s.into())),
        "always_false" => flags
            .always_false_symbols
            .extend(split_commas(expect_value()?).map(|s| s.into())),
        "enable_error_code" => flags
            .enabled_error_codes
            .extend(split_commas(expect_value()?).map(|s| s.into())),
        "disable_error_code" => flags
            .disabled_error_codes
            .extend(split_commas(expect_value()?).map(|s| s.into())),
        "ignore_errors" => (), // TODO
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
    Ok(())
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
    value: Option<&str>,
    invert: bool,
) -> Result<(), Box<str>> {
    match name {
        "strict_equality" => flags.strict_equality = to_bool(value, invert)?,
        "strict_optional" => flags.strict_optional = to_bool(value, invert)?,
        "warn_no_return" => flags.warn_no_return = to_bool(value, invert)?,
        "disallow_any_generics" => flags.disallow_any_generics = to_bool(value, invert)?,
        "allow_untyped_globals" => flags.allow_untyped_globals = to_bool(value, invert)?,
        _ => {
            return Err(format!(
                "Unrecognized option: {} = {}",
                original_name,
                value.unwrap_or("True")
            )
            .into())
        }
    }
    Ok(())
}

pub fn to_bool(value: Option<&str>, invert: bool) -> Result<bool, Box<str>> {
    let result = match value {
        Some(value) => match value.to_lowercase().as_str() {
            "true" | "1" | "yes" | "on" => true,
            "false" | "0" | "no" | "off" => false,
            _ => todo!(),
        },
        None => true,
    };
    Ok(result != invert)
}

fn split_commas(s: &str) -> impl Iterator<Item = &str> {
    let mut s = s.trim();
    if let Some(new_s) = s.strip_suffix(',') {
        s = new_s
    }
    s.split(',').map(|s| s.trim())
}
