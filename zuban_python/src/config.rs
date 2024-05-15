use crate::TypeCheckerFlags;

pub fn set_flag<'x>(
    flags: &mut TypeCheckerFlags,
    name: &str,
    value: Option<&str>,
) -> Result<(), Box<str>> {
    let expect_value = || value.ok_or_else(|| Box::from("TODO string"));
    match name {
        "disallow_any_generics" => flags.disallow_any_generics = true,
        "always_true" => flags
            .always_true_symbols
            .extend(split_commas(expect_value()?).map(|s| s.into())),
        "always_false" => flags
            .always_false_symbols
            .extend(split_commas(expect_value()?).map(|s| s.into())),
        "ignore_errors" => (), // TODO
        _ => {
            let after_no_prefix = name.strip_prefix("no_");
            return set_bool_init_flags(
                flags,
                name,
                after_no_prefix.unwrap_or(name),
                value,
                after_no_prefix.is_some(),
            );
        }
    }
    Ok(())
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

fn to_bool(value: Option<&str>, invert: bool) -> Result<bool, Box<str>> {
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
