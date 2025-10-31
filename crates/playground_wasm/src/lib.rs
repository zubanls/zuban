use std::{any::Any, panic::AssertUnwindSafe};

use anyhow::Context;
use config::{ProjectOptions, Settings, TypeCheckerFlags};
use once_cell::sync::Lazy;
use serde::Serialize;
use vfs::{GlobAbsPath, InMemoryFs, PathWithScheme, VfsHandler};
use wasm_bindgen::prelude::*;
use zuban_python::{Mode, PlaygroundDiagnostic, Project, Severity};

const MAIN_FILE: &str = "main.py";

const TYPESHED_FILES: &[(&str, &str)] = &[
    ("typeshed/stdlib/builtins.pyi", include_str!("../typeshed/stdlib/builtins.pyi")),
    ("typeshed/stdlib/typing.pyi", include_str!("../typeshed/stdlib/typing.pyi")),
    ("typeshed/stdlib/types.pyi", include_str!("../typeshed/stdlib/types.pyi")),
    ("typeshed/stdlib/abc.pyi", include_str!("../typeshed/stdlib/abc.pyi")),
    (
        "typeshed/stdlib/_typeshed/__init__.pyi",
        include_str!("../typeshed/stdlib/_typeshed/__init__.pyi"),
    ),
    (
        "typeshed/stdlib/collections/__init__.pyi",
        include_str!("../typeshed/stdlib/collections/__init__.pyi"),
    ),
    (
        "typeshed/stdlib/_collections_abc.pyi",
        include_str!("../typeshed/stdlib/_collections_abc.pyi"),
    ),
    (
        "typeshed/stdlib/dataclasses.pyi",
        include_str!("../typeshed/stdlib/dataclasses.pyi"),
    ),
    (
        "typeshed/stdlib/typing_extensions.pyi",
        include_str!("../typeshed/stdlib/typing_extensions.pyi"),
    ),
    ("typeshed/stdlib/enum.pyi", include_str!("../typeshed/stdlib/enum.pyi")),
    (
        "typeshed/stdlib/functools.pyi",
        include_str!("../typeshed/stdlib/functools.pyi"),
    ),
    (
        "typeshed/stdlib/warnings.pyi",
        include_str!("../typeshed/stdlib/warnings.pyi"),
    ),
    (
        "typeshed/stubs/mypy-extensions/mypy_extensions.pyi",
        include_str!("../typeshed/stubs/mypy-extensions/mypy_extensions.pyi"),
    ),
    (
        "typeshed/stubs/typing_extensions/typing_extensions.pyi",
        include_str!("../typeshed/stubs/typing_extensions/typing_extensions.pyi"),
    ),
];

static PANIC_HOOK: Lazy<()> = Lazy::new(|| {
    console_error_panic_hook::set_once();
});

#[derive(Serialize)]
struct Position {
    line: usize,
    column: usize,
}

#[derive(Serialize)]
struct JsDiagnostic {
    message: String,
    notes: Vec<String>,
    severity: &'static str,
    code: String,
    start: Position,
    end: Position,
    snippet: String,
}

#[derive(Serialize)]
struct PlaygroundResponse {
    pyright: Vec<JsDiagnostic>,
    mypy: Vec<JsDiagnostic>,
}

#[wasm_bindgen]
pub fn run_check(code: &str) -> Result<JsValue, JsValue> {
    Lazy::force(&PANIC_HOOK);
    match run_internal(code) {
        Ok(response) => serde_wasm_bindgen::to_value(&response)
            .map_err(|err| JsValue::from_str(&format!("serialization error: {err}"))),
        Err(err) => Err(JsValue::from_str(&err.to_string())),
    }
}

fn run_internal(code: &str) -> anyhow::Result<PlaygroundResponse> {
    let pyright = evaluate_mode(code, false).context("pyright-like mode failed")?;
    let mypy = evaluate_mode(code, true).context("mypy-compatible mode failed")?;
    Ok(PlaygroundResponse { pyright, mypy })
}

fn evaluate_mode(code: &str, mypy: bool) -> anyhow::Result<Vec<JsDiagnostic>> {
    let fs = prepare_filesystem();
    let typeshed_root = fs.normalize_uncheck_abs_path("typeshed");
    let cwd = fs.unchecked_abs_path("");
    let glob = GlobAbsPath::new(&fs, &cwd, MAIN_FILE)?;

    let mut settings = Settings::default();
    settings.mypy_compatible = mypy;
    settings.add_global_packages_default = false;
    settings.typeshed_path = Some(typeshed_root);
    settings.files_or_directories_to_check = vec![glob];

    let flags = if mypy {
        TypeCheckerFlags::mypy_default()
    } else {
        TypeCheckerFlags::default()
    };

    let options = ProjectOptions::new(settings, flags);
    let mut project = Project::new(Box::new(fs.clone()), options, Mode::TypeCheckingOnly);

    let main_path = PathWithScheme::with_file_scheme(fs.normalize_uncheck_abs_path(MAIN_FILE));
    let main_code = code.to_owned();
    fs.set_file(MAIN_FILE, main_code.clone());

    let result = std::panic::catch_unwind(AssertUnwindSafe(|| {
        let file_index =
            project.store_in_memory_file_with_index(main_path.clone(), main_code.into_boxed_str());
        project.playground_diagnostics_for_file(file_index)
    }));

    match result {
        Ok(diags) => Ok(diags.into_iter().map(convert_diagnostic).collect()),
        Err(payload) => Err(anyhow::anyhow!(panic_payload_to_string(payload))),
    }
}

fn prepare_filesystem() -> InMemoryFs {
    let fs = InMemoryFs::new();
    for (path, contents) in TYPESHED_FILES {
        fs.set_file(path, contents.to_string());
    }
    fs
}

fn convert_diagnostic(diagnostic: PlaygroundDiagnostic) -> JsDiagnostic {
    JsDiagnostic {
        message: diagnostic.message,
        notes: diagnostic.notes,
        severity: match diagnostic.severity {
            Severity::Error => "error",
            Severity::Warning => "warning",
            Severity::Information => "info",
            Severity::Hint => "hint",
        },
        code: diagnostic.code,
        start: Position {
            line: diagnostic.start_line,
            column: diagnostic.start_column,
        },
        end: Position {
            line: diagnostic.end_line,
            column: diagnostic.end_column,
        },
        snippet: diagnostic.snippet,
    }
}

fn panic_payload_to_string(payload: Box<dyn Any + Send>) -> String {
    if let Some(s) = payload.downcast_ref::<&str>() {
        (*s).to_string()
    } else if let Some(s) = payload.downcast_ref::<String>() {
        s.clone()
    } else {
        "panic".to_string()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn evaluate_pyright() {
        if let Err(err) = evaluate_mode("x = 1\nprint(x)", false) {
            panic!("pyright mode failed: {err:?}");
        }
    }
}
