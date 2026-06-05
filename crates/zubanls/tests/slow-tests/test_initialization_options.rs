use lsp_types::DiagnosticServerCapabilities;
use serde_json::json;
use serial_test::parallel;

use crate::support::Project;

#[test]
#[parallel]
fn client_config_mode() {
    let check = |mode: &str, has_mypy_file, is_enabled| {
        let server = Project::with_fixture(if has_mypy_file {
            r#"
                [file mypy.ini]
                [file m.py]
                1()
                def f():
                    ''()
                "#
        } else {
            r#"
                [file m.py]
                1()
                def f():
                    ''()
                "#
        })
        .with_initialization_options(json!({ "typeCheckingMode": mode }))
        .into_server();
        assert_eq!(
            is_enabled,
            server
                .server_capabilities
                .as_ref()
                .unwrap()
                .diagnostic_provider
                .is_some(),
        );
        server.diagnostics_for_file("m.py")
    };

    const NOT_INT: &str = r#""int" not callable"#;
    const NOT_STR: &str = r#""str" not callable"#;

    // Without Mypy config file
    assert_eq!(check("default", false, true), [NOT_INT, NOT_STR]);
    assert_eq!(check("mypy", false, true), [NOT_INT]);
    assert_eq!(check("auto", false, true), [NOT_INT, NOT_STR]);
    // The capability should not be announced, but if somebody requests diagnostics,it it will
    // still work.
    assert_eq!(check("off", false, false), [NOT_INT, NOT_STR]);

    // With Mypy config file
    assert_eq!(check("default", true, true), [NOT_INT, NOT_STR]);
    assert_eq!(check("mypy", true, true), [NOT_INT]);
    assert_eq!(check("auto", true, true), [NOT_INT]);
}

#[test]
#[parallel]
fn diagnostic_mode() {
    let check = |mode| {
        let server = Project::with_fixture(
            r#"
            [file m.py]
            "#,
        )
        .with_initialization_options(json!({ "diagnosticMode": mode }))
        .into_server();
        let DiagnosticServerCapabilities::Options(diagnostics) = server
            .server_capabilities
            .as_ref()
            .unwrap()
            .diagnostic_provider
            .as_ref()
            .unwrap()
        else {
            unreachable!()
        };
        diagnostics.workspace_diagnostics
    };
    assert!(!check("open-files-only"));
    assert!(!check("something-undefined"));
    assert!(check("workspace"));
}

#[test]
#[parallel]
fn python_executable() {
    let check = |json| {
        let server = Project::with_fixture(
            r#"
                [file build/venv/bin/python]
                [file build/venv/Scripts/python.exe]
                [file build/venv/pyvenv.cfg]
                include-system-site-packages = false
                version = 3.14.3

                [file build/venv/Lib/site-packages/foo.py]
                [file build/venv/lib/python3.12/site-packages/foo.py]

                [file m.py]
                import foo
                "#,
        )
        .with_initialization_options(json)
        .into_server();
        server.diagnostics_for_file("m.py")
    };

    let executable = if cfg!(windows) {
        "build/venv/bin/python"
    } else {
        "build/venv/Scripts/python.exe"
    };
    assert_eq!(
        check(json!({})),
        ["Cannot find implementation or library stub for module named \"foo\""]
    );
    assert_eq!(
        check(json!({ "pythonExecutable": executable })),
        [] as [&str; 0]
    );
}

#[test]
#[parallel]
fn disable_language_services() {
    let check = |enabled: bool| {
        let server = Project::with_fixture(
            r#"
            [file m.py]
            "#,
        )
        .with_initialization_options(json!({ "disableLanguageServices": !enabled }))
        .into_server();
        let cap = server.server_capabilities.as_ref().unwrap();
        assert_eq!(enabled, cap.completion_provider.is_some());
        assert_eq!(enabled, cap.definition_provider.is_some());
        assert_eq!(enabled, cap.declaration_provider.is_some());
        assert_eq!(enabled, cap.hover_provider.is_some());
        assert_eq!(enabled, cap.signature_help_provider.is_some());
        assert_eq!(enabled, cap.type_definition_provider.is_some());
        assert_eq!(enabled, cap.implementation_provider.is_some());
        assert_eq!(enabled, cap.rename_provider.is_some());
        assert!(cap.diagnostic_provider.is_some());
    };
    check(false);
    check(true);
}
