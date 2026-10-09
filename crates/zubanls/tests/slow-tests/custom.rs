use serial_test::parallel;
use zubanls::DisplayStatusRequest;

use crate::support::Project;

#[test]
#[parallel]
fn test_status() {
    let server = Project::with_fixture(
        r#"
        [file pyproject.toml]
        [tool.zuban]
        exclude = ["ignored1.py"]
        [[tool.zuban.overrides]]
        module = 'ignored4'
        ignore_errors = true


        [file fine.py]
        1()

        [file ignored1.py]
        1()

        [file ignored2.py]
        # type: ignore
        1()

        [file ignored3.py]
        # mypy: ignore-errors
        1()

        [file ignored4.py]
        1()
        "#,
    )
    .into_server();

    let check = |for_file| {
        let status = server.request::<DisplayStatusRequest>(for_file);
        assert_eq!(status.version, 1);
        assert!(status.zuban_version.len() >= 5);
        assert!(!status.zuban_path.is_empty());
        assert!(status.type_checking_enabled);
        assert_eq!(status.mode, "default");
        status
    };

    let fine_py = server.doc_id("fine.py");
    let ignored1_py = server.doc_id("ignored1.py");
    let ignored2_py = server.doc_id("ignored2.py");
    let ignored3_py = server.doc_id("ignored3.py");
    let ignored4_py = server.doc_id("ignored4.py");

    assert_eq!(check(fine_py).file_errors_ignored_reason, None);
    // TODO
    assert_eq!(check(ignored1_py).file_errors_ignored_reason, None);
    assert_eq!(
        check(ignored2_py).file_errors_ignored_reason,
        Some("The current file has an entry like `type: ignore` at the top and therefore ignores errors".into())
    );
    assert_eq!(
        check(ignored3_py).file_errors_ignored_reason,
        Some("The current file has an entry like `mypy: ignore-errors=True` at the top and therefore ignores errors".into())
    );
    assert_eq!(
        check(ignored4_py).file_errors_ignored_reason,
        Some("The config file has an entry that ignores errors for this file".into())
    );

    assert_eq!(
        server.diagnostics_for_file("fine.py"),
        ["\"int\" not callable"]
    );
    // assert_eq!(server.diagnostics_for_file("ignored1.py"), [] as [&str; 0]);
    assert_eq!(server.diagnostics_for_file("ignored2.py"), [] as [&str; 0]);
    assert_eq!(server.diagnostics_for_file("ignored3.py"), [] as [&str; 0]);
    assert_eq!(server.diagnostics_for_file("ignored4.py"), [] as [&str; 0]);
}
