use config::ProjectOptions;
use vfs::PathWithScheme;
use zuban_python::{InputPosition, Mode, Project};

#[test]
fn test_signature_param_position() {
    let mut po = ProjectOptions::default();
    po.settings.typeshed_path = Some(test_utils::typeshed_path());
    let mut project = Project::without_watcher(po, Mode::LanguageServer);
    let vfs = project.vfs_handler();
    let path = PathWithScheme::with_file_scheme(
        vfs.normalize_rc_path(vfs.unchecked_abs_path(&format!("/signature-test/test.py"))),
    );

    let mut run = |base_code: &str, check_code: &str, nth_param| {
        let code = format!("{base_code}\n{check_code}");
        project.store_in_memory_file(path.clone(), code.clone().into());
        let document = project.document(&path).unwrap();
        let mut signatures = document
            .call_signatures(InputPosition::Utf8Bytes {
                line: 2,
                column: check_code.len(),
            })
            .unwrap()
            .unwrap()
            .into_iterator();
        let signature = signatures.next().unwrap();
        assert_eq!(
            signature.current_param, nth_param,
            "while checking {code:?}"
        );
        assert!(signatures.next().is_none());
    };
    macro_rules! signature_test {
        (($base_code:expr, $check_code:expr, None)) => {
            run($base_code, $check_code, None);
        };
        (($base_code:expr, $check_code:expr, $nth_param:expr)) => {
            run($base_code, $check_code, Some($nth_param));
        };
    }
    macro_rules! check_all {
        ($($arg:tt),*$(,)?) => {
            $(signature_test!($arg));*
        };
    }

    let code1 = "def f(u, /, v=3, *, abc, abd, xyz): pass";
    let code2 = "def g(u, /, v=3, *, abc, abd, xyz, **kwargs): pass";
    let code3 = "def h(u, /, v, *args, x=1, y): pass";
    let code4 = "def i(u, /, v, *args, x=1, y, **kwargs): pass";

    check_all![
        // No *args, **kwargs
        (code1, "f(", 0),
        (code1, "f(a", 0),
        (code1, "f(a,", 1),
        (code1, "f(a,b", 1),
        (code1, "f(a,b,", 2),
        (code1, "f(a,b,c", None),
        (code1, "f(a,b,a", 2),
        (code1, "f(a,b,a=", None),
        (code1, "f(a,b,abc", 2),
        (code1, "f(a,b,abc=(", 2),
        (code1, "f(a,b,abc=(f,1,2,3", 2),
        (code1, "f(a,b,abd", 3),
        (code1, "f(a,b,x", 4),
        (code1, "f(a,b,xy", 4),
        (code1, "f(a,b,xyz=", 4),
        (code1, "f(a,b,xy=", None),
        (code1, "f(u=", None),
        (code1, "f(v=", 1),
        // **kwargs
        (code2, "g(a,b,a", 2),
        (code2, "g(a,b,abc", 2),
        (code2, "g(a,b,abd", 3),
        (code2, "g(a,b,arr", 5),
        (code2, "g(a,b,xy", 4),
        (code2, "g(a,b,xyz=", 4),
        (code2, "g(a,b,xy=", 5),
        (code2, "g(a,b,abc=1,abd=4,", 4),
        (code2, "g(a,b,abc=1,xyz=3,abd=4,", 5),
        (code2, "g(a,b,abc=1,abd=4,lala", 5),
        (code2, "g(a,b,abc=1,abd=4,lala=", 5),
        (code2, "g(a,b,abc=1,abd=4,abd=", 5),
        (code2, "g(a,b,kw", 5),
        (code2, "g(a,b,kwargs=", 5),
        (code2, "g(u=", 5),
        (code2, "g(v=", 1),
        // *args
        (code3, "h(a,b,c", 2),
        (code3, "h(a,b,c,", 2),
        (code3, "h(a,b,c,d", 2),
        (code3, "h(a,b,c,d[", 2),
        (code3, "h(a,b,c,(3,", 2),
        (code3, "h(a,b,c,(3,)", 2),
        (code3, "h(a,b,args=", None),
        (code3, "h(u,v=", 1),
        (code3, "h(u=", None),
        (code3, "h(u,*xxx", 1),
        (code3, "h(u,*xxx,*yyy", 1),
        (code3, "h(u,*[]", 1),
        (code3, "h(u,*", 1),
        (code3, "h(u,*, *", 1),
        (code3, "h(u,1,**", 3),
        (code3, "h(u,**y", 1),
        (code3, "h(u,x=2,**", 1),
        (code3, "h(u,x=2,**y", 1),
        (code3, "h(u,v=2,**y", 3),
        (code3, "h(u,x=2,**vv", 1),
        // *args, **kwargs
        (code4, "i(a,b,c,d", 2),
        (code4, "i(a,b,c,d,e", 2),
        (code4, "i(a,b,c,d,e=", 5),
        (code4, "i(a,b,c,d,e=3", 5),
        (code4, "i(a,b,c,d=,x=", 3),
        (code4, "i(a,b,c,d=5,x=4", 3),
        (code4, "i(a,b,c,d=5,x=4,y", 4),
        (code4, "i(a,b,c,d=5,x=4,y=3,", 5),
        (code4, "i(a,b,c,d=5,y=4,x=3,", 5),
        (code4, "i(a,b,c,d=4,", 3),
        (code4, "i(a,b,c,x=1,d=,", 4),
        // Error nodes
        (code4, "i(1, [a,b", 1),
        (code4, "i(1, [a,b=,", 2),
        (code4, "i(1, [a?b,", 2),
        (code4, "i(1, [a?b,*", 2),
        (code4, "i(?b,*r,c", 1),
        (code4, "i(?*", 0),
        (code4, "i(?**", 1),
        // Random
        (code4, "i(()", 0),
        (code4, "i((),", 1),
        (code4, "i([(),", 0),
        (code4, "i([(,", 1),
        (code4, "i(x,()", 1),
    ];
}
