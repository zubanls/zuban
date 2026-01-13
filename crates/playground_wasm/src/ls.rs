use std::collections::{HashMap, HashSet};
use std::panic::AssertUnwindSafe;
use std::str::FromStr;

use config::{ProjectOptions, Settings, TypeCheckerFlags};
use lsp_types::*;
use once_cell::sync::Lazy;
use serde::{Deserialize, Serialize};
use serde_json::{json, Value};
use vfs::{GlobAbsPath, InMemoryFs, PathWithScheme, VfsHandler};
use wasm_bindgen::prelude::*;
use zuban_python::{GotoGoal, InputPosition, Mode, Project, ReferencesGoal};

use crate::helpers::{panic_payload_to_string, prepare_filesystem};
use crate::stubs::BUNDLED_STUBS;
use crate::PANIC_HOOK;

macro_rules! pos { ($p:expr) => { Position { line: $p.line_zero_based() as u32, character: $p.utf16_code_units_column() as u32 } }; }
macro_rules! range { ($s:expr, $e:expr) => { Range { start: pos!($s), end: pos!($e) } }; }

#[derive(Deserialize)]
struct Req { id: Option<Value>, method: String, params: Option<Value>, #[allow(dead_code)] jsonrpc: String }

#[wasm_bindgen]
pub struct LS {
    proj: Project,
    fs: InMemoryFs,
    uri: String,
    ver: i32,
    code: String,
    unavail: HashMap<String, HashSet<String>>,
}

#[wasm_bindgen]
impl LS {
    #[wasm_bindgen(constructor)]
    pub fn new(mypy_compat: bool) -> Result<LS, JsValue> {
        Lazy::force(&PANIC_HOOK);
        std::panic::catch_unwind(AssertUnwindSafe(|| {
            let fs = prepare_filesystem();
            let mut s = Settings::default();
            s.mypy_compatible = mypy_compat;
            s.add_global_packages_default = false;
            s.typeshed_path = Some(fs.normalize_unchecked_abs_path("typeshed"));
            s.files_or_directories_to_check = vec![GlobAbsPath::new(&fs, &fs.unchecked_abs_path(""), "**/*.py")?];
            let flags = if mypy_compat { TypeCheckerFlags::mypy_default() } else { TypeCheckerFlags::default() };
            let proj = Project::new(Box::new(fs.clone()), ProjectOptions::new(s, flags), Mode::LanguageServer);
            Ok(LS { proj, fs, uri: String::new(), ver: 0, code: String::new(), unavail: HashMap::new() })
        }))
        .map_err(|p| JsValue::from_str(&panic_payload_to_string(p)))?
        .map_err(|e: anyhow::Error| JsValue::from_str(&e.to_string()))
    }

    #[wasm_bindgen]
    pub fn handle_message(&mut self, msg: &str) -> Option<String> {
        std::panic::catch_unwind(AssertUnwindSafe(|| self.dispatch(msg)))
            .unwrap_or_else(|p| Some(self.err(None, -32603, &format!("Internal error: {}", panic_payload_to_string(p)))))
    }

    #[wasm_bindgen]
    pub fn register_stubs(&mut self, stubs: JsValue) -> Result<u32, JsValue> {
        let stubs: HashMap<String, String> = serde_wasm_bindgen::from_value(stubs).map_err(|e| JsValue::from_str(&e.to_string()))?;
        let n = stubs.len() as u32;
        for (path, content) in stubs { self.fs.set_file(&path, content); }
        self.proj.add_site_packages(self.fs.normalize_unchecked_abs_path("site-packages"));
        Ok(n)
    }

    #[wasm_bindgen]
    pub fn set_unavailable(&mut self, v: JsValue) -> Result<(), JsValue> {
        let raw: HashMap<String, Vec<String>> = serde_wasm_bindgen::from_value(v).map_err(|e| JsValue::from_str(&e.to_string()))?;
        self.unavail = raw.into_iter().map(|(k, v)| (k, v.into_iter().collect())).collect();
        Ok(())
    }

    #[wasm_bindgen]
    pub fn get_bundled_stubs_count(&self) -> usize { BUNDLED_STUBS.len() }
}

impl LS {
    fn dispatch(&mut self, msg: &str) -> Option<String> {
        let r: Req = serde_json::from_str(msg).ok()?;
        match r.method.as_str() {
            "initialize" => self.initialize(r.id),
            "shutdown" => self.ok(r.id, Value::Null),
            "initialized" | "exit" | "textDocument/didClose" | "textDocument/didSave" => None,
            "textDocument/didOpen" => self.did_open(r.params),
            "textDocument/didChange" => self.did_change(r.params),
            "textDocument/completion" => self.completion(r.id, r.params),
            "textDocument/hover" => self.hover(r.id, r.params),
            "textDocument/definition" => self.goto(r.id, r.params, GotoGoal::PreferNonStubs),
            "textDocument/declaration" => self.goto(r.id, r.params, GotoGoal::Indifferent),
            "textDocument/typeDefinition" => self.goto(r.id, r.params, GotoGoal::PreferStubs),
            "textDocument/implementation" => self.goto(r.id, r.params, GotoGoal::PreferNonStubs),
            "textDocument/references" => self.references(r.id, r.params),
            "textDocument/signatureHelp" => self.sig_help(r.id, r.params),
            "textDocument/prepareRename" => self.prepare_rename(r.id, r.params),
            "textDocument/rename" => self.rename(r.id, r.params),
            "textDocument/documentSymbol" => self.doc_symbol(r.id),
            "textDocument/diagnostic" => self.diagnostic(r.id),
            "textDocument/inlayHint" => self.inlay_hints(r.id, r.params),
            _ => r.id.as_ref().map(|_| self.err(r.id.clone(), -32601, &format!("Unknown method: {}", r.method))),
        }
    }
}

impl LS {
    fn initialize(&self, id: Option<Value>) -> Option<String> {
        self.ok(id, InitializeResult {
            capabilities: ServerCapabilities {
                text_document_sync: Some(TextDocumentSyncCapability::Options(TextDocumentSyncOptions {
                    open_close: Some(true), change: Some(TextDocumentSyncKind::FULL),
                    save: Some(TextDocumentSyncSaveOptions::SaveOptions(SaveOptions { include_text: Some(false) })),
                    ..Default::default()
                })),
                completion_provider: Some(CompletionOptions {
                    trigger_characters: Some(vec![".".into(), " ".into(), "(".into(), ",".into()]),
                    resolve_provider: Some(false), ..Default::default()
                }),
                signature_help_provider: Some(SignatureHelpOptions {
                    trigger_characters: Some(vec!["(".into(), ",".into()]),
                    retrigger_characters: Some(vec![",".into()]), ..Default::default()
                }),
                diagnostic_provider: Some(DiagnosticServerCapabilities::Options(DiagnosticOptions {
                    inter_file_dependencies: false, workspace_diagnostics: false, ..Default::default()
                })),
                hover_provider: Some(HoverProviderCapability::Simple(true)),
                definition_provider: Some(OneOf::Left(true)),
                declaration_provider: Some(DeclarationCapability::Simple(true)),
                type_definition_provider: Some(TypeDefinitionProviderCapability::Simple(true)),
                implementation_provider: Some(ImplementationProviderCapability::Simple(true)),
                references_provider: Some(OneOf::Left(true)),
                document_symbol_provider: Some(OneOf::Left(true)),
                inlay_hint_provider: Some(OneOf::Left(true)),
                rename_provider: Some(OneOf::Right(RenameOptions { prepare_provider: Some(true), work_done_progress_options: Default::default() })),
                ..Default::default()
            },
            server_info: Some(ServerInfo { name: "zuban".into(), version: Some(env!("CARGO_PKG_VERSION").into()) }),
            offset_encoding: None,
        })
    }

    fn did_open(&mut self, p: Option<Value>) -> Option<String> {
        let d = p?.get("textDocument")?.clone();
        self.uri = d.get("uri")?.as_str()?.into();
        self.ver = d.get("version")?.as_i64()? as i32;
        self.code = d.get("text")?.as_str()?.into();
        self.sync();
        self.pub_diags()
    }

    fn did_change(&mut self, p: Option<Value>) -> Option<String> {
        let p = p?;
        self.ver = p.get("textDocument")?.get("version")?.as_i64()? as i32;
        self.code = p.get("contentChanges")?.as_array()?.last()?.get("text")?.as_str()?.into();
        self.sync();
        self.pub_diags()
    }

    fn completion(&mut self, id: Option<Value>, p: Option<Value>) -> Option<String> {
        let (line, col) = self.pos_coords(&p)?;
        let module = self.module_at_cursor(line, col);
        let doc = self.proj.document(&self.path())?;
        let unavail = &self.unavail;

        let items: Vec<CompletionItem> = doc.complete(InputPosition::Utf16CodeUnits { line, column: col }, true, |_, c: &dyn zuban_python::Completion| {
            if module.as_ref().and_then(|m| unavail.get(m)).map(|s| s.contains(c.label())).unwrap_or(false) { return None; }
            Some(CompletionItem {
                label: c.label().into(),
                kind: Some(c.kind()),
                insert_text: Some(c.insert_text().into()),
                detail: c.documentation().map(Into::into),
                deprecated: Some(c.deprecated()),
                ..Default::default()
            })
        }).unwrap_or_default();

        self.ok(id, CompletionResponse::List(CompletionList { is_incomplete: false, items }))
    }

    fn hover(&mut self, id: Option<Value>, p: Option<Value>) -> Option<String> {
        let input = self.input_pos(&p)?;
        let h = self.proj.document(&self.path()).and_then(|doc| match doc.documentation(input, false) {
            Ok(Some(r)) => {
                let (s, e) = r.on_symbol_range;
                Some(Hover { contents: HoverContents::Markup(MarkupContent { kind: MarkupKind::Markdown, value: r.documentation }), range: Some(range!(s, e)) })
            }
            _ => None,
        });
        self.ok(id, h.map(|v| serde_json::to_value(v).unwrap()).unwrap_or(Value::Null))
    }

    fn goto(&mut self, id: Option<Value>, p: Option<Value>, goal: GotoGoal) -> Option<String> {
        let input = self.input_pos(&p)?;
        let uri = self.uri.clone();
        let doc = self.proj.document(&self.path())?;
        let locs: Vec<Location> = doc.goto(input, goal, true, |n| loc(&uri, n)).unwrap_or_default();
        self.ok(id, locs)
    }

    fn references(&mut self, id: Option<Value>, p: Option<Value>) -> Option<String> {
        let input = self.input_pos(&p)?;
        let incl = p.as_ref().and_then(|v| v.get("context")?.get("includeDeclaration")?.as_bool()).unwrap_or(true);
        let uri = self.uri.clone();
        let doc = self.proj.document(&self.path())?;
        let locs: Vec<Location> = doc.references(input, ReferencesGoal::OnlyCurrentFile, incl, |n| loc(&uri, n)).unwrap_or_default();
        self.ok(id, locs)
    }

    fn sig_help(&mut self, id: Option<Value>, p: Option<Value>) -> Option<String> {
        let input = self.input_pos(&p)?;
        let doc = self.proj.document(&self.path())?;
        let res = match doc.call_signatures(input) {
            Ok(Some(sigs)) => {
                let (mut act_sig, mut act_param) = (0u32, None);
                let sigs: Vec<SignatureInformation> = sigs.into_iterator().enumerate().map(|(i, s)| {
                    if s.is_valid_with_arguments && act_param.is_none() {
                        act_sig = i as u32;
                        act_param = s.current_param.map(|p| p as u32);
                    }
                    let params = s.params().map(|ps| ps.map(|p| ParameterInformation { label: ParameterLabel::Simple(p.name().into()), documentation: None }).collect());
                    let act = s.current_param.map(|p| p as u32);
                    SignatureInformation { label: s.label.into(), parameters: params, active_parameter: act, documentation: None }
                }).collect();
                serde_json::to_value(SignatureHelp { signatures: sigs, active_signature: Some(act_sig), active_parameter: act_param }).unwrap()
            }
            _ => Value::Null,
        };
        self.ok(id, res)
    }

    fn prepare_rename(&mut self, id: Option<Value>, p: Option<Value>) -> Option<String> {
        let input = self.input_pos(&p)?;
        let res: Result<Option<Range>, String> = {
            let doc = self.proj.document(&self.path())?;
            match doc.is_valid_rename_location(input) {
                Ok(Some((s, e))) => Ok(Some(range!(s, e))),
                Ok(None) => Ok(None),
                Err(e) => Err(e.to_string()),
            }
        };
        match res {
            Ok(Some(r)) => self.ok(id, PrepareRenameResponse::Range(r)),
            Ok(None) => self.ok(id, Value::Null),
            Err(e) => Some(self.err(id, -32600, &e)),
        }
    }

    fn rename(&mut self, id: Option<Value>, p: Option<Value>) -> Option<String> {
        let input = self.input_pos(&p)?;
        let new: String = p.as_ref()?.get("newName")?.as_str()?.into();
        if new.is_empty() { return Some(self.err(id, -32600, "New name required")); }

        let uri = self.uri.clone();
        let doc = self.proj.document(&self.path())?;
        match doc.references_for_rename(input, &new) {
            Ok(chg) => {
                let mut edits: HashMap<Uri, Vec<TextEdit>> = HashMap::new();
                for fc in chg.changes {
                    let u = make_uri(&uri, &fc.path.as_uri());
                    edits.entry(u).or_default().extend(fc.ranges.iter().map(|(s, e)| TextEdit { range: range!(s, e), new_text: new.clone() }));
                }
                self.ok(id, WorkspaceEdit { changes: Some(edits), ..Default::default() })
            }
            Err(e) => Some(self.err(id, -32600, &e.to_string())),
        }
    }

    fn doc_symbol(&mut self, id: Option<Value>) -> Option<String> {
        let doc = self.proj.document(&self.path())?;
        #[allow(deprecated)]
        let syms: Vec<DocumentSymbol> = doc.symbols().map(|s| {
            let n = s.as_name();
            let (rs, re) = n.target_range();
            let (ss, se) = n.name_range();
            DocumentSymbol { name: s.symbol.into(), kind: n.lsp_kind(), range: range!(rs, re), selection_range: range!(ss, se), detail: None, deprecated: None, tags: None, children: None }
        }).collect();
        self.ok(id, syms)
    }

    fn diagnostic(&mut self, id: Option<Value>) -> Option<String> {
        let items = self.make_diags();
        self.ok(id, DocumentDiagnosticReport::Full(RelatedFullDocumentDiagnosticReport {
            full_document_diagnostic_report: FullDocumentDiagnosticReport { items, ..Default::default() },
            ..Default::default()
        }))
    }

    fn inlay_hints(&mut self, id: Option<Value>, p: Option<Value>) -> Option<String> {
        let r = p.as_ref()?.get("range")?;
        let start = r.get("start")?.get("line")?.as_u64()? as usize;
        let end = r.get("end")?.get("line")?.as_u64()? as usize;

        let doc = self.proj.document(&self.path())?;
        let hints: Vec<InlayHint> = doc.inlay_hints(
            InputPosition::Utf16CodeUnits { line: start, column: 0 },
            InputPosition::Utf16CodeUnits { line: end, column: usize::MAX },
        ).map(|it| it.map(|h| InlayHint {
            position: pos!(h.position), label: InlayHintLabel::String(h.label().into()), kind: Some(h.kind),
            text_edits: None, tooltip: None, padding_left: Some(true), padding_right: None, data: None,
        }).collect()).unwrap_or_default();

        self.ok(id, hints)
    }
}

impl LS {
    fn sync(&mut self) {
        let f = self.fname();
        self.fs.set_file(f, self.code.clone());
        self.proj.store_in_memory_file_with_index(self.path(), self.code.clone().into_boxed_str());
    }

    fn pub_diags(&mut self) -> Option<String> {
        Some(serde_json::to_string(&json!({
            "jsonrpc": "2.0",
            "method": "textDocument/publishDiagnostics",
            "params": PublishDiagnosticsParams { uri: Uri::from_str(&self.uri).ok()?, diagnostics: self.make_diags(), version: Some(self.ver) }
        })).unwrap())
    }

    fn make_diags(&mut self) -> Vec<Diagnostic> {
        let Some(mut doc) = self.proj.document(&self.path()) else { return vec![] };
        doc.diagnostics().iter().map(|d| Diagnostic {
            range: range!(d.start_position(), d.end_position()),
            severity: Some(match d.severity() {
                zuban_python::Severity::Error => DiagnosticSeverity::ERROR,
                zuban_python::Severity::Warning => DiagnosticSeverity::WARNING,
                zuban_python::Severity::Information => DiagnosticSeverity::INFORMATION,
                zuban_python::Severity::Hint => DiagnosticSeverity::HINT,
            }),
            code: Some(NumberOrString::String(d.mypy_error_code().into())),
            source: Some("zuban".into()),
            message: d.message().into(),
            ..Default::default()
        }).collect()
    }

    fn fname(&self) -> &str { self.uri.strip_prefix("file:///").or_else(|| self.uri.strip_prefix("file://")).unwrap_or(&self.uri) }
    fn path(&self) -> PathWithScheme { PathWithScheme::with_file_scheme(self.fs.normalize_unchecked_abs_path(self.fname())) }

    fn pos_coords(&self, p: &Option<Value>) -> Option<(usize, usize)> {
        let pos = p.as_ref()?.get("position")?;
        Some((pos.get("line")?.as_u64()? as usize, pos.get("character")?.as_u64()? as usize))
    }

    fn input_pos(&self, p: &Option<Value>) -> Option<InputPosition> {
        let (line, col) = self.pos_coords(p)?;
        Some(InputPosition::Utf16CodeUnits { line, column: col })
    }

    fn module_at_cursor(&self, line: usize, col: usize) -> Option<String> {
        let txt = self.code.lines().nth(line)?;
        let prefix = txt.get(..col.min(txt.len()))?;
        let dot = prefix.rfind('.')?;
        let before = &prefix[..dot];
        let start = before.rfind(|c: char| !c.is_alphanumeric() && c != '_').map(|i| i + 1).unwrap_or(0);
        let m = &before[start..];
        (!m.is_empty()).then(|| m.into())
    }

    fn ok<T: Serialize>(&self, id: Option<Value>, r: T) -> Option<String> {
        Some(serde_json::to_string(&json!({ "jsonrpc": "2.0", "id": id, "result": r })).unwrap())
    }

    fn err(&self, id: Option<Value>, code: i32, msg: &str) -> String {
        serde_json::to_string(&json!({ "jsonrpc": "2.0", "id": id, "error": { "code": code, "message": msg } })).unwrap()
    }
}

fn loc(uri: &str, n: zuban_python::Name) -> Location {
    let (s, e) = n.name_range();
    Location { uri: make_uri(uri, &n.file_path()), range: range!(s, e) }
}

fn make_uri(uri: &str, path: &str) -> Uri {
    let s = if path.starts_with("typeshed") || path.starts_with("site-packages") {
        format!("file:///{path}")
    } else if path.contains("://") {
        path.to_string()
    } else {
        uri.to_string()
    };
    Uri::from_str(&s).unwrap()
}
