use anyhow::bail;

use lsp_types::SemanticTokenType;
use parsa_python_cst::{CodeIndex, Name as CstName};

use crate::{
    Document, InputPosition, PositionInfos,
    database::{ComplexPoint, Database, Point, PointKind, Specific},
    file::{
        ClassNodeRef, File as _, PythonFile, use_cached_annotation_or_type_comment,
        use_cached_param_annotation_type,
    },
    inference_state::InferenceState,
    node_ref::NodeRef,
    type_::{FunctionKind, Type},
};

impl<'project> Document<'project> {
    pub fn semantic_tokens(
        &self,
        range: Option<(InputPosition, InputPosition)>,
    ) -> anyhow::Result<impl Iterator<Item = SemanticToken<'_>>> {
        let file = self.project.db.loaded_python_file(self.file_index);
        let db = &self.project.db;
        let (start, end) = if let Some((start_input, end_input)) = range {
            let start = file.line_column_to_byte(start_input)?;
            let end = file.line_column_to_byte(end_input)?;
            if start.column_out_of_bounds {
                bail!("Start position {start_input:?} is out of scope");
            }
            if end.column_out_of_bounds {
                bail!("End position {end_input:?} is out of scope");
            }
            (start.byte, end.byte)
        } else {
            (0, u32::MAX)
        };
        let result = file.ensure_calculated_diagnostics(db);
        debug_assert!(result.is_ok());
        Ok(file
            .tree
            .filter_all_names(Some(start))
            .filter_map(move |name| {
                if name.end() < start || name.start() > end {
                    return None;
                }

                let (p, node_ref) = self.try_to_follow_point(NodeRef::new(file, name.index()))?;
                let (lsp_type, mut properties) = self.resolved_node_ref_to_lsp_type(node_ref, p)?;
                if let Some(name_def) = name.name_def() {
                    properties.definition = true;
                    properties.declaration = !name_def.name_can_be_overwritten();
                }
                Some(SemanticToken {
                    db,
                    file,
                    name,
                    lsp_type,
                    properties,
                })
            }))
    }

    fn try_to_follow_point(
        &self,
        node_ref: NodeRef<'project>,
    ) -> Option<(Point, NodeRef<'project>)> {
        let p = node_ref.point();
        if !p.calculated() {
            return None;
        }
        match p.kind() {
            PointKind::Redirect => {
                self.try_to_follow_point(p.as_redirected_node_ref(&self.project.db))
            }
            PointKind::Specific
                if matches!(
                    p.specific(),
                    Specific::FirstNameOfNameDef | Specific::NameOfNameDef
                ) =>
            {
                self.try_to_follow_point(node_ref.name_def_ref_of_name())
            }
            _ => Some((p, node_ref)),
        }
    }

    fn resolved_node_ref_to_lsp_type(
        &self,
        node_ref: NodeRef,
        p: Point,
    ) -> Option<(SemanticTokenType, SemanticTokenProperties)> {
        let mut properties = SemanticTokenProperties::default();
        let db = &self.project.db;
        let mut with_t = |t: &Type| match t {
            Type::Type(inner) => match inner.as_ref() {
                Type::Enum(_) => Some(SemanticTokenType::ENUM),
                _ => Some(SemanticTokenType::CLASS),
            },
            Type::Enum(_) => Some(SemanticTokenType::ENUM),
            Type::EnumMember(_) => Some(SemanticTokenType::ENUM_MEMBER),
            Type::Module(_) | Type::Namespace(_) => Some(SemanticTokenType::NAMESPACE),
            Type::Callable(c) => {
                if let Some(func) = NodeRef::from_link(db, c.defined_at).maybe_function()
                    && func.parent().is_async()
                {
                    properties.async_ = true
                }
                properties.read_only = c.is_final;
                properties.deprecated = c.deprecated_reason.is_some();
                properties.abstract_ = c.is_abstract;
                Some(match &c.kind {
                    FunctionKind::Function { .. } => SemanticTokenType::FUNCTION,
                    FunctionKind::Property { setter_type, .. } => {
                        properties.read_only = setter_type.is_none();
                        SemanticTokenType::PROPERTY
                    }
                    FunctionKind::Classmethod { .. } | FunctionKind::Staticmethod => {
                        properties.static_ = true;
                        SemanticTokenType::FUNCTION
                    }
                })
            }
            Type::CustomBehavior(_) | Type::FunctionOverload(_) => {
                Some(SemanticTokenType::FUNCTION)
            }
            Type::Any(_) | Type::Never(_) => None,
            _ => Some(SemanticTokenType::VARIABLE),
        };

        let lsp_type = match p.kind() {
            PointKind::Specific => match p.specific() {
                Specific::AnyDueToError => None,
                Specific::Function => {
                    if node_ref.expect_function().parent().is_async() {
                        properties.async_ = true;
                    }
                    Some(SemanticTokenType::FUNCTION)
                }
                Specific::Param => {
                    if let Some(annotation) = node_ref.expect_name_def().maybe_param_annotation() {
                        let t = use_cached_param_annotation_type(db, node_ref.file, annotation);
                        with_t(&t)
                    } else {
                        Some(SemanticTokenType::VARIABLE)
                    }
                }
                Specific::MaybeSelfParam => Some(SemanticTokenType::VARIABLE),
                Specific::OverloadUnreachable => Some(SemanticTokenType::FUNCTION),
                specific => {
                    if specific.is_partial() {
                        Some(SemanticTokenType::VARIABLE)
                    } else if specific.is_annotation_or_type_comment() {
                        let t = use_cached_annotation_or_type_comment(
                            &InferenceState::new(db, node_ref.file),
                            node_ref,
                        );
                        with_t(&t)
                    } else {
                        Some(SemanticTokenType::CLASS)
                    }
                }
            },
            PointKind::Complex => match node_ref.file.complex_points.get(p.complex_index()) {
                ComplexPoint::TypeInstance(t) => with_t(t),
                ComplexPoint::IndirectFinal(t) => with_t(t),
                ComplexPoint::WidenedType(w) => with_t(&w.widened),
                ComplexPoint::Class(_) => {
                    if let Some(class_infos) =
                        ClassNodeRef::from_node_ref(node_ref).maybe_cached_class_infos(db)
                        && let Some(t) = class_infos.undefined_generics_type.get()
                        && matches!(t.as_ref(), Type::Enum(_))
                    {
                        Some(SemanticTokenType::ENUM)
                    } else {
                        Some(SemanticTokenType::CLASS)
                    }
                }
                ComplexPoint::NamedTupleDefinition(_) | ComplexPoint::TypedDictDefinition(_) => {
                    Some(SemanticTokenType::CLASS)
                }
                ComplexPoint::FunctionOverload(_) => Some(SemanticTokenType::FUNCTION),
                _ => None,
            },
            PointKind::FileReference => Some(SemanticTokenType::NAMESPACE),
            PointKind::Redirect => unreachable!("We have already followed all redirects"),
        }?;
        Some((lsp_type, properties))
    }
}

pub struct SemanticToken<'db> {
    db: &'db Database,
    file: &'db PythonFile,
    name: CstName<'db>,
    pub lsp_type: SemanticTokenType,
    pub properties: SemanticTokenProperties,
}

impl<'db> SemanticToken<'db> {
    pub fn position(&self) -> PositionInfos<'db> {
        self.file.byte_to_position_infos(self.db, self.name.start())
    }

    pub fn len(&self) -> CodeIndex {
        self.name.len()
    }

    pub fn content(&self) -> &'db str {
        self.name.as_code()
    }

    pub fn pretty_properties(&self) -> String {
        let mut pretty = vec![];
        let p = &self.properties;

        macro_rules! add {
            ($name:ident) => {
                if p.$name {
                    pretty.push(stringify!($name).trim_end_matches('_'))
                }
            };
        }
        add!(definition);
        add!(declaration);
        add!(in_stdlib);
        add!(read_only);
        add!(deprecated);
        add!(abstract_);
        add!(async_);
        add!(static_);

        if pretty.is_empty() {
            "none".into()
        } else {
            pretty
                .into_iter()
                .collect::<Vec<&str>>()
                .as_slice()
                .join(",")
        }
    }
}

#[derive(Default)]
pub struct SemanticTokenProperties {
    pub definition: bool,
    pub declaration: bool,
    pub in_stdlib: bool, // TODO this is currently unused
    pub read_only: bool,
    pub static_: bool,
    pub deprecated: bool,
    pub abstract_: bool,
    pub async_: bool,
}
