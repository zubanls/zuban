use std::borrow::Cow;

use lsp_types::InlayHintKind;
use parsa_python_cst::{
    AssignmentContent, AssignmentRightSide, ExpressionContent, ExpressionPart, PotentialInlayHint,
    PrimaryContent, PrimaryOrAtom, Target,
};

use crate::{
    Document, InputPosition, PositionInfos,
    database::{ComplexPoint, Database, Specific},
    debug,
    file::{ClassNodeRef, File as _, PythonFile, assignment_type_node_ref},
    inference_state::InferenceState,
    node_ref::NodeRef,
    type_::{ReplaceTypeVarLikes as _, Type},
    type_helpers::{FuncLike as _, Function},
};

impl<'project> Document<'project> {
    pub fn inlay_hints(
        &self,
        start: InputPosition,
        end: InputPosition,
    ) -> anyhow::Result<impl Iterator<Item = InlayHint<'project>>> {
        let db = &self.project.db;
        let file = db.loaded_python_file(self.file_index);
        debug!(
            "Position for inlay hints {}->{start:?} - {end:?}",
            file.file_path(db),
        );
        let start = file.line_column_to_byte(start)?;
        let end = file.line_column_to_byte(end)?;
        let result = file.ensure_calculated_diagnostics(db);
        debug_assert!(result.is_ok());
        Ok(file
            .tree
            .potential_inlay_hints(start.byte, end.byte)
            .filter_map(|potential| match potential {
                PotentialInlayHint::FunctionDef(f) => {
                    if f.return_annotation().is_some()
                        || matches!(f.name().as_code(), "__init__" | "__init_subclass__")
                    {
                        return None;
                    }
                    let func = Function::new_with_unknown_parent(db, NodeRef::new(file, f.index()));
                    let mut t = func.inferred_return_type(&InferenceState::new(db, file));
                    if let Some(new_t) = t.replace_type_var_likes(db, &mut |usage| {
                        if usage.as_type_var_like().is_untyped() {
                            Some(usage.as_any_generic_item())
                        } else {
                            None
                        }
                    }) {
                        t = Cow::Owned(new_t);
                    }
                    if t.is_any() {
                        return None;
                    }
                    let type_ = t.into_owned();
                    Some(InlayHint {
                        db,
                        type_,
                        kind: InlayHintKind::TYPE,
                        position: file.byte_to_position_infos(db, f.params().end()),
                        label_kind: LabelKind::FunctionReturnAnnotation,
                    })
                }
                PotentialInlayHint::Assignment(assignment) => match assignment.unpack() {
                    AssignmentContent::Normal(mut targets, right_side) => {
                        let target = targets.next().unwrap();
                        if targets.next().is_some() {
                            return None;
                        }
                        let (Target::Name(name_def) | Target::NameExpression(_, name_def)) = target
                        else {
                            return None;
                        };
                        let name_def_ref = NodeRef::new(file, name_def.index());
                        let i_s = &InferenceState::new_in_unknown_file(db);
                        if assignment_type_node_ref(file, assignment)
                            .point()
                            .calculated()
                        {
                            // Type assignments like NamedTuple/Enum/TypedDict definitions should
                            // never have an inlay hint, because they can never make sense.
                            return None;
                        }
                        if name_def_ref
                            .name_ref_of_name_def()
                            .point()
                            .maybe_calculated_and_specific()
                            == Some(Specific::NameOfNameDef)
                        {
                            return None;
                        }
                        let inf = name_def_ref.maybe_inferred(i_s)?;
                        let type_ = inf.as_type(i_s);
                        if type_.is_any() {
                            return None;
                        }
                        // Only allow relevant assignments. Literal/Enum/Class instantiation
                        // assignments are not relevant and we therefore ignore them.
                        if avoid_inline_hint(i_s, file, right_side) {
                            return None;
                        }
                        Some(InlayHint {
                            db,
                            kind: InlayHintKind::TYPE,
                            position: file.byte_to_position_infos(db, name_def.end()),
                            type_,
                            label_kind: LabelKind::NormalAnnotation,
                        })
                    }
                    _ => None,
                },
            }))
    }
}

fn avoid_inline_hint(
    i_s: &InferenceState,
    file: &PythonFile,
    right_side: AssignmentRightSide,
) -> bool {
    right_side.is_simple_assignment(&|expr| match expr.unpack() {
        ExpressionContent::ExpressionPart(ExpressionPart::Atom(atom)) => atom.is_literal_value(),
        ExpressionContent::ExpressionPart(ExpressionPart::Primary(prim)) => match prim.second() {
            PrimaryContent::Attribute(_) if prim.is_only_attributes() => {
                NodeRef::new(file, expr.index())
                    .maybe_type()
                    .is_some_and(|t| matches!(t, Type::EnumMember(_)))
            }
            PrimaryContent::Execution(_) => {
                let check = |index| {
                    if let Some(inf) = NodeRef::new(file, index).maybe_inferred(i_s)
                        && let Some(node_ref) = inf.maybe_saved_node_ref(i_s.db)
                    {
                        if node_ref.maybe_class().is_some() {
                            let c = ClassNodeRef::from_node_ref(node_ref);
                            // Only show inlay hints if there are generics in the initialization
                            return c.use_cached_type_vars(i_s.db).is_empty();
                        }
                        return match inf.maybe_complex_point(i_s.db) {
                            Some(ComplexPoint::TypedDictDefinition(_)) => {
                                if let Some(name_def) = node_ref.maybe_name_def()
                                    && let Some(class_def) = name_def.maybe_name_of_class()
                                {
                                    // Shows inlay hints when generics are present
                                    return ClassNodeRef::new(node_ref.file, class_def.index())
                                        .use_cached_type_vars(i_s.db)
                                        .is_empty();
                                }
                                true
                            }
                            // Types like Type[SomeEnum]() initializations should not be shown
                            Some(ComplexPoint::TypeInstance(Type::Type(_))) => true,
                            _ => false,
                        };
                    }
                    false
                };
                match prim.first() {
                    PrimaryOrAtom::Primary(primary) => match primary.second() {
                        PrimaryContent::Attribute(name) => check(name.index()),
                        _ => false,
                    },
                    PrimaryOrAtom::Atom(atom) => check(atom.index()),
                }
            }
            _ => false,
        },
        _ => false,
    })
}

enum LabelKind {
    NormalAnnotation,
    FunctionReturnAnnotation,
}

pub struct InlayHint<'project> {
    db: &'project Database,
    type_: Type,
    pub kind: InlayHintKind,
    pub position: PositionInfos<'project>,
    label_kind: LabelKind,
}

impl InlayHint<'_> {
    pub fn label(&self) -> String {
        let formatted = self.type_.format_short(self.db);
        match self.label_kind {
            LabelKind::NormalAnnotation => format!(": {formatted}"),
            LabelKind::FunctionReturnAnnotation => format!(" -> {formatted}"),
        }
    }
}
