use std::borrow::Cow;

use lsp_types::InlayHintKind;
use parsa_python_cst::{AssignmentContent, PotentialInlayHint, Target};

use crate::{
    Document, InputPosition, PositionInfos,
    database::{Database, Specific},
    debug,
    file::File as _,
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
                    AssignmentContent::Normal(mut targets, _) => {
                        let target = targets.next().unwrap();
                        if targets.next().is_some() {
                            return None;
                        }
                        let (Target::Name(name_def) | Target::NameExpression(_, name_def)) = target
                        else {
                            return None;
                        };
                        let name_def_ref = NodeRef::new(file, name_def.index());
                        if name_def_ref
                            .name_ref_of_name_def()
                            .point()
                            .maybe_calculated_and_specific()
                            == Some(Specific::NameOfNameDef)
                        {
                            return None;
                        }
                        let i_s = &InferenceState::new_in_unknown_file(db);
                        let inf = name_def_ref.maybe_inferred(i_s)?;
                        let type_ = inf.as_type(i_s);
                        if type_.is_any() {
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
