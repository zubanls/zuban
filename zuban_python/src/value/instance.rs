use super::{Class, ClassLike, LookupResult, OnTypeError, Value, ValueKind};
use crate::arguments::Arguments;
use crate::database::{ComplexPoint, FormatStyle, PointLink};
use crate::diagnostics::IssueType;
use crate::file_state::File;
use crate::getitem::SliceType;
use crate::inference_state::InferenceState;
use crate::inferred::Inferred;
use crate::node_ref::NodeRef;

#[derive(Debug, Clone, Copy)]
pub struct Instance<'db, 'a> {
    pub class: Class<'db, 'a>,
    inferred_link: Option<NodeRef<'db>>,
}

impl<'db, 'a> Instance<'db, 'a> {
    pub fn new(class: Class<'db, 'a>, inferred_link: Option<NodeRef<'db>>) -> Self {
        Self {
            class,
            inferred_link,
        }
    }

    pub fn as_inferred(&self, i_s: &mut InferenceState<'db, '_>) -> Inferred<'db> {
        if let Some(inferred_link) = self.inferred_link {
            Inferred::from_saved_node_ref(inferred_link)
        } else {
            Inferred::new_unsaved_complex(ComplexPoint::Instance(
                self.class.node_ref.as_link(),
                self.class.generics.as_generics_list(i_s),
            ))
        }
    }
}

impl<'db, 'a> Value<'db, 'a> for Instance<'db, 'a> {
    fn kind(&self) -> ValueKind {
        ValueKind::Object
    }

    fn name(&self) -> &'db str {
        self.class.name()
    }

    fn lookup_internal(&self, i_s: &mut InferenceState<'db, '_>, name: &str) -> LookupResult<'db> {
        for (mro_index, class) in self.class.mro(i_s) {
            if let ClassLike::Class(c) = class {
                if let Some(self_symbol) = c.class_storage.self_symbol_table.lookup_symbol(name) {
                    return LookupResult::GotoName(
                        PointLink::new(c.node_ref.file.file_index(), self_symbol),
                        c.node_ref
                            .file
                            .inference(&mut i_s.with_class_context(&c))
                            .infer_name_by_index(self_symbol)
                            .resolve_function_return(i_s),
                    );
                }
            }
            let result = class
                .lookup_symbol(i_s, name)
                .map(|inf| inf.resolve_function_return(i_s).bind(i_s, self, mro_index));
            if !matches!(result, LookupResult::None) {
                return result;
            }
        }
        LookupResult::None
    }

    fn should_add_lookup_error(&self, i_s: &mut InferenceState<'db, '_>) -> bool {
        !self.class.class_infos(i_s).incomplete_mro
    }

    fn execute(
        &self,
        i_s: &mut InferenceState<'db, '_>,
        args: &dyn Arguments<'db>,
        on_type_error: OnTypeError<'db, '_>,
    ) -> Inferred<'db> {
        if let Some(inf) = self.lookup_internal(i_s, "__call__").into_maybe_inferred() {
            inf.run_on_value(i_s, &mut |i_s, value| {
                value.execute(i_s, args, on_type_error)
            })
        } else {
            args.as_node_ref()
                .add_typing_issue(i_s.db, IssueType::NotCallable(format!("{:?}", self.name())));
            Inferred::new_unknown()
        }
    }

    fn get_item(
        &self,
        i_s: &mut InferenceState<'db, '_>,
        slice_type: &SliceType<'db, '_>,
    ) -> Inferred<'db> {
        self.lookup_implicit(i_s, "__getitem__", &|i_s| {
            slice_type.as_node_ref().add_typing_issue(
                i_s.db,
                IssueType::NotIndexable(self.class.as_string(i_s, FormatStyle::Short)),
            )
        })
        .run_on_value(i_s, &mut |i_s, v| {
            v.execute(
                i_s,
                &slice_type.as_args(),
                &|i_s, node_ref, class, function, p, input, wanted| {
                    node_ref.add_typing_issue(
                        i_s.db,
                        IssueType::InvalidGetItem(format!(
                            "Invalid index type {input:?} for {:?}; expected type {wanted:?}",
                            class.unwrap().as_string(i_s, FormatStyle::Short),
                        )),
                    )
                },
            )
        })
    }

    fn as_instance(&self) -> Option<&Instance<'db, 'a>> {
        Some(self)
    }

    fn class(&self, i_s: &mut InferenceState<'db, '_>) -> ClassLike<'db, 'a> {
        ClassLike::Class(self.class)
    }

    fn description(&self, i_s: &mut InferenceState<'db, '_>) -> String {
        format!(
            "{} {}",
            format!("{:?}", self.kind()).to_lowercase(),
            self.class.as_string(i_s, FormatStyle::Short),
        )
    }
}
