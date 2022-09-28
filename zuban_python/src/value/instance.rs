use super::{Class, LookupResult, OnTypeError, Value, ValueKind};
use crate::arguments::Arguments;
use crate::database::PointLink;
use crate::diagnostics::IssueType;
use crate::file_state::File;
use crate::getitem::SliceType;
use crate::inference_state::InferenceState;
use crate::inferred::Inferred;
use crate::matching::{FormatData, ResultContext, Type};
use crate::node_ref::NodeRef;

#[derive(Debug, Clone, Copy)]
pub struct Instance<'a> {
    pub class: Class<'a>,
    inferred_link: Option<NodeRef<'a>>,
}

impl<'a> Instance<'a> {
    pub fn new(class: Class<'a>, inferred_link: Option<NodeRef<'a>>) -> Self {
        Self {
            class,
            inferred_link,
        }
    }

    pub fn as_inferred(&self, i_s: &mut InferenceState) -> Inferred {
        if let Some(inferred_link) = self.inferred_link {
            Inferred::from_saved_node_ref(inferred_link)
        } else {
            let t = self.class.as_db_type(i_s);
            Inferred::execute_db_type(i_s, t)
        }
    }
}

impl<'db, 'a> Value<'db, 'a> for Instance<'a> {
    fn kind(&self) -> ValueKind {
        ValueKind::Object
    }

    fn name(&self) -> &str {
        self.class.name()
    }

    fn lookup_internal(&self, i_s: &mut InferenceState, name: &str) -> LookupResult {
        for (mro_index, class) in self.class.mro(i_s) {
            if let Some(c) = class.maybe_class(i_s.db) {
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
            let result = class.lookup_symbol(i_s, name).map(|inf| {
                inf.resolve_function_return(i_s)
                    .bind(i_s, |i_s| self.as_inferred(i_s), mro_index)
            });
            if !matches!(result, LookupResult::None) {
                return result;
            }
        }
        LookupResult::None
    }

    fn should_add_lookup_error(&self, i_s: &mut InferenceState) -> bool {
        !self.class.class_infos(i_s).incomplete_mro
    }

    fn execute(
        &self,
        i_s: &mut InferenceState<'db, '_>,
        args: &dyn Arguments<'db>,
        result_context: &mut ResultContext,
        on_type_error: OnTypeError<'db, '_>,
    ) -> Inferred {
        if let Some(inf) = self.lookup_internal(i_s, "__call__").into_maybe_inferred() {
            inf.run_on_value(i_s, &mut |i_s, value| {
                value.execute(i_s, args, result_context, on_type_error)
            })
        } else {
            args.as_node_ref().add_typing_issue(
                i_s.db,
                IssueType::NotCallable {
                    type_: format!("{:?}", self.name()).into(),
                },
            );
            Inferred::new_unknown()
        }
    }

    fn get_item(&self, i_s: &mut InferenceState, slice_type: &SliceType) -> Inferred {
        let args = slice_type.as_args(i_s.context);
        self.lookup_implicit(i_s, "__getitem__", &|i_s| {
            slice_type.as_node_ref().add_typing_issue(
                i_s.db,
                IssueType::NotIndexable {
                    type_: self.class.format(&FormatData::new_short(i_s.db)),
                },
            )
        })
        .run_on_value(i_s, &mut |i_s, v| {
            v.execute(
                i_s,
                &args,
                &mut ResultContext::Unknown,
                &|i_s, node_ref, class, function, p, actual, expected| {
                    node_ref.add_typing_issue(
                        i_s.db,
                        IssueType::InvalidGetItem {
                            actual,
                            type_: class.unwrap().format(&FormatData::new_short(i_s.db)),
                            expected,
                        },
                    )
                },
            )
        })
    }

    fn as_instance(&self) -> Option<&Instance<'a>> {
        Some(self)
    }

    fn as_type(&self, i_s: &mut InferenceState<'db, '_>) -> Type<'a> {
        Type::Class(self.class)
    }

    fn description(&self, i_s: &mut InferenceState) -> String {
        format!(
            "{} {}",
            format!("{:?}", self.kind()).to_lowercase(),
            self.class.format(&FormatData::new_short(i_s.db)),
        )
    }
}
