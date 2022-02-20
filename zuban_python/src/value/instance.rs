use super::{Class, ClassLike, Value, ValueKind};
use crate::arguments::Arguments;
use crate::getitem::SliceType;
use crate::inference_state::InferenceState;
use crate::inferred::Inferred;

#[derive(Debug, Clone, Copy)]
pub struct Instance<'db, 'a> {
    pub class: Class<'db, 'a>,
    inferred: &'a Inferred<'db>,
}

impl<'db, 'a> Instance<'db, 'a> {
    pub fn new(class: Class<'db, 'a>, inferred: &'a Inferred<'db>) -> Self {
        Self { class, inferred }
    }

    pub fn as_inferred(&self) -> &'a Inferred<'db> {
        self.inferred
    }
}

impl<'db, 'a> Value<'db, 'a> for Instance<'db, 'a> {
    fn kind(&self) -> ValueKind {
        ValueKind::Object
    }

    fn name(&self) -> &'db str {
        self.class.name()
    }

    fn lookup_internal(
        &self,
        i_s: &mut InferenceState<'db, '_>,
        name: &str,
    ) -> Option<Inferred<'db>> {
        for (mro_index, class) in self.class.mro(i_s) {
            if let ClassLike::Class(c) = class {
                let inf = c
                    .class_storage
                    .self_symbol_table
                    .lookup_symbol(name)
                    .map(|node_index| {
                        c.reference
                            .file
                            .inference(&mut i_s.with_class_context(&c))
                            .infer_name_by_index(node_index)
                    });
                if let Some(inf) = inf {
                    return Some(inf.resolve_function_return(i_s));
                }
            }
            if let Some(inf) = class.lookup_symbol(i_s, name) {
                return Some(inf.resolve_function_return(i_s).bind(i_s, self, mro_index));
            }
        }
        None
    }

    fn should_add_lookup_error(&self, i_s: &mut InferenceState<'db, '_>) -> bool {
        !self.class.class_infos(i_s).incomplete_mro
    }

    fn execute(
        &self,
        i_s: &mut InferenceState<'db, '_>,
        args: &dyn Arguments<'db>,
    ) -> Inferred<'db> {
        todo!()
    }

    fn get_item(
        &self,
        i_s: &mut InferenceState<'db, '_>,
        slice_type: &SliceType<'db>,
    ) -> Inferred<'db> {
        self.lookup(i_s, "__getitem__", slice_type.as_node_ref())
            .run_on_value(i_s, &mut |i_s, v| v.execute(i_s, &slice_type.as_args()))
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
            self.class.as_string(i_s),
        )
    }
}
