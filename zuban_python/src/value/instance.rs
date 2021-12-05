use super::{Class, ClassLike, Value, ValueKind};
use crate::arguments::Arguments;
use crate::database::GenericPart;
use crate::getitem::SliceType;
use crate::inference_state::InferenceState;
use crate::inferred::Inferred;

#[derive(Debug)]
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

impl<'db, 'a> Value<'db> for Instance<'db, 'a> {
    fn kind(&self) -> ValueKind {
        ValueKind::Object
    }

    fn name(&self) -> &'db str {
        self.class.name()
    }

    fn lookup(&self, i_s: &mut InferenceState<'db, '_>, name: &str) -> Inferred<'db> {
        if let Some(node_index) = self.class.symbol_table.lookup_symbol(name) {
            self.class
                .reference
                .file
                .inference(i_s)
                .infer_name_by_index(node_index)
                .resolve_function_return(i_s)
                .bind(i_s, self)
        } else {
            todo!("{:?}", name)
        }
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
        self.lookup(i_s, "__getitem__")
            .run_on_value(i_s, &mut |i_s, v| v.execute(i_s, &slice_type.as_args()))
    }

    fn as_instance(&self) -> Option<&Instance<'db, '_>> {
        Some(self)
    }

    fn class(&self, i_s: &mut InferenceState<'db, '_>) -> ClassLike<'db, '_> {
        ClassLike::ClassRef(&self.class)
    }

    fn as_generic_part(&self, i_s: &mut InferenceState<'db, '_>) -> GenericPart {
        self.class.as_annotation_generic_part(i_s)
    }
}
