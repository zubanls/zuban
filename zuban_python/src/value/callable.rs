use super::{ClassLike, LookupResult, OnTypeError, Value, ValueKind};
use crate::arguments::Arguments;
use crate::base_description;
use crate::database::{
    CallableContent, CallableParam, DbType, FormatStyle, TypeVarType, TypeVars, Variance,
};
use crate::debug;
use crate::diagnostics::IssueType;
use crate::generics::{Generics, Match, Type, TypeVarMatcher};
use crate::getitem::SliceType;
use crate::inference_state::InferenceState;
use crate::inferred::Inferred;

pub trait CallableLike<'db: 'a, 'a>: Value<'db, 'a> {
    fn param_generics(&self) -> Generics<'db, '_>;
    fn result_type(&self, i_s: &mut InferenceState<'db, '_>) -> Type<'db, 'a>;
    fn format(&self, i_s: &mut InferenceState<'db, '_>, style: FormatStyle) -> Box<str>;
    fn matches<T: CallableLike<'db, 'a>>(
        &self,
        i_s: &mut InferenceState<'db, '_>,
        mut matcher: Option<&mut TypeVarMatcher<'db, '_>>,
        other: &T,
    ) -> Match {
        let other_result = other.result_type(i_s);
        self.result_type(i_s).matches(
            i_s,
            matcher.as_deref_mut(),
            other_result,
            Variance::Covariant,
        ) & self.param_generics().matches(
            i_s,
            matcher,
            other.param_generics(),
            Variance::Contravariant,
            None,
        ) | Match::FalseButSimilar
    }
}

#[derive(Debug, Clone, Copy)]
pub struct CallableClass<'a> {
    pub content: &'a CallableContent,
    db_type: &'a DbType,
}

impl<'a> CallableClass<'a> {
    pub fn new(db_type: &'a DbType, content: &'a CallableContent) -> Self {
        Self { db_type, content }
    }

    pub fn as_db_type(&self) -> DbType {
        DbType::Callable(self.content.clone())
    }
}

impl<'db: 'a, 'a> CallableLike<'db, 'a> for CallableClass<'a> {
    fn param_generics(&self) -> Generics<'db, '_> {
        self.content
            .params
            .as_ref()
            .map(|p| Generics::Params(p))
            .unwrap_or(Generics::None)
    }

    fn result_type(&self, i_s: &mut InferenceState<'db, '_>) -> Type<'db, 'a> {
        Type::from_db_type(i_s.db, &self.content.return_class)
    }

    fn format(&self, i_s: &mut InferenceState<'db, '_>, style: FormatStyle) -> Box<str> {
        self.content.format(i_s.db, style).into()
    }
}

impl<'db, 'a> Value<'db, 'a> for CallableClass<'a> {
    fn kind(&self) -> ValueKind {
        ValueKind::Class
    }

    fn name(&self) -> &'db str {
        "Callable"
    }

    fn lookup_internal(&self, i_s: &mut InferenceState<'db, '_>, name: &str) -> LookupResult<'db> {
        debug!("TODO this should at least have the object results");
        LookupResult::None
    }

    fn as_class_like(&self) -> Option<ClassLike<'db, 'a>> {
        Some(ClassLike::Callable(*self))
    }

    fn class(&self, i_s: &mut InferenceState<'db, '_>) -> ClassLike<'db, 'a> {
        ClassLike::TypeWithDbType(self.db_type)
    }

    fn get_item(
        &self,
        i_s: &mut InferenceState<'db, '_>,
        slice_type: &SliceType<'db, '_>,
    ) -> Inferred<'db> {
        slice_type
            .as_node_ref()
            .add_typing_issue(i_s.db, IssueType::OnlyClassTypeApplication);
        Inferred::new_any()
    }
}

#[derive(Debug)]
pub struct Callable<'a> {
    db_type: &'a DbType,
    content: &'a CallableContent,
}

impl<'a> Callable<'a> {
    pub fn new(db_type: &'a DbType, content: &'a CallableContent) -> Self {
        Self { db_type, content }
    }

    pub fn as_db_type(&self) -> DbType {
        DbType::Callable(self.content.clone())
    }

    fn description(&self, i_s: &mut InferenceState) -> String {
        base_description!(self) + &self.content.format(i_s.db, FormatStyle::Short)
    }

    pub fn iter_params(&self) -> Option<impl Iterator<Item = &'a CallableParam>> {
        self.content.params.as_ref().map(|params| params.iter())
    }
}

impl<'db, 'a> Value<'db, 'a> for Callable<'a> {
    fn kind(&self) -> ValueKind {
        ValueKind::Object
    }

    fn name(&self) -> &'db str {
        "Callable"
    }

    fn lookup_internal(&self, i_s: &mut InferenceState<'db, '_>, name: &str) -> LookupResult<'db> {
        todo!()
    }

    fn class(&self, i_s: &mut InferenceState<'db, '_>) -> ClassLike<'db, 'a> {
        ClassLike::Callable(CallableClass::new(self.db_type, self.content))
    }

    fn execute(
        &self,
        i_s: &mut InferenceState<'db, '_>,
        args: &dyn Arguments<'db>,
        on_type_error: OnTypeError<'db, '_>,
    ) -> Inferred<'db> {
        let mut type_vars = vec![]; // todo!()
        if let Some(params) = &self.content.params {
            for param in params.iter() {
                param
                    .db_type
                    .scan_for_late_bound_type_vars(i_s.db, &mut type_vars)
            }
        }
        let type_vars = TypeVars::from_vec(type_vars);
        let mut finder = TypeVarMatcher::from_callable(
            self,
            args,
            Some(&type_vars),
            TypeVarType::LateBound,
            on_type_error,
        );
        finder.matches_signature(i_s); // TODO this should be different
        let g_o = Type::from_db_type(i_s.db, &self.content.return_class);
        g_o.execute_and_resolve_type_vars(i_s, None, Some(&mut finder))
    }

    fn description(&self, i_s: &mut InferenceState) -> String {
        base_description!(self) + &self.content.format(i_s.db, FormatStyle::Short)
    }
}
