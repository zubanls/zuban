use parsa_python_ast::ParamType;

use super::{ClassLike, LookupResult, OnTypeError, Value, ValueKind};
use crate::arguments::Arguments;
use crate::base_description;
use crate::database::{
    CallableContent, CallableParam, DbType, FormatStyle, TypeVarType, TypeVars, Variance,
};
use crate::debug;
use crate::diagnostics::IssueType;
use crate::generics::{Match, Type, TypeVarMatcher};
use crate::getitem::SliceType;
use crate::inference_state::InferenceState;
use crate::inferred::Inferred;
use crate::params::Param;

pub fn matches_params<'db: 'x, 'x>(
    i_s: &mut InferenceState<'db, '_>,
    mut matcher: Option<&mut TypeVarMatcher<'db, '_>>,
    params1: Option<impl Iterator<Item = impl Param<'db, 'x>>>,
    params2: Option<impl Iterator<Item = impl Param<'db, 'x>>>,
    variance: Variance,
) -> Match {
    if let Some(params1) = params1 {
        if let Some(mut params2) = params2 {
            let mut matches = Match::True;
            for param1 in params1 {
                if let Some(param2) = params2.next() {
                    let pt1 = param1.param_type();
                    let pt2 = param2.param_type();
                    if !(pt1 == pt2
                        || pt1 == ParamType::PositionalOnly
                            && pt2 == ParamType::PositionalOrKeyword)
                    {
                        return Match::False;
                    }
                    if param1.has_default() && !param2.has_default() {
                        return Match::False;
                    }
                    if matches!(
                        param1.param_type(),
                        ParamType::PositionalOrKeyword | ParamType::KeywordOnly
                    ) && param1.name() != param2.name()
                    {
                        return Match::False;
                    }
                    if let Some(t1) = param1.annotation_type(i_s) {
                        if let Some(t2) = param2.annotation_type(i_s) {
                            matches &= t1.matches(i_s, matcher.as_deref_mut(), t2, variance)
                        }
                    }
                } else {
                    return Match::False;
                }
            }
            if params2.next().is_some() {
                return Match::False;
            }
            return matches;
        }
    }
    // If there are no params, it means that anything is accepted, i.e. *args, **kwargs
    Match::True
}

pub fn has_overlapping_params<'db: 'x, 'x>(
    i_s: &mut InferenceState<'db, '_>,
    params1: Option<impl Iterator<Item = impl Param<'db, 'x>>>,
    params2: Option<impl Iterator<Item = impl Param<'db, 'x>>>,
) -> bool {
    if let Some(params1) = params1 {
        if let Some(params2) = params2 {
            return overload_has_overlapping_params(i_s, params1, params2);
        }
    }
    todo!()
}
pub fn overload_has_overlapping_params<'db: 'x, 'x, P1: Param<'db, 'x>, P2: Param<'db, 'x>>(
    i_s: &mut InferenceState<'db, '_>,
    params1: impl Iterator<Item = P1>,
    params2: impl Iterator<Item = P2>,
) -> bool {
    let mut check_type = |param1: P1, param2: P2| {
        if let Some(t1) = param1.annotation_type(i_s) {
            if let Some(t2) = param2.annotation_type(i_s) {
                return t1.overlaps(i_s, &t2);
            }
        }
        true
    };
    // Get rid of defaults first, because they always overlap.
    let mut params2 = params2.filter(|p| !p.has_default()).peekable();
    for param1 in params1.filter(|p| !p.has_default()) {
        match param1.param_type() {
            ParamType::PositionalOrKeyword | ParamType::PositionalOnly => {
                if let Some(param2) = params2.peek() {
                    if !check_type(param1, *param2) {
                        return false;
                    }
                    match param2.param_type() {
                        ParamType::PositionalOrKeyword | ParamType::PositionalOnly => {
                            params2.next(); // We only peeked.
                        }
                        ParamType::KeywordOnly => {
                            todo!()
                        }
                        ParamType::Starred => (),
                        ParamType::DoubleStarred => (),
                    }
                } else {
                    return false;
                }
            }
            ParamType::KeywordOnly => {
                if let Some(param2) = params2.peek() {
                    if param2.param_type() == ParamType::Starred {
                        params2.next();
                    }
                }
                if let Some(param2) = params2.peek() {
                    if !check_type(param1, *param2) {
                        return false;
                    }
                    match param2.param_type() {
                        ParamType::PositionalOrKeyword => {
                            todo!()
                        }
                        ParamType::PositionalOnly => todo!(),
                        ParamType::Starred => {
                            todo!()
                        }
                        ParamType::KeywordOnly => {
                            todo!()
                        }
                        ParamType::DoubleStarred => (),
                    }
                } else {
                    return false;
                }
            }
            ParamType::Starred => {
                while match params2.peek() {
                    Some(p) => !matches!(
                        p.param_type(),
                        ParamType::KeywordOnly | ParamType::DoubleStarred
                    ),
                    None => false,
                } {
                    if let Some(param2) = params2.next() {
                        if !check_type(param1, param2) {
                            return false;
                        }
                    }
                }
            }
            ParamType::DoubleStarred => {
                for param2 in params2 {
                    if !check_type(param1, param2) {
                        return false;
                    }
                }
                return true;
            }
        }
    }
    for param2 in params2 {
        if !matches!(
            param2.param_type(),
            ParamType::Starred | ParamType::DoubleStarred
        ) {
            return false;
        }
    }
    true
}

pub trait CallableLike<'db: 'a, 'a>: Value<'db, 'a> {
    fn result_type(&self, i_s: &mut InferenceState<'db, '_>) -> Type<'db, 'a>;
    fn format(&self, i_s: &mut InferenceState<'db, '_>, style: FormatStyle) -> Box<str>;
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

    pub fn param_iterator(&self) -> Option<impl Iterator<Item = &'a CallableParam>> {
        self.content.params.as_ref().map(|params| params.iter())
    }
}

impl<'db: 'a, 'a> CallableLike<'db, 'a> for CallableClass<'a> {
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
