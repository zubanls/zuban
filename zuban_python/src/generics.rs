use parsa_python_ast::{
    Expression, ParamIterator, ParamType, SliceContent, SliceIterator, SliceType, Slices,
};

use crate::arguments::{Argument, Arguments};
use crate::database::CallableParam;
use crate::database::{
    Database, DbType, FormatStyle, GenericsList, TypeVarIndex, TypeVarType, TypeVarUsage, TypeVars,
    Variance,
};
use crate::debug;
use crate::diagnostics::IssueType;
use crate::file::PythonFile;
use crate::inference_state::InferenceState;
use crate::inferred::Inferred;
use crate::node_ref::NodeRef;
use crate::params::{InferrableParamIterator2, Param};
use crate::value::{
    Callable, CallableClass, Class, ClassLike, Function, OnTypeError, TupleClass, Value,
};

macro_rules! replace_class_vars {
    ($i_s:ident, $g:ident, $type_var_generics:ident) => {
        match $type_var_generics {
            None | Some(Generics::None) => $g.clone(),
            Some(type_var_generics) => $g.clone().replace_type_vars(&mut |t| {
                if t.type_ == TypeVarType::Class {
                    type_var_generics.nth($i_s, t.index)
                } else {
                    DbType::Unknown
                }
            }),
        }
    };
}

#[derive(Debug, Clone, Copy)]
pub enum Generics<'db, 'a> {
    Expression(&'db PythonFile, Expression<'db>),
    Slices(&'db PythonFile, Slices<'db>),
    List(&'a GenericsList, Option<&'a Generics<'db, 'a>>),
    Params(&'a [CallableParam]),
    Class(&'a Class<'db, 'a>),
    DbType(&'a DbType),
    FunctionParams(&'a Function<'db, 'a>),
    None,
}

impl<'db, 'a> Generics<'db, 'a> {
    pub fn new_slice(file: &'db PythonFile, slice_type: SliceType<'db>) -> Self {
        match slice_type {
            SliceType::NamedExpression(named) => Self::Expression(file, named.expression()),
            SliceType::Slice(_) => Self::None,
            SliceType::Slices(slices) => Self::Slices(file, slices),
        }
    }

    pub fn new_list(list: &'a GenericsList) -> Self {
        Self::List(list, None)
    }

    pub fn nth(&self, i_s: &mut InferenceState<'db, '_>, n: TypeVarIndex) -> DbType {
        match self {
            Self::Expression(file, expr) => {
                if n.as_usize() == 0 {
                    file.inference(i_s).infer_expression(*expr).as_db_type(i_s)
                } else {
                    debug!(
                        "Generic expr {:?} has one item, but {n:?} was requested",
                        expr.short_debug(),
                    );
                    DbType::Any
                }
            }
            Self::Slices(file, slices) => slices
                .iter()
                .nth(n.as_usize())
                .map(|slice_content| match slice_content {
                    SliceContent::NamedExpression(n) => file
                        .inference(i_s)
                        .infer_expression(n.expression())
                        .as_db_type(i_s),
                    SliceContent::Slice(s) => todo!(),
                })
                .unwrap_or(DbType::Any),
            Self::List(list, type_var_generics) => {
                if let Some(g) = list.nth(n) {
                    replace_class_vars!(i_s, g, type_var_generics)
                } else {
                    debug!(
                        "Generic list {} given, but item {n:?} was requested",
                        self.as_string(i_s, FormatStyle::Short, None),
                    );
                    DbType::Any
                }
            }
            Self::Params(_) => todo!(),
            Self::DbType(g) => (*g).clone(),
            Self::Class(s) => todo!(),
            Self::FunctionParams(f) => todo!(),
            Self::None => {
                debug!("No generics given, but {n:?} was requested");
                DbType::Any
            }
        }
    }

    pub fn iter(&self) -> GenericsIterator<'db, 'a> {
        match self {
            Self::Expression(file, expr) => GenericsIterator::Expression(file, *expr),
            Self::Slices(file, slices) => GenericsIterator::SliceIterator(file, slices.iter()),
            Self::List(l, t) => GenericsIterator::GenericsList(l.iter(), *t),
            Self::DbType(g) => GenericsIterator::DbType(g),
            Self::Class(s) => GenericsIterator::Class(*s),
            Self::Params(p) => GenericsIterator::Params(p.iter()),
            Self::FunctionParams(f) => {
                GenericsIterator::ParamIterator(f.node_ref.file, f.iter_params())
            }
            Self::None => GenericsIterator::None,
        }
    }

    pub fn as_generics_list(&self, i_s: &mut InferenceState<'db, '_>) -> Option<GenericsList> {
        match self {
            Self::Expression(file, expr) => Some(GenericsList::new_generics(Box::new([file
                .inference(i_s)
                .infer_expression(*expr)
                .as_db_type(i_s)]))),
            Self::Slices(file, slices) => Some(GenericsList::new_generics(
                slices
                    .iter()
                    .map(|slice| {
                        if let SliceContent::NamedExpression(n) = slice {
                            file.inference(i_s)
                                .infer_expression(n.expression())
                                .as_db_type(i_s)
                        } else {
                            todo!()
                        }
                    })
                    .collect(),
            )),
            Self::DbType(g) => todo!(),
            Self::Class(_) => todo!(),
            Self::FunctionParams(f) => todo!(),
            Self::List(l, type_var_generics) => Some(GenericsList::new_generics(
                l.iter()
                    .map(|c| replace_class_vars!(i_s, c, type_var_generics))
                    .collect(),
            )),
            Self::Params(_) => todo!(),
            Self::None => None,
        }
    }

    pub fn as_string(
        &self,
        i_s: &mut InferenceState<'db, '_>,
        style: FormatStyle,
        expected: Option<usize>,
    ) -> String {
        // Returns something like [str] or [List[int], Set[Any]]
        let mut strings = vec![];
        let mut i = 0;
        self.iter().run_on_all(i_s, &mut |i_s, g| {
            if expected.map(|e| i < e).unwrap_or(false) {
                strings.push(g.as_string(i_s, None, style));
                i += 1;
            }
        });
        if let Some(expected) = expected {
            for _ in i..expected {
                strings.push("Any".to_owned());
            }
        }
        format!("[{}]", strings.join(", "))
    }

    pub fn matches(
        &self,
        i_s: &mut InferenceState<'db, '_>,
        mut matcher: Option<&mut TypeVarMatcher<'db, '_>>,
        value_generics: Self,
        variance: Variance,
        type_vars: Option<&TypeVars>,
    ) -> bool {
        let mut value_generics = value_generics.iter();
        let mut matches = true;
        let mut type_var_iterator = type_vars.map(|t| t.iter());
        self.iter().run_on_all(i_s, &mut |i_s, type_| {
            let appeared = value_generics.run_on_next(i_s, &mut |i_s, g| {
                let v = if let Some(t) = type_var_iterator.as_mut().and_then(|t| t.next()) {
                    t.variance
                } else {
                    variance
                };
                matches &= type_.matches(i_s, matcher.as_deref_mut(), g, v);
            });
            if appeared.is_none() {
                debug!("Generic not found for: {type_:?}");
            }
        });
        matches
    }
}

pub enum GenericsIterator<'db, 'a> {
    SliceIterator(&'db PythonFile, SliceIterator<'db>),
    GenericsList(std::slice::Iter<'a, DbType>, Option<&'a Generics<'db, 'a>>),
    Params(std::slice::Iter<'a, CallableParam>),
    DbType(&'a DbType),
    Class(&'a Class<'db, 'a>),
    ParamIterator(&'db PythonFile, ParamIterator<'db>),
    Expression(&'db PythonFile, Expression<'db>),
    None,
}

impl<'db> GenericsIterator<'db, '_> {
    fn run_on_next<T>(
        &mut self,
        i_s: &mut InferenceState<'db, '_>,
        callable: &mut impl FnMut(&mut InferenceState<'db, '_>, Type<'db, '_>) -> T,
    ) -> Option<T> {
        match self {
            Self::Expression(file, expr) => {
                let g = file
                    .inference(i_s)
                    .use_annotation_expression_or_generic_type(*expr);
                let result = callable(i_s, g);
                *self = Self::None;
                Some(result)
            }
            Self::SliceIterator(file, iter) => {
                if let Some(SliceContent::NamedExpression(s)) = iter.next() {
                    let g = file
                        .inference(i_s)
                        .use_annotation_expression_or_generic_type(s.expression());
                    Some(callable(i_s, g))
                } else {
                    None
                }
            }
            Self::GenericsList(iterator, type_var_generics) => iterator.next().map(|g| {
                let g = replace_class_vars!(i_s, g, type_var_generics);
                callable(i_s, Type::from_db_type(i_s.db, &g))
            }),
            Self::Params(iterator) => iterator
                .next()
                .map(|p| callable(i_s, Type::from_db_type(i_s.db, &p.db_type))),
            Self::DbType(g) => {
                let result = Some(callable(i_s, Type::from_db_type(i_s.db, g)));
                *self = Self::None;
                result
            }
            Self::Class(s) => {
                let result = callable(i_s, Type::ClassLike(ClassLike::Class(**s)));
                *self = Self::None;
                Some(result)
            }
            Self::ParamIterator(f, params) => params.next().map(|p| {
                p.annotation()
                    .map(|a| {
                        let t = f.inference(i_s).use_cached_annotation_type(a);
                        callable(i_s, t)
                    })
                    .unwrap_or_else(|| callable(i_s, Type::None))
            }),
            Self::None => None,
        }
    }

    pub fn run_on_all(
        mut self,
        i_s: &mut InferenceState<'db, '_>,
        callable: &mut impl FnMut(&mut InferenceState<'db, '_>, Type<'db, '_>),
    ) {
        while self.run_on_next(i_s, callable).is_some() {}
    }
}

#[derive(Debug)]
enum FunctionOrCallable<'db, 'a> {
    Function(Option<&'a Class<'db, 'a>>, Function<'db, 'a>),
    Callable(&'a Callable<'a>),
}

pub struct TypeVarMatcher<'db, 'a> {
    func_or_callable: FunctionOrCallable<'db, 'a>,
    args: &'a dyn Arguments<'db>,
    skip_first_param: bool,
    pub calculated_type_vars: Option<GenericsList>,
    matches: bool,
    type_vars: Option<&'a TypeVars>,
    match_type: TypeVarType,
    on_type_error: Option<OnTypeError<'db, 'a>>,
}

impl<'db, 'a> TypeVarMatcher<'db, 'a> {
    pub fn new(
        class: Option<&'a Class<'db, 'a>>,
        function: Function<'db, 'a>,
        args: &'a dyn Arguments<'db>,
        skip_first_param: bool,
        type_vars: Option<&'a TypeVars>,
        match_type: TypeVarType,
        on_type_error: Option<OnTypeError<'db, 'a>>,
    ) -> Self {
        Self {
            func_or_callable: FunctionOrCallable::Function(class, function),
            args,
            calculated_type_vars: None,
            skip_first_param,
            matches: true,
            type_vars,
            match_type,
            on_type_error,
        }
    }
    // TODO the structure of this impl looks very weird, strange funcs

    pub fn from_callable(
        callable: &'a Callable<'a>,
        args: &'a dyn Arguments<'db>,
        type_vars: Option<&'a TypeVars>,
        match_type: TypeVarType,
        on_type_error: OnTypeError<'db, 'a>,
    ) -> Self {
        Self {
            func_or_callable: FunctionOrCallable::Callable(callable),
            args,
            calculated_type_vars: None,
            skip_first_param: false,
            matches: true,
            type_vars,
            match_type,
            on_type_error: Some(on_type_error),
        }
    }

    pub fn calculate_and_return(
        i_s: &mut InferenceState<'db, '_>,
        class: Option<&'a Class<'db, 'a>>,
        function: Function<'db, 'a>,
        args: &'a dyn Arguments<'db>,
        skip_first_param: bool,
        type_vars: Option<&'db TypeVars>,
        match_type: TypeVarType,
        on_type_error: Option<OnTypeError<'db, 'a>>,
    ) -> Option<GenericsList> {
        let mut self_ = Self::new(
            class,
            function,
            args,
            skip_first_param,
            type_vars,
            match_type,
            on_type_error,
        );
        self_.calculate_type_vars(i_s);
        self_.calculated_type_vars
    }

    fn calculate_type_vars(&mut self, i_s: &mut InferenceState<'db, '_>) {
        // TODO this can be calculated multiple times from different places
        if let Some(type_vars) = self.type_vars {
            if !type_vars.is_empty() {
                self.calculated_type_vars = Some(GenericsList::new_unknown(type_vars.len()));
            }
        }
        match self.func_or_callable {
            FunctionOrCallable::Function(class, function) => {
                // Make sure the type vars are properly pre-calculated, because we are using type
                // vars from in use_cached_annotation_type.
                function.type_vars(i_s);
                self.calculate_type_vars_for_params(
                    i_s,
                    class,
                    Some(&function),
                    function.iter_args_with_params(self.args, self.skip_first_param),
                );
            }
            FunctionOrCallable::Callable(callable) => {
                if let Some(params) = callable.iter_params() {
                    self.calculate_type_vars_for_params(
                        i_s,
                        None,
                        None,
                        InferrableParamIterator2::new(
                            params,
                            self.args.iter_arguments().peekable(),
                        ),
                    );
                }
            }
        }
        if let Some(calculated) = &self.calculated_type_vars {
            let callable_description: String;
            debug!(
                "Calculated type vars: {}[{}]",
                match self.func_or_callable {
                    FunctionOrCallable::Function(_, function) => function.name(),
                    FunctionOrCallable::Callable(callable) => {
                        callable_description = callable.description(i_s);
                        &callable_description
                    }
                },
                calculated.as_string(i_s.db, None, FormatStyle::Short),
            );
        }
    }

    fn calculate_type_vars_for_params<'x, P: Param<'x>>(
        &mut self,
        i_s: &mut InferenceState<'db, '_>,
        class: Option<&Class<'db, '_>>,
        function: Option<&Function<'db, '_>>,
        mut args_with_params: InferrableParamIterator2<'db, '_, impl Iterator<Item = P>, P>,
    ) where
        'db: 'x,
    {
        let mut missing_params = vec![];
        for p in args_with_params.by_ref() {
            if p.argument.is_none() && !p.param.has_default() {
                self.matches = false;
                missing_params.push(p.param);
                continue;
            }
            if let Some(argument) = p.argument {
                if let Some(annotation_type) = p.param.annotation_type(i_s, function) {
                    let value = argument.infer(i_s);
                    let value_class = value.class_as_type(i_s);
                    let mut matches = true;
                    let on_type_error = self.on_type_error;
                    annotation_type.error_if_not_matches(i_s, Some(self), &value, |i_s, t1, t2| {
                        if let Some(on_type_error) = on_type_error {
                            on_type_error(i_s, argument.as_node_ref(), class, function, &p, t1, t2);
                        }
                        matches = false;
                    });
                    self.matches &= matches;
                }
            }
        }
        if args_with_params.too_many_positional_arguments {
            let mut s = "Too many positional arguments".to_owned();
            if let Some(function) = function {
                s += " for ";
                s += &function.diagnostic_string(class);
            }

            self.args
                .as_node_ref()
                .add_typing_issue(i_s.db, IssueType::ArgumentIssue(s));
            self.matches = false
        } else if args_with_params.arguments.peek().is_some() {
            let mut too_many = false;
            for arg in args_with_params.arguments {
                match arg {
                    Argument::Keyword(name, reference) => {
                        let mut s = format!("Unexpected keyword argument {name:?}");
                        if let Some(function) = function {
                            s += " for ";
                            s += &function.diagnostic_string(class);
                        }
                        reference.add_typing_issue(i_s.db, IssueType::ArgumentIssue(s));
                    }
                    _ => too_many = true,
                }
            }
            if too_many {
                let mut s = "Too many arguments".to_owned();
                if let Some(function) = function {
                    s += " for ";
                    s += &function.diagnostic_string(class);
                }

                self.args
                    .as_node_ref()
                    .add_typing_issue(i_s.db, IssueType::ArgumentIssue(s));
            }
            self.matches = false
        } else if !args_with_params.unused_keyword_arguments.is_empty() {
            for unused in args_with_params.unused_keyword_arguments {
                match unused {
                    Argument::Keyword(name, reference) => {
                        let s = if let Some(function) = function {
                            if function
                                .node()
                                .params()
                                .iter()
                                .any(|p| p.name_definition().as_code() == name)
                            {
                                format!(
                                    "{:?} gets multiple values for keyword argument {name:?}",
                                    function.name(),
                                )
                            } else {
                                format!(
                                    "Unexpected keyword argument {name:?} for {:?}",
                                    function.name(),
                                )
                            }
                        } else {
                            debug!("TODO this keyword param could also exist");
                            format!("Unexpected keyword argument {name:?}")
                        };
                        reference.add_typing_issue(i_s.db, IssueType::ArgumentIssue(s));
                    }
                    _ => unreachable!(),
                }
            }
        } else {
            for param in missing_params {
                if let Some(param_name) = param.name() {
                    let s = if param.param_type() == ParamType::KeywordOnly {
                        let mut s = format!("Missing named argument {:?}", param_name);
                        if let Some(function) = function {
                            s += " for ";
                            s += &function.diagnostic_string(class);
                        }
                        s
                    } else {
                        let mut s = format!("Missing positional argument {:?} in call", param_name);
                        if let Some(function) = function {
                            s += " to ";
                            s += &function.diagnostic_string(class);
                        }
                        s
                    };
                    self.args
                        .as_node_ref()
                        .add_typing_issue(i_s.db, IssueType::ArgumentIssue(s));
                } else {
                    todo!()
                }
            }
        }
    }

    fn nth(&mut self, i_s: &mut InferenceState<'db, '_>, index: TypeVarIndex) -> Option<DbType> {
        if let Some(type_vars) = &self.calculated_type_vars {
            type_vars.nth(index).cloned()
        } else {
            self.calculate_type_vars(i_s);
            self.nth(i_s, index)
        }
    }

    pub fn match_or_add_type_var(
        &mut self,
        i_s: &mut InferenceState<'db, '_>,
        type_var_usage: &TypeVarUsage,
        value_type: Type<'db, '_>,
    ) -> bool {
        let type_var = &type_var_usage.type_var;
        if type_var_usage.type_ == TypeVarType::Class {
            match self.func_or_callable {
                FunctionOrCallable::Function(class, f) => {
                    if let Some(type_var_remap) = f.class.unwrap().type_var_remap {
                        let g = type_var_remap.nth(type_var_usage.index).unwrap();
                        let g = Type::from_db_type(i_s.db, g);
                        let mut new_func = f;
                        new_func.class.as_mut().unwrap().type_var_remap = None;
                        // Since we now used the type_var_remap, it needs to be temporarily
                        // replaced with no type_var_remap, to avoid looping when we find type vars
                        // again in the type_var_remap.
                        let old = std::mem::replace(
                            &mut self.func_or_callable,
                            FunctionOrCallable::Function(class, new_func),
                        );
                        let result = g.matches(i_s, Some(self), value_type, type_var.variance);
                        self.func_or_callable = old;
                        return result;
                    } else if !matches!(f.class.unwrap().generics, Generics::None) {
                        let g = f.class.unwrap().generics.nth(i_s, type_var_usage.index);
                        // TODO nth should return a type instead of DbType
                        let g = Type::from_db_type(i_s.db, &g);
                        return g.matches(i_s, Some(self), value_type, type_var.variance);
                    }
                }
                FunctionOrCallable::Callable(c) => todo!(),
            }
        }
        let mut mismatch_constraints = !type_var.restrictions.is_empty()
            && !type_var.restrictions.iter().any(|t| {
                Type::from_db_type(i_s.db, t).matches(
                    i_s,
                    None,
                    value_type.clone(),
                    Variance::Covariant,
                )
            });
        if let Some(bound) = &type_var.bound {
            mismatch_constraints = mismatch_constraints
                || !Type::from_db_type(i_s.db, bound).matches(
                    i_s,
                    None,
                    value_type.clone(),
                    Variance::Covariant,
                );
        }
        if mismatch_constraints {
            match self.func_or_callable {
                FunctionOrCallable::Function(class, f) => {
                    self.args.as_node_ref().add_typing_issue(
                        i_s.db,
                        IssueType::InvalidTypeVarValue {
                            type_var: type_var.name(i_s.db).to_owned(),
                            func: f.diagnostic_string(class),
                            actual: value_type.as_string(i_s, None, FormatStyle::Short),
                        },
                    );
                }
                _ => todo!(),
            }
        }
        if self.match_type == type_var_usage.type_ {
            if let Some(calculated) = self.calculated_type_vars.as_mut() {
                let current = calculated.nth(type_var_usage.index).unwrap();
                if current == &DbType::Unknown {
                    calculated.set_generic(type_var_usage.index, value_type.into_db_type(i_s));
                } else {
                    let value_db_type = value_type.into_db_type(i_s);
                    if current != &value_db_type {
                        dbg!(current, value_db_type);
                        todo!(
                            "should be: Cannot infer type argument {}",
                            type_var_usage.type_var.name(i_s.db)
                        )
                    }
                }
            }
        } else {
            // Happens e.g. for testInvalidNumberOfTypeArgs
            // class C:  # Forgot to add type params here
            //     def __init__(self, t: T) -> None: pass
            debug!(
                "TODO free type param annotations; searched {:?}, found {:?}",
                self.match_type, type_var_usage.type_
            )
        }
        true
    }

    pub fn matches_signature(&mut self, i_s: &mut InferenceState<'db, '_>) -> bool {
        self.calculate_type_vars(i_s);
        self.matches
    }
}

#[derive(Debug, Clone)]
#[allow(clippy::enum_variant_names)]
pub enum Type<'db, 'a> {
    ClassLike(ClassLike<'db, 'a>),
    Union(Vec<DbType>),
    None,
    Any,
    Never,
}

impl<'db, 'a> Type<'db, 'a> {
    pub fn from_db_type(db: &'db Database, db_type: &'a DbType) -> Self {
        match db_type {
            DbType::Class(link) => {
                let node_ref = NodeRef::from_link(db, *link);
                Self::ClassLike(ClassLike::Class(
                    Class::from_position(node_ref, Generics::None, None).unwrap(),
                ))
            }
            DbType::None => Type::None,
            DbType::Any | DbType::Unknown => Type::Any,
            DbType::Never => Type::Never,
            DbType::GenericClass(link, generics) => {
                let node_ref = NodeRef::from_link(db, *link);
                Self::ClassLike(ClassLike::Class(
                    Class::from_position(node_ref, Generics::new_list(generics), None).unwrap(),
                ))
            }
            DbType::Union(list) => Self::Union(list.iter().cloned().collect()),
            DbType::TypeVar(t) => Self::ClassLike(ClassLike::TypeVar(t)),
            DbType::Type(db_type) => Self::ClassLike(ClassLike::TypeWithDbType(db_type)),
            DbType::Tuple(content) => Self::ClassLike(ClassLike::Tuple(TupleClass::new(content))),
            DbType::Callable(content) => {
                Self::ClassLike(ClassLike::Callable(CallableClass::new(db_type, content)))
            }
        }
    }

    pub fn union(self, i_s: &mut InferenceState<'db, '_>, other: Self) -> Self {
        if let Self::Union(mut list1) = self {
            if let Self::Union(list2) = other {
                list1.extend(list2);
            } else {
                list1.push(other.into_db_type(i_s));
            }
            Self::Union(list1)
        } else if let Self::Union(_) = other {
            other.union(i_s, self)
        } else {
            Type::Union(vec![self.into_db_type(i_s), other.into_db_type(i_s)])
        }
    }

    pub fn into_db_type(self, i_s: &mut InferenceState<'db, '_>) -> DbType {
        match self {
            Self::ClassLike(class_like) => class_like.as_db_type(i_s),
            Self::Union(list) => DbType::Union(GenericsList::generics_from_vec(list)),
            Self::None => DbType::None,
            Self::Any => DbType::Any,
            Self::Never => DbType::Never,
        }
    }

    pub fn matches(
        &self,
        i_s: &mut InferenceState<'db, '_>,
        mut matcher: Option<&mut TypeVarMatcher<'db, '_>>,
        value_class: Self,
        variance: Variance,
    ) -> bool {
        let result = match self {
            Self::ClassLike(class) => class.matches(i_s, value_class, matcher, variance),
            Self::Union(list1) => match value_class {
                // TODO this should use the variance argument
                Self::Union(mut list2) => {
                    let mut type_var_usage = None;
                    for g1 in list1 {
                        if let Some(t) = g1.maybe_type_var_index() {
                            type_var_usage = Some(t);
                        }
                        for (i, g2) in list2.iter().enumerate() {
                            if g1.todo_matches(g2) {
                                list2.remove(i);
                                break;
                            }
                        }
                    }
                    /*
                    if type_var_usage.is_some() {
                            Type::from_db_type(i_s.db, g1).matches(
                                i_s,
                                matcher,
                                Type::from_db_type(i_s.db, g2),
                            );
                    }*/
                    if let Some(type_var_usage) = type_var_usage {
                        if let Some(matcher) = matcher {
                            let g = match list2.len() {
                                0 => unreachable!(),
                                1 => Type::from_db_type(i_s.db, &list2[0]),
                                _ => Type::Union(list2),
                            };
                            matcher.match_or_add_type_var(i_s, type_var_usage, g)
                        } else {
                            true
                        }
                    } else {
                        list2.is_empty()
                    }
                }
                _ => list1.iter().any(|g| {
                    Type::from_db_type(i_s.db, g).matches(
                        i_s,
                        matcher.as_deref_mut(),
                        value_class.clone(),
                        variance,
                    )
                }),
            },
            Self::None => matches!(value_class, Self::None),
            Self::Any => true,
            Self::Never => todo!(),
        };
        result
    }

    pub fn error_if_not_matches<'x>(
        &self,
        i_s: &mut InferenceState<'db, 'x>,
        mut matcher: Option<&mut TypeVarMatcher<'db, '_>>,
        value: &Inferred<'db>,
        mut callback: impl FnMut(&mut InferenceState<'db, 'x>, String, String),
    ) {
        let value_type = value.class_as_type(i_s);
        if !self.matches(i_s, matcher.as_deref_mut(), value_type, Variance::Covariant) {
            let class = matcher.and_then(|matcher| match &matcher.func_or_callable {
                FunctionOrCallable::Function(_, func) => func.class.as_ref(),
                FunctionOrCallable::Callable(_) => None,
            });
            let value_type = value.class_as_type(i_s);
            debug!("Mismatch between {value_type:?} and {self:?}");
            let input = value_type.as_string(i_s, None, FormatStyle::Short);
            let wanted = self.as_string(i_s, class, FormatStyle::Short);
            callback(i_s, input, wanted)
        }
    }

    pub fn execute_and_resolve_type_vars(
        &self,
        i_s: &mut InferenceState<'db, '_>,
        class: Option<&Class<'db, '_>>,
        function_matcher: Option<&mut TypeVarMatcher<'db, '_>>,
    ) -> Inferred<'db> {
        let db_type = self.internal_resolve_type_vars(i_s, class, function_matcher);
        debug!(
            "Resolved type vars: {}",
            db_type.as_type_string(i_s.db, None, FormatStyle::Short)
        );
        Inferred::execute_db_type(i_s, db_type)
    }

    fn internal_resolve_type_vars(
        &self,
        i_s: &mut InferenceState<'db, '_>,
        class: Option<&Class<'db, '_>>,
        mut function_matcher: Option<&mut TypeVarMatcher<'db, '_>>,
    ) -> DbType {
        let resolve_type_var = |i_s: &mut InferenceState<'db, '_>,
                                function_matcher: Option<&mut TypeVarMatcher<'db, '_>>,
                                usage: &TypeVarUsage| {
            match usage.type_ {
                TypeVarType::Class => {
                    if let Some(c) = class {
                        c.generics().nth(i_s, usage.index)
                    } else {
                        // TODO we are just passing the type vars again. Does this make sense?
                        DbType::TypeVar(usage.clone())
                    }
                }
                TypeVarType::Function => {
                    if let Some(fm) = function_matcher {
                        fm.nth(i_s, usage.index).unwrap_or_else(|| unreachable!())
                    } else {
                        // TODO we are just passing the type vars again. Does this make sense?
                        DbType::TypeVar(usage.clone())
                    }
                }
                TypeVarType::LateBound => {
                    if let Some(function_matcher) = function_matcher {
                        if function_matcher.match_type == TypeVarType::LateBound {
                            if let Some(calculated) = function_matcher.nth(i_s, usage.index) {
                                return calculated;
                            }
                        }
                    }
                    // Just pass the type var again, because it might be resolved by a future
                    // callable, that is late bound, like Callable[..., Callable[[T], T]]
                    DbType::TypeVar(usage.clone())
                }
                _ => unreachable!(),
            }
        };

        match self {
            Self::ClassLike(c) => c.as_db_type(i_s).replace_type_vars(&mut |t| {
                resolve_type_var(i_s, function_matcher.as_deref_mut(), t)
            }),
            Self::Union(list) => DbType::Union(GenericsList::new_union(
                list.iter()
                    .map(|g| {
                        g.clone().replace_type_vars(&mut |t| {
                            resolve_type_var(i_s, function_matcher.as_deref_mut(), t)
                        })
                    })
                    .collect(),
            )),
            Self::None => DbType::None,
            Self::Any => todo!(),
            Self::Never => DbType::Never,
        }
    }

    pub fn as_string(
        &self,
        i_s: &mut InferenceState<'db, '_>,
        class: Option<&Class<'db, '_>>,
        style: FormatStyle,
    ) -> String {
        match self {
            Self::ClassLike(c) => c.as_string(i_s, class, style),
            Self::Union(list) => list.iter().fold(String::new(), |a, b| {
                if a.is_empty() {
                    a + &b.as_type_string(i_s.db, None, style)
                } else {
                    a + " | " + &b.as_type_string(i_s.db, None, style)
                }
            }),
            Self::None => "None".to_owned(),
            Self::Any => "Any".to_owned(),
            Self::Never => "<nothing>".to_owned(),
        }
    }
}
