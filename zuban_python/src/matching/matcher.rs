use parsa_python_ast::ParamKind;

use super::params::{InferrableParamIterator2, Param};
use super::{
    ArgumentIndexWithParam, FormatData, Generics, Match, MismatchReason, ResultContext,
    SignatureMatch, Type,
};
use crate::arguments::{ArgumentKind, Arguments};
use crate::database::{
    CallableContent, Database, DbType, FormatStyle, GenericsList, PointLink, TypeVarUsage,
    TypeVars, Variance,
};
use crate::debug;
use crate::diagnostics::IssueType;
use crate::inference_state::InferenceState;
use crate::node_ref::NodeRef;
use crate::value::{Class, Function, OnTypeError, Value};

#[derive(Debug, Clone, Copy)]
enum FunctionOrCallable<'a> {
    Function(Function<'a>),
    Callable(&'a CallableContent),
}

#[derive(Debug, Clone)]
enum TypeVarBound {
    Invariant(DbType),
    Lower(DbType),
    LowerAndUpper(DbType, DbType),
    Upper(DbType),
}

impl TypeVarBound {
    fn new(t: DbType, variance: Variance) -> Self {
        match variance {
            Variance::Invariant => Self::Invariant(t),
            Variance::Covariant => Self::Upper(t),
            Variance::Contravariant => Self::Lower(t),
        }
    }

    fn invert_bounds(&mut self) {
        match std::mem::replace(self, Self::Invariant(DbType::Any)) {
            Self::Invariant(t) => *self = Self::Invariant(t),
            Self::Upper(t) => *self = Self::Lower(t),
            Self::Lower(t) => *self = Self::Upper(t),
            Self::LowerAndUpper(_, _) => unreachable!(),
        }
    }

    fn format(&self, i_s: &mut InferenceState, style: FormatStyle) -> Box<str> {
        match self {
            Self::Invariant(t) | Self::Lower(t) | Self::Upper(t) | Self::LowerAndUpper(t, _) => {
                t.format(&FormatData::with_style(i_s.db, style))
            }
        }
    }

    fn into_db_type(self) -> DbType {
        match self {
            Self::Invariant(t) | Self::Lower(t) | Self::Upper(t) | Self::LowerAndUpper(t, _) => t,
        }
    }

    fn update_lower_bound(&mut self, lower: DbType) {
        match self {
            Self::Lower(_) => *self = Self::Lower(lower),
            Self::Upper(upper) | Self::LowerAndUpper(_, upper) => {
                *self = Self::LowerAndUpper(lower, upper.clone())
            }
            Self::Invariant(_) => unreachable!(),
        }
    }

    fn update_upper_bound(&mut self, upper: DbType) {
        match self {
            Self::Upper(_) => *self = Self::Upper(upper),
            Self::Lower(lower) | Self::LowerAndUpper(lower, _) => {
                *self = Self::LowerAndUpper(lower.clone(), upper)
            }
            Self::Invariant(_) => unreachable!(),
        }
    }

    fn merge_or_mismatch<'db>(
        &mut self,
        i_s: &mut InferenceState<'db, '_>,
        other: &Type,
        variance: Variance,
    ) -> Match {
        // First check if the value is between the bounds.
        let matches = match self {
            Self::Invariant(t) => {
                let m = Type::new(t).is_same_type(i_s, None, other);
                if m.bool() {
                    return m; // In the false case we still have to check for the variance cases.
                }
                m
            }
            Self::Lower(lower) => Type::new(lower).is_super_type_of(i_s, None, other),
            Self::Upper(upper) => Type::new(upper).is_sub_type_of(i_s, None, other),
            Self::LowerAndUpper(lower, upper) => {
                Type::new(lower).is_super_type_of(i_s, None, other)
                    & Type::new(upper).is_sub_type_of(i_s, None, other)
            }
        };
        if matches.bool() {
            // If we are between the bounds we might need to update lower/upper bounds
            let db_other = other.as_db_type(i_s);
            match variance {
                Variance::Invariant => *self = Self::Invariant(db_other),
                Variance::Covariant => self.update_upper_bound(db_other),
                Variance::Contravariant => self.update_lower_bound(db_other),
            }
        } else {
            // If we are not between the lower and upper bound, but the value is co or
            // contravariant, it can still be valid.
            match variance {
                Variance::Invariant => (),
                Variance::Covariant => {
                    if let Self::Invariant(ref t)
                    | Self::Upper(ref t)
                    | Self::LowerAndUpper(_, ref t) = self
                    {
                        let m = Type::new(t).is_super_type_of(i_s, None, other);
                        if !m.bool() && matches!(self, Self::Upper(_)) {
                            *self = Self::Upper(Type::new(t).common_base_class(i_s, other));
                            return Match::True;
                        }
                        return m;
                    }
                }
                Variance::Contravariant => {
                    if let Self::Invariant(t) | Self::Lower(t) | Self::LowerAndUpper(t, _) = self {
                        return Type::new(t).is_sub_type_of(i_s, None, other);
                    }
                }
            };
        }
        matches
    }
}

#[derive(Debug, Default)]
pub struct CalculatedTypeVar {
    type_: Option<TypeVarBound>,
    //variance: Variance,
    defined_by_result_context: bool,
}

#[derive(Debug)]
pub struct TypeVarMatcher<'a> {
    class: Option<&'a Class<'a>>,
    func_or_callable: FunctionOrCallable<'a>,
    calculated_type_vars: &'a mut [CalculatedTypeVar],
    match_in_definition: PointLink,
    parent_matcher: Option<&'a mut Self>,
    pub match_reverse: bool, // For contravariance subtypes
}

impl<'a> TypeVarMatcher<'a> {
    fn new(
        class: Option<&'a Class<'a>>,
        func_or_callable: FunctionOrCallable<'a>,
        match_in_definition: PointLink,
        calculated_type_vars: &'a mut [CalculatedTypeVar],
        //parent_matcher: Option<&'a mut Self>,
    ) -> Self {
        Self {
            class,
            func_or_callable,
            calculated_type_vars,
            match_in_definition,
            match_reverse: false,
            parent_matcher: None, //parent_matcher,
        }
    }

    pub fn new_callable(
        callable: &'a CallableContent,
        calculated_type_vars: &'a mut [CalculatedTypeVar],
    ) -> Self {
        Self {
            class: None,
            func_or_callable: FunctionOrCallable::Callable(callable),
            calculated_type_vars,
            match_in_definition: callable.defined_at,
            match_reverse: false,
            parent_matcher: None, //parent_matcher,
        }
    }

    pub fn new_function(
        function: Function<'a>,
        calculated_type_vars: &'a mut [CalculatedTypeVar],
    ) -> Self {
        Self {
            class: None,
            func_or_callable: FunctionOrCallable::Function(function),
            calculated_type_vars,
            match_in_definition: function.node_ref.as_link(),
            match_reverse: false,
            parent_matcher: None, //parent_matcher,
        }
    }

    pub(super) fn class(&self) -> Option<Class<'_>> {
        // Currently this is used for formatting, but it probably shouldn't be.
        match self.func_or_callable {
            FunctionOrCallable::Function(func) => func.class,
            FunctionOrCallable::Callable(_) => None,
        }
    }

    pub fn match_or_add_type_var(
        &mut self,
        i_s: &mut InferenceState,
        type_var_usage: &TypeVarUsage,
        value_type: &Type,
        variance: Variance,
    ) -> Match {
        let type_var = &type_var_usage.type_var;
        if self.match_in_definition == type_var_usage.in_definition {
            let current = &mut self.calculated_type_vars[type_var_usage.index.as_usize()];
            if let Some(current_type) = &mut current.type_ {
                let m = current_type.merge_or_mismatch(i_s, value_type, variance);
                return match m.bool() || !type_var_usage.type_var.restrictions.is_empty() {
                    true => m,
                    false => match current.defined_by_result_context {
                        true => Match::new_false(),
                        false => Match::False(MismatchReason::CannotInferTypeArgument(
                            type_var_usage.index,
                        )),
                    },
                };
            }
            // Before setting the type var, we need to check if the constraints match.
            let mut mismatch_constraints = false;
            if !type_var.restrictions.is_empty() {
                match value_type.maybe_db_type() {
                    Some(DbType::TypeVar(t2)) if !t2.type_var.restrictions.is_empty() => {
                        if let Some(type_) = &current.type_ {
                            todo!()
                        } else if t2.type_var.restrictions.iter().all(|r2| {
                            type_var.restrictions.iter().any(|r1| {
                                Type::new(r1)
                                    .is_super_type_of(i_s, None, &Type::new(r2))
                                    .bool()
                            })
                        }) {
                            current.type_ =
                                Some(TypeVarBound::Invariant(value_type.as_db_type(i_s)));
                            return Match::True;
                        }
                    }
                    _ => {
                        for restriction in type_var.restrictions.iter() {
                            let m = Type::new(restriction).matches(i_s, None, value_type, variance);
                            if m.bool() {
                                current.type_ = Some(TypeVarBound::Invariant(restriction.clone()));
                                return m;
                            }
                        }
                    }
                }
                mismatch_constraints = true;
            }
            if let Some(bound) = &type_var.bound {
                mismatch_constraints |= !Type::new(bound)
                    .is_super_type_of(i_s, None, value_type)
                    .bool();
            }
            if mismatch_constraints {
                return Match::False(MismatchReason::ConstraintMismatch {
                    expected: value_type.as_db_type(i_s),
                    type_var: type_var_usage.type_var.clone(),
                });
            }
            current.type_ = Some(TypeVarBound::new(value_type.as_db_type(i_s), variance));
            if matches!(value_type.maybe_db_type(), Some(DbType::Any)) {
                Match::TrueWithAny
            } else {
                Match::True
            }
        } else {
            if let Some(parent_matcher) = self.parent_matcher.as_mut() {
                return parent_matcher.match_or_add_type_var(
                    i_s,
                    type_var_usage,
                    value_type,
                    variance,
                );
            }
            if let Some(class) = self.class {
                if class.node_ref.as_link() == type_var_usage.in_definition {
                    let g = class.generics.nth(i_s, type_var_usage.index);
                    return g.matches(i_s, None, value_type, type_var.variance);
                }
            }
            match self.func_or_callable {
                FunctionOrCallable::Function(f) => {
                    // If we're in a class context, we must also be in a method.
                    if let Some(func_class) = f.class {
                        if type_var_usage.in_definition == func_class.node_ref.as_link() {
                            // By definition, because the class did not match there will never be a
                            // type_var_remap that is not defined.
                            let type_var_remap = func_class.type_var_remap.unwrap();
                            let g = Type::new(&type_var_remap[type_var_usage.index]);
                            // The remapping of type vars needs to be checked now. In a lot of
                            // cases this is T -> T and S -> S, but it could also be T -> S and S
                            // -> List[T] or something completely arbitrary.
                            g.matches(i_s, Some(self), value_type, type_var.variance)
                        } else {
                            // Happens e.g. for testInvalidNumberOfTypeArgs
                            // class C:  # Forgot to add type params here
                            //     def __init__(self, t: T) -> None: pass
                            todo!(
                                "TODO free type param annotations; searched ({:?}), found {:?}",
                                self.match_in_definition,
                                type_var_usage.in_definition,
                            )
                        }
                    } else {
                        todo!(
                            "Probably nested generic functions??? {:?} {:?}",
                            type_var_usage.in_definition,
                            self.match_in_definition
                        )
                    }
                }
                FunctionOrCallable::Callable(c) => todo!(),
            }
        }
    }

    pub fn set_all_contained_type_vars_to_any(&mut self, i_s: &mut InferenceState, type_: &DbType) {
        type_.search_type_vars(&mut |t| {
            if t.in_definition == self.match_in_definition {
                let current = &mut self.calculated_type_vars[t.index.as_usize()];
                if current.type_.is_none() {
                    current.type_ = Some(TypeVarBound::Invariant(DbType::Any));
                }
            }
        });
    }

    pub fn format(
        &self,
        db: &Database,
        type_var_usage: &TypeVarUsage,
        style: FormatStyle,
    ) -> Box<str> {
        let i_s = &mut InferenceState::new(db);
        // In general this whole function should look very similar to the matches function, since
        // on mismatches this can be run.
        if self.match_in_definition == type_var_usage.in_definition {
            let current = &self.calculated_type_vars[type_var_usage.index.as_usize()];
            if let Some(bound) = current.type_.as_ref() {
                bound.format(i_s, style)
            } else {
                DbType::Never.format(&FormatData::with_style(db, style))
            }
        } else {
            match self.func_or_callable {
                FunctionOrCallable::Function(f) => {
                    if let Some(class) = self.class {
                        if class.node_ref.as_link() == type_var_usage.in_definition {
                            return class
                                .generics
                                .nth(i_s, type_var_usage.index)
                                .format(&FormatData::with_style(db, style));
                        }
                        let func_class = f.class.unwrap();
                        if type_var_usage.in_definition == func_class.node_ref.as_link() {
                            let type_var_remap = func_class.type_var_remap.unwrap();
                            type_var_remap[type_var_usage.index].format(&FormatData {
                                db,
                                matcher: Some(self),
                                style,
                                verbose: false,
                            })
                        } else {
                            type_var_usage.type_var.name(db).into()
                        }
                    } else {
                        todo!("Probably nested generic functions???")
                    }
                }
                FunctionOrCallable::Callable(c) => todo!(),
            }
        }
    }

    pub fn replace_type_vars_for_nested_context(
        &self,
        i_s: &mut InferenceState,
        t: &DbType,
    ) -> DbType {
        t.replace_type_vars(&mut |type_var_usage| {
            if type_var_usage.in_definition == self.match_in_definition {
                let current = &self.calculated_type_vars[type_var_usage.index.as_usize()];
                current
                    .type_
                    .clone()
                    .map(|t| t.into_db_type())
                    // Any is just ignored by the context later.
                    .unwrap_or(DbType::Any)
            } else {
                match self.func_or_callable {
                    FunctionOrCallable::Function(f) => {
                        if let Some(class) = self.class {
                            if class.node_ref.as_link() == type_var_usage.in_definition {
                                return class
                                    .generics
                                    .nth(i_s, type_var_usage.index)
                                    .into_db_type(i_s);
                            }
                            let func_class = f.class.unwrap();
                            if type_var_usage.in_definition == func_class.node_ref.as_link() {
                                let type_var_remap = func_class.type_var_remap.unwrap();
                                let g = &type_var_remap[type_var_usage.index];
                                self.replace_type_vars_for_nested_context(i_s, g)
                            } else {
                                todo!()
                            }
                        } else {
                            todo!()
                        }
                    }
                    FunctionOrCallable::Callable(c) => todo!(),
                }
            }
        })
    }
}

pub fn calculate_class_init_type_vars_and_return<'db>(
    i_s: &mut InferenceState<'db, '_>,
    class: &Class,
    function: Function,
    args: &dyn Arguments<'db>,
    result_context: &mut ResultContext,
    on_type_error: Option<OnTypeError<'db, '_>>,
) -> CalculatedTypeArguments {
    debug!(
        "Calculate type vars for class {} ({})",
        class.name(),
        function.name(),
    );
    let has_generics = !matches!(class.generics, Generics::None | Generics::Any);
    let type_vars = class.type_vars(i_s);
    // Function type vars need to be calculated, so annotations are used.
    let func_type_vars = function.type_vars(i_s);
    if has_generics {
        let mut type_arguments = calculate_type_vars(
            i_s,
            Some(class),
            FunctionOrCallable::Function(function),
            None,
            args,
            true,
            func_type_vars,
            function.node_ref.as_link(),
            result_context,
            on_type_error,
        );
        type_arguments.type_arguments = class.generics_as_list(i_s);
        type_arguments
    } else {
        calculate_type_vars(
            i_s,
            Some(class),
            FunctionOrCallable::Function(function),
            Some(class),
            args,
            true,
            type_vars,
            class.node_ref.as_link(),
            result_context,
            on_type_error,
        )
    }
}

pub struct CalculatedTypeArguments {
    pub in_definition: PointLink,
    pub matches: SignatureMatch,
    pub type_arguments: Option<GenericsList>,
}

impl<'db> CalculatedTypeArguments {
    pub fn lookup_type_var_usage(
        &self,
        i_s: &mut InferenceState,
        class: Option<&Class>,
        usage: &TypeVarUsage,
    ) -> DbType {
        if self.in_definition == usage.in_definition {
            return if let Some(fm) = &self.type_arguments {
                fm[usage.index].clone()
            } else {
                // TODO we are just passing the type vars again. Does this make sense?
                DbType::TypeVar(usage.clone())
            };
        }
        if let Some(c) = class {
            if usage.in_definition == c.node_ref.as_link() {
                return c.generics().nth(i_s, usage.index).into_db_type(i_s);
            }
        }
        DbType::TypeVar(usage.clone())
    }
}

pub fn calculate_function_type_vars_and_return<'db>(
    i_s: &mut InferenceState<'db, '_>,
    class: Option<&Class>,
    function: Function,
    args: &dyn Arguments<'db>,
    skip_first_param: bool,
    type_vars: Option<&TypeVars>,
    match_in_definition: PointLink,
    result_context: &mut ResultContext,
    on_type_error: Option<OnTypeError<'db, '_>>,
) -> CalculatedTypeArguments {
    debug!(
        "Calculate type vars for {} in {}",
        function.name(),
        class.map(|c| c.name()).unwrap_or("-")
    );
    calculate_type_vars(
        i_s,
        class,
        FunctionOrCallable::Function(function),
        None,
        args,
        skip_first_param,
        type_vars,
        match_in_definition,
        result_context,
        on_type_error,
    )
}

pub fn calculate_callable_type_vars_and_return<'db>(
    i_s: &mut InferenceState<'db, '_>,
    class: Option<&Class>,
    callable: &CallableContent,
    args: &dyn Arguments<'db>,
    result_context: &mut ResultContext,
    on_type_error: OnTypeError<'db, '_>,
) -> CalculatedTypeArguments {
    calculate_type_vars(
        i_s,
        None,
        FunctionOrCallable::Callable(callable),
        None,
        args,
        false,
        callable.type_vars.as_ref(),
        callable.defined_at,
        result_context,
        Some(on_type_error),
    )
}

fn calculate_type_vars<'db>(
    i_s: &mut InferenceState<'db, '_>,
    class: Option<&Class>,
    func_or_callable: FunctionOrCallable,
    expected_return_class: Option<&Class>,
    args: &dyn Arguments<'db>,
    skip_first_param: bool,
    type_vars: Option<&TypeVars>,
    match_in_definition: PointLink,
    result_context: &mut ResultContext,
    on_type_error: Option<OnTypeError<'db, '_>>,
) -> CalculatedTypeArguments {
    // We could allocate on stack as described here:
    // https://stackoverflow.com/questions/27859822/is-it-possible-to-have-stack-allocated-arrays-with-the-size-determined-at-runtim
    let type_vars_len = match type_vars {
        Some(type_vars) => type_vars.len(),
        None => 0,
    };
    let mut calculated_type_vars = vec![];
    calculated_type_vars.resize_with(type_vars_len, Default::default);
    let mut matcher = match type_vars {
        Some(type_vars) => Some(TypeVarMatcher::new(
            class,
            func_or_callable,
            match_in_definition,
            &mut calculated_type_vars,
        )),
        None => {
            if let FunctionOrCallable::Function(function) = func_or_callable {
                if let Some(func_class) = function.class {
                    func_class.type_vars(i_s).map(|_| {
                        TypeVarMatcher::new(
                            class,
                            func_or_callable,
                            match_in_definition,
                            &mut calculated_type_vars, // TODO There are no type vars in there, should set it to 0
                        )
                    })
                } else {
                    None
                }
            } else {
                None
            }
        }
    };
    if let Some(matcher) = matcher.as_mut() {
        result_context.with_type_if_exists(i_s, |i_s, type_| {
            if let Some(class) = expected_return_class {
                // This is kind of a special case. Since __init__ has no return annotation, we simply
                // check if the classes match and then push the generics there.
                if let Some(type_vars) = class.type_vars(i_s) {
                    type_.on_any_class(i_s.db, &mut |result_class| {
                        if result_class.node_ref == class.node_ref {
                            let mut calculating = matcher.calculated_type_vars.iter_mut();
                            let mut i = 0;
                            result_class
                                .generics()
                                .iter()
                                .run_on_all(i_s, &mut |i_s, g| {
                                    let calculated = calculating.next().unwrap();
                                    if !g.is_any() {
                                        let mut bound = TypeVarBound::new(
                                            g.as_db_type(i_s),
                                            type_vars[i].variance,
                                        );
                                        bound.invert_bounds();
                                        calculated.type_ = Some(bound);
                                        calculated.defined_by_result_context = true;
                                        i += 1; // TODO please test that this works for multiple type vars
                                    }
                                });
                            true
                        } else {
                            false
                        }
                    });
                }
            } else {
                let result_type = match func_or_callable {
                    FunctionOrCallable::Function(f) => f.result_type(i_s),
                    FunctionOrCallable::Callable(c) => Type::new(&c.result_type),
                };
                // Fill the type var arguments from context
                result_type.is_sub_type_of(i_s, Some(matcher), type_);
                for calculated in matcher.calculated_type_vars.iter_mut() {
                    if let Some(type_) = &mut calculated.type_ {
                        calculated.defined_by_result_context = true;
                    }
                }
            }
        });
    }
    let matches = match func_or_callable {
        FunctionOrCallable::Function(function) => {
            // Make sure the type vars are properly pre-calculated, because we are using type
            // vars from in use_cached_annotation_type.
            function.type_vars(i_s);
            calculate_type_vars_for_params(
                i_s,
                matcher.as_mut(),
                class,
                Some(&function),
                args,
                on_type_error,
                function.iter_args_with_params(i_s.db, args, skip_first_param),
            )
        }
        FunctionOrCallable::Callable(callable) => {
            if let Some(params) = &callable.params {
                calculate_type_vars_for_params(
                    i_s,
                    matcher.as_mut(),
                    None,
                    None,
                    args,
                    on_type_error,
                    InferrableParamIterator2::new(i_s.db, params.iter(), args),
                )
            } else {
                SignatureMatch::True
            }
        }
    };
    let type_arguments = matcher.is_some().then(|| {
        GenericsList::new_generics(
            calculated_type_vars
                .into_iter()
                .map(|c| c.type_.map(|t| t.into_db_type()).unwrap_or(DbType::Never))
                .collect(),
        )
    });
    if cfg!(feature = "zuban_debug") {
        if let Some(type_arguments) = &type_arguments {
            let callable_description: String;
            debug!(
                "Calculated type vars: {}[{}]",
                match &func_or_callable {
                    FunctionOrCallable::Function(function) => function.name(),
                    FunctionOrCallable::Callable(callable) => {
                        callable_description = callable.format(&FormatData::new_short(i_s.db));
                        &callable_description
                    }
                },
                type_arguments.format(&FormatData::new_short(i_s.db)),
            );
        }
    }
    CalculatedTypeArguments {
        in_definition: match_in_definition,
        matches,
        type_arguments,
    }
}

fn calculate_type_vars_for_params<'db: 'x, 'x, P: Param<'x>>(
    i_s: &mut InferenceState<'db, '_>,
    mut matcher: Option<&mut TypeVarMatcher>,
    class: Option<&Class>,
    function: Option<&Function>,
    args: &dyn Arguments<'db>,
    on_type_error: Option<OnTypeError<'db, '_>>,
    mut args_with_params: InferrableParamIterator2<'db, '_, impl Iterator<Item = P>, P>,
) -> SignatureMatch {
    // TODO this can be calculated multiple times from different places
    let should_generate_errors = on_type_error.is_some();
    let mut missing_params = vec![];
    let mut argument_indices_with_any = vec![];
    let mut matches = Match::True;
    for (i, p) in args_with_params.by_ref().enumerate() {
        if p.argument.is_none() && !p.param.has_default() {
            matches = Match::new_false();
            missing_params.push(p.param);
            continue;
        }
        if let Some(ref argument) = p.argument {
            if let Some(annotation_type) = p.param.annotation_type(i_s) {
                let value = if let Some(matcher) = matcher.as_deref_mut() {
                    argument.infer(
                        i_s,
                        &mut ResultContext::WithMatcher {
                            type_: &annotation_type,
                            matcher,
                        },
                    )
                } else {
                    argument.infer(i_s, &mut ResultContext::Known(&annotation_type))
                };
                let m = annotation_type.error_if_not_matches_with_matcher(
                    i_s,
                    matcher.as_deref_mut(),
                    &value,
                    on_type_error.map(|on_type_error| {
                        |i_s: &mut InferenceState<'db, '_>, mut t1, t2, reason: &MismatchReason| {
                            let node_ref = argument.as_node_ref();
                            if let Some(starred) = node_ref.maybe_starred_expression() {
                                t1 = format!(
                                    "*{}",
                                    node_ref.file.inference(i_s).infer_expression(starred.expression()).format(i_s, &FormatData::new_short(i_s.db))
                                ).into()
                            } else if let Some(double_starred) = node_ref.maybe_double_starred_expression() {
                                t1 = format!(
                                    "**{}",
                                    node_ref.file.inference(i_s).infer_expression(double_starred.expression()).format(i_s, &FormatData::new_short(i_s.db))
                                ).into()
                            }
                            match reason {
                                MismatchReason::None => on_type_error(
                                    i_s,
                                    node_ref,
                                    class,
                                    function,
                                    &p,
                                    t1,
                                    t2,
                                ),
                                MismatchReason::CannotInferTypeArgument(index) => {
                                    node_ref.add_typing_issue(
                                        i_s.db,
                                        IssueType::CannotInferTypeArgument {
                                            index: *index,
                                            callable: match function {
                                                Some(f) => f.diagnostic_string(class),
                                                None => Box::from("Callable"),
                                            },
                                        },
                                    );
                                }
                                MismatchReason::ConstraintMismatch { expected, type_var } => {
                                    if should_generate_errors {
                                        node_ref.add_typing_issue(
                                            i_s.db,
                                            IssueType::InvalidTypeVarValue {
                                                type_var: Box::from(type_var.name(i_s.db)),
                                                func: match function {
                                                    Some(f) => f.diagnostic_string(class),
                                                    None => Box::from("function"),
                                                },
                                                actual: expected.format(&FormatData::new_short(i_s.db)),
                                            },
                                        );
                                    } else {
                                        debug!(
                                            "TODO this is wrong, because this might also be Match::FalseButSimilar"
                                        );
                                    }
                                }
                            }
                        }
                    }),
                );
                if matches!(m, Match::TrueWithAny) {
                    if let Some(param_annotation_link) = p.param.func_annotation_link() {
                        // This is never reached when matching callables
                        if let Some(argument) = p.argument {
                            argument_indices_with_any.push(ArgumentIndexWithParam {
                                argument_index: argument.index,
                                param_annotation_link,
                            })
                        }
                    }
                }
                matches &= m
            }
        }
    }
    let add_keyword_argument_issue = |reference: NodeRef, name| {
        let s = if let Some(function) = function {
            if function.iter_params().any(|p| {
                p.name(i_s.db) == Some(name)
                    && matches!(
                        p.kind(i_s.db),
                        ParamKind::PositionalOrKeyword | ParamKind::KeywordOnly
                    )
            }) {
                format!(
                    "{} gets multiple values for keyword argument {name:?}",
                    function.diagnostic_string(class),
                )
            } else {
                format!(
                    "Unexpected keyword argument {name:?} for {}",
                    function.diagnostic_string(class),
                )
            }
        } else {
            debug!("TODO this keyword param could also exist");
            format!("Unexpected keyword argument {name:?}")
        };
        reference.add_typing_issue(i_s.db, IssueType::ArgumentIssue(s.into()));
    };
    if args_with_params.too_many_positional_arguments {
        matches = Match::new_false();
        if should_generate_errors || true {
            // TODO remove true and add test
            let mut s = "Too many positional arguments".to_owned();
            if let Some(function) = function {
                s += " for ";
                s += &function.diagnostic_string(class);
            }

            args.as_node_ref()
                .add_typing_issue(i_s.db, IssueType::ArgumentIssue(s.into()));
        }
    } else if args_with_params.has_unused_arguments() {
        matches = Match::new_false();
        if should_generate_errors {
            let mut too_many = false;
            for arg in args_with_params.arguments {
                match arg.kind {
                    ArgumentKind::Keyword { key, node_ref, .. } => {
                        add_keyword_argument_issue(node_ref, key)
                    }
                    _ => {
                        too_many = true;
                        break;
                    }
                }
            }
            if too_many {
                let mut s = "Too many arguments".to_owned();
                if let Some(function) = function {
                    s += " for ";
                    s += &function.diagnostic_string(class);
                }

                args.as_node_ref()
                    .add_typing_issue(i_s.db, IssueType::ArgumentIssue(s.into()));
            }
        }
    } else if args_with_params.has_unused_keyword_arguments() && should_generate_errors {
        for unused in args_with_params.unused_keyword_arguments {
            match unused.kind {
                ArgumentKind::Keyword { key, node_ref, .. } => {
                    add_keyword_argument_issue(node_ref, key)
                }
                _ => unreachable!(),
            }
        }
    } else if should_generate_errors {
        let mut missing_positional = vec![];
        for param in &missing_params {
            if let Some(param_name) = param.name(i_s.db) {
                if param.kind(i_s.db) == ParamKind::KeywordOnly {
                    let mut s = format!("Missing named argument {:?}", param_name);
                    if let Some(function) = function {
                        s += " for ";
                        s += &function.diagnostic_string(class);
                    }
                    args.as_node_ref()
                        .add_typing_issue(i_s.db, IssueType::ArgumentIssue(s.into()));
                } else {
                    missing_positional.push(format!("\"{param_name}\""));
                }
            } else {
                args.as_node_ref().add_typing_issue(
                    i_s.db,
                    IssueType::ArgumentIssue(Box::from("Too few arguments")),
                );
            }
        }
        if let Some(mut s) = match &missing_positional[..] {
            [] => None,
            [param_name] => Some(format!(
                "Missing positional argument {} in call",
                param_name
            )),
            _ => Some(format!(
                "Missing positional arguments {} in call",
                missing_positional.join(", ")
            )),
        } {
            if let Some(function) = function {
                s += " to ";
                s += &function.diagnostic_string(class);
            }
            args.as_node_ref()
                .add_typing_issue(i_s.db, IssueType::ArgumentIssue(s.into()));
        };
    }
    match matches {
        Match::True => SignatureMatch::True,
        Match::TrueWithAny => SignatureMatch::TrueWithAny {
            argument_indices: argument_indices_with_any.into(),
        },
        Match::FalseButSimilar(_) => SignatureMatch::FalseButSimilar,
        Match::False(_) => SignatureMatch::False,
    }
}
