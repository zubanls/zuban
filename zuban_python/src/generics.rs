use parsa_python_ast::{
    Expression, ExpressionContent, NameParent, NodeIndex, ParamIterator, SliceContent,
    SliceIterator, SliceType, Slices,
};

use crate::arguments::Arguments;
use crate::database::{
    Database, GenericPart, GenericsList, Locality, Point, PointLink, Specific, TypeVarIndex,
};
use crate::debug;
use crate::file::PythonFile;
use crate::inference_state::InferenceState;
use crate::inferred::{Inferrable, Inferred, NodeReference};
use crate::value::{Callable, CallableClass, Class, ClassLike, Function, TupleClass, Value};

#[derive(Debug, Clone, Copy)]
pub enum Generics<'db, 'a> {
    Expression(&'db PythonFile, Expression<'db>),
    Slices(&'db PythonFile, Slices<'db>),
    List(&'a GenericsList),
    Class(&'a Class<'db, 'a>),
    GenericPart(&'a GenericPart),
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

    pub fn nth(&self, i_s: &mut InferenceState<'db, '_>, n: TypeVarIndex) -> GenericPart {
        match self {
            Self::Expression(file, expr) => {
                if n.as_usize() == 0 {
                    file.inference(i_s)
                        .infer_annotation_expression_class(*expr)
                        .as_generic_part(i_s)
                } else {
                    GenericPart::Unknown
                }
            }
            Self::Slices(file, slices) => slices
                .iter()
                .nth(n.as_usize())
                .map(|slice_content| match slice_content {
                    SliceContent::NamedExpression(n) => file
                        .inference(i_s)
                        .infer_annotation_expression_class(n.expression())
                        .as_generic_part(i_s),
                    SliceContent::Slice(s) => todo!(),
                })
                .unwrap_or(GenericPart::Unknown),
            Self::List(l) => l.nth(n).cloned().unwrap_or(GenericPart::Unknown),
            Self::GenericPart(g) => todo!(),
            Self::Class(s) => todo!(),
            Self::FunctionParams(f) => todo!(),
            Self::None => GenericPart::Unknown,
        }
    }

    pub fn iter(&self) -> GenericsIterator<'db, 'a> {
        match self {
            Self::Expression(file, expr) => GenericsIterator::Expression(file, *expr),
            Self::Slices(file, slices) => GenericsIterator::SliceIterator(file, slices.iter()),
            Self::List(l) => GenericsIterator::GenericsList(l.iter()),
            Self::GenericPart(g) => GenericsIterator::GenericPart(g),
            Self::Class(s) => GenericsIterator::Class(*s),
            Self::FunctionParams(f) => {
                GenericsIterator::ParamIterator(f.reference.file, f.iter_params())
            }
            Self::None => GenericsIterator::None,
        }
    }

    pub fn as_generics_list(&self, i_s: &mut InferenceState<'db, '_>) -> Option<GenericsList> {
        match self {
            Self::Expression(file, expr) => Some(GenericsList::new(Box::new([file
                .inference(i_s)
                .infer_annotation_expression_class(*expr)
                .as_generic_part(i_s)]))),
            Self::Slices(file, slices) => Some(GenericsList::new(
                slices
                    .iter()
                    .map(|slice| {
                        if let SliceContent::NamedExpression(n) = slice {
                            file.inference(i_s)
                                .infer_annotation_expression_class(n.expression())
                                .as_generic_part(i_s)
                        } else {
                            todo!()
                        }
                    })
                    .collect(),
            )),
            Self::GenericPart(g) => todo!(),
            Self::Class(_) => todo!(),
            Self::FunctionParams(f) => todo!(),
            Self::List(l) => Some((*l).clone()),
            Self::None => None,
        }
    }

    pub fn as_string(&self, i_s: &mut InferenceState<'db, '_>) -> String {
        // Returns something like [str] or [List[int], Set[Any]]
        let mut strings = vec![];
        self.iter()
            .run_on_all_generic_options(i_s, |i_s, g| strings.push(g.as_string(i_s)));
        format!("[{}]", strings.join(", "))
    }

    pub fn infer_type_vars(
        &self,
        i_s: &mut InferenceState<'db, '_>,
        matcher: &mut TypeVarMatcher<'db, '_>,
        value_generics: Self,
    ) {
        let mut value_generics = value_generics.iter();
        self.iter()
            .run_on_all_generic_options(i_s, |i_s, generic_option| {
                let appeared = value_generics.run_on_next(i_s, |i_s, g| {
                    generic_option.infer_type_vars(i_s, matcher, g)
                });
                if appeared.is_none() {
                    debug!("Generic not found for: {:?}", generic_option);
                }
            });
    }
}

pub enum GenericsIterator<'db, 'a> {
    SliceIterator(&'db PythonFile, SliceIterator<'db>),
    GenericsList(std::slice::Iter<'a, GenericPart>),
    GenericPart(&'a GenericPart),
    Class(&'a Class<'db, 'a>),
    ParamIterator(&'db PythonFile, ParamIterator<'db>),
    Expression(&'db PythonFile, Expression<'db>),
    None,
}

impl<'db> GenericsIterator<'db, '_> {
    pub fn run_on_next<T>(
        &mut self,
        i_s: &mut InferenceState<'db, '_>,
        mut callable: impl FnMut(&mut InferenceState<'db, '_>, GenericOption<'db, '_>) -> T,
    ) -> Option<T> {
        match self {
            Self::Expression(file, expr) => {
                let inferred = file.inference(i_s).infer_annotation_expression_class(*expr);
                let g = inferred.as_generic_option(i_s);
                let result = callable(i_s, g);
                *self = GenericsIterator::None;
                Some(result)
            }
            Self::SliceIterator(file, iter) => {
                if let Some(SliceContent::NamedExpression(s)) = iter.next() {
                    let inferred = file
                        .inference(i_s)
                        .infer_annotation_expression_class(s.expression());
                    let g = inferred.as_generic_option(i_s);
                    Some(callable(i_s, g))
                } else {
                    None
                }
            }
            Self::GenericsList(iterator) => iterator
                .next()
                .map(|g| callable(i_s, GenericOption::from_generic_part(i_s.database, g))),
            Self::GenericPart(g) => {
                let result = Some(callable(
                    i_s,
                    GenericOption::from_generic_part(i_s.database, g),
                ));
                *self = Self::None;
                result
            }
            Self::Class(s) => {
                let result = callable(i_s, GenericOption::ClassLike(ClassLike::Class(**s)));
                *self = Self::None;
                Some(result)
            }
            Self::ParamIterator(f, params) => params.next().map(|p| {
                p.annotation()
                    .map(|a| {
                        let inferred = f
                            .inference(i_s)
                            .infer_annotation_expression_class(a.expression());
                        let g = inferred.as_generic_option(i_s);
                        callable(i_s, g)
                    })
                    .unwrap_or_else(|| callable(i_s, GenericOption::None))
            }),
            GenericsIterator::None => None,
        }
    }

    fn run_on_all_generic_options(
        mut self,
        i_s: &mut InferenceState<'db, '_>,
        mut callable: impl FnMut(&mut InferenceState<'db, '_>, GenericOption<'db, '_>),
    ) {
        loop {
            let inferred = match &mut self {
                Self::Expression(file, expr) => {
                    let result = file.inference(i_s).infer_annotation_expression_class(*expr);
                    let g = result.as_generic_option(i_s);
                    callable(i_s, g);
                    return;
                }
                Self::SliceIterator(file, iter) => {
                    if let Some(SliceContent::NamedExpression(s)) = iter.next() {
                        file.inference(i_s)
                            .infer_annotation_expression_class(s.expression())
                    } else {
                        return;
                    }
                }
                Self::GenericsList(iterator) => {
                    if let Some(g) = iterator.next() {
                        callable(i_s, GenericOption::from_generic_part(i_s.database, g));
                    }
                    return;
                }
                Self::GenericPart(g) => {
                    callable(i_s, GenericOption::from_generic_part(i_s.database, g));
                    return;
                }
                Self::Class(s) => {
                    todo!();
                }
                Self::ParamIterator(f, params) => {
                    for p in params {
                        if let Some(annotation) = p.annotation() {
                            let inferred = f
                                .inference(i_s)
                                .infer_annotation_expression_class(annotation.expression());
                            let g = inferred.as_generic_option(i_s);
                            callable(i_s, g)
                        } else {
                            callable(i_s, GenericOption::None)
                        }
                    }
                    return;
                }
                GenericsIterator::None => return,
            };
            let generic_option = inferred.as_generic_option(i_s);
            callable(i_s, generic_option);
        }
    }
}

enum FunctionOrCallable<'db, 'a> {
    Function(&'a Function<'db, 'a>),
    Callable(&'a Callable<'a>),
}

pub struct TypeVarMatcher<'db, 'a> {
    func_or_callable: FunctionOrCallable<'db, 'a>,
    args: &'a dyn Arguments<'db>,
    skip_first: bool,
    pub calculated_type_vars: Option<GenericsList>,
    matches: bool,
    type_vars: Option<&'a [PointLink]>,
    match_specific: Specific,
}

impl<'db, 'a> TypeVarMatcher<'db, 'a> {
    pub fn new(
        function: &'a Function<'db, 'a>,
        args: &'a dyn Arguments<'db>,
        skip_first: bool,
        type_vars: Option<&'a [PointLink]>,
        match_specific: Specific,
    ) -> Self {
        Self {
            func_or_callable: FunctionOrCallable::Function(function),
            args,
            calculated_type_vars: None,
            skip_first,
            matches: true,
            type_vars,
            match_specific,
        }
    }
    // TODO the structure of this impl looks very weird, strange funcs

    pub fn from_callable(
        callable: &'a Callable<'a>,
        args: &'a dyn Arguments<'db>,
        type_vars: Option<&'a [PointLink]>,
        match_specific: Specific,
    ) -> Self {
        Self {
            func_or_callable: FunctionOrCallable::Callable(callable),
            args,
            calculated_type_vars: None,
            skip_first: false,
            matches: true,
            type_vars,
            match_specific,
        }
    }

    pub fn calculate_and_return(
        i_s: &mut InferenceState<'db, '_>,
        function: &'a Function<'db, 'a>,
        args: &'a dyn Arguments<'db>,
        skip_first: bool,
        type_vars: Option<&'db [PointLink]>,
        match_specific: Specific,
    ) -> Option<GenericsList> {
        let mut self_ = Self::new(function, args, skip_first, type_vars, match_specific);
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
            FunctionOrCallable::Function(function) => {
                function.calculated_type_vars(i_s);
                let mut iter = function.iter_inferrable_params(self.args, self.skip_first);
                while let Some(p) = iter.next() {
                    if let Some(annotation) = p.param.annotation() {
                        if let ExpressionContent::ExpressionPart(part) =
                            annotation.expression().unpack()
                        {
                            let value = p.infer(i_s);
                            let value_class = value.class_as_generic_option(i_s);
                            function
                                .reference
                                .file
                                .inference(i_s)
                                .infer_annotation_expression_class(annotation.expression())
                                .as_generic_option(i_s)
                                .infer_type_vars(i_s, self, value_class);
                        } else {
                            self.matches = false;
                            todo!();
                        }
                    } else if !p.has_argument() {
                        self.matches = false;
                        debug!("Not enough arguments: {:?}", p);
                    }
                }
                if iter.has_unused_argument() {
                    self.matches = false
                }
            }
            FunctionOrCallable::Callable(callable) => {
                for param in callable.iter_params_with_args(self.args) {
                    if let Some(argument) = param.argument {
                        let value = argument.infer(i_s);
                        let value_class = value.class_as_generic_option(i_s);
                        GenericOption::from_generic_part(i_s.database, param.param_type)
                            .infer_type_vars(i_s, self, value_class)
                    }
                }
            }
        }
        if let Some(calculated) = &self.calculated_type_vars {
            let callable_description: String;
            debug!(
                "Calculated type vars: {}[{}]",
                match self.func_or_callable {
                    FunctionOrCallable::Function(function) => function.name(),
                    FunctionOrCallable::Callable(callable) => {
                        callable_description = callable.description(i_s);
                        &callable_description
                    }
                },
                calculated.as_string(i_s.database),
            );
        }
    }

    fn nth(
        &mut self,
        i_s: &mut InferenceState<'db, '_>,
        index: TypeVarIndex,
    ) -> Option<GenericPart> {
        if let Some(type_vars) = &self.calculated_type_vars {
            type_vars.nth(index).cloned()
        } else {
            self.calculate_type_vars(i_s);
            self.nth(i_s, index)
        }
    }

    fn add_type_var_class(
        &mut self,
        i_s: &mut InferenceState<'db, '_>,
        type_var_index: TypeVarIndex,
        class: GenericPart,
    ) {
        self.calculated_type_vars
            .as_mut()
            .unwrap()
            .set_generic(type_var_index, class);
    }

    pub fn does_not_match(&mut self) {
        self.matches = false;
    }

    pub fn matches_signature(&mut self, i_s: &mut InferenceState<'db, '_>) -> bool {
        self.calculate_type_vars(i_s);
        self.matches
    }
}

pub fn search_type_vars<'db>(
    i_s: &mut InferenceState<'db, '_>,
    file: &'db PythonFile,
    expression: &Expression<'db>,
    found_callback: &mut dyn FnMut(NodeIndex, PointLink) -> Option<Specific>,
    found_type_vars: &mut Vec<PointLink>,
    add_new_as_late_bound_type_var: bool,
) {
    let mut late_bound_type_vars = vec![];
    for n in expression.search_names() {
        if matches!(n.parent(), NameParent::Atom) {
            let inferred = file.inference(i_s).infer_name_reference(n);
            if let Some(definition) = inferred.maybe_type_var(i_s) {
                let link = definition.as_link();

                if let Some(point_type) = found_callback(n.index(), link) {
                    let i = found_type_vars.iter().position(|&r| r == link);
                    if i.is_none() {
                        if add_new_as_late_bound_type_var {
                            let i = late_bound_type_vars.iter().position(|&r| r == link);
                            if i.is_none() {
                                late_bound_type_vars.push(link);
                            }
                            let i = i.unwrap_or(late_bound_type_vars.len() - 1);
                            file.points.set(
                                n.index(),
                                Point::new_numbered_type_var(
                                    Specific::LateBoundTypeVar,
                                    TypeVarIndex::new(i),
                                    Locality::Stmt,
                                ),
                            );
                            continue;
                        }
                        found_type_vars.push(link);
                    };
                    let i = i.unwrap_or(found_type_vars.len() - 1);
                    file.points.set(
                        n.index(),
                        Point::new_numbered_type_var(
                            point_type,
                            TypeVarIndex::new(i),
                            Locality::Stmt,
                        ),
                    );
                }
            }
        }
    }
}

#[derive(Debug)]
pub enum GenericOption<'db, 'a> {
    ClassLike(ClassLike<'db, 'a>),
    TypeVar(TypeVarIndex, NodeReference<'db>),
    Union(Vec<GenericPart>),
    None,
    Invalid,
}

impl<'db, 'a> GenericOption<'db, 'a> {
    pub fn from_generic_part(database: &'db Database, generic_part: &'a GenericPart) -> Self {
        match generic_part {
            GenericPart::Class(link) => {
                let node_ref = NodeReference::from_link(database, *link);
                Self::ClassLike(ClassLike::Class(
                    Class::from_position(node_ref, Generics::None, None).unwrap(),
                ))
            }
            GenericPart::Unknown => Self::Invalid,
            GenericPart::None => GenericOption::None,
            GenericPart::GenericClass(link, generics) => {
                let node_ref = NodeReference::from_link(database, *link);
                Self::ClassLike(ClassLike::Class(
                    Class::from_position(node_ref, Generics::List(generics), None).unwrap(),
                ))
            }
            GenericPart::Union(list) => Self::Union(list.iter().cloned().collect()),
            GenericPart::TypeVar(index, link) => {
                Self::TypeVar(*index, NodeReference::from_link(database, *link))
            }
            GenericPart::Type(generic_part) => {
                Self::ClassLike(ClassLike::TypeWithGenericPart(generic_part))
            }
            GenericPart::Tuple(content) => {
                Self::ClassLike(ClassLike::Tuple(TupleClass::new(content)))
            }
            GenericPart::Callable(content) => {
                Self::ClassLike(ClassLike::Callable(CallableClass::new(content)))
            }
        }
    }

    pub fn union(self, i_s: &mut InferenceState<'db, '_>, other: Self) -> Self {
        if let Self::Union(mut list1) = self {
            if let Self::Union(list2) = other {
                list1.extend(list2);
            } else {
                list1.push(other.as_generic_part(i_s));
            }
            Self::Union(list1)
        } else if let Self::Union(_) = other {
            other.union(i_s, self)
        } else {
            GenericOption::Union(vec![self.as_generic_part(i_s), other.as_generic_part(i_s)])
        }
    }

    fn as_generic_part(&self, i_s: &mut InferenceState<'db, '_>) -> GenericPart {
        match self {
            Self::ClassLike(class_like) => class_like.as_generic_part(i_s),
            Self::TypeVar(type_var_index, node_ref) => {
                GenericPart::TypeVar(*type_var_index, node_ref.as_link())
            }
            Self::Union(_) => unreachable!(),
            Self::None => GenericPart::None,
            Self::Invalid => todo!(),
        }
    }

    pub fn infer_type_vars(
        &self,
        i_s: &mut InferenceState<'db, '_>,
        matcher: &mut TypeVarMatcher<'db, '_>,
        value_class: Self,
    ) {
        match self {
            Self::ClassLike(class) => class.infer_type_vars(i_s, value_class, matcher),
            Self::TypeVar(type_var_index, node_ref) => match value_class {
                GenericOption::ClassLike(class) => {
                    let generic = class.as_generic_part(i_s);
                    matcher.add_type_var_class(i_s, *type_var_index, generic);
                }
                GenericOption::TypeVar(_, _) | GenericOption::Invalid => {
                    todo!("{:?}", value_class)
                }
                GenericOption::Union(list) => {
                    let generic = GenericPart::Union(GenericsList::from_vec(list));
                    matcher.add_type_var_class(i_s, *type_var_index, generic);
                }
                GenericOption::None => {
                    //matcher.add_type_var_class(i_s, *type_var_index, GenericPart::None)
                    todo!()
                }
            },
            Self::Union(list1) => match value_class {
                Self::Union(mut list2) => {
                    let mut type_var_index = None;
                    for g1 in list1 {
                        if let Some(t) = g1.maybe_type_var_index() {
                            type_var_index = Some(t);
                        }
                        for (i, g2) in list2.iter().enumerate() {
                            if g1.todo_matches(g2) {
                                list2.remove(i);
                                break;
                            }
                        }
                    }
                    /*
                    if type_var_index.is_some() {
                            GenericOption::from_generic_part(i_s.database, g1).infer_type_vars(
                                i_s,
                                matcher,
                                GenericOption::from_generic_part(i_s.database, g2),
                            );
                    }*/
                    if let Some(type_var_index) = type_var_index {
                        let g = match list2.len() {
                            0 => {
                                matcher.does_not_match();
                                GenericPart::Unknown
                            }
                            1 => list2.into_iter().next().unwrap(),
                            _ => GenericPart::Union(GenericsList::from_vec(list2)),
                        };
                        matcher.add_type_var_class(i_s, type_var_index, dbg!(g));
                    } else if !list2.is_empty() {
                        matcher.does_not_match()
                    }
                }
                _ => matcher.does_not_match(),
            },
            Self::None => {
                if !matches!(value_class, Self::None) {
                    matcher.does_not_match()
                }
            }
            Self::Invalid => matcher.does_not_match(),
        }
    }

    pub fn execute_and_resolve_type_vars(
        &self,
        i_s: &mut InferenceState<'db, '_>,
        class: Option<&Class<'db, '_>>,
        function_matcher: &mut Option<TypeVarMatcher<'db, '_>>,
    ) -> Inferred<'db> {
        let generic_part = self.internal_resolve_type_vars(i_s, class, function_matcher);
        debug!(
            "Resolved type vars: {}",
            generic_part.as_type_string(i_s.database)
        );
        Inferred::execute_generic_part(i_s, generic_part)
    }

    fn internal_resolve_type_vars(
        &self,
        i_s: &mut InferenceState<'db, '_>,
        class: Option<&Class<'db, '_>>,
        function_matcher: &mut Option<TypeVarMatcher<'db, '_>>,
    ) -> GenericPart {
        let resolve_type_var = |i_s: &mut InferenceState<'db, '_>,
                                function_matcher: &mut Option<TypeVarMatcher<'db, '_>>,
                                type_var_index: TypeVarIndex,
                                node_ref: &NodeReference| {
            let point = node_ref.point();
            match point.specific() {
                Specific::ClassTypeVar => {
                    let class = class.unwrap();
                    let mut generic = |type_var_index| class.generics.nth(i_s, type_var_index);
                    class
                        .type_var_remap
                        .map(|remaps| {
                            remaps
                                .nth(type_var_index)
                                .map(|x| x.remap_type_vars(&mut generic))
                                // This means that no generic was provided
                                .unwrap_or(GenericPart::Unknown)
                        })
                        .unwrap_or_else(|| generic(type_var_index))
                }
                Specific::FunctionTypeVar => function_matcher
                    .as_mut()
                    .unwrap()
                    .nth(i_s, type_var_index)
                    .unwrap_or(GenericPart::Unknown),
                Specific::LateBoundTypeVar => {
                    if let Some(function_matcher) = function_matcher {
                        if function_matcher.match_specific == Specific::LateBoundTypeVar {
                            if let Some(calculated) = function_matcher.nth(i_s, type_var_index) {
                                return calculated;
                            }
                        }
                    }
                    // Just pass the type var again, because it might be resolved by a future
                    // callable, that is late bound, like Callable[..., Callable[[T], T]]
                    GenericPart::TypeVar(type_var_index, node_ref.as_link())
                }
                _ => unreachable!(),
            }
        };

        match self {
            Self::ClassLike(c) => {
                c.as_generic_part(i_s)
                    .replace_type_vars(&mut |type_var_index, link| {
                        let node_ref = NodeReference::from_link(i_s.database, link);
                        resolve_type_var(i_s, function_matcher, type_var_index, &node_ref)
                    })
            }
            Self::TypeVar(type_var_index, node_ref) => {
                resolve_type_var(i_s, function_matcher, *type_var_index, node_ref)
            }
            Self::Union(list) => GenericPart::Union(GenericsList::new(
                list.iter()
                    .map(|g| {
                        g.clone().replace_type_vars(&mut |type_var_index, link| {
                            let node_ref = NodeReference::from_link(i_s.database, link);
                            resolve_type_var(i_s, function_matcher, type_var_index, &node_ref)
                        })
                    })
                    .collect(),
            )),
            Self::None => todo!(),
            Self::Invalid => GenericPart::Unknown,
        }
    }

    fn as_string(&self, i_s: &mut InferenceState<'db, '_>) -> String {
        match self {
            Self::ClassLike(c) => c.as_string(i_s),
            Self::TypeVar(_, node_ref) => node_ref.as_name().as_str().to_owned(),
            Self::Union(list) => list.iter().fold(String::new(), |a, b| {
                if a.is_empty() {
                    a + &b.as_type_string(i_s.database)
                } else {
                    a + &b.as_type_string(i_s.database) + ","
                }
            }),
            Self::None => "None".to_owned(),
            Self::Invalid => "Unknown".to_owned(),
        }
    }

    pub fn maybe_execute(&self, i_s: &mut InferenceState<'db, '_>) -> Option<Inferred<'db>> {
        match self {
            Self::ClassLike(c) => {
                let g = c.as_generic_part(i_s);
                Some(Inferred::execute_generic_part(i_s, g))
            }
            Self::Union(list) => Some(Inferred::gather_union(|callable| {
                for generic_part in list.iter() {
                    callable(Inferred::execute_generic_part(i_s, generic_part.clone()))
                }
            })),
            Self::TypeVar(index, node_ref) => Some(Inferred::execute_generic_part(
                i_s,
                GenericPart::TypeVar(*index, node_ref.as_link()),
            )),
            Self::None => Some(Inferred::new_unsaved_specific(Specific::None)),
            Self::Invalid => None,
        }
    }
}
