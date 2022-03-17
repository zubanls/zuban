use parsa_python_ast::{
    Expression, ExpressionContent, Name, NameParent, NodeIndex, ParamIterator, ParamType,
    PrimaryParent, SliceContent, SliceIterator, SliceType, Slices,
};

use crate::arguments::Arguments;
use crate::database::{
    ClassInfos, Database, DbType, FormatStyle, GenericsList, Locality, Point, PointLink, Specific,
    TypeVarIndex,
};
use crate::debug;
use crate::diagnostics::IssueType;
use crate::file::PythonFile;
use crate::inference_state::InferenceState;
use crate::inferred::Inferred;
use crate::node_ref::NodeRef;
use crate::value::{Callable, CallableClass, Class, ClassLike, Function, TupleClass, Value};

macro_rules! replace_class_vars {
    ($i_s:ident, $g:ident, $type_var_generics:ident) => {
        match $type_var_generics {
            Some(type_var_generics) => $g.clone().replace_type_vars(&mut |type_var_index, link| {
                let node_ref = NodeRef::from_link($i_s.database, link);
                if node_ref.point().specific() != Specific::ClassTypeVar {
                    return DbType::Unknown;
                }
                type_var_generics.nth($i_s, type_var_index)
            }),
            None => $g.clone(),
        }
    };
}

#[derive(Debug, Clone, Copy)]
pub enum Generics<'db, 'a> {
    Expression(&'db PythonFile, Expression<'db>),
    Slices(&'db PythonFile, Slices<'db>),
    List(&'a GenericsList, Option<&'a Generics<'db, 'a>>),
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
                    file.inference(i_s)
                        .infer_annotation_expression_class(*expr)
                        .as_db_type(i_s)
                } else {
                    debug!(
                        "Generic expr {:?} has one item, but {:?} was requested",
                        expr.short_debug(),
                        n
                    );
                    DbType::Unknown
                }
            }
            Self::Slices(file, slices) => slices
                .iter()
                .nth(n.as_usize())
                .map(|slice_content| match slice_content {
                    SliceContent::NamedExpression(n) => file
                        .inference(i_s)
                        .infer_annotation_expression_class(n.expression())
                        .as_db_type(i_s),
                    SliceContent::Slice(s) => todo!(),
                })
                .unwrap_or(DbType::Unknown),
            Self::List(list, type_var_generics) => {
                if let Some(g) = list.nth(n) {
                    replace_class_vars!(i_s, g, type_var_generics)
                } else {
                    debug!(
                        "Generic list {} given, but item {:?} was requested",
                        self.as_string(i_s, FormatStyle::Short, None),
                        n
                    );
                    DbType::Unknown
                }
            }
            Self::DbType(g) => todo!(),
            Self::Class(s) => todo!(),
            Self::FunctionParams(f) => todo!(),
            Self::None => {
                debug!("No generics given, but {:?} was requested", n);
                DbType::Unknown
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
                .as_db_type(i_s)]))),
            Self::Slices(file, slices) => Some(GenericsList::new(
                slices
                    .iter()
                    .map(|slice| {
                        if let SliceContent::NamedExpression(n) = slice {
                            file.inference(i_s)
                                .infer_annotation_expression_class(n.expression())
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
            Self::List(l, type_var_generics) => Some(GenericsList::new(
                l.iter()
                    .map(|c| replace_class_vars!(i_s, c, type_var_generics))
                    .collect(),
            )),
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
    ) -> bool {
        let mut value_generics = value_generics.iter();
        let mut matches = true;
        self.iter().run_on_all(i_s, &mut |i_s, type_| {
            let appeared = value_generics.run_on_next(i_s, &mut |i_s, g| {
                matches &= type_.matches(i_s, matcher.as_deref_mut(), g);
            });
            if appeared.is_none() {
                debug!("Generic not found for: {:?}", type_);
            }
        });
        matches
    }
}

pub enum GenericsIterator<'db, 'a> {
    SliceIterator(&'db PythonFile, SliceIterator<'db>),
    GenericsList(std::slice::Iter<'a, DbType>, Option<&'a Generics<'db, 'a>>),
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
                let inferred = file.inference(i_s).infer_annotation_expression_class(*expr);
                let g = inferred.as_type(i_s);
                let result = callable(i_s, g);
                *self = GenericsIterator::None;
                Some(result)
            }
            Self::SliceIterator(file, iter) => {
                if let Some(SliceContent::NamedExpression(s)) = iter.next() {
                    let inferred = file
                        .inference(i_s)
                        .infer_annotation_expression_class(s.expression());
                    let g = inferred.as_type(i_s);
                    Some(callable(i_s, g))
                } else {
                    None
                }
            }
            Self::GenericsList(iterator, type_var_generics) => iterator.next().map(|g| {
                let g = replace_class_vars!(i_s, g, type_var_generics);
                callable(i_s, Type::from_db_type(i_s.database, &g))
            }),
            Self::DbType(g) => {
                let result = Some(callable(i_s, Type::from_db_type(i_s.database, g)));
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
                        let inferred = f
                            .inference(i_s)
                            .infer_annotation_expression_class(a.expression());
                        let g = inferred.as_type(i_s);
                        callable(i_s, g)
                    })
                    .unwrap_or_else(|| callable(i_s, Type::None))
            }),
            GenericsIterator::None => None,
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
                    if !p.has_argument() && p.param.default().is_none() {
                        // TODO?! comments?!
                        //self.matches = false;
                        self.args.node_reference().add_typing_issue(
                            i_s.database,
                            IssueType::ArgumentIssue(format!(
                                "Missing positional argument {:?} in call to {}",
                                p.param.name_definition().name().as_str(),
                                function.diagnostic_string(),
                            )),
                        );
                        //continue
                    }
                    if let Some(annotation) = p.param.annotation() {
                        match p.param.type_() {
                            ParamType::Starred => continue, // TODO this is *args: Foo
                            ParamType::DoubleStarred => todo!(),
                            _ => (),
                        }
                        if let ExpressionContent::ExpressionPart(part) =
                            annotation.expression().unpack()
                        {
                            if let Some(value) = p.infer(i_s) {
                                let value_class = value.class_as_type(i_s);
                                let inf = function
                                    .reference
                                    .file
                                    .inference(i_s)
                                    .infer_annotation_expression_class(annotation.expression());
                                let annotation_g = inf.as_type(i_s);
                                if !annotation_g.matches(i_s, Some(self), value_class) {
                                    let value_class = value.class_as_type(i_s);
                                    p.as_argument_node_reference().add_typing_issue(
                                        i_s.database,
                                        IssueType::ArgumentIssue(format!(
                                            "Argument {} to {} has incompatible type {:?}; expected {:?}",
                                            1,
                                            function.diagnostic_string(),
                                            value_class.as_string(i_s, None, FormatStyle::Short),
                                            annotation_g.as_string(i_s, Some(function), FormatStyle::Short),
                                        )),
                                    );
                                    self.matches = false;
                                }
                            }
                        } else {
                            self.matches = false;
                            todo!();
                        }
                    }
                }
                if iter.has_unused_argument() {
                    self.args.node_reference().add_typing_issue(
                        i_s.database,
                        IssueType::ArgumentIssue(format!(
                            "Too many arguments for {}",
                            function.diagnostic_string(),
                        )),
                    );
                    self.matches = false
                }
            }
            FunctionOrCallable::Callable(callable) => {
                for param in callable.iter_params_with_args(self.args) {
                    if let Some(argument) = param.argument {
                        let value = argument.infer(i_s);
                        let value_class = value.class_as_type(i_s);
                        let m = Type::from_db_type(i_s.database, param.param_type).matches(
                            i_s,
                            Some(self),
                            value_class,
                        );
                        self.matches &= m;
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
                calculated.as_string(i_s.database, None, FormatStyle::Short),
            );
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

    fn match_or_add_type_var(
        &mut self,
        i_s: &mut InferenceState<'db, '_>,
        type_var_index: TypeVarIndex,
        node_ref: NodeRef<'db>,
        class: Type<'db, '_>,
    ) -> bool {
        let specific = node_ref.point().specific();
        if self.match_specific == specific {
            self.calculated_type_vars
                .as_mut()
                .unwrap()
                .set_generic(type_var_index, class.into_db_type(i_s));
            true
        } else if specific == Specific::ClassTypeVar {
            match self.func_or_callable {
                FunctionOrCallable::Function(f) => {
                    let g = f.class.unwrap().generics.nth(i_s, type_var_index);
                    // TODO nth should return a type instead of DbType
                    let g = Type::from_db_type(i_s.database, &g);
                    g.matches(i_s, Some(self), class)
                }
                FunctionOrCallable::Callable(c) => todo!(),
            }
        } else {
            todo!()
        }
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
    let set_point = |n: Name<'db>, point_type, i| {
        let point = Point::new_numbered_type_var(point_type, TypeVarIndex::new(i), Locality::Todo);
        match n.parent() {
            NameParent::Primary(primary) => {
                file.points.set(primary.index(), point);
            }
            _ => (),
        }
        file.points.set(n.index(), point);
    };
    let mut late_bound_type_vars = vec![];
    for n in expression.search_names() {
        let inferred = match n.parent() {
            NameParent::Atom => Some(file.inference(i_s).infer_name_reference(n)),
            NameParent::Primary(mut primary) => {
                loop {
                    if primary.end() != n.end() {
                        // This filters out if the name is not the last name and also if it ends
                        // with a bracket (execution or index).
                        break None;
                    }
                    match primary.parent() {
                        PrimaryParent::Primary(p) => primary = p,
                        _ => break Some(file.inference(i_s).infer_primary(primary)),
                    }
                }
            }
            _ => None,
        };
        if let Some(inferred) = inferred {
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
                            set_point(n, Specific::LateBoundTypeVar, i);
                            continue;
                        }
                        found_type_vars.push(link);
                    };
                    let i = i.unwrap_or(found_type_vars.len() - 1);
                    set_point(n, point_type, i);
                }
            }
        }
    }
}

pub fn search_type_vars_within_possible_class<'db>(
    i_s: &mut InferenceState<'db, '_>,
    file: &'db PythonFile,
    expression: &Expression<'db>,
    found_type_vars: &mut Vec<PointLink>,
    class_infos: Option<&'db ClassInfos>,
    add_new_as_late_bound_type_var: bool,
    newly_found_type: Specific,
) {
    let mut add = |n: NodeIndex, type_var_link: PointLink| {
        if let Some(class_infos) = class_infos {
            if let Some(index) = class_infos.find_type_var_index(type_var_link) {
                // Overwrite with a better type var definition.
                file.points.set(
                    n,
                    Point::new_numbered_type_var(Specific::ClassTypeVar, index, Locality::Todo),
                );
                return None;
            }
        }
        Some(newly_found_type)
    };
    search_type_vars(
        i_s,
        file,
        expression,
        &mut add,
        found_type_vars,
        add_new_as_late_bound_type_var,
    );
}

#[derive(Debug, Clone)]
pub enum Type<'db, 'a> {
    ClassLike(ClassLike<'db, 'a>),
    TypeVar(TypeVarIndex, NodeRef<'db>),
    Union(Vec<DbType>),
    None,
    Any,
    Unknown,
}

impl<'db, 'a> Type<'db, 'a> {
    pub fn from_db_type(database: &'db Database, db_type: &'a DbType) -> Self {
        match db_type {
            DbType::Class(link) => {
                let node_ref = NodeRef::from_link(database, *link);
                Self::ClassLike(ClassLike::Class(
                    Class::from_position(node_ref, Generics::None, None).unwrap(),
                ))
            }
            DbType::Unknown => Self::Unknown,
            DbType::None => Type::None,
            DbType::Any => Type::Any,
            DbType::GenericClass(link, generics) => {
                let node_ref = NodeRef::from_link(database, *link);
                Self::ClassLike(ClassLike::Class(
                    Class::from_position(node_ref, Generics::new_list(generics), None).unwrap(),
                ))
            }
            DbType::Union(list) => Self::Union(list.iter().cloned().collect()),
            DbType::TypeVar(index, link) => {
                Self::TypeVar(*index, NodeRef::from_link(database, *link))
            }
            DbType::Type(db_type) => Self::ClassLike(ClassLike::TypeWithDbType(db_type)),
            DbType::Tuple(content) => Self::ClassLike(ClassLike::Tuple(TupleClass::new(content))),
            DbType::Callable(content) => {
                Self::ClassLike(ClassLike::Callable(CallableClass::new(content)))
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
            Self::TypeVar(type_var_index, node_ref) => {
                DbType::TypeVar(type_var_index, node_ref.as_link())
            }
            Self::Union(list) => DbType::Union(GenericsList::from_vec(list)),
            Self::None => DbType::None,
            Self::Any => DbType::Any,
            Self::Unknown => todo!(),
        }
    }

    pub fn matches(
        &self,
        i_s: &mut InferenceState<'db, '_>,
        mut matcher: Option<&mut TypeVarMatcher<'db, '_>>,
        value_class: Self,
    ) -> bool {
        match self {
            Self::ClassLike(class) => class.matches(i_s, value_class, matcher),
            Self::TypeVar(type_var_index, node_ref) => match value_class {
                Type::ClassLike(class) => {
                    if let Some(matcher) = matcher {
                        let generic = class.as_db_type(i_s);
                        matcher.match_or_add_type_var(i_s, *type_var_index, *node_ref, value_class)
                    } else {
                        true
                    }
                }
                Type::TypeVar(_, _) | Type::Unknown => {
                    todo!("{:?}", value_class)
                }
                Type::Union(ref list) => {
                    if let Some(matcher) = matcher {
                        matcher.match_or_add_type_var(i_s, *type_var_index, *node_ref, value_class)
                    } else {
                        true
                    }
                }
                Type::Any => {
                    todo!()
                }
                Type::None => {
                    //matcher.match_or_add_type_var(i_s, *type_var_index, node_ref, value_class)
                    todo!()
                }
            },
            Self::Union(list1) => match value_class {
                Self::Union(mut list2) => {
                    let mut type_var_content = None;
                    for g1 in list1 {
                        if let Some(t) = g1.maybe_type_var_index() {
                            type_var_content = Some(t);
                        }
                        for (i, g2) in list2.iter().enumerate() {
                            if g1.todo_matches(g2) {
                                list2.remove(i);
                                break;
                            }
                        }
                    }
                    /*
                    if type_var_content.is_some() {
                            Type::from_db_type(i_s.database, g1).matches(
                                i_s,
                                matcher,
                                Type::from_db_type(i_s.database, g2),
                            );
                    }*/
                    if let Some((type_var_index, link)) = type_var_content {
                        if let Some(matcher) = matcher {
                            let g = match list2.len() {
                                0 => unreachable!(),
                                1 => Type::from_db_type(i_s.database, &list2[0]),
                                _ => Type::Union(list2),
                            };
                            let node_ref = NodeRef::from_link(i_s.database, link);
                            matcher.match_or_add_type_var(i_s, type_var_index, node_ref, g)
                        } else {
                            true
                        }
                    } else if !list2.is_empty() {
                        false
                    } else {
                        true
                    }
                }
                _ => list1.iter().any(|g| {
                    Type::from_db_type(i_s.database, g).matches(
                        i_s,
                        matcher.as_deref_mut(),
                        value_class.clone(),
                    )
                }),
            },
            Self::None => matches!(value_class, Self::None),
            Self::Any => true,
            Self::Unknown => false,
        }
    }

    pub fn error_if_not_matches(
        &self,
        i_s: &mut InferenceState<'db, '_>,
        value: &Inferred<'db>,
        mut callback: impl FnMut(String, String),
    ) {
        let value_type = value.class_as_type(i_s);
        if !self.matches(i_s, None, value_type) {
            callback(
                value
                    .class_as_type(i_s)
                    .as_string(i_s, None, FormatStyle::Short),
                self.as_string(i_s, None, FormatStyle::Short),
            )
        }
    }

    pub fn execute_and_resolve_type_vars(
        &self,
        i_s: &mut InferenceState<'db, '_>,
        class: Option<&Class<'db, '_>>,
        function_matcher: &mut TypeVarMatcher<'db, '_>,
    ) -> Inferred<'db> {
        let db_type = self.internal_resolve_type_vars(i_s, class, function_matcher);
        debug!(
            "Resolved type vars: {}",
            db_type.as_type_string(i_s.database, None, FormatStyle::Short)
        );
        Inferred::execute_db_type(i_s, db_type)
    }

    fn internal_resolve_type_vars(
        &self,
        i_s: &mut InferenceState<'db, '_>,
        class: Option<&Class<'db, '_>>,
        function_matcher: &mut TypeVarMatcher<'db, '_>,
    ) -> DbType {
        let resolve_type_var = |i_s: &mut InferenceState<'db, '_>,
                                function_matcher: &mut TypeVarMatcher<'db, '_>,
                                type_var_index: TypeVarIndex,
                                node_ref: &NodeRef| {
            let point = node_ref.point();
            match point.specific() {
                Specific::ClassTypeVar => {
                    let class = class.unwrap();
                    let mut generic = |type_var_index| class.generics().nth(i_s, type_var_index);
                    class
                        .type_var_remap
                        .map(|remaps| {
                            remaps
                                .nth(type_var_index)
                                .map(|x| x.remap_type_vars(&mut generic))
                                // This means that no generic was provided
                                .unwrap_or(DbType::Unknown)
                        })
                        .unwrap_or_else(|| generic(type_var_index))
                }
                Specific::FunctionTypeVar => function_matcher
                    .nth(i_s, type_var_index)
                    .unwrap_or_else(|| unreachable!()),
                Specific::LateBoundTypeVar => {
                    if function_matcher.match_specific == Specific::LateBoundTypeVar {
                        if let Some(calculated) = function_matcher.nth(i_s, type_var_index) {
                            return calculated;
                        }
                    }
                    // Just pass the type var again, because it might be resolved by a future
                    // callable, that is late bound, like Callable[..., Callable[[T], T]]
                    DbType::TypeVar(type_var_index, node_ref.as_link())
                }
                _ => unreachable!(),
            }
        };

        match self {
            Self::ClassLike(c) => {
                c.as_db_type(i_s)
                    .replace_type_vars(&mut |type_var_index, link| {
                        let node_ref = NodeRef::from_link(i_s.database, link);
                        resolve_type_var(i_s, function_matcher, type_var_index, &node_ref)
                    })
            }
            Self::TypeVar(type_var_index, node_ref) => {
                resolve_type_var(i_s, function_matcher, *type_var_index, node_ref)
            }
            Self::Union(list) => DbType::Union(GenericsList::new(
                list.iter()
                    .map(|g| {
                        g.clone().replace_type_vars(&mut |type_var_index, link| {
                            let node_ref = NodeRef::from_link(i_s.database, link);
                            resolve_type_var(i_s, function_matcher, type_var_index, &node_ref)
                        })
                    })
                    .collect(),
            )),
            Self::None => DbType::None,
            Self::Any => todo!(),
            Self::Unknown => DbType::Unknown,
        }
    }

    pub fn as_string(
        &self,
        i_s: &mut InferenceState<'db, '_>,
        func: Option<&Function<'db, '_>>,
        style: FormatStyle,
    ) -> String {
        match self {
            Self::ClassLike(c) => c.as_string(i_s, style),
            Self::TypeVar(index, node_ref) => {
                if let Some(func) = func {
                    if node_ref.point().specific() == Specific::ClassTypeVar {
                        if let Some(class) = func.class {
                            return class.generics.nth(i_s, *index).as_type_string(
                                i_s.database,
                                None,
                                style,
                            );
                        }
                    }
                }
                node_ref.as_name().as_str().to_owned()
            }
            Self::Union(list) => list.iter().fold(String::new(), |a, b| {
                if a.is_empty() {
                    a + &b.as_type_string(i_s.database, None, style)
                } else {
                    a + " | " + &b.as_type_string(i_s.database, None, style)
                }
            }),
            Self::None => "None".to_owned(),
            Self::Any => "Any".to_owned(),
            Self::Unknown => "Unknown".to_owned(),
        }
    }

    pub fn maybe_execute(&self, i_s: &mut InferenceState<'db, '_>) -> Inferred<'db> {
        match self {
            Self::ClassLike(c) => {
                let g = c.as_db_type(i_s);
                Inferred::execute_db_type(i_s, g)
            }
            Self::Union(list) => Inferred::gather_union(|callable| {
                for db_type in list.iter() {
                    callable(Inferred::execute_db_type(i_s, db_type.clone()))
                }
            }),
            Self::TypeVar(index, node_ref) => {
                Inferred::execute_db_type(i_s, DbType::TypeVar(*index, node_ref.as_link()))
            }
            Self::None => Inferred::new_unsaved_specific(Specific::None),
            Self::Any => todo!(),
            Self::Unknown => unreachable!(), // Was checked earlier
        }
    }
}
