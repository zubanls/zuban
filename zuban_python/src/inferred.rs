use parsa_python_ast::{NodeIndex, Primary, PrimaryContent, PythonString};
use std::borrow::Cow;
use std::fmt;

use crate::arguments::{Arguments, NoArguments, SimpleArguments};
use crate::database::{
    AnyLink, ComplexPoint, Database, DbType, FileIndex, GenericItem, GenericsList, Locality,
    MroIndex, NewType, Point, PointLink, PointType, Specific, TypeVarLike,
};
use crate::diagnostics::IssueType;
use crate::file::File;
use crate::file::PythonFile;
use crate::inference_state::InferenceState;
use crate::matching::{FormatData, Generics, ResultContext, Type};
use crate::name::{ValueName, ValueNameIterator, WithValueName};
use crate::node_ref::NodeRef;
use crate::value::{
    BoundMethod, BoundMethodFunction, Callable, Class, DictLiteral, Function, Instance,
    IteratorContent, ListLiteral, Module, NewTypeClass, NoneInstance, OnTypeError,
    OverloadedFunction, ParamSpecClass, RevealTypeFunction, Tuple, TypeAlias, TypeVarClass,
    TypeVarInstance, TypeVarTupleClass, TypingCast, TypingClass, TypingClassVar, TypingType, Value,
};

#[derive(Debug)]
pub enum FunctionOrOverload<'a> {
    Function(Function<'a>),
    Overload(OverloadedFunction<'a>),
}

#[derive(Debug, Clone, PartialEq)]
enum InferredState {
    Saved(PointLink, Point),
    UnsavedFileReference(FileIndex),
    UnsavedComplex(ComplexPoint),
    UnsavedSpecific(Specific),
    Unknown,
}

#[derive(Clone)]
pub struct Inferred {
    state: InferredState,
}

impl<'db: 'slf, 'slf> Inferred {
    pub fn new_and_save(file: &'db PythonFile, node_index: NodeIndex, point: Point) -> Self {
        file.points.set(node_index, point);
        Self::new_saved(file, node_index, point)
    }

    pub fn from_saved_node_ref(node_ref: NodeRef) -> Self {
        Self {
            state: InferredState::Saved(node_ref.as_link(), node_ref.point()),
        }
    }

    pub fn new_saved2(file: &'db PythonFile, node_index: NodeIndex) -> Self {
        // TODO rethink this method and new_saved
        let node_ref = NodeRef { file, node_index };
        Self {
            state: InferredState::Saved(node_ref.as_link(), node_ref.point()),
        }
    }

    pub fn new_saved(file: &'db PythonFile, node_index: NodeIndex, point: Point) -> Self {
        Self {
            state: InferredState::Saved(PointLink::new(file.file_index(), node_index), point),
        }
    }

    pub fn new_unsaved_complex(complex: ComplexPoint) -> Self {
        Self {
            state: InferredState::UnsavedComplex(complex),
        }
    }

    pub fn new_unsaved_specific(specific: Specific) -> Self {
        Self {
            state: InferredState::UnsavedSpecific(specific),
        }
    }

    pub fn new_unknown() -> Self {
        Self {
            state: InferredState::Unknown,
        }
    }

    pub fn new_none() -> Self {
        Self {
            state: InferredState::UnsavedSpecific(Specific::None),
        }
    }

    pub fn new_any() -> Self {
        Self {
            state: InferredState::UnsavedSpecific(Specific::TypingAny),
        }
    }

    pub fn new_file_reference(index: FileIndex) -> Self {
        // TODO maybe remove this and UnsavedFileReference??? unused??
        Self {
            state: InferredState::UnsavedFileReference(index),
        }
    }

    pub fn execute_db_type(i_s: &mut InferenceState<'db, '_>, generic: DbType) -> Self {
        let state = match generic {
            DbType::Class(l, g) => InferredState::UnsavedComplex(ComplexPoint::Instance(l, g)),
            DbType::Type(ref c) if matches!(c.as_ref(), DbType::Class(_, _)) => match c.as_ref() {
                DbType::Class(link, None) => {
                    let node_ref = NodeRef::from_link(i_s.db, *link);
                    InferredState::Saved(*link, node_ref.point())
                }
                _ => unreachable!(),
            },
            DbType::None => return Inferred::new_none(),
            DbType::Any => return Inferred::new_any(),
            _ => InferredState::UnsavedComplex(ComplexPoint::TypeInstance(Box::new(generic))),
        };
        Self { state }
    }

    pub fn create_instance(class: PointLink, generics: Option<&[GenericItem]>) -> Self {
        Self::new_unsaved_complex(ComplexPoint::Instance(
            class,
            generics.map(|lst| GenericsList::generics_from_vec(lst.to_vec())),
        ))
    }

    pub fn class_as_type(&'slf self, i_s: &mut InferenceState<'db, '_>) -> Type<'slf> {
        match self.state {
            InferredState::Saved(definition, _) => {
                let node_ref = NodeRef::from_link(i_s.db, definition);
                if let Some(ComplexPoint::TypeInstance(ref t)) = node_ref.complex() {
                    return Type::new(t);
                }
            }
            InferredState::UnsavedComplex(ComplexPoint::TypeInstance(ref t)) => {
                return Type::new(t)
            }
            _ => (),
        };
        self.internal_run(
            i_s,
            &mut |i_s, v| v.as_type(i_s),
            &|i_s, g1, g2| g1.union(i_s, g2),
            &mut |i_s| Type::new(&DbType::Any),
        )
    }

    pub fn class_as_db_type(&self, i_s: &mut InferenceState<'db, '_>) -> DbType {
        self.class_as_type(i_s).into_db_type(i_s)
    }

    pub fn format(&self, i_s: &mut InferenceState<'db, '_>, format_data: &FormatData) -> Box<str> {
        self.class_as_type(i_s).format(format_data)
    }

    #[inline]
    pub fn internal_run<'a, T>(
        &'a self,
        i_s: &mut InferenceState<'db, '_>,
        callable: &mut impl FnMut(&mut InferenceState<'db, '_>, &dyn Value<'db, 'a>) -> T,
        reducer: &impl Fn(&mut InferenceState<'db, '_>, T, T) -> T,
        on_missing: &mut impl FnMut(&mut InferenceState<'db, '_>) -> T,
    ) -> T
    where
        'db: 'a,
    {
        match &self.state {
            InferredState::Saved(definition, point) => {
                run_on_saved(i_s, *definition, *point, callable, reducer, on_missing)
            }
            InferredState::UnsavedComplex(complex) => {
                run_on_complex(i_s, complex, None, callable, reducer, on_missing)
            }
            InferredState::UnsavedSpecific(specific) => match specific {
                Specific::None => callable(i_s, &NoneInstance()),
                Specific::TypingAny => on_missing(i_s),
                _ => todo!("{specific:?}"),
            },
            InferredState::UnsavedFileReference(file_index) => {
                let f = i_s.db.loaded_python_file(*file_index);
                callable(i_s, &Module::new(i_s.db, f))
            }
            InferredState::Unknown => on_missing(i_s),
        }
    }

    #[inline]
    pub fn internal_run_after_save<T>(
        &self,
        i_s: &mut InferenceState<'db, '_>,
        callable: &mut impl FnMut(&mut InferenceState<'db, '_>, &dyn Value<'db, 'db>) -> T,
        reducer: &impl Fn(&mut InferenceState<'db, '_>, T, T) -> T,
        on_missing: &mut impl FnMut(&mut InferenceState<'db, '_>) -> T,
    ) -> T {
        match &self.state {
            InferredState::Saved(definition, point) => {
                run_on_saved(i_s, *definition, *point, callable, reducer, on_missing)
            }
            InferredState::UnsavedComplex(complex) => unreachable!(),
            InferredState::UnsavedSpecific(specific) => match specific {
                Specific::None => callable(i_s, &NoneInstance()),
                Specific::TypingAny => on_missing(i_s),
                _ => todo!("{specific:?}"),
            },
            InferredState::UnsavedFileReference(file_index) => {
                let f = i_s.db.loaded_python_file(*file_index);
                callable(i_s, &Module::new(i_s.db, f))
            }
            InferredState::Unknown => on_missing(i_s),
        }
    }

    pub fn run_on_value(
        &self,
        i_s: &mut InferenceState<'db, '_>,
        callable: &mut impl FnMut(&mut InferenceState<'db, '_>, &dyn Value<'db, '_>) -> Self,
    ) -> Self {
        self.internal_run(i_s, callable, &|i_s, i1, i2| i1.union(i2), &mut |i_s| {
            Inferred::new_unknown()
        })
    }

    pub fn run_on_value_names<C, T>(
        &self,
        i_s: &mut InferenceState<'db, '_>,
        callable: &C,
    ) -> ValueNameIterator<T>
    where
        C: Fn(&dyn ValueName<'db>) -> T,
    {
        self.internal_run(
            i_s,
            &mut |i_s, value| {
                ValueNameIterator::Single(callable(&WithValueName::new(i_s.db, value)))
            },
            &|_, iter1, iter2| {
                // Reducer
                match iter1 {
                    ValueNameIterator::Single(element1) => match iter2 {
                        ValueNameIterator::Single(element2) => {
                            ValueNameIterator::Multiple(vec![element1, element2])
                        }
                        ValueNameIterator::Multiple(mut list2) => {
                            list2.push(element1);
                            ValueNameIterator::Multiple(list2)
                        }
                        ValueNameIterator::Finished => ValueNameIterator::Single(element1),
                    },
                    ValueNameIterator::Multiple(mut list1) => match iter2 {
                        ValueNameIterator::Single(element2) => {
                            list1.push(element2);
                            ValueNameIterator::Multiple(list1)
                        }
                        ValueNameIterator::Multiple(mut list2) => {
                            list1.append(&mut list2);
                            ValueNameIterator::Multiple(list1)
                        }
                        ValueNameIterator::Finished => ValueNameIterator::Multiple(list1),
                    },
                    ValueNameIterator::Finished => iter2,
                }
            },
            &mut |i_s| ValueNameIterator::Finished,
        )
    }

    pub fn run_mut(
        &self,
        i_s: &mut InferenceState<'db, '_>,
        callable: &mut impl for<'a, 'b, 'c> FnMut(&mut InferenceState<'db, 'c>, &'b dyn Value<'db, 'a>),
        mut on_missing: impl FnMut(),
    ) {
        self.internal_run(i_s, callable, &|_, i1, i2| (), &mut |i_s| on_missing())
    }

    pub fn maybe_type_var_like(&self, i_s: &mut InferenceState<'db, '_>) -> Option<TypeVarLike> {
        if let InferredState::Saved(definition, point) = self.state {
            let node_ref = NodeRef::from_link(i_s.db, definition);
            if let Some(ComplexPoint::TypeVarLike(t)) = node_ref.complex() {
                return Some(t.clone());
            }
        }
        None
    }

    pub fn maybe_new_type(&self, i_s: &mut InferenceState<'db, '_>) -> Option<NewType> {
        if let InferredState::Saved(definition, point) = self.state {
            let node_ref = NodeRef::from_link(i_s.db, definition);
            if let Some(ComplexPoint::TypeInstance(t)) = node_ref.complex() {
                if let DbType::Type(t) = t.as_ref() {
                    if let DbType::NewType(n) = t.as_ref() {
                        return Some(n.clone());
                    }
                }
            }
        }
        None
    }

    pub fn resolve_function_return(self, i_s: &mut InferenceState<'db, '_>) -> Self {
        if let InferredState::Saved(definition, point) = self.state {
            if point.type_() == PointType::Specific {
                match point.specific() {
                    Specific::InstanceWithArguments => {
                        let node_ref = NodeRef::from_link(i_s.db, definition);
                        let inf_cls = infer_instance_with_arguments_cls(i_s, node_ref)
                            .resolve_function_return(i_s);
                        let class = inf_cls.maybe_class(i_s).unwrap();
                        debug_assert!(class.type_vars(i_s).is_none());
                        let args = SimpleArguments::from_primary(
                            i_s.clone(),
                            node_ref.file,
                            node_ref.as_primary(),
                            None,
                        );
                        let init = class.simple_init_func(i_s, &args);
                        return Inferred::new_unsaved_complex(match args.as_execution(&init) {
                            Some(execution) => ComplexPoint::ExecutionInstance(
                                inf_cls.get_saved(i_s.db).unwrap().0.as_link(),
                                Box::new(execution),
                            ),
                            None => ComplexPoint::Instance(
                                inf_cls.get_saved(i_s.db).unwrap().0.as_link(),
                                None,
                            ),
                        });
                    }
                    Specific::Closure => {
                        return Inferred::new_unsaved_complex(ComplexPoint::Closure(
                            definition,
                            Box::new(i_s.args_as_execution().unwrap()),
                        ));
                    }
                    Specific::Param => {
                        todo!("might not even happen - remove")
                        //return i_s.infer_param(&definition);
                    }
                    _ => (),
                }
            }
        }
        self
    }

    fn with_instance<'a, T>(
        &self,
        i_s: &mut InferenceState<'db, '_>,
        instance: NodeRef<'db>,
        generics: Option<Generics<'a>>,
        callable: impl FnOnce(&mut InferenceState<'db, '_>, &Instance<'a>) -> T,
    ) -> T
    where
        'db: 'a,
    {
        match &self.state {
            InferredState::Saved(definition, point) => {
                let definition = NodeRef::from_link(i_s.db, *definition);
                if point.type_() == PointType::Specific {
                    if let Specific::SimpleGeneric = point.specific() {
                        let p = Primary::by_index(&definition.file.tree, definition.node_index);
                        let cls = definition
                            .file
                            .inference(i_s)
                            .infer_primary_or_atom(p.first());
                        cls.with_instance(
                            i_s,
                            instance,
                            Some(Generics::new_simple_generic_slice(
                                definition.file,
                                p.expect_slice(),
                            )),
                            callable,
                        )
                    } else {
                        unreachable!("{point:?}")
                    }
                } else {
                    callable(
                        i_s,
                        &use_instance(
                            definition,
                            generics.unwrap_or(Generics::Any),
                            Some(instance),
                        ),
                    )
                }
            }
            _ => unreachable!("{:?}", self.state),
        }
    }

    fn expect_instance(&self, i_s: &mut InferenceState<'db, '_>) -> Instance<'db> {
        let mut instance = None;
        self.run_mut(
            i_s,
            &mut |i_s, v| {
                // TODO this is a weird issue, probably a compiler bug...
                // https://github.com/rust-lang/rust/issues/91942
                let v: &dyn Value = unsafe { std::mem::transmute(v) };
                if let Some(i) = v.as_instance() {
                    instance = Some(*i);
                } else {
                    unreachable!("{self:?} -> {v:?}")
                }
            },
            || unreachable!(),
        );
        instance.unwrap()
    }

    pub fn maybe_callable<'x>(&'x self, i_s: &mut InferenceState<'db, '_>) -> Option<Callable<'x>>
    where
        'db: 'x,
    {
        self.internal_run(
            i_s,
            &mut |i_s, v| v.as_callable(),
            &|_, _, _| None,
            &mut |_| None,
        )
    }

    pub fn maybe_class(&self, i_s: &mut InferenceState<'db, '_>) -> Option<Class<'db>> {
        let mut generics = None;
        if let InferredState::Saved(definition, point) = &self.state {
            if point.type_() == PointType::Specific {
                let definition = NodeRef::from_link(i_s.db, *definition);
                generics = Self::expect_generics(definition, *point);
            }
        }
        self.maybe_class_internal(i_s, generics.unwrap_or(Generics::Any))
    }

    fn maybe_class_internal<'a>(
        &self,
        i_s: &mut InferenceState<'db, '_>,
        generics: Generics<'a>,
    ) -> Option<Class<'a>>
    where
        'db: 'a,
    {
        match &self.state {
            InferredState::Saved(definition, point) => {
                let definition = NodeRef::from_link(i_s.db, *definition);
                match point.type_() {
                    PointType::Complex => {
                        let complex = definition.file.complex_points.get(point.complex_index());
                        if let ComplexPoint::Class(c) = complex {
                            Some(Class::new(definition, c, generics, None))
                        } else {
                            None
                        }
                    }
                    PointType::Specific => match point.specific() {
                        Specific::SimpleGeneric => {
                            let inferred = definition
                                .file
                                .inference(i_s)
                                .infer_primary_or_atom(definition.as_primary().first());
                            inferred.maybe_class_internal(i_s, generics)
                        }
                        _ => None,
                    },
                    _ => None,
                }
            }
            InferredState::UnsavedComplex(complex) => {
                if let ComplexPoint::TypeInstance(g) = complex {
                    return None; // TODO this was originally a return None for tuple class
                }
                todo!("{complex:?}")
            }
            InferredState::UnsavedSpecific(specific) => todo!(),
            InferredState::UnsavedFileReference(file_index) => todo!(),
            InferredState::Unknown => None,
        }
    }

    pub fn expect_int(&self, db: &Database) -> Option<i64> {
        if let InferredState::Saved(definition, point) = self.state {
            if let Some(Specific::Integer) = point.maybe_specific() {
                let definition = NodeRef::from_link(db, definition);
                return definition.infer_int();
            }
        }
        None
    }

    pub fn maybe_str(&self, db: &'db Database) -> Option<PythonString<'db>> {
        if let InferredState::Saved(definition, point) = self.state {
            if let Some(Specific::String) = point.maybe_specific() {
                let definition = NodeRef::from_link(db, definition);
                return definition.infer_str();
            }
        }
        None
    }

    pub fn save_redirect(self, db: &Database, file: &PythonFile, index: NodeIndex) -> Self {
        // TODO this locality should be calculated in a more correct way
        let p = file.points.get(index);
        if p.calculated() && p.maybe_specific() == Some(Specific::Cycle) {
            return Self::new_saved(file, index, file.points.get(index));
        }
        let point = match &self.state {
            InferredState::Saved(definition, point) => {
                // Overwriting strings needs to be possible, because of string annotations
                if p.calculated()
                    && !matches!(
                        p.maybe_specific(),
                        Some(Specific::String | Specific::Cycle | Specific::LazyInferredFunction)
                    )
                {
                    todo!(
                        "{self:?} >>>> {p:?} {index:?}, {}",
                        file.tree.short_debug_of_index(index)
                    );
                }
                file.points.set(
                    index,
                    Point::new_redirect(definition.file, definition.node_index, Locality::Todo),
                );
                return self;
            }
            InferredState::UnsavedComplex(complex) => {
                file.complex_points
                    .insert(&file.points, index, complex.clone(), Locality::Todo);
                return Self::new_saved(file, index, file.points.get(index));
            }
            InferredState::UnsavedSpecific(mut specific) => {
                if specific == Specific::Cycle {
                    let r = NodeRef::new(file, index);
                    r.add_typing_issue(
                        db,
                        IssueType::CyclicDefinition {
                            name: Box::from(r.as_code()),
                        },
                    );
                    specific = Specific::TypingAny;
                }
                Point::new_simple_specific(specific, Locality::Todo)
            }
            InferredState::UnsavedFileReference(file_index) => {
                Point::new_file_reference(*file_index, Locality::Todo)
            }
            InferredState::Unknown => Point::new_unknown(file.file_index(), Locality::Todo),
        };
        file.points.set(index, point);
        Self::new_saved(file, index, point)
    }

    pub fn save_if_unsaved(self, db: &Database, file: &'db PythonFile, index: NodeIndex) -> Self {
        if matches!(self.state, InferredState::Saved(_, _)) {
            self
        } else {
            self.save_redirect(db, file, index)
        }
    }

    pub fn init_as_function<'a>(
        &self,
        db: &'db Database,
        class: Class<'a>,
    ) -> Option<FunctionOrOverload<'a>>
    where
        'db: 'a,
    {
        if let InferredState::Saved(definition, point) = &self.state {
            let definition = NodeRef::from_link(db, *definition);
            if let Some(Specific::Function) = point.maybe_specific() {
                return Some(FunctionOrOverload::Function(Function::new(
                    definition,
                    Some(class),
                )));
            }
            if let Some(ComplexPoint::FunctionOverload(overload)) = definition.complex() {
                return Some(FunctionOrOverload::Overload(OverloadedFunction::new(
                    definition,
                    overload,
                    Some(class),
                )));
            }
        }
        None
    }

    fn get_saved(&self, db: &'db Database) -> Option<(NodeRef<'db>, Point)> {
        match self.state {
            InferredState::Saved(definition, point) => {
                let definition = NodeRef::from_link(db, definition);
                Some((definition, point))
            }
            _ => None,
        }
    }

    pub fn union(self, other: Self) -> Self {
        if self.state == other.state {
            self
        } else {
            let mut list = vec![];
            let insert = |list: &mut Vec<AnyLink>, state| {
                match state {
                    InferredState::Saved(definition, _) => {
                        list.push(AnyLink::Reference(definition));
                    }
                    InferredState::UnsavedComplex(complex) => match complex {
                        ComplexPoint::Union(lst) => {
                            list.extend(lst.iter().cloned());
                        }
                        _ => list.push(AnyLink::Complex(Box::new(complex))),
                    },
                    InferredState::UnsavedSpecific(specific) => {
                        list.push(AnyLink::SimpleSpecific(specific))
                    }
                    InferredState::UnsavedFileReference(file_index) => todo!(),
                    InferredState::Unknown => list.push(AnyLink::Unknown),
                };
            };
            insert(&mut list, self.state);
            insert(&mut list, other.state);
            Self::new_unsaved_complex(ComplexPoint::Union(list.into_boxed_slice()))
        }
    }

    #[inline]
    pub fn gather_union(callable: impl FnOnce(&mut dyn FnMut(Self))) -> Self {
        let mut result: Option<Self> = None;
        let r = &mut result;
        callable(&mut |inferred| {
            *r = Some(match r.take() {
                Some(i) => i.union(inferred),
                None => inferred,
            });
        });
        result.unwrap_or_else(|| todo!())
    }

    #[inline]
    pub fn bind(
        self,
        i_s: &mut InferenceState<'db, '_>,
        get_inferred: impl Fn(&mut InferenceState<'db, '_>) -> Inferred,
        mro_index: MroIndex,
    ) -> Self {
        match &self.state {
            InferredState::Saved(definition, point) => match point.type_() {
                PointType::Specific => {
                    if point.specific() == Specific::Function {
                        let complex = ComplexPoint::BoundMethod(
                            get_inferred(i_s).as_any_link(i_s),
                            mro_index,
                            *definition,
                        );
                        return Self::new_unsaved_complex(complex);
                    }
                }
                PointType::Complex => {
                    let file = i_s.db.loaded_python_file(definition.file);
                    match file.complex_points.get(point.complex_index()) {
                        ComplexPoint::FunctionOverload(o) => {
                            let complex = ComplexPoint::BoundMethod(
                                get_inferred(i_s).as_any_link(i_s),
                                mro_index,
                                *definition,
                            );
                            return Self::new_unsaved_complex(complex);
                        }
                        ComplexPoint::TypeInstance(t) => {
                            if let DbType::Callable(c) = t.as_ref() {
                                let complex = ComplexPoint::BoundMethod(
                                    get_inferred(i_s).as_any_link(i_s),
                                    mro_index,
                                    *definition,
                                );
                                return Self::new_unsaved_complex(complex);
                            }
                        }
                        _ => (),
                    }
                }
                _ => (),
            },
            InferredState::UnsavedComplex(complex) => (),
            InferredState::UnsavedSpecific(specific) => todo!(),
            InferredState::UnsavedFileReference(file_index) => todo!(),
            InferredState::Unknown => (),
        }
        self
    }

    pub fn description(&self, i_s: &mut InferenceState<'db, '_>) -> String {
        self.internal_run(
            i_s,
            &mut |i_s, v| v.description(i_s),
            &|_, i1, i2| format!("{i1}|{i2}"),
            &mut |i_s| "Unknown".to_owned(),
        )
    }

    pub fn debug_info(&self, i_s: &mut InferenceState<'db, '_>) -> String {
        let details = match &self.state {
            InferredState::Saved(definition, point) => {
                let definition = NodeRef::from_link(i_s.db, *definition);
                format!(
                    "{} (complex?: {:?})",
                    definition.file.file_path(i_s.db),
                    definition.complex(),
                )
            }
            _ => "".to_owned(),
        };
        format!(
            "description = {}\ndebug = {self:?}\ndetails = {details}",
            self.description(i_s),
        )
    }

    pub fn as_any_link(&self, i_s: &InferenceState<'db, '_>) -> AnyLink {
        match &self.state {
            InferredState::Saved(definition, _) => AnyLink::Reference(*definition),
            InferredState::UnsavedComplex(complex) => AnyLink::Complex(Box::new(complex.clone())),
            InferredState::UnsavedSpecific(specific) => todo!(),
            InferredState::UnsavedFileReference(file_index) => todo!(),
            InferredState::Unknown => todo!(),
        }
    }

    fn from_any_link(db: &'db Database, any: &AnyLink) -> Self {
        match any {
            AnyLink::Reference(def) => {
                let file = db.loaded_python_file(def.file);
                Self::new_saved(file, def.node_index, file.points.get(def.node_index))
            }
            AnyLink::Complex(complex) => Self::new_unsaved_complex(*complex.clone()),
            AnyLink::SimpleSpecific(_) => todo!(),
            AnyLink::Unknown => todo!(),
        }
    }

    fn expect_generics(definition: NodeRef<'db>, point: Point) -> Option<Generics<'db>> {
        if point.type_() == PointType::Specific && point.specific() == Specific::SimpleGeneric {
            let primary = definition.as_primary();
            match primary.second() {
                PrimaryContent::GetItem(slice_type) => {
                    return Some(Generics::new_simple_generic_slice(
                        definition.file,
                        slice_type,
                    ))
                }
                _ => {
                    unreachable!()
                }
            }
        }
        None
    }

    pub fn maybe_simple<'a, T>(
        &'a self,
        i_s: &mut InferenceState<'db, '_>,
        c: impl Fn(&dyn Value<'db, 'a>) -> Option<T>,
    ) -> Option<T>
    where
        'db: 'a,
    {
        self.internal_run(i_s, &mut |i_s, v| c(v), &|_, i1, i2| None, &mut |i_s| None)
    }

    pub fn is_unknown(&self) -> bool {
        match &self.state {
            InferredState::Saved(_, point) => matches!(point.type_(), PointType::Unknown),
            InferredState::Unknown => true,
            _ => false,
        }
    }

    pub fn is_union(&self, db: &'db Database) -> bool {
        let check_complex_point = |c: &_| match c {
            ComplexPoint::Union(_) => true,
            ComplexPoint::TypeInstance(t) => matches!(t.as_ref(), DbType::Union(_)),
            _ => false,
        };
        match &self.state {
            InferredState::Saved(reference, point) => {
                let node_ref = NodeRef::from_link(db, *reference);
                node_ref
                    .complex()
                    .map(|c| check_complex_point(c))
                    .unwrap_or(false)
            }
            InferredState::UnsavedComplex(c) => check_complex_point(c),
            _ => false,
        }
    }

    pub fn execute_function(
        &self,
        i_s: &mut InferenceState<'db, '_>,
        name: &str,
        from: NodeRef,
    ) -> Inferred {
        self.run_on_value(i_s, &mut |i_s, value| {
            value.lookup_implicit(i_s, name, &|i_s| todo!("{value:?}"))
        })
        .run_on_value(i_s, &mut |i_s, value| {
            value.execute(
                i_s,
                &NoArguments::new(from),
                &mut ResultContext::Unknown,
                OnTypeError::new(&|_, _, _, _, _, _| todo!("currently only used for __next__")),
            )
        })
    }

    pub fn save_and_iter(
        self,
        i_s: &mut InferenceState<'db, '_>,
        from: NodeRef,
    ) -> IteratorContent<'db> {
        self.save_if_unsaved(i_s.db, from.file, from.node_index)
            .internal_run_after_save(
                i_s,
                &mut |i_s, v| v.iter(i_s, from),
                &|_, i1, i2| todo!(),
                &mut |i_s| IteratorContent::Any,
            )
    }
}

impl fmt::Debug for Inferred {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        let mut s = f.debug_struct("Inferred");
        match &self.state {
            InferredState::Saved(definition, point) => {
                s.field("definition", &definition).field("point", &point)
            }
            InferredState::UnsavedComplex(complex) => s.field("complex", &complex),
            InferredState::UnsavedSpecific(specific) => s.field("specific", &specific),
            InferredState::UnsavedFileReference(file_index) => todo!(),
            InferredState::Unknown => s.field("unknown", &true),
        }
        .finish()
    }
}

#[inline]
fn run_on_saved<'db: 'a, 'a, T>(
    i_s: &mut InferenceState<'db, '_>,
    definition: PointLink,
    point: Point,
    callable: &mut impl FnMut(&mut InferenceState<'db, '_>, &dyn Value<'db, 'a>) -> T,
    reducer: &impl Fn(&mut InferenceState<'db, '_>, T, T) -> T,
    on_missing: &mut impl FnMut(&mut InferenceState<'db, '_>) -> T,
) -> T {
    match point.type_() {
        PointType::Specific => run_on_specific(
            i_s,
            definition,
            point.specific(),
            callable,
            reducer,
            on_missing,
        ),
        PointType::Complex => {
            let definition = NodeRef::from_link(i_s.db, definition);
            let complex = definition.file.complex_points.get(point.complex_index());
            if let ComplexPoint::Class(cls_storage) = complex {
                let class = Class::new(definition, cls_storage, Generics::Any, None);
                callable(i_s, &class)
            } else {
                run_on_complex(
                    i_s,
                    complex,
                    Some(definition),
                    callable,
                    reducer,
                    on_missing,
                )
            }
        }
        PointType::Unknown => on_missing(i_s),
        PointType::FileReference => {
            let f = i_s.db.loaded_python_file(point.file_index());
            callable(i_s, &Module::new(i_s.db, f))
        }
        _ => unreachable!(),
    }
}

fn run_on_complex<'db: 'a, 'a, T>(
    i_s: &mut InferenceState<'db, '_>,
    complex: &'a ComplexPoint,
    definition: Option<NodeRef<'a>>,
    callable: &mut impl FnMut(&mut InferenceState<'db, '_>, &dyn Value<'db, 'a>) -> T,
    reducer: &impl Fn(&mut InferenceState<'db, '_>, T, T) -> T,
    on_missing: &mut impl FnMut(&mut InferenceState<'db, '_>) -> T,
) -> T {
    match complex {
        ComplexPoint::ExecutionInstance(cls_definition, execution) => {
            let def = NodeRef::from_link(i_s.db, *cls_definition);
            let init = Function::from_execution(i_s.db, execution, None);
            let complex = def.complex().unwrap();
            if let ComplexPoint::Class(cls_storage) = complex {
                /*
                let args = SimpleArguments::from_execution(i_s.db, execution);
                let class = Class::new(def, cls_storage, Generics::None, None);
                debug_assert!(class.type_vars(i_s).is_none());
                let instance = Instance::new(class, None);
                // TODO is this MroIndex fine? probably not!
                let instance_arg = KnownArguments::new(self, None);
                let args = CombinedArguments::new(&instance_arg, &args);
                callable(&mut i_s.with_func_and_args(&init, &args), &instance)
                */
                todo!()
            } else {
                unreachable!()
            }
        }
        ComplexPoint::Union(lst) => {
            let mut previous = None;
            for any_link in lst.iter() {
                let result = match any_link {
                    AnyLink::Reference(link) => {
                        let reference = NodeRef::from_link(i_s.db, *link);
                        run_on_saved(i_s, *link, reference.point(), callable, reducer, on_missing)
                    }
                    AnyLink::Complex(c) => {
                        run_on_complex(i_s, c, definition, callable, reducer, on_missing)
                    }
                    AnyLink::SimpleSpecific(specific) => match specific {
                        Specific::None => callable(i_s, &NoneInstance()),
                        Specific::TypingAny => on_missing(i_s),
                        _ => todo!("not even sure if this should be a separate class {specific:?}"),
                    },
                    AnyLink::Unknown => on_missing(i_s),
                };
                if let Some(p) = previous {
                    previous = Some(reducer(i_s, p, result))
                } else {
                    previous = Some(result)
                }
            }
            previous.unwrap()
        }
        ComplexPoint::BoundMethod(instance_link, mro_index, func_link) => {
            let reference = NodeRef::from_link(i_s.db, *func_link);

            // TODO this is potentially not needed, a class could lazily be fetched with a
            // closure
            let inf = Inferred::from_any_link(i_s.db, instance_link);
            let instance = inf.expect_instance(i_s);

            let class_t = instance.class.mro(i_s).nth(mro_index.0 as usize).unwrap().1;
            let class = class_t.maybe_class(i_s.db).unwrap();
            match reference.complex() {
                Some(ComplexPoint::FunctionOverload(overload)) => {
                    let func = OverloadedFunction::new(reference, overload, Some(class));
                    callable(
                        i_s,
                        &BoundMethod::new(
                            &instance,
                            *mro_index,
                            BoundMethodFunction::Overload(func),
                        ),
                    )
                }
                Some(ComplexPoint::TypeInstance(t)) => match t.as_ref() {
                    DbType::Callable(c) => callable(
                        i_s,
                        &BoundMethod::new(
                            &instance,
                            *mro_index,
                            BoundMethodFunction::Callable(Callable::new(t, c)),
                        ),
                    ),
                    _ => unreachable!("{t:?}"),
                },
                None => {
                    let func = Function::new(reference, Some(class));
                    callable(
                        i_s,
                        &BoundMethod::new(
                            &instance,
                            *mro_index,
                            BoundMethodFunction::Function(func),
                        ),
                    )
                }
                _ => unreachable!(),
            }
        }
        ComplexPoint::DecoratedFunction(c) => {
            callable(i_s, &Function::new(definition.unwrap(), None))
        }
        ComplexPoint::Closure(function, execution) => {
            let f = i_s.db.loaded_python_file(function.file);
            let func = Function::from_execution(i_s.db, execution, None);
            let args = SimpleArguments::from_execution(i_s.db, execution);
            callable(
                &mut i_s.with_func_and_args(&func, &args),
                &Function::new(NodeRef::from_link(i_s.db, *function), None),
            )
        }
        ComplexPoint::Instance(cls, generics_list) => {
            let generics = generics_list
                .as_ref()
                .map(Generics::new_list)
                .unwrap_or(Generics::None);
            let instance = use_instance(NodeRef::from_link(i_s.db, *cls), generics, None);
            callable(i_s, &instance)
        }
        ComplexPoint::FunctionOverload(overload) => callable(
            i_s,
            &OverloadedFunction::new(definition.unwrap(), overload, None),
        ),
        ComplexPoint::GenericClass(link, generics) => {
            let class = Class::from_position(
                NodeRef::from_link(i_s.db, *link),
                Generics::new_list(generics),
                None,
            )
            .unwrap();
            callable(i_s, &class)
        }
        ComplexPoint::TypeInstance(t) => run_on_db_type(i_s, t, callable, reducer, on_missing),
        ComplexPoint::TypeAlias(alias) => callable(i_s, &TypeAlias::new(alias)),
        ComplexPoint::TypeVarLike(t) => callable(
            i_s,
            &Instance::new(i_s.db.python_state.object_class(), None),
        ),
        _ => {
            unreachable!("Classes are handled earlier {complex:?}")
        }
    }
}

#[inline]
fn run_on_specific<'db: 'a, 'a, T>(
    i_s: &mut InferenceState<'db, '_>,
    definition: PointLink,
    specific: Specific,
    callable: &mut impl FnMut(&mut InferenceState<'db, '_>, &dyn Value<'db, 'a>) -> T,
    reducer: &impl Fn(&mut InferenceState<'db, '_>, T, T) -> T,
    on_missing: &mut impl FnMut(&mut InferenceState<'db, '_>) -> T,
) -> T {
    let definition = NodeRef::from_link(i_s.db, definition);
    match specific {
        Specific::Function => callable(i_s, &Function::new(definition, None)),
        Specific::AnnotationClassInstance => {
            let expr_def = definition.add_to_node_index(2);
            let inferred = expr_def
                .file
                .inference(i_s)
                .check_point_cache(expr_def.node_index)
                .unwrap();
            inferred.with_instance(i_s, definition, None, |i_s, instance| {
                callable(&mut i_s.with_annotation_instance(), instance)
            })
        }
        Specific::InstanceWithArguments => {
            let inf_cls = infer_instance_with_arguments_cls(i_s, definition);
            let class = inf_cls.maybe_class(i_s).unwrap();
            let args = SimpleArguments::from_primary(
                i_s.clone(),
                definition.file,
                definition.as_primary(),
                None,
            );
            let init = class.simple_init_func(i_s, &args);
            inf_cls.with_instance(i_s, definition, None, |i_s, instance| {
                // TODO is this MroIndex correct?
                /*
                let instance_arg = KnownArguments::new(self, None);
                let args = CombinedArguments::new(&instance_arg, &args);
                callable(&mut i_s.with_func_and_args(&init, &args), instance)
                */
                todo!()
            })
        }
        Specific::SimpleGeneric => {
            /*
            let class = self.maybe_class(i_s).unwrap();
            callable(i_s, &class)
            */
            todo!()
        }
        Specific::List => callable(i_s, &ListLiteral::new(definition)),
        Specific::Dict => callable(i_s, &DictLiteral::new(definition)),
        Specific::AnnotationWithTypeVars => {
            let db_type = definition
                .file
                .inference(i_s)
                .use_db_type_of_annotation(definition.node_index);
            run_on_db_type(i_s, db_type, callable, reducer, on_missing)
        }
        Specific::TypingTypeVarClass => callable(i_s, &TypeVarClass()),
        Specific::TypingTypeVarTupleClass => callable(i_s, &TypeVarTupleClass()),
        Specific::TypingParamSpecClass => callable(i_s, &ParamSpecClass()),
        Specific::TypingProtocol
        | Specific::TypingGeneric
        | Specific::TypingTuple
        | Specific::TypingUnion
        | Specific::TypingOptional
        | Specific::TypingType
        | Specific::TypingCallable => callable(i_s, &TypingClass::new(specific)),
        Specific::TypingAny | Specific::Cycle => on_missing(i_s),
        Specific::TypingCast => callable(i_s, &TypingCast()),
        Specific::TypingClassVar => callable(i_s, &TypingClassVar()),
        Specific::RevealTypeFunction => callable(i_s, &RevealTypeFunction()),
        Specific::None => callable(i_s, &NoneInstance()),
        Specific::TypingNewType => callable(i_s, &NewTypeClass()),
        Specific::MypyExtensionsArg
        | Specific::MypyExtensionsDefaultArg
        | Specific::MypyExtensionsNamedArg
        | Specific::MypyExtensionsDefaultNamedArg
        | Specific::MypyExtensionsVarArg
        | Specific::MypyExtensionsKwArg => {
            let func = i_s.db.python_state.mypy_extensions_arg_func(specific);
            callable(i_s, &func)
        }
        _ => {
            let instance = resolve_specific(i_s.db, specific);
            callable(i_s, &instance)
        }
    }
}

fn resolve_specific(db: &Database, specific: Specific) -> Instance {
    load_builtin_instance_from_str(
        db,
        match specific {
            Specific::String => "str",
            Specific::Integer => "int",
            Specific::Float => "float",
            Specific::Boolean => "bool",
            Specific::Bytes => "bytes",
            Specific::Complex => "complex",
            Specific::Ellipsis => "ellipsis", // TODO this should not even be public
            actual => todo!("{actual:?}"),
        },
    )
}

fn load_builtin_instance_from_str<'db>(db: &'db Database, name: &'static str) -> Instance<'db> {
    let builtins = db.python_state.builtins();
    let node_index = builtins.lookup_global(name).unwrap().node_index - 1;
    let v = builtins.points.get(node_index);
    debug_assert_eq!(v.type_(), PointType::Redirect);
    debug_assert_eq!(v.file_index(), builtins.file_index());
    use_instance(NodeRef::new(builtins, v.node_index()), Generics::None, None)
}

fn infer_instance_with_arguments_cls(i_s: &mut InferenceState, definition: NodeRef) -> Inferred {
    definition
        .file
        .inference(i_s)
        .infer_primary_or_atom(definition.as_primary().first())
}

fn use_instance<'a>(
    class_reference: NodeRef<'a>,
    generics: Generics<'a>,
    instance_reference: Option<NodeRef<'a>>,
) -> Instance<'a> {
    let class = Class::from_position(class_reference, generics, None).unwrap();
    Instance::new(class, instance_reference)
}

pub fn run_on_db_type<'db: 'a, 'a, T>(
    i_s: &mut InferenceState<'db, '_>,
    db_type: &'a DbType,
    callable: &mut impl FnMut(&mut InferenceState<'db, '_>, &dyn Value<'db, 'a>) -> T,
    reducer: &impl Fn(&mut InferenceState<'db, '_>, T, T) -> T,
    on_missing: &mut impl FnMut(&mut InferenceState<'db, '_>) -> T,
) -> T {
    match db_type {
        DbType::Class(link, generics) => {
            let g = Generics::new_maybe_list(generics);
            let inst = use_instance(NodeRef::from_link(i_s.db, *link), g, None);
            callable(i_s, &inst)
        }
        DbType::Union(lst) => lst
            .iter()
            .fold(None, |input, t| match input {
                None => Some(run_on_db_type(i_s, t, callable, reducer, on_missing)),
                Some(t1) => {
                    let t2 = run_on_db_type(i_s, t, callable, reducer, on_missing);
                    Some(reducer(i_s, t1, t2))
                }
            })
            .unwrap(),
        DbType::Intersection(lst) => todo!(),
        DbType::TypeVar(t) => callable(i_s, &TypeVarInstance::new(i_s.db, db_type, t)),
        DbType::Tuple(content) => callable(i_s, &Tuple::new(db_type, content)),
        DbType::Callable(content) => callable(i_s, &Callable::new(db_type, content)),
        DbType::None => callable(i_s, &NoneInstance()),
        DbType::Any => on_missing(i_s),
        DbType::Never => on_missing(i_s),
        DbType::Type(t) => run_on_db_type_type(i_s, db_type, t, callable, reducer, on_missing),
        DbType::NewType(n) => {
            let t = n.type_(i_s);
            run_on_db_type(i_s, t, callable, reducer, on_missing)
        }
        DbType::RecursiveAlias(rec1) => run_on_db_type(
            i_s,
            rec1.calculated_db_type(i_s.db),
            callable,
            reducer,
            on_missing,
        ),
        DbType::ParamSpecArgs(usage) => todo!(),
        DbType::ParamSpecKwargs(usage) => todo!(),
    }
}

fn run_on_db_type_type<'db: 'a, 'a, T>(
    i_s: &mut InferenceState<'db, '_>,
    db_type: &'a DbType,
    type_: &'a DbType,
    callable: &mut impl FnMut(&mut InferenceState<'db, '_>, &dyn Value<'db, 'a>) -> T,
    reducer: &impl Fn(&mut InferenceState<'db, '_>, T, T) -> T,
    on_missing: &mut impl FnMut(&mut InferenceState<'db, '_>) -> T,
) -> T {
    match type_ {
        DbType::Class(link, generics) => {
            let class = Class::from_position(
                NodeRef::from_link(i_s.db, *link),
                Generics::new_maybe_list(generics),
                None,
            )
            .unwrap();
            callable(i_s, &class)
        }
        DbType::Union(lst) => lst
            .iter()
            .fold(None, |input, t| match input {
                None => Some(run_on_db_type_type(
                    i_s, db_type, t, callable, reducer, on_missing,
                )),
                Some(t1) => {
                    let t2 = run_on_db_type_type(i_s, db_type, t, callable, reducer, on_missing);
                    Some(reducer(i_s, t1, t2))
                }
            })
            .unwrap(),
        DbType::Never => todo!(),
        _ => callable(i_s, &TypingType::new(i_s.db, Cow::Borrowed(db_type), type_)),
    }
}

#[cfg(test)]
mod tests {
    #[test]
    fn test_sizes() {
        use super::*;
        use std::mem::size_of;
        assert_eq!(size_of::<Inferred>(), 40);
    }
}
