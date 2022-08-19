use std::fmt;
use std::rc::Rc;

use parsa_python_ast::{Argument, ArgumentsIterator, ClassDef};

use super::{Function, LookupResult, Module, OnTypeError, Value, ValueKind};
use crate::arguments::Arguments;
use crate::database::{
    ClassInfos, ClassStorage, ComplexPoint, Database, DbType, FormatStyle, GenericsList, Locality,
    MroIndex, ParentScope, Point, PointLink, PointType, TypeVar, TypeVarUsage, TypeVars,
};
use crate::diagnostics::IssueType;
use crate::file::{BaseClass, ClassTypeVarFinder, PythonFile, TypeComputation};
use crate::file_state::File;
use crate::getitem::SliceType;
use crate::inference_state::InferenceState;
use crate::inferred::{FunctionOrOverload, Inferred};
use crate::matching::{
    calculate_class_init_type_vars_and_return, ClassLike, Generics, Match, ResultContext,
    TypeVarMatcher,
};
use crate::node_ref::NodeRef;
use crate::{base_qualified_name, debug};

#[derive(Clone, Copy)]
pub struct Class<'db, 'a> {
    pub node_ref: NodeRef<'db>,
    pub class_storage: &'db ClassStorage,
    pub generics: Generics<'db, 'a>,
    pub type_var_remap: Option<&'db GenericsList>,
}

impl<'db, 'a> Class<'db, 'a> {
    pub fn new(
        node_ref: NodeRef<'db>,
        class_storage: &'db ClassStorage,
        generics: Generics<'db, 'a>,
        type_var_remap: Option<&'db GenericsList>,
    ) -> Self {
        Self {
            node_ref,
            class_storage,
            generics,
            type_var_remap,
        }
    }

    #[inline]
    pub fn from_position(
        node_ref: NodeRef<'db>,
        generics: Generics<'db, 'a>,
        type_var_remap: Option<&'db GenericsList>,
    ) -> Option<Self> {
        let complex = node_ref.complex().unwrap();
        match complex {
            ComplexPoint::Class(c) => Some(Self::new(node_ref, c, generics, type_var_remap)),
            _ => unreachable!("Probably an issue with indexing: {complex:?}"),
        }
    }

    pub fn has_non_overloaded_init_func(&self, i_s: &mut InferenceState<'db, '_>) -> bool {
        let (init, class) = self.lookup_and_class(i_s, "__init__");
        let cls = class.unwrap_or_else(|| todo!());
        match init.into_maybe_inferred().unwrap().init_as_function(cls) {
            Some(FunctionOrOverload::Function(_)) => true,
            Some(FunctionOrOverload::Overload(_)) => false,
            None => unreachable!(), // There is always an init func
        }
    }

    pub fn type_check_init_func(
        &self,
        i_s: &mut InferenceState<'db, '_>,
        args: &dyn Arguments<'db>,
        result_context: ResultContext<'db, '_>,
        on_type_error: OnTypeError<'db, '_>,
    ) -> Option<(Function<'db, '_>, Option<GenericsList>, bool)> {
        let (init, class) = self.lookup_and_class(i_s, "__init__");
        let cls = class.unwrap_or_else(|| todo!());
        match init.into_maybe_inferred().unwrap().init_as_function(cls) {
            Some(FunctionOrOverload::Function(func)) => {
                let calculated_type_args = calculate_class_init_type_vars_and_return(
                    i_s,
                    self,
                    func,
                    args,
                    result_context,
                    Some(on_type_error),
                );
                Some((func, calculated_type_args.type_arguments, false))
            }
            Some(FunctionOrOverload::Overload(overloaded_function)) => overloaded_function
                .find_matching_function(i_s, args, class.as_ref(), true, result_context)
                .map(|(func, list)| (func, list, true)),
            None => unreachable!("Should never happen, because there's always object.__init__"),
        }
    }

    pub fn simple_init_func(
        &self,
        i_s: &mut InferenceState<'db, '_>,
        args: &dyn Arguments<'db>,
    ) -> Function<'db, '_> {
        let (init, class) = self.lookup_and_class(i_s, "__init__");
        let class = class.unwrap_or_else(|| todo!());
        match init.into_maybe_inferred().unwrap().init_as_function(class) {
            Some(FunctionOrOverload::Function(func)) => func,
            _ => unreachable!(),
        }
    }

    pub fn node(&self) -> ClassDef<'db> {
        ClassDef::by_index(&self.node_ref.file.tree, self.node_ref.node_index)
    }

    pub fn type_vars(&self, i_s: &mut InferenceState<'db, '_>) -> Option<&'db TypeVars> {
        let node_ref = self.type_vars_node_ref();
        let point = node_ref.point();
        if point.calculated() {
            return (point.type_() != PointType::NodeAnalysis).then(|| {
                match node_ref.complex().unwrap() {
                    ComplexPoint::TypeVars(type_vars) => type_vars,
                    _ => unreachable!(),
                }
            });
        }

        let type_vars = ClassTypeVarFinder::find(&mut self.node_ref.file.inference(i_s), self);
        if type_vars.is_empty() {
            self.type_vars_node_ref()
                .set_point(Point::new_node_analysis(Locality::Todo));
        } else {
            self.type_vars_node_ref()
                .insert_complex(ComplexPoint::TypeVars(type_vars), Locality::Todo);
        }
        self.type_vars(i_s)
    }

    pub fn maybe_type_var_in_parent(
        &self,
        i_s: &mut InferenceState<'db, '_>,
        type_var: &Rc<TypeVar>,
    ) -> Option<TypeVarUsage> {
        match self.class_storage.parent_scope {
            ParentScope::Module => None,
            ParentScope::Class(node_index) => {
                let parent_class = Self::from_position(
                    NodeRef::new(self.node_ref.file, node_index),
                    Generics::None,
                    None,
                )
                .unwrap();
                parent_class
                    .maybe_type_var_in_parent(i_s, type_var)
                    .or_else(|| {
                        parent_class
                            .type_vars(i_s)
                            .and_then(|t| t.find(type_var.clone(), parent_class.node_ref.as_link()))
                    })
            }
            ParentScope::Function(node_index) => todo!(),
        }
    }

    fn is_calculating_class_infos(&self) -> bool {
        self.class_info_node_ref().point().calculating()
    }

    fn type_vars_node_ref(&self) -> NodeRef<'db> {
        self.node_ref.add_to_node_index(1)
    }

    fn class_info_node_ref(&self) -> NodeRef<'db> {
        self.node_ref.add_to_node_index(4)
    }

    pub fn class_infos(&self, i_s: &mut InferenceState<'db, '_>) -> &'db ClassInfos {
        let node_ref = self.class_info_node_ref();
        let point = node_ref.point();
        if point.calculated() {
            match node_ref.complex().unwrap() {
                ComplexPoint::ClassInfos(class_infos) => class_infos,
                _ => unreachable!(),
            }
        } else {
            node_ref.set_point(Point::new_calculating());
            node_ref.insert_complex(
                ComplexPoint::ClassInfos(self.calculate_class_infos(i_s)),
                Locality::Todo,
            );
            debug_assert!(node_ref.point().calculated());
            self.class_infos(i_s)
        }
    }

    fn calculate_class_infos(&self, i_s: &mut InferenceState<'db, '_>) -> Box<ClassInfos> {
        debug!("Calculate class infos for {}", self.name());
        // Calculate all type vars beforehand
        let type_vars = self.type_vars(i_s);

        let mut mro = vec![];
        let mut incomplete_mro = false;
        let mut is_protocol = false;
        if let Some(arguments) = self.node().arguments() {
            let mut i_s = i_s.with_annotation_instance();
            // Calculate the type var remapping
            for argument in arguments.iter() {
                match argument {
                    Argument::Positional(n) => {
                        let db = i_s.db;
                        let mut inference = self.node_ref.file.inference(&mut i_s);
                        let base = TypeComputation::new(
                            &mut inference,
                            self.node_ref.as_link(),
                            Some(&mut |i_s, type_var, _, _| {
                                if let Some(type_vars) = type_vars {
                                    if let Some(index) =
                                        type_vars.iter().position(|t| *t == type_var)
                                    {
                                        return Some(DbType::TypeVar(TypeVarUsage {
                                            type_var,
                                            index: index.into(),
                                            in_definition: self.node_ref.as_link(),
                                        }));
                                    }
                                }
                                if let Some(usage) = self.maybe_type_var_in_parent(i_s, &type_var) {
                                    return Some(DbType::TypeVar(usage));
                                }
                                todo!("Maybe class in func");
                            }),
                        )
                        .compute_base_class(n.expression());
                        match base {
                            BaseClass::DbType(t) => {
                                let mro_index = mro.len();
                                mro.push(t);
                                let class = match &mro.last().unwrap() {
                                    DbType::Class(link, generics) => Some(
                                        Class::from_position(
                                            NodeRef::from_link(i_s.db, *link),
                                            generics
                                                .as_ref()
                                                .map(Generics::new_list)
                                                .unwrap_or(Generics::None),
                                            None,
                                        )
                                        .unwrap(),
                                    ),
                                    DbType::Tuple(content) => None,
                                    DbType::Type(_) => todo!(),
                                    DbType::Callable(content) => todo!(),
                                    _ => unreachable!(),
                                };
                                if let Some(class) = class {
                                    if class.is_calculating_class_infos() {
                                        let name = Box::<str>::from(class.name());
                                        mro.pop();
                                        incomplete_mro = true;
                                        NodeRef::new(self.node_ref.file, n.index())
                                            .add_typing_issue(
                                                db,
                                                IssueType::CyclicDefinition { name },
                                            );
                                    } else {
                                        for base in class.class_infos(&mut i_s).mro.iter() {
                                            mro.push(base.replace_type_vars(&mut |t| {
                                                mro[mro_index].expect_class_generics()[t.index]
                                                    .clone()
                                            }));
                                        }
                                    }
                                }
                            }
                            BaseClass::Protocol => is_protocol = true,
                            BaseClass::Generic => {}
                            BaseClass::Invalid => {
                                incomplete_mro = true;
                            }
                        };
                    }
                    Argument::Keyword(_, _) => (), // Ignore for now -> part of meta class
                    Argument::Starred(_) | Argument::DoubleStarred(_) => (), // Nobody probably cares about this
                }
            }
        }
        Box::new(ClassInfos {
            mro: mro.into_boxed_slice(),
            incomplete_mro,
            is_protocol,
        })
    }

    pub fn check_protocol_match(&self, i_s: &mut InferenceState<'db, '_>, other: Self) -> bool {
        for c in self.class_infos(i_s).mro.iter() {
            let symbol_table = &self.class_storage.class_symbol_table;
            for (class_name, _) in unsafe { symbol_table.iter_on_finished_table() } {
                if let Some(l) = other.lookup_internal(i_s, class_name).into_maybe_inferred() {
                    // TODO check signature details here!
                } else {
                    return false;
                }
            }
        }
        true
    }

    pub fn lookup_symbol(
        &self,
        i_s: &mut InferenceState<'db, '_>,
        name: &str,
    ) -> LookupResult<'db> {
        match self.class_storage.class_symbol_table.lookup_symbol(name) {
            None => LookupResult::None,
            Some(node_index) => {
                let inf = self
                    .node_ref
                    .file
                    .inference(&mut i_s.with_class_context(self))
                    .infer_name_by_index(node_index);
                LookupResult::GotoName(
                    PointLink::new(self.node_ref.file.file_index(), node_index),
                    inf,
                )
            }
        }
    }

    fn lookup_and_class(
        &self,
        i_s: &mut InferenceState<'db, '_>,
        name: &str,
    ) -> (LookupResult<'db>, Option<Class<'db, '_>>) {
        for (mro_index, c) in self.mro(i_s) {
            let result = c.lookup_symbol(i_s, name);
            if !matches!(result, LookupResult::None) {
                if let ClassLike::Class(c) = c {
                    return (result, Some(c));
                } else {
                    todo!()
                    //return (result, None);
                }
            }
        }
        (LookupResult::None, None)
    }

    pub fn generics(&self) -> Generics<'db, '_> {
        if let Some(type_var_remap) = self.type_var_remap {
            Generics::List(type_var_remap, Some(&self.generics))
        } else {
            self.generics
        }
    }

    pub fn mro(&self, i_s: &mut InferenceState<'db, '_>) -> MroIterator<'db, '_> {
        let class_infos = self.class_infos(i_s);
        MroIterator::new(
            i_s.db,
            ClassLike::Class(*self),
            Some(self.generics),
            class_infos.mro.iter(),
        )
    }

    pub fn in_mro(&self, i_s: &mut InferenceState<'db, '_>, t: &DbType) -> bool {
        if let DbType::Class(link, _) = t {
            if self.node_ref.as_link() == *link {
                return true;
            }
        }
        let class_infos = self.class_infos(i_s);
        class_infos.mro.contains(t)
    }

    pub fn is_object_class(&self, db: &Database) -> Match {
        (self.node_ref == db.python_state.object()).into()
    }

    pub fn format(
        &self,
        i_s: &mut InferenceState<'db, '_>,
        matcher: Option<&TypeVarMatcher<'db, '_>>,
        style: FormatStyle,
    ) -> Box<str> {
        let mut result = match style {
            FormatStyle::Short | FormatStyle::MypyOverload => self.name().to_owned(),
            FormatStyle::Qualified | FormatStyle::MypyRevealType => self.qualified_name(i_s.db),
        };
        let type_vars = self.type_vars(i_s);
        if let Some(type_vars) = type_vars {
            result += &self
                .generics()
                .format(i_s, matcher, style, Some(type_vars.len()));
        }
        result.into()
    }

    pub fn generics_as_list(&self, i_s: &mut InferenceState<'db, '_>) -> Option<GenericsList> {
        let type_vars = self.type_vars(i_s);
        self.generics().as_generics_list(i_s, type_vars)
    }

    pub fn as_db_type(&self, i_s: &mut InferenceState<'db, '_>) -> DbType {
        let lst = self.generics_as_list(i_s);
        let link = self.node_ref.as_link();
        DbType::Class(link, lst)
    }
}

impl<'db, 'a> Value<'db, 'a> for Class<'db, 'a> {
    fn kind(&self) -> ValueKind {
        ValueKind::Class
    }

    fn name(&self) -> &'db str {
        self.node().name().as_str()
    }

    fn qualified_name(&self, db: &'db Database) -> String {
        match self.class_storage.parent_scope {
            ParentScope::Module => base_qualified_name!(self, db, self.name()),
            ParentScope::Class(node_index) => {
                let parent_class = Self::from_position(
                    NodeRef::new(self.node_ref.file, node_index),
                    Generics::None,
                    None,
                )
                .unwrap();
                format!("{}.{}", parent_class.qualified_name(db), self.name())
            }
            ParentScope::Function(node_index) => {
                let node_ref = NodeRef::new(self.node_ref.file, node_index);
                let line = self
                    .node_ref
                    .file
                    .byte_to_line_column(self.node().start())
                    .0;
                // Add the position like `foo.Bar@7`
                base_qualified_name!(self, db, format!("{}@{line}", self.name()))
            }
        }
    }

    fn module(&self, db: &'db Database) -> Module<'db> {
        Module::new(db, self.node_ref.file)
    }

    fn lookup_internal(&self, i_s: &mut InferenceState<'db, '_>, name: &str) -> LookupResult<'db> {
        self.lookup_and_class(i_s, name).0
    }

    fn should_add_lookup_error(&self, i_s: &mut InferenceState<'db, '_>) -> bool {
        !self.class_infos(i_s).incomplete_mro
    }

    fn execute(
        &self,
        i_s: &mut InferenceState<'db, '_>,
        args: &dyn Arguments<'db>,
        result_context: ResultContext<'db, '_>,
        on_type_error: OnTypeError<'db, '_>,
    ) -> Inferred<'db> {
        // TODO locality!!!
        if let Some((func, generics_list, is_overload)) =
            self.type_check_init_func(i_s, args, result_context, on_type_error)
        {
            debug!(
                "Class execute: {}{}",
                self.name(),
                match generics_list.as_ref() {
                    Some(generics_list) => Generics::new_list(generics_list).format(
                        i_s,
                        None,
                        FormatStyle::Short,
                        None
                    ),
                    None => "".to_owned(),
                }
            );
            Inferred::new_unsaved_complex(if generics_list == None && !is_overload {
                match args.as_execution(&func) {
                    Some(execution) => {
                        todo!();
                        //ComplexPoint::ExecutionInstance(self.node_ref.as_link(), Box::new(execution))
                    }
                    None => ComplexPoint::Instance(self.node_ref.as_link(), None),
                }
            } else {
                ComplexPoint::Instance(self.node_ref.as_link(), generics_list)
            })
        } else {
            Inferred::new_any()
        }
    }

    fn get_item(
        &self,
        i_s: &mut InferenceState<'db, '_>,
        slice_type: &SliceType<'db, '_>,
    ) -> Inferred<'db> {
        slice_type
            .file
            .inference(i_s)
            .compute_type_application_on_class(*self, *slice_type)
    }

    fn description(&self, i_s: &mut InferenceState<'db, '_>) -> String {
        format!(
            "{} {}",
            format!("{:?}", self.kind()).to_lowercase(),
            self.format(i_s, None, FormatStyle::Short),
        )
    }

    fn class(&self, i_s: &mut InferenceState<'db, '_>) -> ClassLike<'db, 'a> {
        ClassLike::Type(*self)
    }
}

impl fmt::Debug for Class<'_, '_> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        f.debug_struct("Class")
            .field("file_index", &self.node_ref.file.file_index())
            .field("node_index", &self.node_ref.node_index)
            .field("name", &self.name())
            .field("generics", &self.generics)
            .field("type_var_remap", &self.type_var_remap)
            .finish()
    }
}

struct BasesIterator<'db> {
    file: &'db PythonFile,
    args: Option<ArgumentsIterator<'db>>,
}

impl<'db> BasesIterator<'db> {
    fn next(&mut self, i_s: &mut InferenceState<'db, '_>) -> Option<Inferred<'db>> {
        if let Some(args) = self.args.as_mut() {
            match args.next() {
                Some(Argument::Positional(p)) => {
                    return Some(self.file.inference(i_s).infer_named_expression(p))
                }
                None => (),
                other => todo!("{other:?}"),
            }
        }
        None
    }
}

pub struct MroIterator<'db, 'a> {
    db: &'db Database,
    generics: Option<Generics<'db, 'a>>,
    class: Option<ClassLike<'db, 'a>>,
    iterator: std::slice::Iter<'db, DbType>,
    mro_index: u32,
    returned_object: bool,
}

impl<'db, 'a> MroIterator<'db, 'a> {
    pub fn new(
        db: &'db Database,
        class: ClassLike<'db, 'a>,
        generics: Option<Generics<'db, 'a>>,
        iterator: std::slice::Iter<'db, DbType>,
    ) -> Self {
        Self {
            db,
            generics,
            class: Some(class),
            iterator,
            mro_index: 0,
            returned_object: false,
        }
    }
}

impl<'db, 'a> Iterator for MroIterator<'db, 'a> {
    type Item = (MroIndex, ClassLike<'db, 'a>);

    fn next(&mut self) -> Option<Self::Item> {
        if self.class.is_some() {
            self.mro_index += 1;
            Some((MroIndex(0), std::mem::take(&mut self.class).unwrap()))
        } else if let Some(c) = self.iterator.next() {
            let r = Some((
                MroIndex(self.mro_index),
                match c {
                    DbType::Class(c, generics) => ClassLike::Class(
                        Class::from_position(
                            NodeRef::from_link(self.db, *c),
                            self.generics.unwrap(),
                            generics.as_ref(),
                        )
                        .unwrap(),
                    ),
                    _ => todo!("{c:?}"),
                },
            ));
            self.mro_index += 1;
            r
        } else if !self.returned_object {
            self.returned_object = true;
            Class::from_position(self.db.python_state.object(), Generics::None, None)
                .map(|c| (MroIndex(self.mro_index), ClassLike::Class(c)))
        } else {
            None
        }
    }
}
