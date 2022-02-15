use parsa_python_ast::{Name, NodeIndex};
use std::cell::Cell;
use std::collections::HashMap;
use std::fmt;
use std::iter::repeat;
use std::mem;
use std::path::Path;
use std::pin::Pin;

use crate::file::PythonFile;
use crate::file_state::{
    File, FileState, FileStateLoader, FileSystemReader, LanguageFileState, PythonFileLoader, Vfs,
};
use crate::node_ref::NodeRef;
use crate::python_state::PythonState;
use crate::utils::{InsertOnlyVec, Invalidations, SymbolTable};
use crate::workspaces::{WorkspaceFileIndex, Workspaces};

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct FileIndex(pub u32);
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct TypeVarIndex(u32);
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct MroIndex(pub u32);

impl TypeVarIndex {
    pub fn new(i: usize) -> Self {
        Self(i as u32)
    }

    pub fn as_usize(&self) -> usize {
        self.0 as usize
    }
}

impl fmt::Display for FileIndex {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{}", self.0)
    }
}

type FileStateLoaders = Box<[Box<dyn FileStateLoader>]>;

// Most significant bits
// 27 bits = 134217728; 20 bits = 1048576
// oxxxx is_analyzed
// xoxxx is_invalidated
// xxooo Locality (xXxx is_external)
// xxxxxo in_module_scope  TODO remove
// xxxxxxo is_nullable  TODO remove
// xxxxxxxooo PointType
// if true rest 22 bits reserved for Point details

const IS_ANALIZED_BIT_INDEX: usize = 31;
const IS_INVALIDATED_BIT_INDEX: usize = 30;
const LOCALITY_BIT_INDEX: usize = 27; // Uses 3 bits
const IN_MODULE_SCOPE_BIT_INDEX: usize = 26;
const IS_NULLABLE_BIT_INDEX: usize = 25;
const TYPE_BIT_INDEX: usize = 22; // Uses 3 bits
const TYPE_VAR_BIT_INDEX: usize = 8;

const REST_MASK: u32 = 0b11_1111_1111_1111_1111_1111;
const SPECIFIC_MASK: u32 = 0xFF; // 8 bits
const MAX_TYPE_VAR: u32 = 0xFF; // 256
const TYPE_VAR_MASK: u32 = MAX_TYPE_VAR << TYPE_VAR_BIT_INDEX; // 8 bits
const FILE_MASK: u32 = 0xFFFFFF; // 24 bits
const IS_ANALIZED_MASK: u32 = 1 << IS_ANALIZED_BIT_INDEX;
const IN_MODULE_SCOPE_MASK: u32 = 1 << IN_MODULE_SCOPE_BIT_INDEX;
const IS_NULLABLE_MASK: u32 = 1 << IN_MODULE_SCOPE_BIT_INDEX;
const LOCALITY_MASK: u32 = 0b111 << LOCALITY_BIT_INDEX;
const TYPE_MASK: u32 = 0b111 << TYPE_BIT_INDEX;

const IS_EXTERN_MASK: u32 = 1 << 30;

#[derive(Copy, Clone, Eq, PartialEq, Default)]
pub struct Point {
    flags: u32,
    node_index: u32,
}

impl Point {
    #[inline]
    fn calculate_flags(type_: PointType, rest: u32, locality: Locality) -> u32 {
        debug_assert!(rest & !REST_MASK == 0);
        rest | IS_ANALIZED_MASK
            | (locality as u32) << LOCALITY_BIT_INDEX
            | (type_ as u32) << TYPE_BIT_INDEX
    }

    pub fn new_redirect(file: FileIndex, node_index: NodeIndex, locality: Locality) -> Self {
        let flags = Self::calculate_flags(PointType::Redirect, file.0, locality);
        Self { flags, node_index }
    }

    pub fn new_multi_definition(node_index: NodeIndex, locality: Locality) -> Self {
        let flags = Self::calculate_flags(PointType::MultiDefinition, 0, locality);
        Self { flags, node_index }
    }

    pub fn new_complex_point(complex_index: u32, locality: Locality) -> Self {
        let flags = Self::calculate_flags(PointType::Complex, complex_index, locality);
        Self {
            flags,
            node_index: 0,
        }
    }

    pub fn new_unknown(file: FileIndex, locality: Locality) -> Self {
        let flags = Self::calculate_flags(PointType::Unknown, file.0, locality);
        Self {
            flags,
            node_index: 0,
        }
    }

    pub fn new_simple_specific(type_: Specific, locality: Locality) -> Self {
        let flags = Self::calculate_flags(PointType::Specific, type_ as u32, locality);
        Self {
            flags,
            node_index: 0,
        }
    }

    pub fn new_specific(type_: Specific, node_index: NodeIndex, locality: Locality) -> Self {
        todo!()
    }

    pub fn new_file_reference(file: FileIndex, locality: Locality) -> Self {
        let flags = Self::calculate_flags(PointType::FileReference, file.0 as u32, locality);
        Self {
            flags,
            node_index: 0,
        }
    }

    pub fn new_node_analysis(locality: Locality) -> Self {
        Self {
            flags: Self::calculate_flags(PointType::NodeAnalysis, 0, locality),
            node_index: 0,
        }
    }

    pub fn new_node_analysis_with_node_index(locality: Locality, node_index: NodeIndex) -> Self {
        Self {
            flags: Self::calculate_flags(PointType::NodeAnalysis, node_index, locality),
            node_index,
        }
    }

    pub fn new_uncalculated() -> Self {
        Self {
            flags: 0,
            node_index: 0,
        }
    }

    pub fn new_numbered_type_var(
        specific: Specific,
        index: TypeVarIndex,
        locality: Locality,
    ) -> Self {
        assert!(index.0 <= MAX_TYPE_VAR);
        debug_assert!(matches!(
            specific,
            Specific::ClassTypeVar | Specific::FunctionTypeVar | Specific::LateBoundTypeVar
        ));
        let flags = Self::calculate_flags(
            PointType::Specific,
            specific as u32 | index.0 << TYPE_VAR_BIT_INDEX,
            locality,
        );
        Self {
            flags,
            node_index: 0,
        }
    }

    pub fn type_(self) -> PointType {
        unsafe { mem::transmute((self.flags & TYPE_MASK) >> TYPE_BIT_INDEX) }
    }

    pub fn locality(self) -> Locality {
        unsafe { mem::transmute((self.flags & LOCALITY_MASK) >> LOCALITY_BIT_INDEX) }
    }

    pub fn calculated(self) -> bool {
        (self.flags & IS_ANALIZED_MASK) != 0
    }

    pub fn calculating(self) -> bool {
        self.flags == 1
    }

    fn is_recursion_error(self) -> bool {
        unimplemented!();
        //self.flags & REST_MASK & 1 == 1
    }

    pub fn file_index(self) -> FileIndex {
        debug_assert!(
            self.type_() == PointType::Redirect || self.type_() == PointType::FileReference
        );
        FileIndex(self.flags & REST_MASK)
    }

    pub fn complex_index(self) -> usize {
        debug_assert!(
            self.type_() == PointType::Complex,
            "Expected complex, got {:?}",
            self
        );
        (self.flags & REST_MASK) as usize
    }

    pub fn maybe_complex_index(self) -> Option<usize> {
        if self.type_() == PointType::Complex {
            return Some(self.complex_index());
        }
        None
    }

    pub fn node_index(self) -> NodeIndex {
        debug_assert!(
            self.type_() == PointType::Redirect
                || self.type_() == PointType::NodeAnalysis
                || self.type_() == PointType::MultiDefinition
        );
        self.node_index
    }

    pub fn maybe_specific(self) -> Option<Specific> {
        if self.type_() == PointType::Specific {
            Some(self.specific())
        } else {
            None
        }
    }

    pub fn specific(self) -> Specific {
        debug_assert!(self.type_() == PointType::Specific);
        unsafe { mem::transmute(self.flags & SPECIFIC_MASK) }
    }

    pub fn type_var_index(self) -> TypeVarIndex {
        debug_assert!(self.type_() == PointType::Specific);
        TypeVarIndex(unsafe { mem::transmute((self.flags & TYPE_VAR_MASK) >> TYPE_VAR_BIT_INDEX) })
    }
}

impl fmt::Debug for Point {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        let mut s = f.debug_struct("Point");
        if self.calculating() {
            s.field("calculating", &self.calculating());
        } else if !self.calculated() {
            s.field("calculated", &self.calculated());
        } else {
            s.field("type", &self.type_())
                .field("locality", &self.locality())
                .field("node_index", &self.node_index);
            if self.type_() == PointType::Specific {
                s.field("specific", &self.specific());
                if matches!(
                    self.specific(),
                    Specific::ClassTypeVar | Specific::FunctionTypeVar | Specific::LateBoundTypeVar
                ) {
                    s.field("type_var_index", &self.type_var_index());
                }
            }
            if self.type_() == PointType::Redirect || self.type_() == PointType::FileReference {
                s.field("file_index", &self.file_index().0);
            }
        }
        s.finish()
    }
}

#[derive(Debug)]
pub struct Points(Vec<Cell<Point>>);

impl Points {
    pub fn new(length: usize) -> Self {
        Self(vec![Default::default(); length])
    }

    #[inline]
    pub fn get(&self, index: NodeIndex) -> Point {
        self.0[index as usize].get()
    }

    #[inline]
    pub fn set(&self, index: NodeIndex, point: Point) {
        self.0[index as usize].set(point);
    }

    pub fn set_on_name(&self, name: &Name, point: Point) {
        debug_assert!(point.type_() != PointType::MultiDefinition);
        let mut index = name.index();
        let current = self.get(index);
        if current.calculated() && current.type_() == PointType::MultiDefinition {
            index -= 1 // Set it on NameDefinition
        }
        self.set(index, point);
    }

    pub fn invalidate_references_to(&mut self, file_index: FileIndex) {
        for cell in &self.0 {
            let locality = cell.get().locality();
            if locality == Locality::DirectExtern && cell.get().file_index() == file_index {
                cell.set(Point::new_uncalculated());
            } else if locality as u32 >= Locality::ComplexExtern as u32 {
                cell.set(Point::new_uncalculated())
            }
        }
    }
}

#[derive(Debug, PartialEq, Eq)]
#[repr(u32)]
pub enum PointType {
    Redirect,
    MultiDefinition,
    Complex,
    // In case of a reference it's missing otherwise unknown.
    Unknown,
    Specific,
    FileReference,
    // Basically stuff like if/for nodes
    NodeAnalysis,
}

#[derive(Debug, PartialEq, Eq, Clone, Copy)]
#[repr(u32)]
pub enum Specific {
    String,
    Bytes,
    Float,
    Integer,
    Complex,
    Boolean,
    None,

    Ellipsis,
    GeneratorComprehension,
    List,
    ListComprehension,
    Dict,

    // SelfParam, TODO Use maybe?
    Param,
    LazyInferredClass,        // A class that will be inferred later.
    LazyInferredDynamicClass, // A class defined in a function that will be inferred later.
    LazyInferredFunction,     // A function that will be inferred later.
    LazyInferredClosure,      // A closure that will be inferred later.
    Function,                 // The node point so the index of the result
    Closure,
    NoReturnFunction,
    BoundMethod,

    InstanceWithArguments, // A primary node
    AnnotationInstance,
    SimpleGeneric,      // primary: primary '[' slices ']'
    TypingWithGenerics, // Same as SimpleGeneric, but with a Typing*Class instead

    TypingProtocol,
    TypingGeneric,
    TypingTuple,
    TypingCallable,
    TypingType,
    TypingClassVar,
    TypingUnion,
    TypingOptional,
    TypingCast,

    // TODO reactivate these or remove
    //TypingFinal,
    //TypingLiteral,
    //TypingTypeAlias,
    //TypingConcatenate,
    //TypingAnnotated,

    //TypingAliasClass,
    //TypingAliasInstance,
    //TypingAny,
    //TypedDict,
    ClassTypeVar,
    FunctionTypeVar,
    LateBoundTypeVar,
}

#[derive(Debug, PartialEq, Eq)]
#[repr(u32)]
pub enum Locality {
    // Intern: 0xx
    Stmt,
    ClassOrFunction,
    MostOuterClassOrFunction,
    File,

    // Extern: 1xx
    DirectExtern,   // Contains a direct link that can be checked
    ComplexExtern,  // Means we have to recalculate the value all the links
    ImplicitExtern, // Contains star imports for now (always recheck on invalidation of the module)
    Todo,
}

#[derive(Debug, Copy, Clone, PartialEq)]
pub struct PointLink {
    pub file: FileIndex,
    pub node_index: NodeIndex,
}

impl PointLink {
    pub fn new(file: FileIndex, node_index: NodeIndex) -> Self {
        Self { file, node_index }
    }
}

pub struct LocalityLink {
    pub file: FileIndex,
    pub node_index: NodeIndex,
    pub locality: Locality,
}

impl LocalityLink {
    pub fn into_point_redirect(self) -> Point {
        Point::new_redirect(self.file, self.node_index, self.locality)
    }
}

#[derive(Debug, Clone, PartialEq)]
pub enum AnyLink {
    Reference(PointLink),
    Complex(Box<ComplexPoint>),
    SimpleSpecific(Specific),
}

#[derive(Debug, Clone, PartialEq)]
pub enum ComplexPoint {
    Class(Box<ClassStorage>),
    Union(Box<[AnyLink]>),
    ExecutionInstance(PointLink, Box<Execution>),
    BoundMethod(AnyLink, MroIndex, PointLink),
    Closure(PointLink, Box<Execution>),
    GenericClass(PointLink, GenericsList),
    Instance(PointLink, Option<GenericsList>),
    ClassInfos(Box<ClassInfos>),
    FunctionTypeVars(Box<[PointLink]>),
    FunctionOverload(Box<Overload>),
    TupleClass(TupleContent),
    Tuple(TupleContent),
    Callable(CallableContent),
    CallableClass(CallableContent),
    Type(Box<GenericPart>),
}

#[derive(Debug, Clone, PartialEq)]
pub struct Execution {
    pub function: PointLink,
    pub in_: Option<Box<Execution>>,
    pub argument_node: PointLink,
}

impl Execution {
    pub fn new(function: PointLink, argument_node: PointLink, in_: Option<&Execution>) -> Self {
        Self {
            function,
            in_: in_.map(|x| Box::new(x.clone())),
            argument_node,
        }
    }
}

#[derive(Debug, Clone, PartialEq)]
pub struct ClassInfos {
    pub type_vars: Box<[PointLink]>,
    pub mro: Box<[GenericPart]>, // Does never include `object`
    pub is_protocol: bool,
}

impl ClassInfos {
    pub fn find_type_var_index(&self, link: PointLink) -> Option<TypeVarIndex> {
        self.type_vars
            .iter()
            .position(|&r| r == link)
            .map(|i| TypeVarIndex(i as u32))
    }
}

#[derive(Debug, Clone, PartialEq)]
pub struct GenericsList(Box<[GenericPart]>);

impl GenericsList {
    pub fn new(parts: Box<[GenericPart]>) -> Self {
        debug_assert!(parts.len() > 0);
        Self(parts)
    }

    pub fn from_vec(parts: Vec<GenericPart>) -> Self {
        Self::new(parts.into_boxed_slice())
    }

    pub fn new_unknown(length: usize) -> Self {
        debug_assert!(length > 0);
        let vec: Vec<_> = repeat(GenericPart::Unknown).take(length).collect();
        Self(vec.into_boxed_slice())
    }

    pub fn set_generic(&mut self, index: TypeVarIndex, generic: GenericPart) {
        self.0[index.0 as usize].union_in_place(generic);
    }

    pub fn nth(&self, index: TypeVarIndex) -> Option<&GenericPart> {
        self.0.get(index.0 as usize)
    }

    pub fn iter(&self) -> std::slice::Iter<GenericPart> {
        self.0.iter()
    }

    pub fn as_string(
        &self,
        db: &Database,
        type_var_generics: Option<&mut dyn FnMut(TypeVarIndex) -> GenericPart>,
    ) -> String {
        if let Some(type_var_generics) = type_var_generics {
            // TODO is there no better way than writing this twice???
            self.0
                .iter()
                .map(|g| g.as_type_string(db, Some(type_var_generics)))
                .fold(String::new(), |a, b| {
                    if a.is_empty() {
                        a + &b
                    } else {
                        a + ", " + &b
                    }
                })
        } else {
            self.0
                .iter()
                .map(|g| g.as_type_string(db, None))
                .fold(String::new(), |a, b| {
                    if a.is_empty() {
                        a + &b
                    } else {
                        a + ", " + &b
                    }
                })
        }
    }

    pub fn scan_for_late_bound_type_vars(&self, db: &Database, result: &mut Vec<PointLink>) {
        for g in self.0.iter() {
            g.scan_for_late_bound_type_vars(db, result)
        }
    }
}

#[derive(Debug, Clone, PartialEq)]
pub enum GenericPart {
    Class(PointLink),
    GenericClass(PointLink, GenericsList),
    Union(GenericsList),
    TypeVar(TypeVarIndex, PointLink),
    Type(Box<GenericPart>),
    Tuple(TupleContent),
    Callable(CallableContent),
    None,
    Unknown,
}

impl GenericPart {
    pub fn union(self, other: GenericPart) -> Self {
        match self {
            Self::Union(list) => {
                let mut vec = list.0.into_vec();
                match other {
                    Self::Union(other_list) => {
                        for o in other_list.0.into_vec().into_iter() {
                            if !vec.contains(&o) {
                                vec.push(o);
                            }
                        }
                    }
                    Self::Unknown => (),
                    _ => {
                        if !vec.contains(&other) {
                            vec.push(other)
                        }
                    }
                };
                Self::Union(GenericsList::from_vec(vec))
            }
            Self::Unknown => other,
            _ => match other {
                Self::Union(list) => {
                    if list.0.contains(&self) {
                        Self::Union(list)
                    } else {
                        let mut vec = list.0.into_vec();
                        vec.push(self);
                        Self::Union(GenericsList::from_vec(vec))
                    }
                }
                Self::Unknown => self,
                _ => {
                    if self == other {
                        self
                    } else {
                        Self::Union(GenericsList::new(Box::new([self, other])))
                    }
                }
            },
        }
    }

    pub fn union_in_place(&mut self, other: GenericPart) {
        *self = mem::replace(self, Self::Unknown).union(other);
    }

    pub fn as_type_string(
        &self,
        db: &Database,
        type_var_generics: Option<&mut dyn FnMut(TypeVarIndex) -> GenericPart>,
    ) -> String {
        let class_name = |link| {
            NodeRef::from_link(db, link)
                .maybe_class()
                .unwrap()
                .name()
                .as_str()
        };
        match self {
            Self::Class(link) => class_name(*link).to_owned(),
            Self::GenericClass(link, generics_lst) => {
                format!(
                    "{}[{}]",
                    class_name(*link),
                    generics_lst.as_string(db, type_var_generics)
                )
            }
            Self::Union(list) => {
                format!("Union[{}]", list.as_string(db, type_var_generics))
            }
            Self::TypeVar(index, link) => {
                if let Some(type_var_generics) = type_var_generics {
                    return type_var_generics(*index).as_type_string(db, None);
                }
                NodeRef::from_link(db, *link).as_name().as_str().to_owned()
            }
            Self::Type(generic_part) => format!(
                "Type[{}]",
                generic_part.as_type_string(db, type_var_generics)
            ),
            Self::Tuple(content) => format!("Tuple{}", &content.as_string(db)),
            Self::Callable(content) => format!("Callable{}", &content.as_string(db)),
            Self::None => "None".to_owned(),
            Self::Unknown => "Unknown".to_owned(),
        }
    }

    pub fn replace_type_vars<C>(self, callable: &mut C) -> Self
    where
        C: FnMut(TypeVarIndex, PointLink) -> Self,
    {
        let replace_list = |list: &mut Box<[GenericPart]>, callable: &mut C| {
            for item in list.iter_mut() {
                let g = std::mem::replace(&mut *item, GenericPart::Unknown);
                *item = g.replace_type_vars(callable);
            }
        };
        match self {
            Self::Class(_) | Self::Unknown | Self::None => self,
            Self::GenericClass(link, mut generics) => {
                replace_list(&mut generics.0, callable);
                Self::GenericClass(link, generics)
            }
            Self::Union(list) => {
                todo!()
            }
            Self::TypeVar(type_var_index, link) => callable(type_var_index, link),
            Self::Type(mut generic_part) => {
                let g = std::mem::replace(&mut *generic_part, GenericPart::Unknown);
                *generic_part = g.replace_type_vars(callable);
                Self::Type(generic_part)
            }
            Self::Tuple(mut content) => {
                if let Some(generics) = content.generics.as_mut() {
                    replace_list(&mut generics.0, callable)
                }
                Self::Tuple(content)
            }
            Self::Callable(mut content) => {
                if let Some(params) = content.params.as_mut() {
                    replace_list(&mut params.0, callable)
                }
                let g = std::mem::replace(&mut *content.return_class, GenericPart::Unknown);
                *content.return_class = g.replace_type_vars(callable);
                Self::Callable(content)
            }
        }
    }

    pub fn expect_generics(&self) -> &GenericsList {
        match self {
            Self::GenericClass(link, generics) => generics,
            Self::Tuple(content) => todo!(),
            Self::Callable(content) => todo!(),
            Self::Class(_)
            | Self::Unknown
            | Self::None
            | Self::Union(_)
            | Self::TypeVar(_, _)
            | Self::Type(_) => unreachable!(),
        }
    }

    pub fn remap_type_vars(
        &self,
        resolve_type_var: &mut impl FnMut(TypeVarIndex) -> GenericPart,
    ) -> Self {
        let mut remap_generics = |generics: &GenericsList| {
            GenericsList::new(
                generics
                    .iter()
                    .map(|g| g.remap_type_vars(resolve_type_var))
                    .collect(),
            )
        };
        match self {
            Self::Class(c) => Self::Class(*c),
            Self::Unknown => Self::Unknown,
            Self::None => Self::None,
            Self::GenericClass(link, generics) => {
                Self::GenericClass(*link, remap_generics(generics))
            }
            Self::Union(list) => Self::Union(remap_generics(list)),
            Self::TypeVar(index, _) => resolve_type_var(*index),
            Self::Type(generic_part) => {
                Self::Type(Box::new(generic_part.remap_type_vars(resolve_type_var)))
            }
            Self::Tuple(content) => todo!(),
            Self::Callable(content) => todo!(),
        }
    }

    fn scan_for_late_bound_type_vars(&self, db: &Database, result: &mut Vec<PointLink>) {
        match self {
            Self::GenericClass(link, generics) => {
                generics.scan_for_late_bound_type_vars(db, result)
            }
            Self::Union(list) => list.scan_for_late_bound_type_vars(db, result),
            Self::TypeVar(index, link) => {
                loop {
                    if index.as_usize() == result.len() {
                        result.push(*link);
                        break;
                    } else {
                        // This a bit special, because these are late-bound parameters that are not
                        // part of the GenericPart anymore. This won't ever be accessed, but it's a
                        // placeholder in the array so that type var indexes still work normally.
                        // e.g. Tuple[Callable[[T], T], Callable[[U], U]] needs this.
                        result.push(PointLink::new(FileIndex(0), u32::MAX));
                    }
                }
            }
            Self::Type(generic_part) => generic_part.scan_for_late_bound_type_vars(db, result),
            Self::Tuple(content) => {
                if let Some(generics) = &content.generics {
                    generics.scan_for_late_bound_type_vars(db, result)
                }
            }
            Self::Callable(content) => {
                if let Some(params) = &content.params {
                    params.scan_for_late_bound_type_vars(db, result)
                }
                content
                    .return_class
                    .scan_for_late_bound_type_vars(db, result)
            }
            _ => (),
        }
    }

    pub fn maybe_type_var_index(&self) -> Option<TypeVarIndex> {
        match self {
            Self::TypeVar(index, _) => Some(*index),
            _ => None,
        }
    }

    pub fn todo_matches(&self, other: &Self) -> bool {
        match self {
            Self::None => matches!(other, Self::None),
            _ => false,
        }
    }
}

#[derive(Debug, Clone, Copy, PartialEq)]
pub enum FunctionType {
    Function,
    Property,
    ClassMethod,
    StaticMethod,
}

#[derive(Debug, Clone, PartialEq)]
pub struct Overload {
    pub implementing_function: Option<PointLink>,
    pub functions: Box<[PointLink]>,
    pub function_type: FunctionType,
    pub is_async: bool,
}

impl Overload {
    pub fn add_another_overload(&self, function: PointLink) -> Self {
        debug_assert!(self.implementing_function.is_none());
        let mut functions = Vec::with_capacity(self.functions.len() + 1);
        functions.extend_from_slice(self.functions.as_ref());
        functions.push(function);
        Self {
            implementing_function: None,
            functions: functions.into_boxed_slice(),
            function_type: self.function_type,
            is_async: self.is_async,
        }
    }
}

#[derive(Debug, Clone, PartialEq)]
pub struct TupleContent {
    pub generics: Option<GenericsList>,
    pub arbitrary_length: bool, // Is also homogenous
}

impl TupleContent {
    pub fn as_string(&self, db: &Database) -> String {
        if let Some(generics) = self.generics.as_ref() {
            let list = generics.as_string(db, None);
            if self.arbitrary_length {
                format!("[{}, ...]", list)
            } else {
                format!("[{}]", list)
            }
        } else {
            "".to_owned()
        }
    }
}

#[derive(Debug, Clone, PartialEq)]
pub struct CallableContent {
    pub params: Option<GenericsList>,
    pub return_class: Box<GenericPart>,
}

impl CallableContent {
    pub fn as_string(&self, db: &Database) -> String {
        format!(
            "[{}, {}]",
            self.params
                .as_ref()
                .map(|p| format!("[{}]", p.as_string(db, None)))
                .unwrap_or_else(|| "...".to_owned()),
            self.return_class.as_type_string(db, None)
        )
    }
}

pub struct Database {
    in_use: bool,
    pub vfs: Box<dyn Vfs>,
    file_state_loaders: FileStateLoaders,
    files: InsertOnlyVec<dyn FileState>,
    path_to_file: HashMap<&'static str, FileIndex>,
    pub workspaces: Workspaces,
    in_memory_files: HashMap<String, FileIndex>,

    pub python_state: PythonState,
}

impl Database {
    pub fn new(file_state_loaders: FileStateLoaders, workspaces: Workspaces) -> Self {
        let mut this = Self {
            in_use: false,
            vfs: Box::<FileSystemReader>::new(Default::default()),
            file_state_loaders,
            files: Default::default(),
            path_to_file: Default::default(),
            workspaces,
            in_memory_files: Default::default(),
            python_state: PythonState::reserve(),
        };
        this.initial_python_load();
        this
    }

    pub fn acquire(&mut self) {
        assert!(!self.in_use);
        self.in_use = true;
    }

    pub fn release(&mut self) {
        assert!(self.in_use);
        self.in_use = false;
        // todo handle watcher events here
    }

    pub fn file_state(&self, index: FileIndex) -> &(dyn FileState + 'static) {
        self.files.get(index.0 as usize).unwrap()
    }

    pub fn file_state_mut(&mut self, index: FileIndex) -> &mut (dyn FileState + 'static) {
        &mut self.files[index.0 as usize]
    }

    pub fn file_path(&self, index: FileIndex) -> &str {
        self.file_state(index).path()
    }

    pub fn file_state_index_by_path(&self, path: &str) -> Option<FileIndex> {
        self.path_to_file.get(path).copied()
    }

    pub fn loaded_file(&self, index: FileIndex) -> &(dyn File + 'static) {
        self.file_state(index).file(&*self.vfs).unwrap()
    }

    fn loader(&self, path: &str) -> Option<&dyn FileStateLoader> {
        for loader in self.file_state_loaders.iter() {
            let extension = Path::new(path).extension().and_then(|e| e.to_str());
            if let Some(e) = extension {
                if loader.responsible_for_file_endings().contains(&e) {
                    return Some(loader.as_ref());
                }
            } else {
                return Some(&PythonFileLoader {});
            }
        }
        None
    }

    fn add_file_state(&self, file_state: Pin<Box<dyn FileState>>) -> FileIndex {
        self.files.push(file_state);
        let file_index = FileIndex(self.files.len() as u32 - 1);
        self.files.last().unwrap().set_file_index(file_index);
        file_index
    }

    fn update_file_state(&mut self, file_index: FileIndex, file_state: Pin<Box<dyn FileState>>) {
        file_state.set_file_index(file_index);
        self.files.set(file_index.0 as usize, file_state);
    }

    pub fn load_annotation_file(&self, in_file: FileIndex, code: String) -> &PythonFile {
        // TODO should probably not need a newline
        let mut file = PythonFile::new(code + "\n");
        file.star_imports.push(in_file);
        // TODO just saving this in the cache and forgetting about it is a bad idea
        let index =
            self.add_file_state(Box::pin(LanguageFileState::new_parsed("".to_owned(), file)));
        self.loaded_python_file(index)
    }

    pub fn load_file_from_workspace(&self, path: String, index: &WorkspaceFileIndex) {
        // A loader should be available for all files in the workspace.
        let loader = self.loader(&path).unwrap();
        let file_index = self.add_file_state(if let Some(code) = self.vfs.read_file(&path) {
            loader.load_parsed(path, code)
        } else {
            //loader.inexistent_file_state(path)
            todo!()
        });
        index.set(file_index);
    }

    pub fn load_unparsed(&self, path: String) -> Option<FileIndex> {
        self.loader(&path)
            .map(|loader| self.add_file_state(loader.load_unparsed(path)))
    }

    pub fn load_in_memory_file(&mut self, path: String, code: String) -> FileIndex {
        if let Some(file_index) = self.in_memory_file(&path) {
            self.unload_file(file_index);
            let invalidations = self.workspaces.add_file(&*self.vfs, &path, file_index);
            self.invalidate_file(file_index, invalidations);
            let file_state = self.loader(&path).unwrap().load_parsed(path, code);
            self.update_file_state(file_index, file_state);
            file_index
        } else {
            // TODO there could be no loader...
            let loader = self.loader(&path).unwrap();
            let file_index = self.add_file_state(loader.load_parsed(path.clone(), code));
            let invalidations = self.workspaces.add_file(&*self.vfs, &path, file_index);
            self.invalidate_file(file_index, invalidations);
            self.in_memory_files.insert(path, file_index);
            file_index
        }
    }

    pub fn in_memory_file(&mut self, path: &str) -> Option<FileIndex> {
        self.in_memory_files.get(path).cloned()
    }

    fn unload_file(&mut self, file_index: FileIndex) {
        let file_state = &mut self.files[file_index.0 as usize];
        self.workspaces.unload_if_not_available(file_state.path());
        let invalidations = file_state.unload_and_return_invalidations();
        self.invalidate_file(file_index, invalidations)
    }

    fn invalidate_file(&mut self, original_file_index: FileIndex, invalidations: Invalidations) {
        for invalid_index in invalidations.into_iter() {
            let file_state = self.file_state_mut(invalid_index);
            let invalidations = file_state.take_invalidations();
            if let Some(file) = file_state.maybe_loaded_file_mut() {
                file.invalidate_references_to(original_file_index);
            }

            self.invalidate_file(original_file_index, invalidations);
        }
    }

    pub fn add_invalidates(&self, file: FileIndex, invalidates: FileIndex) {
        self.file_state(file).add_invalidates(invalidates)
    }

    pub fn unload_in_memory_file(&mut self, path: &str) -> Result<(), &'static str> {
        if let Some(file_index) = self.in_memory_files.get(path) {
            self.unload_file(*file_index);
            self.in_memory_files.remove(path);
            Ok(())
        } else {
            Err("The path is not known to be an in memory file")
        }
    }

    pub fn unload_all_in_memory_files(&mut self) {
        let in_memory_files = mem::take(&mut self.in_memory_files);
        for (path, file_index) in in_memory_files.into_iter() {
            self.unload_file(file_index);
        }
    }

    fn py_load_tmp(&self, p: &'static str) -> &PythonFile {
        let file_index = self.load_unparsed(p.to_owned()).unwrap();
        self.loaded_python_file(file_index)
    }

    pub fn loaded_python_file(&self, index: FileIndex) -> &PythonFile {
        self.loaded_file(index).as_any().downcast_ref().unwrap()
    }

    fn initial_python_load(&mut self) {
        let builtins = self.py_load_tmp("../typeshed/stdlib/builtins.pyi") as *const _;
        let typing = self.py_load_tmp("../typeshed/stdlib/typing.pyi") as *const _;
        let collections =
            self.py_load_tmp("../typeshed/stdlib/collections/__init__.pyi") as *const _;
        PythonState::initialize(self, builtins, typing, collections);
    }
}

#[derive(Debug)]
pub struct ClassStorage {
    pub class_symbol_table: SymbolTable,
    pub self_symbol_table: SymbolTable,
}

impl ClassStorage {
    pub fn new(class_symbol_table: SymbolTable, self_symbol_table: SymbolTable) -> Self {
        Self {
            class_symbol_table,
            self_symbol_table,
        }
    }
}

impl std::clone::Clone for ClassStorage {
    fn clone(&self) -> Self {
        unreachable!("This should never happen, because should never be cloned");
    }
}

impl<'db> std::cmp::PartialEq for ClassStorage {
    fn eq(&self, other: &Self) -> bool {
        unreachable!("Should never happen with classes")
    }
}

#[cfg(test)]
mod tests {
    #[test]
    fn test_sizes() {
        use super::*;
        use std::mem::size_of;
        assert_eq!(size_of::<ClassStorage>(), 96);
        assert_eq!(size_of::<ClassInfos>(), 40);
        assert_eq!(size_of::<PointLink>(), 8);
        assert_eq!(size_of::<AnyLink>(), 16);
        assert_eq!(size_of::<Execution>(), 24);
        assert_eq!(size_of::<ComplexPoint>(), 32);
        assert_eq!(size_of::<GenericPart>(), 32);
    }
}
