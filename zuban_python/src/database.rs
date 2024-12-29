use std::{
    borrow::Cow,
    cell::{Cell, OnceCell, RefCell},
    collections::HashMap,
    fmt, mem,
    ops::Range,
    path::Path,
    pin::Pin,
    rc::Rc,
};

use parsa_python_cst::NodeIndex;

use crate::{
    config::{OverrideConfig, Settings},
    debug,
    file::{
        File, FileState, FileStateLoader, FileSystemReader, LanguageFileState, PythonFile,
        PythonFileLoader, Vfs,
    },
    node_ref::NodeRef,
    python_state::PythonState,
    sys_path,
    type_::{
        CallableContent, DataclassTransformObj, FunctionKind, FunctionOverload, GenericItem,
        GenericsList, NewType, ParamSpecUsage, RecursiveType, StringSlice, Type, TypeVarLike,
        TypeVarLikeUsage, TypeVarLikes, TypeVarTupleUsage, TypeVarUsage, TypedDict, Variance,
    },
    type_helpers::{Class, Function},
    utils::{InsertOnlyVec, SymbolTable},
    workspaces::{
        Directory, DirectoryEntry, FileEntry, Invalidations, Parent, WorkspaceKind, Workspaces,
    },
    ProjectOptions, TypeCheckerFlags,
};

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct FileIndex(pub u32);
type FileStateLoaders = Box<[Box<dyn FileStateLoader>]>;

// Most significant bits
// 27 bits = 134217728; 20 bits = 1048576
// oxxxx is_analyzed
// xoxxx in_global_scope
// xxooo Locality (xxXxx is_external)
// xxxxxo needs_flow_analysis
// xxxxxxxooo PointKind
// the other 23 bits are reserved for Point details

const IS_ANALIZED_BIT_INDEX: usize = 31;
const IN_GLOBAL_SCOPE_INDEX: usize = 30;
const LOCALITY_BIT_INDEX: usize = 27; // Uses 3 bits
const NEEDS_FLOW_ANALYSIS_BIT_INDEX: usize = 26;
const KIND_BIT_INDEX: usize = 23; // Uses 3 bits

const REST_MASK: u32 = (1 << KIND_BIT_INDEX) - 1;
const SPECIFIC_BIT_LEN: u32 = 8;
const SPECIFIC_MASK: u32 = (1 << SPECIFIC_BIT_LEN) - 1; // 8 bits
                                                        // const MAX_KIND_VAR: u32 = 0xFF; // 256
                                                        // const FILE_MASK: u32 = 0xFFFFFF; // 24 bits
const IS_ANALIZED_MASK: u32 = 1 << IS_ANALIZED_BIT_INDEX;
const IN_GLOBAL_SCOPE_MASK: u32 = 1 << IN_GLOBAL_SCOPE_INDEX;
const NEEDS_FLOW_ANALYSIS_MASK: u32 = 1 << NEEDS_FLOW_ANALYSIS_BIT_INDEX;
const LOCALITY_MASK: u32 = 0b111 << LOCALITY_BIT_INDEX;
const KIND_MASK: u32 = 0b111 << KIND_BIT_INDEX;

const PARTIAL_NULLABLE_INDEX: u32 = SPECIFIC_BIT_LEN + 1;
const PARTIAL_NULLABLE_MASK: u32 = 1 << PARTIAL_NULLABLE_INDEX;
const PARTIAL_REPORTED_ERROR_INDEX: u32 = SPECIFIC_BIT_LEN + 2;
const PARTIAL_REPORTED_ERROR_MASK: u32 = 1 << PARTIAL_REPORTED_ERROR_INDEX;
const PARTIAL_FINISHED_INDEX: u32 = SPECIFIC_BIT_LEN + 3;
const PARTIAL_FINISHED_MASK: u32 = 1 << PARTIAL_FINISHED_INDEX;

const CALCULATED_OR_REDIRECT_LIKE_KIND_OR_REST_MASK: u32 = IS_ANALIZED_MASK | KIND_MASK | REST_MASK;
const REDIRECT_KIND_VALUE: u32 = (PointKind::Redirect as u32) << KIND_BIT_INDEX;

#[derive(Copy, Clone, Eq, PartialEq, Default)]
pub struct Point {
    flags: u32,
    node_index: u32,
}

impl Point {
    #[inline]
    fn calculate_flags(kind: PointKind, rest: u32, locality: Locality) -> u32 {
        debug_assert!(rest & !REST_MASK == 0);
        rest | IS_ANALIZED_MASK
            | (locality as u32) << LOCALITY_BIT_INDEX
            | (kind as u32) << KIND_BIT_INDEX
    }

    pub fn new_redirect(file: FileIndex, node_index: NodeIndex, locality: Locality) -> Self {
        let flags = Self::calculate_flags(PointKind::Redirect, file.0, locality);
        Self { flags, node_index }
    }

    pub fn new_name_of_name_def(
        node_index: NodeIndex,
        in_global_scope: bool,
        locality: Locality,
    ) -> Self {
        Self {
            node_index,
            flags: Self::calculate_flags(
                PointKind::Specific,
                Specific::NameOfNameDef as u32,
                locality,
            ),
        }
        .with_in_global_scope(in_global_scope)
    }

    pub fn new_parent(node_index: NodeIndex, locality: Locality) -> Self {
        Self {
            flags: Self::calculate_flags(PointKind::Specific, Specific::Parent as u32, locality),
            node_index,
        }
    }

    pub fn new_complex_point(complex_index: u32, locality: Locality) -> Self {
        let flags = Self::calculate_flags(PointKind::Complex, complex_index, locality);
        Self {
            flags,
            node_index: 0,
        }
    }

    pub fn new_specific(specific: Specific, locality: Locality) -> Self {
        let flags = Self::calculate_flags(PointKind::Specific, specific as u32, locality);
        Self {
            flags,
            node_index: 0,
        }
    }

    pub fn new_calculating() -> Self {
        Self {
            flags: Specific::Calculating as u32,
            node_index: 0,
        }
    }

    pub fn new_file_reference(file: FileIndex, locality: Locality) -> Self {
        let flags = Self::calculate_flags(PointKind::FileReference, file.0, locality);
        Self {
            flags,
            node_index: 0,
        }
    }

    pub fn new_analyzed_with_node_index(locality: Locality, node_index: NodeIndex) -> Self {
        Self {
            node_index,
            ..Self::new_specific(Specific::Analyzed, locality)
        }
    }

    pub fn new_uncalculated() -> Self {
        Self {
            flags: 0,
            node_index: 0,
        }
    }

    #[inline]
    pub fn with_needs_flow_analysis(mut self, needs_flow_analysis: bool) -> Self {
        self.flags |= (needs_flow_analysis as u32) << NEEDS_FLOW_ANALYSIS_BIT_INDEX;
        self
    }

    #[inline]
    pub fn with_in_global_scope(mut self, in_global_scope: bool) -> Self {
        self.flags |= (in_global_scope as u32) << IN_GLOBAL_SCOPE_INDEX;
        self
    }

    pub fn kind(self) -> PointKind {
        debug_assert!(self.calculated());
        unsafe { mem::transmute((self.flags & KIND_MASK) >> KIND_BIT_INDEX) }
    }

    pub fn locality(self) -> Locality {
        unsafe { mem::transmute((self.flags & LOCALITY_MASK) >> LOCALITY_BIT_INDEX) }
    }

    pub fn needs_flow_analysis(self) -> bool {
        debug_assert!(self.calculated());
        (self.flags & NEEDS_FLOW_ANALYSIS_MASK) > 0
    }

    pub fn calculated(self) -> bool {
        (self.flags & IS_ANALIZED_MASK) != 0
    }

    pub fn calculating(self) -> bool {
        self.flags == Specific::Calculating as u32
    }

    pub fn in_global_scope(self) -> bool {
        (self.flags & IN_GLOBAL_SCOPE_MASK) != 0
    }

    pub fn file_index(self) -> FileIndex {
        debug_assert!(
            self.kind() == PointKind::Redirect || self.kind() == PointKind::FileReference,
            "{:?}",
            self.kind()
        );
        FileIndex(self.flags & REST_MASK)
    }

    pub fn complex_index(self) -> usize {
        debug_assert!(
            self.kind() == PointKind::Complex,
            "Expected complex, got {self:?}",
        );
        (self.flags & REST_MASK) as usize
    }

    pub fn maybe_complex_index(self) -> Option<usize> {
        if self.calculated() && self.kind() == PointKind::Complex {
            return Some(self.complex_index());
        }
        None
    }

    pub fn node_index(self) -> NodeIndex {
        debug_assert!(
            self.kind() == PointKind::Redirect
                || matches!(
                    self.maybe_specific(),
                    Some(Specific::NameOfNameDef | Specific::Parent | Specific::Analyzed)
                )
        );
        self.node_index
    }

    #[inline]
    pub fn maybe_redirect_to(self, link: PointLink) -> bool {
        let relevant_flag_stuff = self.flags & CALCULATED_OR_REDIRECT_LIKE_KIND_OR_REST_MASK;
        self.node_index == link.node_index
            && relevant_flag_stuff == IS_ANALIZED_MASK | REDIRECT_KIND_VALUE | link.file.0
    }

    pub fn as_redirected_node_ref(self, db: &Database) -> NodeRef<'_> {
        debug_assert!(self.kind() == PointKind::Redirect);
        let file = db.loaded_python_file(self.file_index());
        NodeRef::new(file, self.node_index())
    }

    pub fn maybe_specific(self) -> Option<Specific> {
        if self.kind() == PointKind::Specific {
            Some(self.specific())
        } else {
            None
        }
    }

    pub fn maybe_calculated_and_specific(self) -> Option<Specific> {
        if !self.calculated() {
            return None;
        }
        self.maybe_specific()
    }

    pub fn specific(self) -> Specific {
        debug_assert!(self.kind() == PointKind::Specific, "{:?}", self);
        unsafe { mem::transmute(self.flags & SPECIFIC_MASK) }
    }

    pub fn partial_flags(self) -> PartialFlags {
        debug_assert!(self.specific().is_partial(), "{:?}", self);
        PartialFlags {
            nullable: self.flags & PARTIAL_NULLABLE_MASK != 0,
            reported_error: self.flags & PARTIAL_REPORTED_ERROR_MASK != 0,
            finished: self.flags & PARTIAL_FINISHED_MASK != 0,
        }
    }

    pub fn set_partial_flags(self, partial_flags: PartialFlags) -> Point {
        debug_assert!(
            matches!(
                self.specific(),
                Specific::PartialNone
                    | Specific::PartialList
                    | Specific::PartialDict
                    | Specific::PartialSet
                    | Specific::PartialDefaultDict
                    | Specific::PartialDefaultDictWithList
                    | Specific::PartialDefaultDictWithSet
            ),
            "{:?}",
            self
        );
        let mut flags = self.flags & !PARTIAL_NULLABLE_MASK & !PARTIAL_REPORTED_ERROR_MASK;
        flags |= (partial_flags.nullable as u32) << PARTIAL_NULLABLE_INDEX;
        flags |= (partial_flags.reported_error as u32) << PARTIAL_REPORTED_ERROR_INDEX;
        flags |= (partial_flags.finished as u32) << PARTIAL_FINISHED_INDEX;
        Point {
            flags,
            node_index: self.node_index,
        }
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
            s.field("kind", &self.kind())
                .field("locality", &self.locality())
                .field("node_index", &self.node_index)
                .field("needs_flow_analysis", &self.needs_flow_analysis());
            if self.kind() == PointKind::Specific {
                let specific = self.specific();
                s.field("specific", &specific);
                if specific.is_partial() {
                    let partial = self.partial_flags();
                    s.field("partial: nullable", &partial.nullable);
                    s.field("partial: reported_error", &partial.reported_error);
                    s.field("partial: finished", &partial.finished);
                }
            }
            if self.kind() == PointKind::Redirect || self.kind() == PointKind::FileReference {
                s.field("file_index", &self.file_index().0);
            }
            if self.in_global_scope() {
                s.field("in_global_scope", &true);
            }
        }
        s.finish()
    }
}

#[derive(Debug, Clone, Default)]
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

    pub fn invalidate_references_to(&mut self, file_index: FileIndex) {
        for cell in &self.0 {
            let locality = cell.get().locality();
            if locality == Locality::DirectExtern && cell.get().file_index() == file_index {
                cell.set(Point::new_uncalculated());
            } else if locality as u32 >= Locality::Complex as u32 {
                cell.set(Point::new_uncalculated())
            }
        }
    }

    pub fn invalidate_full_db(&mut self) {
        for cell in &self.0 {
            cell.set(Point::new_uncalculated())
        }
    }

    #[inline]
    pub fn iter(&self) -> impl Iterator<Item = Point> + '_ {
        self.0.iter().map(|p| p.get())
    }

    pub fn backup(&self, range: Range<NodeIndex>) -> PointsBackup {
        let slice = &self.0[range.start as usize..range.end as usize];
        PointsBackup {
            range,
            points: slice.to_vec(),
        }
    }

    pub fn reset_from_backup(&self, backup: &PointsBackup) {
        for (i, points_index) in backup.range.clone().enumerate() {
            self.0[points_index as usize].set(backup.points[i].get());
        }
    }
}

pub struct PointsBackup {
    pub range: Range<NodeIndex>,
    points: Vec<Cell<Point>>,
}

#[derive(Debug, PartialEq, Eq)]
#[repr(u32)]
pub enum PointKind {
    Specific,
    Complex,
    Redirect,
    FileReference,
}

#[derive(Debug, PartialEq, Eq, Clone, Copy)]
#[repr(u32)]
pub enum Specific {
    // This is reserved, because if everything is initialized as zero, this is the value it takes.
    ReservedBecauseUnused,
    Analyzed, // Signals that a node has been analyzed
    Calculating,
    Cycle,
    NameOfNameDef, // Cycles for the same name definition in e.g. different branches
    Parent,        // Has a link to the parent scope
    OverloadUnreachable,
    AnyDueToError,
    InvalidTypeDefinition,
    ModuleNotFound,
    IfBranchAlwaysReachableInNameBinder,
    IfBranchAlwaysReachableInTypeCheckingBlock, // For if TYPE_CHECKING:
    IfBranchAfterAlwaysReachableInNameBinder,
    IfBranchAlwaysUnreachableInNameBinder,
    AssertAlwaysFails,
    GlobalVariable,
    NonlocalVariable,

    String,
    Float,
    Complex,
    Bytes,
    Int,
    Bool,
    None,
    // Literals are used for things like Literal[42]
    StringLiteral,
    BytesLiteral,
    IntLiteral,
    BoolLiteral,

    Ellipsis,

    MaybeSelfParam,
    Param,
    Function, // The node point so the index of the result

    // A class with either SimpleGeneric or just a class that contains no generics
    AnnotationOrTypeCommentSimpleClassInstance,
    AnnotationOrTypeCommentWithTypeVars, // Will contain a Type a few points later.
    AnnotationOrTypeCommentWithoutTypeVars,
    AnnotationOrTypeCommentClassVar,
    AnnotationOrTypeCommentFinal,
    AnnotationTypeAlias,
    // A generic class where the generics are either SimpleGeneric or classes without generics
    SimpleGeneric, // primary: primary '[' slices ']'

    BuiltinsType,
    BuiltinsSuper,
    BuiltinsIsinstance,
    BuiltinsIssubclass,
    TypingProtocol,
    TypingGeneric,
    TypingTuple,
    TypingCallable,
    TypingType,
    TypingClassVar,
    TypingUnion,
    TypingOptional,
    TypingCast,
    TypingNewType,
    TypingTypeVarClass,
    TypingTypeVarTupleClass,
    TypingParamSpecClass,
    TypingConcatenateClass,
    TypingLiteralString,
    TypingUnpack,
    TypingTypeAlias,
    TypingFinal,
    TypingLiteral,
    TypingSelf,
    TypingAnnotated,
    TypingNeverOrNoReturn,
    TypingAny,
    TypingDataclassTransform,
    TypingTypedDict,
    TypingRequired,
    TypingNotRequired,
    TypingTypeGuard,
    TypingTypeIs,
    RevealTypeFunction,
    AssertTypeFunction,
    TypingNamedTuple,      // typing.NamedTuple
    CollectionsNamedTuple, // collections.namedtuple
    DataclassesDataclass,
    MypyExtensionsFlexibleAlias,

    MypyExtensionsArg,
    MypyExtensionsDefaultArg,
    MypyExtensionsNamedArg,
    MypyExtensionsDefaultNamedArg,
    MypyExtensionsVarArg,
    MypyExtensionsKwArg,
    PartialNone,
    PartialList,
    PartialDict,
    PartialSet,
    PartialDefaultDict,
    PartialDefaultDictWithList,
    PartialDefaultDictWithSet,
}

impl Specific {
    pub fn is_partial(self) -> bool {
        matches!(
            self,
            Specific::PartialNone
                | Specific::PartialList
                | Specific::PartialDict
                | Specific::PartialSet
                | Specific::PartialDefaultDict
                | Specific::PartialDefaultDictWithList
                | Specific::PartialDefaultDictWithSet
        )
    }

    pub fn is_partial_container(self) -> bool {
        matches!(
            self,
            Specific::PartialList
                | Specific::PartialDict
                | Specific::PartialSet
                | Specific::PartialDefaultDict
                | Specific::PartialDefaultDictWithList
                | Specific::PartialDefaultDictWithSet
        )
    }
}

#[derive(Debug, PartialEq, Eq, Clone, Copy)]
#[repr(u32)]
pub enum Locality {
    // Intern: 0xx
    NameBinder,
    _Reserved1,
    _Reserved2,
    File,

    // Extern: 1xx
    DirectExtern,   // Contains a direct link that can be checked
    Complex,        // Means we have to recalculate the value all the links
    ImplicitExtern, // Contains star imports for now (always recheck on invalidation of the module)
    Todo,
}

#[derive(Debug, Copy, Clone, PartialEq, Eq, Hash)]
pub struct PointLink {
    pub file: FileIndex,
    pub node_index: NodeIndex,
}

impl PointLink {
    pub fn new(file: FileIndex, node_index: NodeIndex) -> Self {
        Self { file, node_index }
    }

    pub fn into_redirect_point(self, locality: Locality) -> Point {
        Point::new_redirect(self.file, self.node_index, locality)
    }
}

impl From<LocalityLink> for PointLink {
    fn from(item: LocalityLink) -> Self {
        PointLink::new(item.file, item.node_index)
    }
}

#[derive(Debug, Clone, Copy)]
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

#[derive(Debug)]
pub struct PartialFlags {
    pub nullable: bool,
    pub reported_error: bool,
    pub finished: bool,
}

// This is a core data structure and it should be kept as small as possible, because it's used in
// arrays. It therefore uses a lot of Rcs.
#[derive(Debug, Clone, PartialEq)]
pub enum ComplexPoint {
    TypeInstance(Type),
    Class(Box<ClassStorage>),
    ClassInfos(Box<ClassInfos>),
    TypeVarLikes(TypeVarLikes),
    FunctionOverload(Box<OverloadDefinition>),
    NewTypeDefinition(Rc<NewType>),
    // e.g. X = NamedTuple('X', []), does not include classes.
    NamedTupleDefinition(Rc<Type>),
    // e.g. X = TypedDict('X', {'x': int}), does not include classes.
    TypedDictDefinition(TypedDictDefinition),
    // Sometimes needed when a Final is defined in a class and initialized in __init__.
    IndirectFinal(Rc<Type>),

    // Relevant for types only (not inference)
    TypeVarLike(TypeVarLike),
    TypeAlias(Box<TypeAlias>),
}

#[derive(Debug, Clone, PartialEq)]
pub struct OverloadImplementation {
    pub function_link: PointLink,
    pub callable: CallableContent,
}

impl OverloadImplementation {
    pub fn function<'db, 'class>(
        &self,
        db: &'db Database,
        class: Option<Class<'class>>,
    ) -> Function<'db, 'class> {
        Function::new(NodeRef::from_link(db, self.function_link), class)
    }
}

#[derive(Debug, Clone, PartialEq)]
pub struct OverloadDefinition {
    pub implementation: Option<OverloadImplementation>,
    pub functions: Rc<FunctionOverload>,
    pub is_final: bool,    // Had @final
    pub is_override: bool, // Had @override
}

impl OverloadDefinition {
    pub fn iter_functions(&self) -> impl Iterator<Item = &Rc<CallableContent>> {
        self.functions.iter_functions()
    }

    pub fn kind(&self) -> FunctionKind {
        self.functions.kind()
    }
}

#[derive(Debug, Clone, PartialEq)]
pub struct TypedDictDefinition {
    pub type_: Rc<Type>,
    pub deferred_subclass_member_initializations: Box<RefCell<Vec<Rc<TypedDict>>>>,
    pub total: bool,
}

impl TypedDictDefinition {
    pub fn new(typed_dict: Rc<TypedDict>, total: bool) -> Self {
        Self {
            type_: Rc::new(Type::TypedDict(typed_dict)),
            deferred_subclass_member_initializations: Default::default(),
            total,
        }
    }

    pub fn typed_dict(&self) -> Rc<TypedDict> {
        match self.type_.as_ref() {
            Type::TypedDict(typed_dict) => typed_dict.clone(),
            _ => unreachable!(),
        }
    }
}

#[derive(Debug, PartialEq, Clone)]
struct CalculatedTypeAlias {
    // This is intentionally private, it should not be used anywhere else, because the behavior of
    // a type alias that has `is_recursive` is different.
    type_: Rc<Type>,
    is_recursive: bool,
}

#[derive(Debug, PartialEq, Clone)]
enum TypeAliasState {
    Valid(CalculatedTypeAlias),
    Invalid,
}
#[derive(Debug, PartialEq, Clone)]
pub struct TypeAlias {
    pub type_vars: TypeVarLikes,
    pub location: PointLink,
    pub name: Option<PointLink>,
    // The two attributes around is_recursive are calculated after the TypeAlias is
    // added to the DB.
    state: OnceCell<TypeAliasState>,
}

impl TypeAlias {
    pub fn new(type_vars: TypeVarLikes, location: PointLink, name: Option<PointLink>) -> Self {
        Self {
            type_vars,
            location,
            name,
            state: OnceCell::new(),
        }
    }

    pub fn new_valid(
        type_vars: TypeVarLikes,
        location: PointLink,
        name: Option<PointLink>,
        type_: Rc<Type>,
        is_recursive: bool,
    ) -> Self {
        let slf = Self::new(type_vars, location, name);
        slf.state
            .set(TypeAliasState::Valid(CalculatedTypeAlias {
                type_,
                is_recursive,
            }))
            .unwrap();
        slf
    }

    pub fn is_recursive(&self) -> bool {
        match self.state.get().unwrap() {
            TypeAliasState::Invalid => unreachable!(),
            TypeAliasState::Valid(a) => a.is_recursive,
        }
    }

    pub fn is_valid(&self) -> bool {
        !matches!(self.state.get().unwrap(), TypeAliasState::Invalid)
    }

    pub fn type_if_valid(&self) -> &Type {
        match self.state.get().unwrap() {
            TypeAliasState::Invalid => unreachable!(),
            TypeAliasState::Valid(a) => a.type_.as_ref(),
        }
    }

    pub fn calculating(&self) -> bool {
        self.state.get().is_none()
    }

    pub fn set_valid(&self, type_: Type, is_recursive: bool) {
        self.state
            .set(TypeAliasState::Valid(CalculatedTypeAlias {
                type_: Rc::new(type_),
                is_recursive,
            }))
            .unwrap()
    }

    pub fn set_invalid(&self) {
        self.state.set(TypeAliasState::Invalid).unwrap()
    }

    pub fn name<'db>(&self, db: &'db Database) -> Option<&'db str> {
        self.name.map(|name| NodeRef::from_link(db, name).as_code())
    }

    pub fn application_allowed(&self) -> bool {
        self.is_valid()
            && matches!(
                self.type_if_valid(),
                Type::Class(_) | Type::TypedDict(_) | Type::Dataclass(_)
            )
    }

    pub fn as_type_and_set_type_vars_any(&self, db: &Database) -> Type {
        if self.is_recursive() {
            return Type::RecursiveType(Rc::new(RecursiveType::new(
                self.location,
                (!self.type_vars.is_empty()).then(|| {
                    GenericsList::new_generics(
                        self.type_vars
                            .iter()
                            .map(|tv| tv.as_any_generic_item())
                            .collect(),
                    )
                }),
            )));
        }
        let type_ = self.type_if_valid();
        if self.type_vars.is_empty() {
            type_.clone()
        } else {
            type_
                .replace_type_var_likes(db, &mut |t| {
                    (t.in_definition() == self.location).then(|| t.as_any_generic_item())
                })
                .unwrap_or_else(|| type_.clone())
        }
    }

    pub fn replace_type_var_likes(
        &self,
        db: &Database,
        remove_recursive_wrapper: bool,
        callable: &mut impl FnMut(TypeVarLikeUsage) -> GenericItem,
    ) -> Cow<Type> {
        if self.is_recursive() && !remove_recursive_wrapper {
            return Cow::Owned(Type::RecursiveType(Rc::new(RecursiveType::new(
                self.location,
                (!self.type_vars.is_empty()).then(|| {
                    GenericsList::new_generics(
                        self.type_vars
                            .iter()
                            .enumerate()
                            .map(|(i, type_var_like)| match type_var_like {
                                TypeVarLike::TypeVar(type_var) => {
                                    callable(TypeVarLikeUsage::TypeVar(TypeVarUsage {
                                        type_var: type_var.clone(),
                                        index: i.into(),
                                        in_definition: self.location,
                                        temporary_matcher_id: 0,
                                    }))
                                }
                                TypeVarLike::TypeVarTuple(t) => {
                                    callable(TypeVarLikeUsage::TypeVarTuple(TypeVarTupleUsage {
                                        type_var_tuple: t.clone(),
                                        index: i.into(),
                                        in_definition: self.location,
                                        temporary_matcher_id: 0,
                                    }))
                                }
                                TypeVarLike::ParamSpec(p) => {
                                    callable(TypeVarLikeUsage::ParamSpec(ParamSpecUsage {
                                        param_spec: p.clone(),
                                        index: i.into(),
                                        in_definition: self.location,
                                        temporary_matcher_id: 0,
                                    }))
                                }
                            })
                            .collect(),
                    )
                }),
            ))));
        }
        let type_ = self.type_if_valid();
        if self.type_vars.is_empty() {
            Cow::Borrowed(type_)
        } else {
            let replaced = type_.replace_type_var_likes(db, &mut |u| Some(callable(u)));
            replaced
                .map(Cow::Owned)
                .unwrap_or_else(|| Cow::Borrowed(type_))
        }
    }
}

impl fmt::Debug for Database {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        f.debug_struct("Database")
            .field("file_count", &self.files.len())
            .finish()
    }
}

pub struct Database {
    in_use: bool,
    pub vfs: Box<dyn Vfs>,
    file_state_loaders: FileStateLoaders,
    pub files: InsertOnlyVec<dyn FileState>,
    pub workspaces: Workspaces,
    in_memory_files: HashMap<Box<str>, FileIndex>,

    pub python_state: PythonState,
    pub project: PythonProject,
}

impl Database {
    pub fn new(file_state_loaders: FileStateLoaders, options: ProjectOptions) -> Self {
        let vfs = Box::<FileSystemReader>::default();

        let project = PythonProject {
            sys_path: sys_path::create_sys_path(&options.settings),
            settings: options.settings,
            flags: options.flags,
            overrides: options.overrides,
        };

        let mut workspaces = Workspaces::default();
        for p in project.settings.mypy_path.iter() {
            workspaces.add(
                vfs.as_ref(),
                file_state_loaders.as_ref(),
                p.clone(),
                WorkspaceKind::TypeChecking,
            );
        }

        // Theoretically according to PEP 561 (Distributing and Packaging Type Information), this
        // should be last, but for now this should be good enough.
        for p in [
            "/home/dave/source/rust/zuban/typeshed/stdlib",
            "/home/dave/source/rust/zuban/typeshed/stubs/mypy-extensions",
        ] {
            workspaces.add(
                vfs.as_ref(),
                file_state_loaders.as_ref(),
                p.into(),
                WorkspaceKind::Typeshed,
            )
        }

        for p in &project.sys_path {
            workspaces.add(
                vfs.as_ref(),
                file_state_loaders.as_ref(),
                p.clone().into(),
                WorkspaceKind::SitePackages,
            )
        }

        let mut this = Self {
            in_use: false,
            vfs,
            file_state_loaders,
            files: Default::default(),
            workspaces,
            in_memory_files: Default::default(),
            python_state: PythonState::reserve(),
            project,
        };
        this.generate_python_state();
        this
    }

    pub fn try_to_reuse_project_resources_for_tests(
        &self,
        file_state_loaders: FileStateLoaders,
        options: ProjectOptions,
    ) -> Self {
        let project = PythonProject {
            sys_path: sys_path::create_sys_path(&options.settings),
            settings: options.settings,
            flags: options.flags,
            overrides: options.overrides,
        };
        let files = InsertOnlyVec::<dyn FileState>::default();
        let mut workspaces = self.workspaces.clone_with_new_rcs();
        for file_state in unsafe { self.files.iter() } {
            fn search_parent(
                workspaces: &Workspaces,
                parent: Parent,
                name: &str,
            ) -> DirectoryEntry {
                let tmp;
                let parent_dir = match parent {
                    Parent::Directory(dir) => {
                        tmp = dir.upgrade().unwrap();
                        &tmp
                    }
                    Parent::Workspace(w_name) => {
                        &workspaces
                            .iter()
                            .find(|workspace| *workspace.root_path() == **w_name)
                            .unwrap()
                            .directory
                    }
                };
                let x = parent_dir.search(name).unwrap().clone();
                x
            }
            fn replace_from_new_workspace(workspaces: &Workspaces, parent: &Parent) -> Parent {
                match parent {
                    Parent::Directory(dir) => {
                        let dir = dir.upgrade().unwrap();
                        let replaced = replace_from_new_workspace(workspaces, &dir.parent);
                        let search = search_parent(workspaces, replaced, &dir.name);
                        let DirectoryEntry::Directory(new_dir) = search else {
                            unreachable!();
                        };
                        Parent::Directory(Rc::downgrade(&new_dir))
                    }
                    Parent::Workspace(_) => parent.clone(),
                }
            }
            let current_entry = file_state.file_entry();
            let parent_dir = replace_from_new_workspace(&workspaces, &current_entry.parent);
            let DirectoryEntry::File(new_file_entry) =
                search_parent(&workspaces, parent_dir, &current_entry.name)
            else {
                unreachable!()
            };
            //debug_assert_ne!(new_file_entry.as_ref() as *const _, current_entry.as_ref() as *const _);
            files.push(file_state.clone_box(new_file_entry.clone()));
        }

        let mut mypy_path_iter = project.settings.mypy_path.iter();
        assert_eq!(
            mypy_path_iter.next_back().map(|p| p.as_str()),
            Some("/mypylike/"),
            "{:?}",
            project.settings.mypy_path
        );
        for p in mypy_path_iter.rev() {
            workspaces.add_at_start(
                self.vfs.as_ref(),
                file_state_loaders.as_ref(),
                p.clone(),
                WorkspaceKind::TypeChecking,
            )
        }
        for p in &project.sys_path {
            workspaces.add(
                self.vfs.as_ref(),
                file_state_loaders.as_ref(),
                p.clone().into(),
                WorkspaceKind::SitePackages,
            )
        }

        let mut python_state = self.python_state.clone();
        let set_pointer = |pointer_ref: &mut *const PythonFile, name, is_package| {
            for (i, file_state) in unsafe { files.iter() }.enumerate() {
                let entry = file_state.file_entry();
                if is_package
                    && entry
                        .parent
                        .maybe_dir()
                        .is_ok_and(|dir| dir.name.as_ref() == name)
                    || !is_package && entry.name.as_ref() == name
                {
                    *pointer_ref = file_state
                        .file(&*self.vfs)
                        .unwrap()
                        .as_any()
                        .downcast_ref()
                        .unwrap();
                    debug_assert!(i < 12);
                    return;
                }
            }
            unreachable!()
        };
        set_pointer(&mut python_state.builtins, "builtins.pyi", false);
        set_pointer(&mut python_state.typing, "typing.pyi", false);
        // Since those files are loaded in the beginning, we can just match against that and the
        // first __init__.pyi will automaticall be the typeshed module
        set_pointer(&mut python_state.typeshed, "_typeshed", true);
        set_pointer(&mut python_state.collections, "collections", true);
        set_pointer(
            &mut python_state._collections_abc,
            "_collections_abc.pyi",
            false,
        );
        set_pointer(&mut python_state.types, "types.pyi", false);
        set_pointer(&mut python_state.abc, "abc.pyi", false);
        set_pointer(&mut python_state.functools, "functools.pyi", false);
        set_pointer(&mut python_state.enum_file, "enum.pyi", false);
        set_pointer(&mut python_state.dataclasses_file, "dataclasses.pyi", false);
        set_pointer(
            &mut python_state.typing_extensions,
            "typing_extensions.pyi",
            false,
        );
        set_pointer(
            &mut python_state.mypy_extensions,
            "mypy_extensions.pyi",
            false,
        );
        let db = Self {
            in_use: false,
            vfs: Box::<FileSystemReader>::default(),
            file_state_loaders,
            files,
            workspaces,
            in_memory_files: Default::default(),
            python_state,
            project,
        };
        if db.project.flags.disable_bytearray_promotion {
            db.python_state
                .bytearray()
                .class_storage
                .promote_to
                .set(None);
        }
        if db.project.flags.disable_memoryview_promotion {
            db.python_state
                .memoryview()
                .class_storage
                .promote_to
                .set(None);
        }
        db
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

    pub fn loaded_file(&self, index: FileIndex) -> &(dyn File + 'static) {
        let state = self.file_state(index);
        let f = state
            .file(&*self.vfs)
            .unwrap_or_else(|| panic!("file #{index}: {}", state.path()));
        f
    }

    fn loader(&self, path: &str) -> Option<&dyn FileStateLoader> {
        for loader in self.file_state_loaders.iter() {
            let extension = Path::new(path).extension().and_then(|e| e.to_str());
            if let Some(e) = extension {
                if loader.responsible_for_file_endings().contains(&e) {
                    return Some(loader.as_ref());
                }
            } else if Path::new(path)
                .file_name()
                .is_some_and(|n| n.to_str() == Some("__main__"))
            {
                return Some(&PythonFileLoader {});
            }
        }
        None
    }

    fn with_add_file_state(
        &self,
        add: impl FnOnce(FileIndex) -> Pin<Box<dyn FileState>>,
    ) -> FileIndex {
        let file_index = FileIndex(self.files.len() as u32);
        self.files.push(add(file_index));
        file_index
    }

    pub fn load_sub_file(
        &self,
        super_file: &PythonFile,
        add: impl FnOnce(FileIndex) -> PythonFile,
    ) -> &PythonFile {
        let index = self.with_add_file_state(|file_index| {
            Box::pin(LanguageFileState::new_parsed(
                self.file_state(super_file.file_index).file_entry().clone(),
                "".into(),
                add(file_index),
                self.file_state(super_file.file_index)
                    .invalidate_invalidates_db(),
            ))
        });
        self.loaded_python_file(index)
    }

    pub fn load_file_from_workspace(
        &self,
        file_entry: Rc<FileEntry>,
        invalidates_db: bool,
    ) -> Option<FileIndex> {
        // A loader should be available for all files in the workspace.
        let path = file_entry.path(&*self.vfs);
        let loader = self.loader(&path)?;
        let file_index = match self.vfs.read_file(&path) {
            Ok(code) => self.with_add_file_state(|file_index| {
                loader.load_parsed(
                    &self.project,
                    file_index,
                    file_entry.clone(),
                    path.into(),
                    code.into(),
                    invalidates_db,
                )
            }),
            Err(err) => {
                debug!("Tried to load file, but failed: {err}");
                return None;
            }
        };
        file_entry.file_index.set(file_index);
        Some(file_index)
    }

    pub fn load_in_memory_file(&mut self, path: Box<str>, code: Box<str>) -> FileIndex {
        let ensured = self
            .workspaces
            .ensure_file(&self.project.flags, &*self.vfs, &path);

        let in_mem_file = self.in_memory_file(&path);
        debug_assert!(
            in_mem_file.is_none()
                || in_mem_file.is_some() && ensured.file_entry.file_index.get().is_some(),
            "{path}; in_mem_file: {in_mem_file:?}; ensured file_index: {:?}",
            ensured.file_entry.file_index.get(),
        );

        let in_mem_file = in_mem_file.or_else(|| {
            let file_index = ensured.file_entry.file_index.get()?;
            self.in_memory_files.insert(path.clone(), file_index);
            Some(file_index)
        });
        if let Some(file_index) = in_mem_file {
            self.unload_file_and_maybe_workspace_part(file_index, false);
        }

        // TODO there could be no loader...
        let loader = self.loader(&path).unwrap();
        let new_file_state = |file_index| {
            loader.load_parsed(
                &self.project,
                file_index,
                ensured.file_entry.clone(),
                path.clone(),
                code,
                false,
            )
        };
        let file_index = if let Some(file_index) = in_mem_file {
            self.files
                .set(file_index.0 as usize, new_file_state(file_index));
            debug_assert!(ensured.file_entry.file_index.get().is_some(), "for {path}");
            file_index
        } else {
            let file_index = self.with_add_file_state(new_file_state);
            self.in_memory_files.insert(path.clone(), file_index);
            ensured.set_file_index(file_index);
            file_index
        };
        if cfg!(feature = "zuban_debug") {
            for invalidation in &ensured.invalidations.iter() {
                let p = self.file_state_mut(*invalidation).path();
                debug!("Invalidate {p} because we're loading {path}");
            }
        }
        self.invalidate_files(file_index, ensured.invalidations);
        file_index
    }

    pub fn in_memory_file(&mut self, path: &str) -> Option<FileIndex> {
        self.in_memory_files.get(path).cloned()
    }

    fn unload_file(&mut self, file_index: FileIndex) {
        self.unload_file_and_maybe_workspace_part(file_index, true)
    }

    fn unload_file_and_maybe_workspace_part(
        &mut self,
        file_index: FileIndex,
        maybe_workspace: bool,
    ) {
        let file_state = &mut self.files[file_index.0 as usize];
        if maybe_workspace {
            self.workspaces
                .unload_file(&self.project.flags, &*self.vfs, file_state.path());
        }
        let invalidations = file_state
            .unload_and_return_invalidations()
            .expect("We don't support rebuilding/unloading after changing of typeshed, yet.");
        self.invalidate_files(file_index, invalidations)
    }

    fn invalidate_files(&mut self, original_file_index: FileIndex, invalidations: Invalidations) {
        for invalid_index in invalidations.into_iter() {
            let file_state = self.file_state_mut(invalid_index);
            let Some(invalidations) = file_state.take_invalidations() else {
                // None here means that the file was created with `invalidates_db = true`, which
                // means we have to invalidate the whole database.
                debug!(
                    "Invalidate whole db because we have invalidated {}",
                    self.file_state(invalid_index).path()
                );
                self.invalidate_db();
                return;
            };
            if let Some(file) = file_state.maybe_loaded_file_mut() {
                file.invalidate_references_to(original_file_index);
            }

            if cfg!(feature = "zuban_debug") {
                for invalidation in &invalidations.iter() {
                    let p = self.file_state(*invalidation).path();
                    debug!(
                        "Invalidate {p} because we have invalidated {}",
                        self.file_state(invalid_index).path()
                    );
                }
            }
            self.invalidate_files(original_file_index, invalidations);
        }
    }

    fn invalidate_db(&mut self) {
        for file_state in self.files.iter_mut() {
            if let Some(file) = file_state.maybe_loaded_file_mut() {
                if file.has_super_file() {
                    file_state.unload_and_return_invalidations();
                } else {
                    file.invalidate_full_db(&self.project);
                }
            }
        }
        self.python_state = PythonState::reserve();
        self.generate_python_state();
    }

    pub fn add_invalidates(&self, file: FileIndex, invalidates: FileIndex) {
        self.file_state(file).add_invalidates(invalidates)
    }

    pub fn delete_directory(&mut self, mut dir_path: &str) -> Result<(), String> {
        if let Some(p) = dir_path.strip_suffix('/') {
            dir_path = p;
        }

        let in_mem_paths: Vec<_> = self
            .in_memory_files
            .iter()
            .filter_map(|(path, _)| {
                let matches = path.starts_with(dir_path)
                    && path
                        .as_bytes()
                        .get(dir_path.len())
                        .is_some_and(|chr| *chr == self.vfs.separator_u8());
                matches.then_some(path.clone())
            })
            .collect();
        for path in in_mem_paths {
            self.unload_in_memory_file(&path);
        }
        self.workspaces
            .delete_directory(&self.project.flags, &*self.vfs, dir_path)
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
        for (_path, file_index) in in_memory_files.into_iter() {
            self.unload_file(file_index);
        }
    }

    fn preload_typeshed_stub(&self, dir: &Directory, file_name: &'static str) -> &PythonFile {
        let entry = dir.search(file_name).unwrap().clone();
        let DirectoryEntry::File(file_entry) = &entry else {
            panic!(
                "It seems like you are using directories in typeshed for {}: {file_name}",
                dir.path(&*self.vfs, true)
            )
        };
        let file_index = file_entry.file_index.get().unwrap_or_else(|| {
            self.load_file_from_workspace(file_entry.clone(), true)
                .unwrap()
        });
        debug!("Preloaded typeshed stub {file_name} as #{}", file_index.0);
        self.loaded_python_file(file_index)
    }

    pub fn loaded_python_file(&self, index: FileIndex) -> &PythonFile {
        self.loaded_file(index).as_any().downcast_ref().unwrap()
    }

    fn generate_python_state(&mut self) {
        // TODO this is wrong, because it's just a random dir...
        let mut dirs = self.workspaces.directories_not_type_checked();
        let stdlib_dir = dirs.next().unwrap();
        let mypy_extensions_dir = dirs.next().unwrap();
        let collections_dir = match &*stdlib_dir.search("collections").unwrap() {
            DirectoryEntry::Directory(c) => c.clone(),
            _ => unreachable!(),
        };
        let typeshed_dir = match &*stdlib_dir.search("_typeshed").unwrap() {
            DirectoryEntry::Directory(c) => c.clone(),
            _ => unreachable!(),
        };
        drop(dirs);

        let builtins = self.preload_typeshed_stub(stdlib_dir, "builtins.pyi") as *const _;
        let typing = self.preload_typeshed_stub(stdlib_dir, "typing.pyi") as *const _;
        let typeshed = self.preload_typeshed_stub(&typeshed_dir, "__init__.pyi") as *const _;
        let types = self.preload_typeshed_stub(stdlib_dir, "types.pyi") as *const _;
        let abc = self.preload_typeshed_stub(stdlib_dir, "abc.pyi") as *const _;
        let functools = self.preload_typeshed_stub(stdlib_dir, "functools.pyi") as *const _;
        let enum_file = self.preload_typeshed_stub(stdlib_dir, "enum.pyi") as *const _;
        let dataclasses_file =
            self.preload_typeshed_stub(stdlib_dir, "dataclasses.pyi") as *const _;
        let typing_extensions =
            self.preload_typeshed_stub(stdlib_dir, "typing_extensions.pyi") as *const _;
        let mypy_extensions =
            self.preload_typeshed_stub(mypy_extensions_dir, "mypy_extensions.pyi") as *const _;

        let collections = self.preload_typeshed_stub(&collections_dir, "__init__.pyi") as *const _;
        let _collections_abc =
            self.preload_typeshed_stub(stdlib_dir, "_collections_abc.pyi") as *const _;

        PythonState::initialize(
            self,
            builtins,
            typing,
            typeshed,
            collections,
            _collections_abc,
            types,
            abc,
            functools,
            enum_file,
            dataclasses_file,
            typing_extensions,
            mypy_extensions,
        );
    }
}

pub struct PythonProject {
    pub sys_path: Vec<Box<str>>,
    pub settings: Settings,
    pub flags: TypeCheckerFlags,
    pub(crate) overrides: Vec<OverrideConfig>,
    // is_django: bool,  // TODO maybe add?
}

impl PythonProject {
    pub fn strict_optional_partials(&self) -> bool {
        // Mypy is currently just replacing the nullable partial to a non-nullable one.
        self.settings.mypy_compatible
    }
}

#[derive(Debug, PartialEq, Eq, Clone, Copy)]
pub enum ParentScope {
    Module,
    Function(NodeIndex),
    Class(NodeIndex),
}

impl ParentScope {
    pub fn qualified_name(self, db: &Database, defined_at: NodeRef, name: &str) -> String {
        let file = defined_at.file;
        match self {
            ParentScope::Module => format!("{}.{name}", file.qualified_name(db)),
            ParentScope::Class(node_index) => {
                let parent_class = Class::with_undefined_generics(NodeRef::new(file, node_index));
                format!("{}.{}", parent_class.qualified_name(db), name)
            }
            ParentScope::Function(_) => {
                let line = file.byte_to_line_column(defined_at.node_start_position()).0;
                // Add the position like `foo.Bar@7`
                format!("{}.{name}@{line}", file.qualified_name(db))
            }
        }
    }
}

#[derive(Debug, Clone)]
pub struct ClassStorage {
    pub class_symbol_table: SymbolTable,
    pub self_symbol_table: SymbolTable,
    pub abstract_attributes: Box<[NodeIndex]>,
    pub parent_scope: ParentScope,
    pub promote_to: Cell<Option<PointLink>>,
    pub slots: Option<Box<[StringSlice]>>,
}

#[derive(Debug, Clone, Copy, PartialEq)]
pub enum MetaclassState {
    None,
    Unknown,
    Some(PointLink),
}

#[derive(Debug, Clone, Copy, PartialEq)]
pub enum ClassKind {
    Normal,
    Protocol,
    Enum,
    TypedDict,
    Tuple,
    NamedTuple,
}

#[derive(Debug, Clone, PartialEq)]
pub struct BaseClass {
    pub type_: Type,
    pub is_direct_base: bool,
}

#[derive(Debug, Clone, Copy, PartialEq)]
pub struct ProtocolMember {
    pub name_index: NodeIndex,
    pub is_abstract: bool,
    pub variance: Variance,
}

#[derive(Debug, Clone, PartialEq)]
pub struct ClassInfos {
    pub mro: Box<[BaseClass]>, // Does never include `object`
    pub metaclass: MetaclassState,
    pub class_kind: ClassKind,
    pub incomplete_mro: bool,
    pub protocol_members: Box<[ProtocolMember]>,
    pub has_slots: bool,
    pub is_final: bool,
    pub total_ordering: bool,
    pub is_runtime_checkable: bool,
    pub abstract_attributes: Box<[PointLink]>,
    pub dataclass_transform: Option<Box<DataclassTransformObj>>,
    // We have this less for caching and more to be able to have different types.
    pub undefined_generics_type: OnceCell<Rc<Type>>,
}

impl ClassInfos {
    pub fn metaclass<'db>(&self, db: &'db Database) -> Class<'db> {
        match self.metaclass {
            MetaclassState::Some(link) => Class::from_non_generic_link(db, link),
            _ => db.python_state.bare_type_class(),
        }
    }
}

impl std::cmp::PartialEq for ClassStorage {
    fn eq(&self, _other: &Self) -> bool {
        unreachable!("Should never happen with classes")
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    #[test]
    fn test_sizes() {
        use std::mem::size_of;

        use crate::type_::{ClassGenerics, StringSlice, Tuple, UnionType};
        assert_eq!(size_of::<ClassGenerics>(), 24);
        assert_eq!(size_of::<UnionType>(), 16);
        assert_eq!(size_of::<Tuple>(), 88);
        assert_eq!(size_of::<Type>(), 40); // TODO Would like it to be 32, but ClassGenerics is 24
        assert_eq!(size_of::<ComplexPoint>(), size_of::<Type>());
        assert_eq!(size_of::<ClassStorage>(), 152);
        assert_eq!(size_of::<ClassInfos>(), 88);
        assert_eq!(size_of::<PointLink>(), 8);
        assert_eq!(size_of::<StringSlice>(), 12);
    }

    #[test]
    fn point_masks_are_big_enough() {
        let max_specific_kinds = 1 << SPECIFIC_MASK.count_ones();
        let max_locality_kinds = 1 << LOCALITY_MASK.count_ones();
        let max_point_kinds = 1 << KIND_MASK.count_ones();
        assert_eq!(max_specific_kinds, 256);
        assert_eq!(max_locality_kinds, 8);
        assert_eq!(max_point_kinds, 8);
    }

    #[test]
    fn test_empty_point() {
        let p = Point::new_specific(Specific::ReservedBecauseUnused, Locality::NameBinder);
        assert_eq!(p.flags & !IS_ANALIZED_MASK, 0, "{p:?}");
        assert_eq!(p.node_index, 0);
        assert!(p.calculated());
        assert_eq!(p.kind(), PointKind::Specific);
        assert_eq!(p.specific(), Specific::ReservedBecauseUnused);
    }
}
