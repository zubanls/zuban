use std::{
    borrow::Cow,
    cell::{Cell, OnceCell, RefCell},
    fmt, mem,
    ops::Range,
    rc::Rc,
};

use config::{OverrideConfig, Settings};
use parsa_python_cst::NodeIndex;
use utils::InsertOnlyVec;
use vfs::{
    Directory, DirectoryEntry, FileEntry, FileIndex, InvalidationResult, LocalFS, Parent, Vfs,
    VfsHandler, WorkspaceKind, Workspaces,
};

use crate::{
    debug,
    file::{File, PythonFile},
    node_ref::NodeRef,
    python_state::PythonState,
    sys_path,
    type_::{
        CallableContent, DataclassTransformObj, FunctionKind, FunctionOverload, GenericItem,
        GenericsList, NewType, ParamSpecUsage, RecursiveType, StringSlice, Type, TypeVarLike,
        TypeVarLikeUsage, TypeVarLikes, TypeVarTupleUsage, TypeVarUsage, TypedDict, Variance,
    },
    type_helpers::{Class, Function},
    utils::SymbolTable,
    ProjectOptions, TypeCheckerFlags,
};

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
            .field("file_count", &self.vfs.files.len())
            .finish()
    }
}

pub struct Database {
    pub vfs: Vfs<PythonFile>,
    pub python_state: PythonState,
    pub project: PythonProject,
}

impl Database {
    pub fn new(vfs_handler: Box<dyn VfsHandler>, options: ProjectOptions) -> Self {
        let project = PythonProject {
            sys_path: sys_path::create_sys_path(&options.settings),
            settings: options.settings,
            flags: options.flags,
            overrides: options.overrides,
        };

        let mut vfs = Vfs::new(vfs_handler);

        for p in project.settings.mypy_path.iter() {
            vfs.add_workspace(p.clone(), WorkspaceKind::TypeChecking);
        }

        // Theoretically according to PEP 561 (Distributing and Packaging Type Information), this
        // should be last, but for now this should be good enough.
        for p in [
            "/home/dave/source/rust/zuban/typeshed/stdlib",
            "/home/dave/source/rust/zuban/typeshed/stubs/mypy-extensions",
        ] {
            vfs.add_workspace(p.into(), WorkspaceKind::Typeshed)
        }

        for p in &project.sys_path {
            vfs.add_workspace(p.clone().into(), WorkspaceKind::SitePackages)
        }

        let mut this = Self {
            vfs,
            python_state: PythonState::reserve(),
            project,
        };
        this.generate_python_state();
        this
    }

    pub fn try_to_reuse_project_resources_for_tests(&self, options: ProjectOptions) -> Self {
        let project = PythonProject {
            sys_path: sys_path::create_sys_path(&options.settings),
            settings: options.settings,
            flags: options.flags,
            overrides: options.overrides,
        };
        let files = InsertOnlyVec::default();
        let mut workspaces = self.vfs.workspaces.clone_with_new_rcs();
        for file_state in unsafe { self.vfs.files.iter() } {
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
            workspaces.add_at_start(&*self.vfs.handler, p.clone(), WorkspaceKind::TypeChecking)
        }
        for p in &project.sys_path {
            workspaces.add(
                &*self.vfs.handler,
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
                    *pointer_ref = file_state.file().unwrap();
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
            vfs: Vfs {
                handler: Box::new(LocalFS::without_watcher()),
                files,
                workspaces,
                in_memory_files: Default::default(),
            },
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

    pub fn file_path(&self, index: FileIndex) -> &str {
        self.vfs.file_path(index)
    }

    pub fn load_sub_file(
        &self,
        super_file: &PythonFile,
        add: impl FnOnce(&str, FileIndex) -> PythonFile,
    ) -> &PythonFile {
        let index = self.vfs.create_sub_file(super_file.file_index, add);
        self.loaded_python_file(index)
    }

    pub fn load_file_from_workspace(
        &self,
        file_entry: Rc<FileEntry>,
        invalidates_db: bool,
    ) -> Option<FileIndex> {
        self.vfs.load_file_from_workspace(
            file_entry.clone(),
            invalidates_db,
            |file_index, path, code| {
                PythonFile::from_path_and_code(
                    &self.project,
                    file_index,
                    &file_entry,
                    path,
                    code.into(),
                )
            },
        )
    }

    pub fn load_in_memory_file(&mut self, path: Box<str>, code: Box<str>) -> FileIndex {
        let (file_index, invalidation) = self.vfs.load_in_memory_file(
            self.project.flags.case_sensitive,
            path,
            code,
            |file_index, file_entry, path, new_code| {
                PythonFile::from_path_and_code(
                    &self.project,
                    file_index,
                    file_entry,
                    path,
                    new_code,
                )
            },
        );
        self.handle_invalidation(invalidation);
        file_index
    }

    fn handle_invalidation(&mut self, invalidation_result: InvalidationResult) {
        if invalidation_result == InvalidationResult::InvalidatedDb {
            self.invalidate_db();
        }
    }

    fn invalidate_db(&mut self) {
        for file_state in self.vfs.files.iter_mut() {
            if let Some(file) = file_state.file_mut() {
                if file.has_super_file() {
                    file_state.unload();
                } else {
                    file.invalidate_full_db(&self.project);
                }
            }
        }
        self.python_state = PythonState::reserve();
        self.generate_python_state();
    }

    pub fn delete_directory_of_in_memory_files(&mut self, dir_path: &str) -> Result<(), String> {
        let invalidation = self.vfs.delete_in_memory_files_directory(
            self.project.flags.case_sensitive,
            dir_path,
            |file_state, file_index, new_code| {
                PythonFile::from_path_and_code(
                    &self.project,
                    file_index,
                    &file_state.file_entry(),
                    file_state.path(),
                    new_code,
                )
            },
        )?;
        Ok(self.handle_invalidation(invalidation))
    }

    pub fn unload_in_memory_file(&mut self, path: &str) -> Result<(), &'static str> {
        let result = self.vfs.unload_in_memory_file(
            self.project.flags.case_sensitive,
            path,
            |file_state, file_index, new_code| {
                PythonFile::from_path_and_code(
                    &self.project,
                    file_index,
                    &file_state.file_entry(),
                    file_state.path(),
                    new_code,
                )
            },
        )?;
        Ok(self.handle_invalidation(result))
    }

    pub fn unload_all_in_memory_files(&mut self) {
        let result = self
            .vfs
            .unload_all_in_memory_files(self.project.flags.case_sensitive);
        self.handle_invalidation(result);
    }

    fn preload_typeshed_stub(&self, dir: &Directory, file_name: &'static str) -> &PythonFile {
        let entry = dir.search(file_name).unwrap().clone();
        let DirectoryEntry::File(file_entry) = &entry else {
            panic!(
                "It seems like you are using directories in typeshed for {}: {file_name}",
                dir.path(&*self.vfs.handler, true)
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
        self.vfs
            .file(index)
            .unwrap_or_else(|| panic!("file #{index}: {}", self.vfs.file_path(index)))
    }

    fn generate_python_state(&mut self) {
        // TODO this is wrong, because it's just a random dir...
        let mut dirs = self.vfs.workspaces.directories_not_type_checked();
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
