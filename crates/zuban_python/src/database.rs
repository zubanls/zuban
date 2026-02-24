use std::{
    borrow::Cow,
    cell::Cell,
    fmt, mem,
    ops::Range,
    sync::{Arc, Mutex, OnceLock, RwLock, Weak},
};

use config::{FinalizedTypeCheckerFlags, OverrideConfig, Settings};
use parsa_python_cst::{NodeIndex, Tree};
use rayon::prelude::*;
use vfs::{
    AbsPath, DirOrFile, Directory, DirectoryEntry, Entries, FileEntry, FileIndex,
    InvalidationResult, LocalFS, NormalizedPath, PathWithScheme, Vfs, VfsFile as _, VfsHandler,
    Workspace, WorkspaceKind,
};

use crate::{
    ProjectOptions, debug,
    file::{ClassNodeRef, File, PythonFile, SuperFile},
    lines::split_lines,
    node_ref::NodeRef,
    python_state::PythonState,
    recoverable_error, sys_path,
    type_::{
        CallableContent, DataclassTransformObj, FunctionKind, FunctionOverload, GenericItem,
        GenericsList, ParamSpecUsage, RecursiveType, ReplaceTypeVarLikes, StringSlice, Type,
        TypeVarLike, TypeVarLikeUsage, TypeVarLikes, TypeVarName, TypeVarTupleUsage, TypeVarUsage,
        TypedDict, Variance,
    },
    type_helpers::{Class, Function},
    utils::SymbolTable,
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

pub type DeferredTypedDictMembers = (Arc<TypedDict>, TypedDictArgs);

#[derive(Copy, Clone, Eq, PartialEq, Default)]
pub(crate) struct Point {
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

    pub fn new_first_name_of_name_def(
        node_index: NodeIndex,
        in_global_scope: bool,
        locality: Locality,
    ) -> Self {
        Self {
            node_index,
            flags: Self::calculate_flags(
                PointKind::Specific,
                Specific::FirstNameOfNameDef as u32,
                locality,
            ),
        }
        .with_in_global_scope(in_global_scope)
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

    pub fn with_changed_node_index(mut self, node_index: NodeIndex) -> Self {
        if cfg!(debug_assertions) {
            // Make sure node_index is accessible
            self.node_index();
        }
        self.node_index = node_index;
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

    pub fn can_be_redefined(self) -> bool {
        // This is intentionally an alias for now, because it's not guarantueed that this will
        // always match in the future and in this way we can quickly find the origins.
        self.needs_flow_analysis()
    }

    pub fn calculated(self) -> bool {
        (self.flags & IS_ANALIZED_MASK) != 0
    }

    pub fn calculating(self) -> bool {
        self.flags == Specific::Calculating as u32
    }

    pub fn in_global_scope(self) -> bool {
        debug_assert!(self.calculated());
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
                    Some(
                        Specific::NameOfNameDef
                            | Specific::FirstNameOfNameDef
                            | Specific::Parent
                            | Specific::Analyzed
                    )
                )
        );
        self.node_index
    }

    pub fn is_name_of_name_def_like(self) -> bool {
        matches!(
            self.maybe_specific(),
            Some(Specific::NameOfNameDef | Specific::FirstNameOfNameDef)
        )
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

    pub fn maybe_file_reference(self) -> Option<FileIndex> {
        (self.kind() == PointKind::FileReference).then(|| self.file_index())
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
pub(crate) struct Points(Vec<Cell<Point>>);

// Points are guarded by specific logic and if they are overwritten by something that shouldn't it
// should not be that tragic.
unsafe impl Sync for Points {}

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

    pub fn invalidate_references_to(&mut self, file_index: Option<FileIndex>) {
        for cell in &self.0 {
            let locality = cell.get().locality();
            if locality == Locality::DirectExtern && Some(cell.get().file_index()) == file_index {
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

pub(crate) struct PointsBackup {
    pub range: Range<NodeIndex>,
    points: Vec<Cell<Point>>,
}

#[derive(Debug, PartialEq, Eq)]
#[repr(u32)]
pub(crate) enum PointKind {
    Specific,
    Complex,
    Redirect,
    FileReference,
}

#[derive(Debug, PartialEq, Eq, Clone, Copy)]
#[repr(u32)]
pub(crate) enum Specific {
    // This is reserved, because if everything is initialized as zero, this is the value it takes.
    #[allow(dead_code)]
    ReservedBecauseUnused,

    Analyzed, // Signals that a node has been analyzed
    Calculating,
    Cycle,
    FirstNameOfNameDef, // Cycles for the same name definition in e.g. different branches
    NameOfNameDef,      // Cycles for the same name definition in e.g. different branches
    Parent,             // Has a link to the parent scope
    FunctionEndIsUnreachable,
    OverloadUnreachable,
    AnyDueToError,
    InvalidTypeDefinition,
    ModuleNotFound,
    PyTypedMissing,
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
    TypingTypeAliasType,
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
    TypingReadOnly,
    TypingTypeGuard,
    TypingTypeIs,
    TypingTypeForm,
    RevealTypeFunction,
    AssertTypeFunction,
    TypingNamedTuple,      // typing.NamedTuple
    CollectionsNamedTuple, // collections.namedtuple
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

    pub fn might_be_used_in_alias(self) -> bool {
        matches!(
            self,
            Specific::TypingTuple
                | Specific::TypingCallable
                | Specific::TypingType
                | Specific::TypingUnion
                | Specific::TypingOptional
                | Specific::TypingAnnotated
                | Specific::TypingLiteral
                | Specific::TypingLiteralString
                | Specific::TypingSelf
                | Specific::TypingAny
                | Specific::TypingNeverOrNoReturn
                | Specific::BuiltinsType
        )
    }

    pub fn is_annotation_or_type_comment(self) -> bool {
        matches!(
            self,
            Specific::AnnotationOrTypeCommentSimpleClassInstance
                | Specific::AnnotationOrTypeCommentWithoutTypeVars
                | Specific::AnnotationOrTypeCommentWithTypeVars
                | Specific::AnnotationOrTypeCommentClassVar
                | Specific::AnnotationOrTypeCommentFinal
        )
    }
}

#[derive(Debug, PartialEq, Eq, Clone, Copy)]
#[repr(u32)]
pub(crate) enum Locality {
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

#[derive(Debug, Copy, Clone, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub(crate) struct PointLink {
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
pub(crate) struct LocalityLink {
    pub file: FileIndex,
    pub node_index: NodeIndex,
    pub locality: Locality,
}

impl LocalityLink {
    #[expect(dead_code)]
    pub fn into_point_redirect(self) -> Point {
        Point::new_redirect(self.file, self.node_index, self.locality)
    }
}

#[derive(Debug)]
pub(crate) struct PartialFlags {
    pub nullable: bool,
    pub reported_error: bool,
    pub finished: bool,
}

// This is a core data structure and it should be kept as small as possible, because it's used in
// arrays. It therefore uses a lot of Arcs.
#[derive(Debug, Clone, PartialEq)]
pub(crate) enum ComplexPoint {
    TypeInstance(Type),
    Class(Box<ClassStorage>),
    ClassInfos(Box<ClassInfos>),
    TypeVarLikes(TypeVarLikes),
    FunctionOverload(Box<OverloadDefinition>),
    // e.g. X = NamedTuple('X', []), does not include classes.
    NamedTupleDefinition(Arc<Type>),
    // e.g. X = TypedDict('X', {'x': int}), does not include classes.
    TypedDictDefinition(TypedDictDefinition),
    // Sometimes needed when a Final is defined in a class and initialized in __init__.
    IndirectFinal(Arc<Type>),
    WidenedType(Arc<WidenedType>),

    // Relevant for types only (not inference)
    TypeVarLike(TypeVarLike),
    TypeAlias(Box<TypeAlias>),
}

impl ComplexPoint {
    pub fn maybe_instance(&self) -> Option<&Type> {
        match self {
            Self::TypeInstance(t) => Some(t),
            Self::WidenedType(w) => w.original.maybe_instance(),
            Self::IndirectFinal(t) => Some(t),
            _ => None,
        }
    }
}

#[derive(Debug, Clone, PartialEq)]
pub(crate) struct OverloadImplementation {
    pub function_link: PointLink,
    pub callable: CallableContent,
}

impl OverloadImplementation {
    pub(crate) fn function<'db, 'class>(
        &self,
        db: &'db Database,
        class: Option<Class<'class>>,
    ) -> Function<'db, 'class> {
        Function::new(NodeRef::from_link(db, self.function_link), class)
    }
}

#[derive(Debug, Clone, PartialEq)]
pub(crate) struct OverloadDefinition {
    pub implementation: Option<OverloadImplementation>,
    pub functions: Arc<FunctionOverload>,
    pub is_final: bool,    // Had @final
    pub is_override: bool, // Had @override
    pub dataclass_transform: Option<DataclassTransformObj>,
}

impl OverloadDefinition {
    pub fn iter_functions(&self) -> impl Iterator<Item = &Arc<CallableContent>> {
        self.functions.iter_functions()
    }

    pub fn kind(&self) -> &FunctionKind {
        self.functions.kind()
    }
}

#[derive(Debug, Clone, PartialEq)]
pub(crate) struct WidenedType {
    pub original: ComplexPoint,
    pub widened: Type,
}

#[derive(Debug, Default, Clone)]
pub(super) struct TypedDictArgs {
    pub total: Option<bool>,
    pub extra_items: Option<NodeIndex>,
    pub closed: Option<bool>,
}

#[derive(Debug)]
pub(crate) struct TypedDictDefinition {
    pub type_: Arc<Type>,
    pub deferred_subclass_member_initializations: Box<RwLock<Vec<DeferredTypedDictMembers>>>,
    pub initialization_args: TypedDictArgs,
}

impl Clone for TypedDictDefinition {
    fn clone(&self) -> Self {
        Self {
            type_: self.type_.clone(),
            // This is probably not necessary, because cloning is only used for some optimizations
            // around tests, but we'll implement it anyway so people can count on a proper Clone in
            // the future.
            deferred_subclass_member_initializations: Box::new(RwLock::new(
                self.deferred_subclass_member_initializations
                    .read()
                    .unwrap()
                    .clone(),
            )),
            initialization_args: self.initialization_args.clone(),
        }
    }
}
impl PartialEq for TypedDictDefinition {
    fn eq(&self, other: &Self) -> bool {
        self.type_ == other.type_
    }
}

impl TypedDictDefinition {
    pub fn new(typed_dict: Arc<TypedDict>, initialization_args: TypedDictArgs) -> Self {
        Self {
            type_: Arc::new(Type::TypedDict(typed_dict)),
            deferred_subclass_member_initializations: Default::default(),
            initialization_args,
        }
    }

    pub fn typed_dict(&self) -> Arc<TypedDict> {
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
    type_: Arc<Type>,
    is_recursive: bool,
    is_annotated: bool, // e.g. X: TypeAlias = Annotated[int, "something"]
}

#[derive(Debug, PartialEq, Clone)]
enum TypeAliasState {
    Valid(CalculatedTypeAlias),
    Invalid,
}
#[derive(Debug, PartialEq, Clone)]
pub(crate) struct TypeAlias {
    pub type_vars: TypeVarLikes,
    pub location: PointLink,
    pub name: PointLink,
    pub from_type_syntax: bool, // `type X = int` or `X = TypeAlias(int)
    // The two attributes around is_recursive are calculated after the TypeAlias is
    // added to the DB.
    state: OnceLock<TypeAliasState>,
}

impl TypeAlias {
    pub fn new(
        type_vars: TypeVarLikes,
        location: PointLink,
        name: PointLink,
        from_type_syntax: bool,
    ) -> Self {
        Self {
            type_vars,
            location,
            name,
            from_type_syntax,
            state: OnceLock::new(),
        }
    }

    pub fn is_recursive(&self) -> bool {
        match self.state.get() {
            Some(TypeAliasState::Invalid) => unreachable!(),
            Some(TypeAliasState::Valid(a)) => a.is_recursive,
            // This can happen with invalid recursive aliases like type T[U: T] = T[Any]
            None => true,
        }
    }

    pub fn is_valid(&self) -> bool {
        !matches!(self.state.get().unwrap(), TypeAliasState::Invalid)
    }

    pub fn is_annotated(&self) -> bool {
        self.state.get().is_some_and(|s| match s {
            TypeAliasState::Valid(a) => a.is_annotated,
            TypeAliasState::Invalid => false,
        })
    }

    pub fn type_if_valid(&self) -> &Type {
        let Some(state) = self.state.get() else {
            recoverable_error!("Alias type access while still calculating should not happen");
            return &Type::ERROR;
        };
        match state {
            TypeAliasState::Invalid => {
                debug!("Recursive type loop with invalid recursive type");
                &Type::ERROR
            }
            TypeAliasState::Valid(a) => a.type_.as_ref(),
        }
    }

    pub fn calculating(&self) -> bool {
        self.state.get().is_none()
    }

    pub fn set_valid(&self, type_: Type, is_recursive: bool, is_annotated: bool) {
        self.state
            .set(TypeAliasState::Valid(CalculatedTypeAlias {
                type_: Arc::new(type_),
                is_recursive,
                is_annotated,
            }))
            .unwrap()
    }

    pub fn set_invalid(&self) {
        self.state.set(TypeAliasState::Invalid).unwrap()
    }

    pub fn name<'db>(&self, db: &'db Database) -> &'db str {
        NodeRef::from_link(db, self.name).as_code()
    }

    pub fn name_slice<'db>(&self, db: &'db Database) -> StringSlice {
        NodeRef::from_link(db, self.name).string_slice()
    }

    pub fn application_allowed(&self, db: &Database) -> bool {
        self.is_valid() && {
            let t = self.type_if_valid();
            matches!(t, Type::Class(_) | Type::TypedDict(_) | Type::Dataclass(_))
                || !db.mypy_compatible() && matches!(t, Type::Tuple(_))
        }
    }

    pub fn as_type_and_set_type_vars_any(&self, db: &Database) -> Type {
        if self.is_recursive() {
            return Type::RecursiveType(Arc::new(RecursiveType::new(
                self.location,
                (!self.type_vars.is_empty()).then(|| {
                    GenericsList::new_generics(
                        self.type_vars
                            .iter()
                            .map(|tv| tv.as_default_or_any_generic_item(db))
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
                    (t.in_definition() == self.location)
                        .then(|| t.as_default_or_any_generic_item(db))
                })
                .unwrap_or_else(|| type_.clone())
        }
    }

    pub fn replace_type_var_likes(
        &self,
        db: &Database,
        remove_recursive_wrapper: bool,
        callable: &mut impl FnMut(TypeVarLikeUsage) -> GenericItem,
    ) -> Cow<'_, Type> {
        if self.is_recursive() && !remove_recursive_wrapper {
            return Cow::Owned(Type::RecursiveType(Arc::new(RecursiveType::new(
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
            let replaced = type_
                .replace_type_var_likes_without_simplified_unions(db, &mut |u| Some(callable(u)));
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

#[derive(Copy, Clone, PartialEq, Eq, Hash)]
pub enum RunCause {
    TypeChecking,
    LanguageServer,
}

pub(crate) struct Database {
    pub vfs: Vfs<PythonFile>,
    pub python_state: PythonState,
    pub project: PythonProject,
    pub run_cause: RunCause,
    pub pytest_folder: RwLock<Option<Weak<Directory>>>,
}

impl Database {
    pub fn new(vfs_handler: Box<dyn VfsHandler>, options: ProjectOptions, cause: RunCause) -> Self {
        Self::new_internal(vfs_handler, options, cause, None)
    }

    pub fn new_internal(
        vfs_handler: Box<dyn VfsHandler>,
        options: ProjectOptions,
        run_cause: RunCause,
        recovery: Option<vfs::VfsPanicRecovery<Tree>>,
    ) -> Self {
        let project = PythonProject {
            sys_path: sys_path::create_sys_path(&*vfs_handler, &options.settings),
            settings: options.settings,
            flags: options.flags.finalize(),
            overrides: options.overrides,
        };

        let mut vfs = Vfs::new(vfs_handler);

        for p in project.settings.mypy_path.iter() {
            vfs.add_workspace(p.clone(), WorkspaceKind::TypeChecking);
        }

        // Theoretically according to PEP 561 (Distributing and Packaging Type Information), this
        // should be last, but for now this should be good enough.

        let typeshed_path = project
            .settings
            .typeshed_path
            .clone()
            .unwrap_or_else(sys_path::typeshed_path_from_executable);
        let sep = vfs.handler.separator();
        for p in [
            format!("{typeshed_path}{sep}stdlib"),
            format!("{typeshed_path}{sep}stubs{sep}mypy-extensions"),
        ] {
            vfs.add_workspace(
                vfs.handler
                    .unchecked_normalized_path(vfs.handler.unchecked_abs_path(&p)),
                WorkspaceKind::Typeshed,
            );
        }

        for (kind, p) in &project.sys_path {
            add_workspace_and_check_for_pth_files(&mut vfs, p.clone(), recovery.is_some(), *kind);
        }
        // This AbsPath is not really an absolute path, it's just a fallback so anything can be
        // part of it.
        vfs.add_workspace(
            vfs.handler
                .unchecked_normalized_path(vfs.handler.unchecked_abs_path("")),
            WorkspaceKind::Fallback,
        );

        if let Some(recovery) = recovery {
            vfs.load_panic_recovery(
                project.flags.case_sensitive,
                recovery,
                |index, file_entry, tree| PythonFile::new(&project, index, file_entry, tree),
            );
        }

        let mut this = Self {
            vfs,
            python_state: PythonState::reserve(),
            project,
            run_cause,
            pytest_folder: Default::default(),
        };

        this.generate_python_state();

        tracing::debug!(
            "Workspace base paths: {:?}",
            this.vfs
                .workspaces
                .iter()
                .map(|w| (w.kind, w.root_path()))
                .collect::<Vec<_>>()
        );
        this
    }

    pub fn from_recovery(
        vfs_handler: Box<dyn VfsHandler>,
        options: ProjectOptions,
        cause: RunCause,
        recovery: vfs::VfsPanicRecovery<Tree>,
    ) -> Self {
        Database::new_internal(vfs_handler, options, cause, Some(recovery))
    }

    pub fn try_to_reuse_project_resources_for_tests(&mut self, options: ProjectOptions) -> Self {
        let project = PythonProject {
            sys_path: sys_path::create_sys_path(&*self.vfs.handler, &options.settings),
            settings: options.settings,
            flags: options.flags.finalize(),
            overrides: options.overrides,
        };

        let mut mypy_path_iter = project.settings.mypy_path.iter().map(|p| &**p);
        assert!(
            mypy_path_iter.next_back().unwrap().contains("mypylike"),
            "{:?}",
            project.settings.mypy_path
        );
        let vfs = self
            .vfs
            .with_reused_test_resources(Box::new(LocalFS::without_watcher()), mypy_path_iter);
        let mut new_db = Self {
            vfs,
            python_state: self.python_state.clone(),
            run_cause: self.run_cause,
            project,
            pytest_folder: Default::default(),
        };

        for (kind, p1) in &new_db.project.sys_path {
            new_db.vfs.add_workspace(p1.clone(), *kind);
        }
        tracing::debug!(
            "Workspace base paths (for reused project): {:?}",
            new_db
                .vfs
                .workspaces
                .iter()
                .map(|w| (w.kind, w.root_path()))
                .collect::<Vec<_>>()
        );

        let mut set_pointer = |pointer_ref: &mut *const PythonFile, name, is_package| {
            for (i, file_state) in new_db.vfs.files.iter_mut().enumerate() {
                let entry = file_state.file_entry();
                if is_package
                    && entry
                        .parent
                        .maybe_dir()
                        .is_ok_and(|dir| dir.name.as_ref() == name)
                    || !is_package && entry.name.as_ref() == name
                {
                    *pointer_ref = file_state.file().unwrap();
                    debug_assert!(i < 13);
                    return;
                }
            }
            unreachable!()
        };
        set_pointer(&mut new_db.python_state.builtins, "builtins.pyi", false);
        set_pointer(&mut new_db.python_state.typing, "typing.pyi", false);
        // Since those files are loaded in the beginning, we can just match against that and the
        // first __init__.pyi will automaticall be the typeshed module
        set_pointer(&mut new_db.python_state.typeshed, "_typeshed", true);
        set_pointer(&mut new_db.python_state.collections, "collections", true);
        set_pointer(
            &mut new_db.python_state._collections_abc,
            "_collections_abc.pyi",
            false,
        );
        set_pointer(&mut new_db.python_state.types, "types.pyi", false);
        set_pointer(&mut new_db.python_state.abc, "abc.pyi", false);
        set_pointer(&mut new_db.python_state.functools, "functools.pyi", false);
        set_pointer(&mut new_db.python_state.enum_file, "enum.pyi", false);
        set_pointer(&mut new_db.python_state.warnings, "warnings.pyi", false);
        set_pointer(
            &mut new_db.python_state.dataclasses_file,
            "dataclasses.pyi",
            false,
        );
        set_pointer(
            &mut new_db.python_state.typing_extensions,
            "typing_extensions.pyi",
            false,
        );
        set_pointer(
            &mut new_db.python_state.mypy_extensions,
            "mypy_extensions.pyi",
            false,
        );

        if new_db.project.flags.disable_bytearray_promotion {
            new_db
                .python_state
                .bytearray()
                .use_cached_class_infos(&new_db)
                .set_promote_to(None);
        }
        if new_db.project.flags.disable_memoryview_promotion {
            new_db
                .python_state
                .memoryview_class_with_generics_to_be_defined()
                .use_cached_class_infos(&new_db)
                .set_promote_to(None);
        }
        new_db
    }

    #[inline]
    pub fn mypy_compatible(&self) -> bool {
        self.project.settings.mypy_compatible()
    }

    pub fn file_path(&self, index: FileIndex) -> &NormalizedPath {
        self.vfs.file_path(index).path()
    }

    pub fn file_by_file_path(&self, path: &PathWithScheme) -> Option<FileIndex> {
        let DirOrFile::File(file_entry) = self
            .vfs
            .search_path(self.project.flags.case_sensitive, path)?
        else {
            return None;
        };
        self.load_file_index_from_workspace(&file_entry, false)
    }

    pub fn load_sub_file(
        &self,
        super_file: &PythonFile,
        add: impl FnOnce(FileIndex) -> PythonFile,
    ) -> &PythonFile {
        let index = self.vfs.create_sub_file(super_file.file_index, add);
        self.loaded_python_file(index)
    }

    pub fn load_file_from_workspace(&self, file_entry: &Arc<FileEntry>) -> Option<&PythonFile> {
        let index = self.load_file_index_from_workspace(file_entry, false)?;
        Some(self.loaded_python_file(index))
    }

    pub fn load_file_index_from_workspace(
        &self,
        file_entry: &Arc<FileEntry>,
        invalidates_db: bool,
    ) -> Option<FileIndex> {
        self.vfs.ensure_file_for_file_entry(
            file_entry.clone(),
            invalidates_db,
            |file_index, code| {
                tracing::trace!(
                    "Start parsing {}",
                    file_entry.absolute_path(&*self.vfs.handler).as_uri()
                );
                PythonFile::from_file_entry_and_code(&self.project, file_index, file_entry, code)
            },
        )
    }

    pub fn ensure_file_for_file_index(
        &self,
        file_index: FileIndex,
    ) -> Result<&PythonFile, &'static str> {
        self.vfs
            .ensure_file_for_file_index(file_index, |file_entry, code| {
                PythonFile::from_file_entry_and_code(&self.project, file_index, file_entry, code)
            })
    }

    pub fn store_in_memory_file(
        &mut self,
        path: PathWithScheme,
        code: Box<str>,
        parent: Option<FileIndex>,
    ) {
        if let Some(parent) = parent
            && let Some(in_mem_file) = self.vfs.in_memory_file(&path)
            && let Some(file) = self.vfs.file_mut(in_mem_file)
        {
            let super_file = file.super_file.map(|sup| sup.file);
            if super_file != Some(parent) {
                file.super_file = Some(SuperFile {
                    file: parent,
                    offset: None,
                });
                file.invalidate_references_to(super_file)
            }
        }
        let (file_index, invalidation) = self.vfs.store_in_memory_file(
            self.project.flags.case_sensitive,
            path,
            code,
            |file_index, file_entry, new_code| {
                let mut file = PythonFile::from_file_entry_and_code(
                    &self.project,
                    file_index,
                    file_entry,
                    new_code,
                );
                file.super_file = parent.map(|file| SuperFile { file, offset: None });
                file
            },
        );
        if let Some(parent) = parent {
            debug_assert!(
                file_index.is_some(),
                "With subfiles we should not get into the situation where the file index is not available"
            );
            if let Some(file_index) = file_index {
                // self.vfs.file_entry(parent).add_invalidation(file_index);
                self.vfs
                    .file_mut(parent)
                    .unwrap()
                    .sub_files
                    .add_separate_file(file_index)
            }
        }
        self.handle_invalidation(invalidation);
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

    pub fn delete_directory_of_in_memory_files(
        &mut self,
        dir_path: &PathWithScheme,
    ) -> Result<(), String> {
        let invalidation = self.vfs.delete_in_memory_files_directory(
            self.project.flags.case_sensitive,
            dir_path,
            |file_state, file_index, new_code| {
                PythonFile::from_file_entry_and_code(
                    &self.project,
                    file_index,
                    file_state.file_entry(),
                    new_code,
                )
            },
        )?;
        self.handle_invalidation(invalidation);
        Ok(())
    }

    pub fn close_in_memory_file(&mut self, path: &PathWithScheme) -> Result<(), &'static str> {
        if let Some(in_mem) = self.vfs.in_memory_file(path) {
            for separate_file in self
                .vfs
                .file_mut(in_mem)
                .unwrap()
                .sub_files
                .take_separate_files()
            {
                // Avoid an invalid pointer to a non-existing super file
                if let Some(f) = self.vfs.file_mut(separate_file) {
                    f.super_file = None;
                }
            }
        }
        let result = self.vfs.close_in_memory_file(
            self.project.flags.case_sensitive,
            path,
            |file_state, file_index, new_code| {
                PythonFile::from_file_entry_and_code(
                    &self.project,
                    file_index,
                    file_state.file_entry(),
                    new_code,
                )
            },
        )?;
        self.handle_invalidation(result);
        Ok(())
    }

    pub fn invalidate_path(&mut self, path: &AbsPath) {
        let invalidation = self
            .vfs
            .invalidate_path(self.project.flags.case_sensitive, path);
        self.handle_invalidation(invalidation);
    }

    fn preload_typeshed_stub(&self, workspace: &Workspace, file_name: &'static str) -> &PythonFile {
        self.preload_typeshed_stub_in_entries(&workspace.entries, file_name, || {
            workspace.root_path().to_string()
        })
    }

    fn preload_typeshed_stub_in_entries(
        &self,
        entries: &Entries,
        file_name: &'static str,
        as_debug_path: impl Fn() -> String,
    ) -> &PythonFile {
        let entry = entries
            .search(file_name)
            .unwrap_or_else(|| panic!("Did not find file {file_name:?} in {}", as_debug_path()))
            .clone();
        let DirectoryEntry::File(file_entry) = &entry else {
            panic!(
                "It seems like you are using directories in typeshed for {}: {file_name}",
                as_debug_path()
            )
        };
        let file_index = self
            .load_file_index_from_workspace(file_entry, true)
            .unwrap_or_else(|| panic!("Unable to read {file_name:?} in {}", as_debug_path()));
        debug!("Preloaded typeshed stub {file_name} as #{}", file_index.0);
        self.loaded_python_file(file_index)
    }

    pub fn loaded_python_file(&self, index: FileIndex) -> &PythonFile {
        self.vfs.file(index).unwrap_or_else(|| {
            panic!(
                "Expected loaded file #{index}: {}",
                self.vfs.file_path(index).path()
            )
        })
    }

    fn generate_python_state(&mut self) {
        let mut dirs = self.vfs.workspaces.iter_not_type_checked();
        // TODO this is wrong, because it's just a random dir...
        let stdlib_workspace = dirs.next().expect("Expected there to be a typeshed dir");
        let mypy_extensions_dir = dirs
            .next()
            .expect("Expected there to be a mypy_extensions dir");
        let find_dir = |name| match &*stdlib_workspace.entries.search(name).unwrap_or_else(|| {
            panic!(
                "Expected a {name} directory in {}",
                stdlib_workspace.root_path()
            )
        }) {
            DirectoryEntry::Directory(c) => c.clone(),
            _ => unreachable!(),
        };
        let collections_dir = find_dir("collections");
        let typeshed_dir = find_dir("_typeshed");
        drop(dirs);

        let typeshed_dir_path: &(dyn (Fn() -> String) + Sync + Send) = &|| {
            typeshed_dir
                .absolute_path(&*self.vfs.handler)
                .path()
                .to_string()
        };
        let col_dir_path: &(dyn (Fn() -> String) + Sync + Send) = &|| {
            collections_dir
                .absolute_path(&*self.vfs.handler)
                .path()
                .to_string()
        };
        let mypy_extensions_path: &(dyn (Fn() -> String) + Sync + Send) =
            &|| mypy_extensions_dir.root_path().to_string();
        let [
            builtins,
            typing,
            typeshed,
            types,
            abc,
            functools,
            enum_file,
            dataclasses_file,
            typing_extensions,
            mypy_extensions,
            collections,
            _collections_abc,
            warnings,
        ]: [&PythonFile; _] = [
            (None, "builtins.pyi"),
            (None, "typing.pyi"),
            (
                Some((
                    Directory::entries(&self.vfs, &typeshed_dir),
                    typeshed_dir_path,
                )),
                "__init__.pyi",
            ),
            (None, "types.pyi"),
            (None, "abc.pyi"),
            (None, "functools.pyi"),
            (None, "enum.pyi"),
            (None, "dataclasses.pyi"),
            (None, "typing_extensions.pyi"),
            (
                Some((&mypy_extensions_dir.entries, mypy_extensions_path)),
                "mypy_extensions.pyi",
            ),
            (
                Some((
                    Directory::entries(&self.vfs, &collections_dir),
                    col_dir_path,
                )),
                "__init__.pyi",
            ),
            (None, "_collections_abc.pyi"),
            (None, "warnings.pyi"),
        ]
        .into_par_iter()
        .map(|(in_dir, name)| {
            if let Some((entries, path_callback)) = in_dir {
                self.preload_typeshed_stub_in_entries(entries, name, path_callback)
            } else {
                self.preload_typeshed_stub(stdlib_workspace, name)
            }
        })
        .collect::<Vec<_>>()
        .try_into()
        .unwrap();

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
            warnings,
        );
    }
}

fn add_workspace_and_check_for_pth_files(
    vfs: &mut Vfs<PythonFile>,
    path: Arc<NormalizedPath>,
    is_recovery: bool,
    kind: WorkspaceKind,
) {
    if !vfs.add_workspace(path, kind) {
        // The workspace was already added
        return;
    };
    if !is_recovery {
        // Imitate the logic for .pth files. Copied some of the logic from site.py from the Python
        // standard library.
        let last = vfs.workspaces.iter().next_back().unwrap();
        let mut pth_files = vec![];
        for dir_entry in &last.entries.iter() {
            if let DirectoryEntry::File(file_entry) = dir_entry
                && file_entry.name.ends_with(".pth")
                && !file_entry.name.starts_with('.')
            {
                pth_files.push(file_entry.clone())
            }
        }
        if !pth_files.is_empty() {
            let workspace_path = last.root_path.clone();
            for pth_file in pth_files {
                let pth_path = pth_file.absolute_path(&*vfs.handler);
                tracing::info!("Found .pth file: {}", pth_path.as_uri());
                if let Some(content) = vfs.handler.read_and_watch_file(&pth_path) {
                    for line in split_lines(&content) {
                        let line = line.trim_end();
                        if line.is_empty()
                            || line.starts_with("#")
                            || line.starts_with("import ")
                            || line.starts_with("import\t")
                        {
                            continue;
                        }
                        let path = vfs
                            .handler
                            .normalize_rc_path(vfs.handler.absolute_path(&workspace_path, line));
                        tracing::info!("Add entry {path} in .pth file: {}", pth_path.as_uri());
                        add_workspace_and_check_for_pth_files(
                            vfs,
                            path,
                            is_recovery,
                            WorkspaceKind::SitePackages,
                        )
                    }
                }
            }
        }
    }
}

#[derive(Debug)]
pub(crate) struct PythonProject {
    pub sys_path: Vec<(WorkspaceKind, Arc<NormalizedPath>)>,
    pub settings: Settings,
    pub flags: FinalizedTypeCheckerFlags,
    pub(crate) overrides: Vec<OverrideConfig>,
    // is_django: bool,  // TODO maybe add?
}

impl PythonProject {
    pub fn strict_optional_partials(&self) -> bool {
        // Mypy is currently just replacing the nullable partial to a non-nullable one.
        self.settings.mypy_compatible()
    }

    pub fn should_infer_untyped_params(&self) -> bool {
        self.settings.should_infer_untyped_params() && self.flags.check_untyped_defs
    }

    pub fn should_infer_return_types(&self) -> bool {
        self.settings.should_infer_return_types() && self.flags.check_untyped_defs
    }
}

#[derive(Debug, PartialEq, Eq, Clone, Copy)]
pub(crate) enum ParentScope {
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
                let parent_class =
                    Class::with_self_generics(db, ClassNodeRef::new(file, node_index));
                format!("{}.{}", parent_class.qualified_name(db), name)
            }
            ParentScope::Function(_) => {
                Self::qualified_name_for_unreachable_scope(db, defined_at, name)
            }
        }
    }

    pub fn qualified_name_for_unreachable_scope(
        db: &Database,
        defined_at: NodeRef,
        name: &str,
    ) -> String {
        let line = defined_at
            .file
            .byte_to_position_infos(db, defined_at.node_start_position())
            .line_one_based();
        // Add the position like `foo.Bar@7`
        format!("{}.{name}@{line}", defined_at.file.qualified_name(db))
    }
}

#[derive(Debug, Clone)]
pub(crate) struct ClassStorage {
    pub class_symbol_table: SymbolTable,
    pub self_symbol_table: SymbolTable,
    pub abstract_attributes: Box<[NodeIndex]>,
    pub parent_scope: ParentScope,
    pub slots: Option<Box<[StringSlice]>>,
}

#[derive(Debug, Clone, Copy, PartialEq)]
pub(crate) enum MetaclassState {
    None,
    Unknown,
    Some(PointLink),
}

#[derive(Debug, Clone, Copy, PartialEq)]
pub(crate) enum ClassKind {
    Normal,
    Protocol,
    Enum,
    TypedDict,
    Tuple,
    NamedTuple,
}

#[derive(Debug, Clone, PartialEq)]
pub(crate) struct BaseClass {
    pub type_: Type,
    pub is_direct_base: bool,
}

#[derive(Debug, Clone, Copy, PartialEq)]
pub(crate) struct ProtocolMember {
    pub name_index: NodeIndex,
    pub is_abstract: bool,
    pub variance: Variance,
}

#[derive(Debug)]
pub(crate) struct ClassInfos {
    pub mro: Box<[BaseClass]>, // Does never include `object`
    pub metaclass: MetaclassState,
    pub kind: ClassKind,
    pub incomplete_mro: bool,
    pub protocol_members: Box<[ProtocolMember]>,
    pub has_slots: bool,
    pub is_final: bool,
    pub total_ordering: bool,
    pub is_runtime_checkable: bool,
    pub abstract_attributes: Box<[PointLink]>,
    pub in_django_stubs: OnceLock<bool>,
    pub dataclass_transform: Option<Box<DataclassTransformObj>>,
    pub promote_to: Mutex<Option<PointLink>>,
    pub deprecated_reason: Option<Arc<Box<str>>>,
    // Does not need to be a HashMap, because this is typically the size of 1-2
    pub variance_map: Vec<(TypeVarName, OnceLock<Variance>)>,
    // We have this less for caching and more to be able to have different types.
    pub undefined_generics_type: OnceLock<Arc<Type>>,
}

impl Clone for ClassInfos {
    fn clone(&self) -> Self {
        Self {
            mro: self.mro.clone(),
            metaclass: self.metaclass,
            kind: self.kind,
            incomplete_mro: self.incomplete_mro,
            protocol_members: self.protocol_members.clone(),
            has_slots: self.has_slots,
            is_final: self.is_final,
            total_ordering: self.total_ordering,
            is_runtime_checkable: self.is_runtime_checkable,
            abstract_attributes: self.abstract_attributes.clone(),
            in_django_stubs: self.in_django_stubs.clone(),
            dataclass_transform: self.dataclass_transform.clone(),
            promote_to: Mutex::new(*self.promote_to.lock().unwrap()),
            deprecated_reason: self.deprecated_reason.clone(),
            variance_map: self.variance_map.clone(),
            undefined_generics_type: self.undefined_generics_type.clone(),
        }
    }
}

impl PartialEq for ClassInfos {
    fn eq(&self, other: &Self) -> bool {
        self.mro == other.mro
            && self.metaclass == other.metaclass
            && self.kind == other.kind
            && self.incomplete_mro == other.incomplete_mro
            && self.protocol_members == other.protocol_members
            && self.has_slots == other.has_slots
            && self.is_final == other.is_final
            && self.total_ordering == other.total_ordering
            && self.is_runtime_checkable == other.is_runtime_checkable
            && self.abstract_attributes == other.abstract_attributes
            && self.dataclass_transform == other.dataclass_transform
            && *self.promote_to.lock().unwrap() == *other.promote_to.lock().unwrap()
            && self.deprecated_reason == other.deprecated_reason
            && self.variance_map == other.variance_map
            && self.undefined_generics_type == other.undefined_generics_type
    }
}

impl ClassInfos {
    pub fn metaclass<'db>(&self, db: &'db Database) -> Class<'db> {
        match self.metaclass {
            MetaclassState::Some(link) => Class::from_undefined_generics(db, link),
            _ => db.python_state.bare_type_class(),
        }
    }

    pub fn has_uncalculated_variances(&self) -> bool {
        self.variance_map
            .iter()
            .any(|(_, lazy_variance)| lazy_variance.get().is_none())
    }

    pub fn promote_to(&self) -> Option<PointLink> {
        *self.promote_to.lock().unwrap()
    }

    pub fn set_promote_to(&self, link: Option<PointLink>) {
        *self.promote_to.lock().unwrap() = link
    }

    pub fn base_types(&self) -> impl Iterator<Item = &'_ Type> {
        self.mro
            .iter()
            .filter(|&b| b.is_direct_base)
            .map(|b| &b.type_)
    }
}

impl std::cmp::PartialEq for ClassStorage {
    fn eq(&self, _other: &Self) -> bool {
        recoverable_error!("Should never compare  class storage with ==");
        false
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
        assert_eq!(size_of::<UnionType>(), 24);
        assert_eq!(size_of::<Tuple>(), 104);
        assert_eq!(size_of::<Type>(), 40); // TODO Would like it to be 32, but ClassGenerics is 24
        assert_eq!(size_of::<ComplexPoint>(), size_of::<Type>());
        assert_eq!(size_of::<ClassStorage>(), 136);
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
