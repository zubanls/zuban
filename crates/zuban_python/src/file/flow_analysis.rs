use std::{
    borrow::{Borrow, Cow},
    cell::{Cell, OnceCell, Ref, RefCell, RefMut},
    collections::VecDeque,
    sync::Arc,
};

use parsa_python_cst::{
    Argument, Arguments, ArgumentsDetails, AssertStmt, AssignmentContent, Atom, AtomContent, Block,
    BreakStmt, CaseBlock, CasePattern, ClassPattern, CompIfIterator, ComparisonContent,
    Comparisons, Conjunction, ContinueStmt, DelTarget, DelTargets, Disjunction, ElseBlock,
    ExceptExpression, ExceptExpressionContent, Expression, ExpressionContent, ExpressionPart,
    ForIfClauseIterator, ForStmt, FunctionDef, IfBlockIterator, IfBlockType, IfStmt,
    KeyEntryInPattern, LiteralPattern, LiteralPatternContent, MappingPattern, MappingPatternItem,
    MatchStmt, Name, NameDef, NamedExpression, NamedExpressionContent, NodeIndex, Operand,
    ParamPattern, Pattern, PatternKind, Primary, PrimaryContent, PrimaryOrAtom, PrimaryTarget,
    PrimaryTargetOrAtom, SequencePatternItem, SliceType as CSTSliceType, StarLikeExpression,
    StarLikeExpressionIterator, StarPatternContent, SubjectExprContent, Target, Ternary,
    TryBlockType, TryStmt, UnpackedNumber, WhileStmt,
};

use crate::{
    arguments::{KnownArgsWithCustomAddIssue, SimpleArgs},
    database::{
        ComplexPoint, Database, Locality, Point, PointKind, PointLink, Specific, WidenedType,
    },
    debug,
    diagnostics::IssueKind,
    file::{ClassNodeRef, OtherDefinitionIterator, utils::TupleGatherer},
    format_data::FormatData,
    getitem::SliceType,
    inference_state::InferenceState,
    inferred::{Inferred, UnionValue, add_attribute_error},
    match_::Match,
    matching::{LookupKind, Matcher, OnTypeError},
    new_class,
    node_ref::NodeRef,
    recoverable_error,
    result_context::{CouldBeALiteral, ResultContext},
    type_::{
        AnyCause, CallableContent, CallableLike, CallableParams, ClassGenerics, DbBytes, DbString,
        Enum, EnumKind, EnumMember, GenericClass, Intersection, Literal, LiteralKind, LookupResult,
        NamedTuple, NeverCause, StringSlice, Tuple, TupleArgs, TupleUnpack, Type, TypeVar,
        TypeVarKind, TypedDict, UnionEntry, UnionType, WithUnpack, lookup_on_enum_instance,
    },
    type_helpers::{
        Callable, Class, ClassLookupOptions, FirstParamKind, Function, InstanceLookupOptions,
        LookupDetails, OverloadResult, OverloadedFunction,
    },
    utils::{EitherIterator, debug_indent},
};

use super::{
    FuncNodeRef, PythonFile, first_defined_name,
    inference::{AssignKind, Inference, instantiate_except},
    name_binder::{Truthiness, is_expr_part_reachable_for_name_binder},
    on_argument_type_error,
    utils::func_of_self_symbol,
};

type Entries = Vec<Entry>;
type ParentUnions = Vec<(FlowKey, UnionType)>;

const MAX_PRECISE_TUPLE_SIZE: usize = 8; // Constant taken from Mypy

thread_local! {
    pub static FLOW_ANALYSIS: FlowAnalysis = FlowAnalysis::default();
}

#[derive(Debug, Clone)]
enum FlowKey {
    Name(PointLink),
    Member(Arc<FlowKey>, DbString),
    Index {
        base_key: Arc<FlowKey>,
        node_index: NodeIndex,
        match_index: FlowKeyIndex,
    },
}

impl FlowKey {
    fn is_child_of(&self, db: &Database, search_key: &FlowKey) -> bool {
        let Some(base_key) = self.base_key() else {
            return false;
        };
        base_key.equals(db, search_key) || base_key.is_child_of(db, search_key)
    }

    fn base_key(&self) -> Option<&FlowKey> {
        match self {
            Self::Name(_) => None,
            Self::Member(base_key, _) | Self::Index { base_key, .. } => Some(base_key.as_ref()),
        }
    }

    fn equals(&self, db: &Database, other: &Self) -> bool {
        match self {
            Self::Name(link1) => matches!(other, Self::Name(link2) if link1 == link2),
            Self::Member(key1, s1) => match other {
                Self::Member(key2, s2) => key1.equals(db, key2) && s1.as_str(db) == s2.as_str(db),
                _ => false,
            },
            Self::Index {
                base_key: key1,
                match_index: match_index1,
                ..
            } => match other {
                Self::Index {
                    base_key: key2,
                    match_index: match_index2,
                    ..
                } => key1.equals(db, key2) && match_index1 == match_index2,
                _ => false,
            },
        }
    }

    fn declaration_t(&self, i_s: &InferenceState) -> Type {
        match self {
            FlowKey::Name(link) => NodeRef::from_link(i_s.db, *link)
                .infer_name_of_definition_by_index(i_s)
                .as_type(i_s),
            _ => {
                recoverable_error!(
                    "For now we do not expect original declarations to have simplified unions "
                );
                Type::ERROR
            }
        }
    }

    fn is_simple_name(&self) -> bool {
        matches!(self, Self::Name(_))
    }
}

#[derive(Debug, Clone, PartialEq)]
enum FlowKeyIndex {
    Int(isize),
    Str(String),
}

#[derive(Debug, Clone, PartialEq)]
enum EntryKind {
    Type(Type),
    OriginalDeclaration,
}

#[derive(Debug, Clone)]
struct Entry {
    key: FlowKey,
    type_: EntryKind,
    modifies_ancestors: bool,
    deleted: bool, // e.g. after a `del foo`
    // TODO currently unused, delete?
    widens: bool, // e.g. if a type is defined as None and later made an optional.
}

impl Entry {
    fn new(key: FlowKey, type_: Type) -> Self {
        Entry {
            key,
            type_: EntryKind::Type(type_),
            modifies_ancestors: false,
            deleted: false,
            widens: false,
        }
    }

    fn with_declaration(&self, allow_redefinition: bool) -> Self {
        Entry {
            key: self.key.clone(),
            type_: if allow_redefinition && matches!(&self.key, FlowKey::Name(_)) {
                // Redefinitions define the original declaration always in the name binder, we
                // therefore never need to fallback to the original definition, because it is part
                // of name binding already and can offer more precise types.
                self.type_.clone()
            } else {
                EntryKind::OriginalDeclaration
            },
            modifies_ancestors: self.modifies_ancestors,
            deleted: self.deleted,
            widens: self.widens,
        }
    }

    #[inline]
    fn simplified_union(&self, i_s: &InferenceState, other: &Self) -> EntryKind {
        let merge_with_original = |entry: &Self, other_t| {
            EntryKind::Type(entry.key.declaration_t(i_s).simplified_union(i_s, other_t))
        };
        match (&self.type_, &other.type_) {
            (EntryKind::Type(t1), EntryKind::Type(t2)) => {
                EntryKind::Type(t1.simplified_union(i_s, t2))
            }
            (EntryKind::OriginalDeclaration, EntryKind::Type(t)) if other.widens => {
                merge_with_original(self, t)
            }
            (EntryKind::Type(t), EntryKind::OriginalDeclaration) if self.widens => {
                merge_with_original(other, t)
            }
            _ => EntryKind::OriginalDeclaration,
        }
    }

    #[inline]
    fn union(&mut self, i_s: &InferenceState, other: &Self, invert_type: bool) {
        match (self.deleted, other.deleted) {
            (false, true) => (),
            (true, false) => self.type_ = other.type_.clone(),
            _ => {
                if invert_type {
                    self.type_ = other.simplified_union(i_s, self);
                } else {
                    self.type_ = self.simplified_union(i_s, other);
                }
            }
        }
        self.modifies_ancestors |= other.modifies_ancestors;
        self.deleted &= other.deleted;
        self.widens |= other.widens;
    }

    fn union_of_refs(&self, i_s: &InferenceState, other: &Self) -> Self {
        Self {
            key: self.key.clone(),
            type_: match (self.deleted, other.deleted) {
                (false, true) => self.type_.clone(),
                (true, false) => other.type_.clone(),
                _ => self.simplified_union(i_s, other),
            },
            modifies_ancestors: self.modifies_ancestors | other.modifies_ancestors,
            deleted: self.deleted & other.deleted,
            widens: self.widens | other.widens,
        }
    }

    fn common_sub_type(&self, i_s: &InferenceState, other: &Self) -> Option<EntryKind> {
        let EntryKind::Type(t1) = &self.type_ else {
            return Some(other.type_.clone());
        };
        let EntryKind::Type(t2) = &other.type_ else {
            return Some(self.type_.clone());
        };
        t1.common_sub_type(i_s, t2).map(EntryKind::Type)
    }

    fn debug_format_type(&self, db: &Database) -> Box<str> {
        match &self.type_ {
            EntryKind::Type(t) => t.format_short(db),
            EntryKind::OriginalDeclaration => "<widened back to declaration>".into(),
        }
    }
}

#[derive(Debug, Clone, Copy)]
enum FrameKind {
    BaseScope,
    Conditional,
}

#[derive(Debug, Clone)]
struct Frame {
    entries: Entries,
    unreachable: bool,
    reported_unreachable: bool,
    kind: FrameKind,
}

impl Frame {
    fn new(kind: FrameKind, entries: Entries) -> Self {
        Self {
            kind,
            entries,
            unreachable: false,
            reported_unreachable: false,
        }
    }

    fn new_conditional() -> Self {
        Self {
            entries: Default::default(),
            unreachable: false,
            reported_unreachable: false,
            kind: FrameKind::Conditional,
        }
    }

    fn new_base_scope() -> Self {
        Self {
            entries: Default::default(),
            unreachable: false,
            reported_unreachable: false,
            kind: FrameKind::BaseScope,
        }
    }

    fn new_unreachable() -> Self {
        Self {
            entries: Default::default(),
            unreachable: true,
            reported_unreachable: false,
            kind: FrameKind::Conditional,
        }
    }

    fn take(&mut self) -> Self {
        Self {
            entries: std::mem::take(&mut self.entries),
            unreachable: std::mem::take(&mut self.unreachable),
            reported_unreachable: std::mem::take(&mut self.reported_unreachable),
            kind: self.kind,
        }
    }

    fn add_entry(&mut self, i_s: &InferenceState, entry: Entry) {
        for old_entry in &mut self.entries {
            if old_entry.key.equals(i_s.db, &entry.key) {
                if let Some(new) = old_entry.common_sub_type(i_s, &entry) {
                    old_entry.type_ = new;
                }
                return;
            }
        }
        self.entries.push(entry)
    }

    fn overwrite_entry(&mut self, db: &Database, entry: Entry) {
        for old_entry in &mut self.entries {
            if old_entry.key.equals(db, &entry.key) {
                *old_entry = entry;
                return;
            }
        }
        self.entries.push(entry)
    }

    fn from_type_without_entry(t: &Type) -> Self {
        match t {
            Type::Never(_) => Self::new_unreachable(),
            _ => Self::new_conditional(),
        }
    }

    fn lookup_entry(&self, db: &Database, key: &FlowKey) -> Option<&Entry> {
        self.entries.iter().find(|entry| entry.key.equals(db, key))
    }

    fn from_type(key: FlowKey, type_: Type) -> Self {
        match type_ {
            Type::Never(_) => Self::new_unreachable(),
            type_ => Self::new(FrameKind::Conditional, vec![Entry::new(key, type_)]),
        }
    }

    fn has_entries(&self) -> bool {
        !self.entries.is_empty()
    }
}

fn invalidate_child_entries(entries: &mut Vec<Entry>, db: &Database, key: &FlowKey) {
    entries.retain(|entry| !entry.key.is_child_of(db, key))
}

#[derive(Debug)]
struct LoopDetails {
    break_frames: Vec<Frame>,
    continue_frames: Vec<Frame>,
    loop_frame_index: usize,
}

#[derive(Debug, Clone)]
pub enum DelayedDiagnostic {
    Func(DelayedFunc),
    Class(PointLink),
    ClassTypeParams { class_link: PointLink },
    ConstraintVerification(Box<DelayedConstraintVerification>),
}

#[derive(Debug, Clone)]
pub(crate) struct DelayedConstraintVerification {
    pub type_var: Arc<TypeVar>,
    pub add_issue_at: PointLink,
    pub actual: Type,
    pub of_name: StringSlice,
}

#[derive(Debug, Clone)]
pub(crate) struct DelayedFunc {
    pub func: PointLink,
    pub class: Option<PointLink>,
    pub in_type_checking_only_block: bool,
    reused_narrowings: Entries,
}

#[must_use]
pub(crate) struct FlowAnalysisResult<T> {
    pub result: T,
    pub unfinished_partials: Vec<PointLink>,
}

#[derive(Debug)]
struct TryFrame {
    entries: Entries,
    // This is true only when an explicit AttributeError is provided and not when e.g.
    // BaseException or Exception is caught.
    ignores_attribute_error: bool,
}

#[derive(Debug, Default)]
pub(crate) struct FlowAnalysis {
    frames: RefCell<Vec<Frame>>,
    try_frames: RefCell<Vec<TryFrame>>,
    loop_details: RefCell<Option<LoopDetails>>,
    delayed_diagnostics: RefCell<VecDeque<DelayedDiagnostic>>,
    partials_in_module: RefCell<Vec<PointLink>>,
    in_type_checking_only_block: Cell<bool>, // For stuff like if TYPE_CHECKING:
    accumulating_types: Cell<usize>, // Can accumulate nested and thereore use this counter like a stack
    in_pattern_matching: Cell<usize>, // Counts how many times we're inside pattern matching
}

impl FlowAnalysis {
    fn with_new_empty<T>(&self, db: &Database, callable: impl FnOnce() -> T) -> T {
        let FlowAnalysisResult {
            result,
            unfinished_partials,
        } = self.with_new_empty_without_unfinished_partial_checking(callable);
        process_unfinished_partials(db, unfinished_partials);
        result
    }

    pub fn with_new_empty_for_file<T>(
        &self,
        db: &Database,
        file: &PythonFile,
        callable: impl FnOnce() -> T,
    ) -> T {
        self.with_new_empty(db, || {
            debug_assert!(self.delayed_diagnostics.borrow().is_empty());
            *self.delayed_diagnostics.borrow_mut() =
                std::mem::take(&mut file.delayed_diagnostics.write().unwrap());
            let result = callable();
            let mut delayed = self.delayed_diagnostics.take();
            if db.project.flags.local_partial_types {
                let mut file_delayed = file.delayed_diagnostics.write().unwrap();
                delayed.extend(file_delayed.drain(..));
                *file_delayed = delayed;
            } else {
                self.process_delayed_diagnostics(db, delayed)
            }
            result
        })
    }
    pub fn with_new_empty_and_delay_further<T>(
        &self,
        db: &Database,
        callable: impl FnOnce() -> T,
    ) -> T {
        let (result, delayed) = self.with_new_empty(db, || {
            let result = callable();
            let delayed: VecDeque<_> = std::mem::take(&mut self.delayed_diagnostics.borrow_mut());
            (result, delayed)
        });
        self.delayed_diagnostics.borrow_mut().extend(delayed);
        result
    }

    pub fn with_new_empty_without_unfinished_partial_checking<T>(
        &self,
        callable: impl FnOnce() -> T,
    ) -> FlowAnalysisResult<T> {
        if self.frames.try_borrow_mut().is_err() {
            // TODO This is completely wrong, but is related to the test
            // narrowing_with_key_in_different_file and executing narrows
            return FlowAnalysisResult {
                result: callable(),
                unfinished_partials: Default::default(),
            };
        }
        let old_frames = self.frames.take();
        let try_frames = self.try_frames.take();
        let loop_details = self.loop_details.take();
        let delayed = self.delayed_diagnostics.take();
        let partials = self.partials_in_module.take();
        let in_type_checking_only_block = self.in_type_checking_only_block.take();
        let accumulating_types = self.accumulating_types.take();
        let in_pattern_matching = self.in_pattern_matching.take();

        let result = FlowAnalysisResult {
            result: callable(),
            unfinished_partials: self.partials_in_module.take(),
        };
        self.debug_assert_is_empty();

        *self.frames.borrow_mut() = old_frames;
        *self.try_frames.borrow_mut() = try_frames;
        *self.loop_details.borrow_mut() = loop_details;
        *self.delayed_diagnostics.borrow_mut() = delayed;
        *self.partials_in_module.borrow_mut() = partials;
        self.in_type_checking_only_block
            .set(in_type_checking_only_block);
        self.accumulating_types.set(accumulating_types);
        self.in_pattern_matching.set(in_pattern_matching);
        result
    }

    pub(crate) fn add_delayed_func_with_reused_narrowings_for_nested_function(
        &self,
        func_node_ref: FuncNodeRef,
    ) {
        let reused_narrowings = self
            .frames
            .borrow()
            .iter()
            .rev()
            .flat_map(|frame| {
                frame.entries.iter().filter_map(|entry| {
                    // We can only use narrowings of names in functions. More complex variables could
                    // have been tampered in different ways.
                    let FlowKey::Name(link) = entry.key else {
                        return None;
                    };

                    if func_node_ref.file_index() != link.file {
                        // TODO what about star imports? See also star_import_with_import_overwrite
                        return None;
                    }
                    // We try to filter out narrowed names that are reassigned within the
                    // function later than where that function is defined.
                    for name_index in
                        OtherDefinitionIterator::new(&func_node_ref.file.points, link.node_index)
                    {
                        if name_index > func_node_ref.node_index {
                            return None;
                        }
                    }
                    Some(entry.clone())
                })
            })
            .collect();
        self.delayed_diagnostics
            .borrow_mut()
            .push_back(DelayedDiagnostic::Func(DelayedFunc {
                func: func_node_ref.as_link(),
                class: None,
                in_type_checking_only_block: self.in_type_checking_only_block.get(),
                reused_narrowings,
            }))
    }

    pub fn debug_assert_is_empty(&self) {
        debug_assert!(self.frames.borrow().is_empty());
        debug_assert!(self.try_frames.borrow().is_empty());
        debug_assert!(self.loop_details.borrow().is_none());
        debug_assert!(self.delayed_diagnostics.borrow().is_empty());
        debug_assert!(self.partials_in_module.borrow().is_empty());
        debug_assert!(!self.in_type_checking_only_block.get());
        debug_assert!(!self.in_type_checking_only_block.get());
        debug_assert_eq!(self.in_pattern_matching.get(), 0);
    }

    fn lookup_narrowed_key_and_deleted(
        &self,
        db: &Database,
        lookup_key: FlowKey,
    ) -> (Option<Inferred>, bool) {
        let frames = self.frames.borrow();
        let Some(entry) = frames
            .iter()
            .rev()
            .find_map(|frame| frame.lookup_entry(db, &lookup_key))
        else {
            return (None, false);
        };
        (
            match &entry.type_ {
                EntryKind::Type(t) => Some(Inferred::from_type(t.clone())),
                EntryKind::OriginalDeclaration => None,
            },
            entry.deleted,
        )
    }

    fn lookup_entry(&self, db: &Database, lookup_key: FlowKey) -> Option<Ref<'_, Entry>> {
        let frames = self.frames.borrow();
        Ref::filter_map(frames, |frames| {
            frames
                .iter()
                .rev()
                .find_map(|frame| frame.lookup_entry(db, &lookup_key))
        })
        .ok()
    }

    pub fn is_unreachable(&self) -> bool {
        self.frames.borrow().last().unwrap().unreachable
    }

    #[inline]
    fn tos_frame(&self) -> RefMut<'_, Frame> {
        // tos = top of the stack
        RefMut::map(self.frames.borrow_mut(), |frames| {
            frames.last_mut().unwrap()
        })
    }

    #[inline]
    fn maybe_tos_frame(&self) -> Option<RefMut<'_, Frame>> {
        // tos = top of the stack
        let frames = self.frames.borrow_mut();
        (!frames.is_empty()).then(|| RefMut::map(frames, |frames| frames.last_mut().unwrap()))
    }

    pub fn enable_reported_unreachable_in_top_frame(&self) {
        self.tos_frame().reported_unreachable = true;
    }

    pub fn report_unreachable_if_not_reported_before(&self, callback: impl FnOnce()) {
        let mut tos_frame = self.tos_frame();
        if !tos_frame.reported_unreachable {
            tos_frame.reported_unreachable = true;
            drop(tos_frame);
            // Currently we don't recheck loops so we should not report unreachable frames, because
            // they might just be fine if types are widened for example.
            if self.loop_details.borrow().is_none() {
                callback()
            }
        }
    }

    fn merge_conditional(
        &self,
        i_s: &InferenceState,
        mut true_frame: Frame,
        mut false_frame: Frame,
    ) {
        // TODO merge frames properly, this is just a special case
        if false_frame.unreachable || true_frame.unreachable {
            if !false_frame.unreachable {
                self.overwrite_entries(i_s.db, false_frame.entries, true_frame.has_entries())
            } else if !true_frame.unreachable {
                self.overwrite_entries(i_s.db, true_frame.entries, false_frame.has_entries())
            } else {
                self.mark_current_frame_unreachable()
            }
        } else {
            self.merge_assignments_for_first_frame(i_s, &mut true_frame, &mut false_frame);
            self.merge_assignments_for_first_frame(i_s, &mut false_frame, &mut true_frame);
        }
    }

    fn merge_assignments_for_first_frame(
        &self,
        i_s: &InferenceState,
        first_frame: &mut Frame,
        other_frame: &mut Frame,
    ) {
        'outer: for first_entry in &first_frame.entries {
            if first_entry.modifies_ancestors {
                for other_entry in &mut other_frame.entries {
                    if first_entry.key.equals(i_s.db, &other_entry.key) {
                        if other_entry.modifies_ancestors {
                            self.overwrite_entry(i_s, first_entry.union_of_refs(i_s, other_entry));
                        } else {
                            self.overwrite_entry(i_s, other_entry.union_of_refs(i_s, first_entry));
                        }

                        // Assign false to make sure it is not handled again from the other side.
                        other_entry.modifies_ancestors = false;
                        continue 'outer;
                    }
                }
                self.overwrite_entry(
                    i_s,
                    self.merge_key_with_ancestor_assignment(i_s, first_entry),
                )
            }
        }
    }

    fn overwrite_entry(&self, i_s: &InferenceState, new_entry: Entry) {
        for try_frame in self.try_frames.borrow_mut().iter_mut() {
            invalidate_child_entries(&mut try_frame.entries, i_s.db, &new_entry.key);
            // We don't want to add entries if they are already overwritten in the same frame.
            if try_frame
                .entries
                .iter()
                .any(|e| new_entry.key.is_child_of(i_s.db, &e.key))
            {
                continue;
            }

            let mut add_entry_to_try_frame = |new_entry: &Entry| {
                for entry in &mut try_frame.entries {
                    if entry.key.equals(i_s.db, &new_entry.key) {
                        entry.union(i_s, new_entry, false);
                        return true;
                    }
                }
                false
            };
            let new = self.merge_key_with_ancestor_assignment(i_s, &new_entry);
            // If we have a key that narrows in our ancestors, we either add it to an existing
            // one or push a new one.
            if !add_entry_to_try_frame(&new) {
                try_frame.entries.push(new)
            }
        }

        if self.frames.borrow().is_empty() {
            // TODO why this????
            return;
        }
        let mut tos_frame = self.tos_frame();
        invalidate_child_entries(&mut tos_frame.entries, i_s.db, &new_entry.key);
        let entries = &mut tos_frame.entries;
        for entry in &mut *entries {
            if entry.key.equals(i_s.db, &new_entry.key) {
                if self.accumulating_types.get() > 0 {
                    entry.type_ = entry.simplified_union(i_s, &new_entry);
                    entry.widens |= new_entry.widens;
                } else {
                    *entry = new_entry;
                }
                return;
            }
        }
        entries.push(new_entry)
    }

    fn add_initial_name_definition(&self, db: &Database, name: PointLink) {
        let new_entry = Entry {
            key: FlowKey::Name(name),
            type_: EntryKind::OriginalDeclaration,
            modifies_ancestors: true,
            deleted: false,
            widens: false,
        };
        let Ok(borrowed_mut) = self.frames.try_borrow_mut() else {
            // TODO This is completely wrong, but is related to the test
            // narrowing_with_key_in_different_file and executing narrows
            return;
        };
        if borrowed_mut.is_empty() {
            // TODO why this????
            return;
        }
        drop(borrowed_mut);
        let mut tos_frame = self.tos_frame();
        let entries = &mut tos_frame.entries;
        if cfg!(debug_assertions) {
            for try_frame in self.try_frames.borrow().iter() {
                for entry in try_frame.entries.iter() {
                    if entry.key.equals(db, &new_entry.key)
                        && entry.type_ != EntryKind::OriginalDeclaration
                    {
                        unreachable!();
                    }
                }
            }
        }
        for entry in entries.iter() {
            if entry.key.equals(db, &new_entry.key) {
                if entry.type_ == EntryKind::OriginalDeclaration {
                    return;
                } else {
                    recoverable_error!("Did not expect an already existing entry")
                }
            }
        }
        entries.push(new_entry)
    }

    fn merge_key_with_ancestor_assignment(
        &self,
        i_s: &InferenceState,
        search_for: &Entry,
    ) -> Entry {
        self.frames
            .borrow()
            .iter()
            .rev()
            .find_map(|frame| {
                frame.entries.iter().find_map(|e| {
                    if e.key.equals(i_s.db, &search_for.key) {
                        return Some(e.union_of_refs(i_s, search_for));
                    }
                    None
                })
            })
            // The fallback just assigns an "empty" key. This is needed, because otherwise we would
            // not be able to know if the entry invalidated entries further up the stack.
            .unwrap_or_else(|| {
                search_for.with_declaration(
                    i_s.flags().allow_redefinition || self.in_pattern_matching.get() > 0,
                )
            })
    }

    fn remove_key(&self, i_s: &InferenceState, key: &FlowKey) {
        // We don't have to remove anything if nothing is narrowed.
        if let Some(tos_frame) = self.frames.borrow_mut().last_mut() {
            tos_frame
                .entries
                .retain(|entry| !entry.key.equals(i_s.db, key))
        }
    }

    fn remove_key_if_modifies_ancestors(&self, i_s: &InferenceState, key: &FlowKey) {
        let Some(mut tos) = self.maybe_tos_frame() else {
            recoverable_error!("Expected a tos to remove {key:?}");
            return;
        };
        tos.entries
            .retain(|entry| !entry.modifies_ancestors || !entry.key.equals(i_s.db, key))
    }

    fn overwrite_entries(
        &self,
        db: &Database,
        new_entries: Entries,
        overwritten_entries_possibly_modify_ancestors: bool,
    ) {
        let Some(mut tos_frame) = self.maybe_tos_frame() else {
            recoverable_error!("Trying to overwrite entries, but there are no frames");
            return;
        };

        for entry in &new_entries {
            invalidate_child_entries(&mut tos_frame.entries, db, &entry.key);
        }

        let entries = &mut tos_frame.entries;
        'outer: for mut new_entry in new_entries {
            for entry in &mut *entries {
                if entry.key.equals(db, &new_entry.key) {
                    new_entry.modifies_ancestors |=
                        entry.modifies_ancestors | overwritten_entries_possibly_modify_ancestors;
                    new_entry.widens |= entry.widens;
                    *entry = new_entry;
                    continue 'outer;
                }
            }
            entries.push(new_entry)
        }
    }

    fn overwrite_frame(&self, db: &Database, new_frame: Frame) {
        self.overwrite_entries(db, new_frame.entries, false);
        self.tos_frame().unreachable |= new_frame.unreachable;
    }

    pub fn with_new_func_frame_and_return_unreachable(
        &self,
        db: &Database,
        callable: impl FnOnce(),
    ) -> bool {
        let old_partials = self.partials_in_module.take();
        let result = self
            .with_frame(Frame::new_base_scope(), callable)
            .unreachable;
        let new_partials = self.partials_in_module.replace(old_partials);
        process_unfinished_partials(db, new_partials);
        result
    }

    pub fn with_frame_that_exports_widened_entries<T>(
        &self,
        i_s: &InferenceState,
        callable: impl FnOnce() -> T,
    ) -> T {
        let (frame, result) = self.with_frame_and_result(Frame::new_base_scope(), callable);
        for entry in frame.entries {
            if entry.widens
                && let EntryKind::Type(widened) = entry.type_
            {
                let name_def_ref = match &entry.key {
                    FlowKey::Name(link) => {
                        let name_ref = NodeRef::from_link(i_s.db, *link);
                        if !name_ref.point().can_be_redefined() {
                            // The name is only narrowed from e.g. x: int | str and should not
                            // be saved as a widened name
                            continue;
                        }
                        name_ref.name_def_ref_of_name()
                    }
                    _ => {
                        recoverable_error!("Widening is not supported for key {:?}", entry.key);
                        continue;
                    }
                };
                let declaration_t = entry.key.declaration_t(i_s);
                if !declaration_t
                    .is_simple_super_type_of(i_s, &widened)
                    .non_any_match()
                {
                    debug!(
                        "Save widened type {:?} to {}",
                        widened.format_short(i_s.db),
                        name_def_ref.as_code()
                    );
                    name_def_ref.insert_complex(
                        ComplexPoint::WidenedType(Arc::new(WidenedType {
                            original: ComplexPoint::TypeInstance(declaration_t),
                            widened,
                        })),
                        Locality::Todo,
                    )
                }
            }
        }
        result
    }

    pub fn with_class_frame<T>(&self, i_s: &InferenceState, callable: impl FnOnce() -> T) -> T {
        self.with_frame_that_exports_widened_entries(i_s, || {
            let start = self.partials_in_module.borrow().len();
            let result = callable();
            let mut partials_in_module = self.partials_in_module.borrow_mut();
            // Partials of a class should be closed here, otherwise we would probably get into very
            // weird situations where arbitrary other code after the class could "fill" the
            // partial and accessing it would return e.g. None, which is definitely not what
            // anybody wants.
            process_unfinished_partials(i_s.db, partials_in_module.iter().skip(start).copied());
            partials_in_module.truncate(start);
            result
        })
    }

    fn with_frame_and_result<T>(&self, frame: Frame, callable: impl FnOnce() -> T) -> (Frame, T) {
        self.frames.borrow_mut().push(frame);
        let result = callable();
        (self.frames.borrow_mut().pop().unwrap(), result)
    }

    fn with_frame(&self, frame: Frame, callable: impl FnOnce()) -> Frame {
        self.frames.borrow_mut().push(frame);
        callable();
        self.frames.borrow_mut().pop().unwrap()
    }

    fn with_in_type_checking_only_block(&self, callable: impl FnOnce()) {
        let old = self.in_type_checking_only_block.get();
        self.in_type_checking_only_block.set(true);
        callable();
        self.in_type_checking_only_block.set(old);
    }

    fn with_new_try_frame(&self, ignores_attribute_error: bool, callable: impl FnOnce()) -> Frame {
        self.try_frames.borrow_mut().push(TryFrame {
            entries: vec![],
            ignores_attribute_error,
        });
        callable();
        Frame {
            entries: self.try_frames.borrow_mut().pop().unwrap().entries,
            ..Frame::new_conditional()
        }
    }

    fn with_new_loop_frame(&self, frame: Frame, callable: impl FnOnce()) -> (Frame, LoopDetails) {
        let old = self.loop_details.borrow_mut().replace(LoopDetails {
            break_frames: vec![],
            continue_frames: vec![],
            loop_frame_index: self.frames.borrow().len(),
        });
        let after_frame = self.with_frame(frame, callable);
        let mut loop_details = self.loop_details.borrow_mut();
        let result = loop_details.take().unwrap();
        *loop_details = old;
        (after_frame, result)
    }

    fn merge_frames_for_index(&self, db: &Database, frame_index: usize) -> Frame {
        let mut result = Frame::new_conditional();
        for check_frame in self.frames.borrow().iter().skip(frame_index).rev() {
            for entry in &check_frame.entries {
                if result.lookup_entry(db, &entry.key).is_none() {
                    result.entries.push(entry.clone())
                }
            }
        }
        result
    }

    pub fn mark_current_frame_unreachable(&self) {
        if let Some(mut tos) = self.maybe_tos_frame() {
            tos.unreachable = true
        }
    }

    pub fn add_partial(&self, defined_at: PointLink) {
        self.partials_in_module.borrow_mut().push(defined_at)
    }

    pub fn add_delayed_func(&self, func: PointLink, class: Option<PointLink>) {
        self.delayed_diagnostics
            .borrow_mut()
            .push_back(DelayedDiagnostic::Func(DelayedFunc {
                func,
                class,
                in_type_checking_only_block: self.in_type_checking_only_block.get(),
                reused_narrowings: Default::default(),
            }))
    }

    pub fn add_delayed_class_diagnostics(&self, class: PointLink) {
        self.delayed_diagnostics
            .borrow_mut()
            .push_back(DelayedDiagnostic::Class(class))
    }

    pub fn add_delayed_type_params_variance_inference(&self, class: ClassNodeRef) {
        self.delayed_diagnostics
            .borrow_mut()
            .push_back(DelayedDiagnostic::ClassTypeParams {
                class_link: class.as_link(),
            })
    }

    pub(super) fn process_delayed_diagnostics(
        &self,
        db: &Database,
        delayed: VecDeque<DelayedDiagnostic>,
    ) {
        let old = self.delayed_diagnostics.replace(delayed);
        while let Some(delayed) = {
            let mut borrowed = self.delayed_diagnostics.borrow_mut();
            let result = borrowed.pop_front();
            drop(borrowed);
            result
        } {
            match delayed {
                DelayedDiagnostic::Func(delayed_func) => {
                    let func = Function::new(
                        NodeRef::from_link(db, delayed_func.func),
                        delayed_func
                            .class
                            .map(|c| Class::with_self_generics(db, ClassNodeRef::from_link(db, c))),
                    );
                    let run = || {
                        let i_s = if let Some(cls) = &func.class {
                            InferenceState::from_class(db, cls)
                        } else {
                            InferenceState::new(db, func.node_ref.file)
                        };
                        self.with_frame(
                            Frame::new(FrameKind::BaseScope, delayed_func.reused_narrowings),
                            || {
                                let result = func
                                    .node_ref
                                    .file
                                    .inference(&i_s)
                                    .ensure_func_diagnostics(func);
                                debug_assert!(result.is_ok());
                            },
                        );
                    };
                    if delayed_func.in_type_checking_only_block {
                        self.with_in_type_checking_only_block(run)
                    } else {
                        run()
                    }
                }
                DelayedDiagnostic::Class(c) => {
                    let node_ref = ClassNodeRef::from_link(db, c);
                    node_ref
                        .file
                        .inference(&InferenceState::new(db, node_ref.file))
                        .ensure_class_diagnostics(node_ref);
                }
                DelayedDiagnostic::ClassTypeParams { class_link } => {
                    ClassNodeRef::from_link(db, class_link).infer_variance_of_type_params(db, true);
                }
                DelayedDiagnostic::ConstraintVerification(constraint) => {
                    verify_constraint(db, constraint)
                }
            }
        }
        debug_assert!(self.delayed_diagnostics.borrow().is_empty());
        *self.delayed_diagnostics.borrow_mut() = old;
    }

    pub fn start_accumulating_types(&self) {
        self.accumulating_types
            .set(self.accumulating_types.get() + 1);
    }

    pub fn stop_accumulating_types(&self) {
        self.accumulating_types
            .set(self.accumulating_types.get() - 1);
    }

    fn merge_or(
        &self,
        i_s: &InferenceState,
        x: Frame,
        mut y: Frame,
        second_frame_optional: bool,
    ) -> Frame {
        if x.unreachable {
            return y;
        }
        if y.unreachable {
            return x;
        }
        let mut new_entries = vec![];

        let add_entry = |new_entries: &mut Vec<_>, e: Entry| {
            invalidate_child_entries(new_entries, i_s.db, &e.key);
            new_entries.push(self.merge_key_with_ancestor_assignment(i_s, &e));
        };
        'outer: for mut x_entry in x.entries {
            for y_entry in &mut y.entries {
                // Only when both sides narrow the same type we actually have learned anything about
                // the expression.
                if x_entry.key.equals(i_s.db, &y_entry.key) {
                    x_entry.union(i_s, y_entry, false);
                    new_entries.push(x_entry);
                    // Make sure we avoid adding another entry below.
                    y_entry.modifies_ancestors = false;
                    continue 'outer;
                }
            }
            if x_entry.modifies_ancestors {
                if second_frame_optional {
                    // This works a bit different for the y frame (as opposed to the x frame). In
                    // case of
                    //
                    //     v == 1 and (u := B())
                    //
                    // u is assigned only if the left frame is true (2), which is not known in
                    // merge_or. This is opposed to
                    //
                    //     (u := B()) and v == 1
                    //
                    // where u is known to always be B(), this is why we just assign it here.
                    new_entries.push(x_entry)
                } else {
                    add_entry(&mut new_entries, x_entry)
                }
            }
        }
        for y_entry in y.entries {
            // Filter out entries that are invalidated by the other side.
            if y_entry.modifies_ancestors
                && !new_entries
                    .iter()
                    .any(|e| y_entry.key.is_child_of(i_s.db, &e.key))
            {
                // (2)
                add_entry(&mut new_entries, y_entry)
            }
        }
        Frame::new(FrameKind::Conditional, new_entries)
    }

    fn merge_conjunction(
        &self,
        i_s: &InferenceState,
        old: Option<FramesWithParentUnions>,
        new: FramesWithParentUnions,
    ) -> FramesWithParentUnions {
        if let Some(old) = old {
            let mut parent_unions = old.parent_unions;
            parent_unions.extend(new.parent_unions);
            FramesWithParentUnions {
                truthy: merge_and(i_s, old.truthy, new.truthy),
                falsey: self.merge_or(i_s, old.falsey, new.falsey, true),
                parent_unions,
            }
        } else {
            new
        }
    }

    pub fn in_try_that_ignores_attribute_errors(&self) -> bool {
        if let Ok(borrowed) = self.try_frames.try_borrow() {
            borrowed
                .iter()
                .any(|try_frame| try_frame.ignores_attribute_error)
        } else {
            recoverable_error!("Expected to be able to access the frames");
            false
        }
    }
}

fn merge_and(i_s: &InferenceState, mut x: Frame, y: Frame) -> Frame {
    if x.unreachable {
        // TODO shouldn't we still merge here?
        return x;
    }
    if y.unreachable {
        return y;
    }
    'outer: for y_entry in y.entries {
        for x_entry in &mut x.entries {
            if x_entry.key.equals(i_s.db, &y_entry.key) {
                if y_entry.modifies_ancestors {
                    // This is the case in walrus assignments with something like
                    //
                    //     isinstance(x, BSubclass) and (x := B())
                    //
                    // This means that the walrus overwrites the previous narrowing again.
                    *x_entry = y_entry;
                } else if let Some(t) = x_entry.common_sub_type(i_s, &y_entry) {
                    x_entry.type_ = t
                } else {
                    x_entry.type_ = EntryKind::Type(Type::Never(NeverCause::Other));
                    x.unreachable = true;
                }
                continue 'outer;
            }
        }
        x.entries.push(y_entry)
    }
    x
}

fn has_explicit_literal(db: &Database, t: &Type) -> bool {
    t.iter_with_unpacked_unions(db).any(|t| match t {
        Type::Literal(literal) => !literal.implicit,
        Type::TypeVar(tv) => match tv.type_var.kind(db) {
            TypeVarKind::Bound(bound) => has_explicit_literal(db, bound),
            _ => false,
        },
        _ => false,
    })
}

pub fn has_custom_special_method(i_s: &InferenceState, t: &Type, method: &str) -> bool {
    t.iter_with_unpacked_unions(i_s.db).any(|t| {
        let Some(cls) = t.inner_generic_class(i_s) else {
            return false;
        };
        let details = cls.lookup(i_s, method, ClassLookupOptions::new(&|_| ()));
        details.lookup.is_some() && !details.class.originates_in_builtins_or_typing(i_s.db)
    })
}

fn has_custom_eq(i_s: &InferenceState, t: &Type) -> bool {
    has_custom_special_method(i_s, t, "__eq__") || has_custom_special_method(i_s, t, "__ne__")
}

fn split_off_enum_member(
    i_s: &InferenceState,
    of_type: &Type,
    enum_member: &EnumMember,
    abort_on_custom_eq: bool,
) -> Option<(Type, Type)> {
    let mut truthy = Type::Never(NeverCause::Other);
    let mut falsey = Type::Never(NeverCause::Other);
    let mut add = |t| falsey.union_in_place(t);
    let mut set_truthy = || truthy = Type::EnumMember(enum_member.clone());

    for sub_t in of_type.iter_with_unpacked_unions(i_s.db) {
        match sub_t {
            Type::Any(_) => {
                if abort_on_custom_eq {
                    return None; // Can always contain a custom eq.
                }
                // Add it to both sides
                set_truthy();
                add(sub_t.clone());
            }
            Type::Class(c) if c.link == i_s.db.python_state.object_link() => {
                if abort_on_custom_eq {
                    return None; // Can always contain a custom eq.
                }
                // Add it to both sides
                set_truthy();
                add(sub_t.clone());
            }
            Type::EnumMember(m) => {
                if enum_member.is_same_member(m) {
                    set_truthy();
                    continue;
                }
            }
            Type::Enum(e2) => {
                if enum_member.enum_.defined_at == e2.defined_at {
                    let enum_class = enum_member.enum_.class(i_s.db);
                    let is_flag =
                        enum_class
                            .mro_maybe_without_object(i_s.db, true)
                            .any(|(_, c)| {
                                c.maybe_class().is_some_and(|c| {
                                    c.node_ref.file_index()
                                        == i_s.db.python_state.enum_file().file_index
                                        && c.name() == "Flag"
                                })
                            });
                    if is_flag {
                        add(sub_t.clone())
                    }
                    for new_member in Enum::implicit_members(e2) {
                        if new_member.member_index == enum_member.member_index {
                            set_truthy();
                        } else if !is_flag {
                            add(Type::EnumMember(new_member))
                        }
                    }
                    continue;
                }
            }
            Type::None => (),
            _ => {
                if matches!(sub_t, Type::Self_)
                    && let Some(cls) = i_s.current_class()
                    && let Some(enum_) = cls.maybe_enum(i_s.db)
                {
                    let (_, f) = split_off_enum_member(
                        i_s,
                        &Type::Enum(enum_),
                        enum_member,
                        abort_on_custom_eq,
                    )?;
                    set_truthy();
                    add(f);
                    continue;
                }
                if abort_on_custom_eq
                    && matches!(
                        enum_member.enum_.kind(i_s),
                        EnumKind::IntEnum | EnumKind::StrEnum
                    )
                {
                    return None;
                }
            }
        };
        if abort_on_custom_eq {
            if has_custom_eq(i_s, sub_t) {
                return None;
            }
            // Also abort on a subclass of IntEnum/StrEnum, because they can match any
            // str/int. (see also is_ambiguous_mix_of_enums)
            if let Type::Enum(e) = sub_t
                && matches!(e.kind(i_s), EnumKind::IntEnum | EnumKind::StrEnum)
            {
                return None;
            }
        }
        add(sub_t.clone())
    }
    Some((truthy, falsey))
}

fn split_off_singleton(
    i_s: &InferenceState,
    of_type: &Type,
    singleton: &Type,
    is_eq: bool,
) -> (Type, Type) {
    let mut truthy = Type::Never(NeverCause::Other);
    let mut falsey = Type::Never(NeverCause::Other);
    let mut add = |t| falsey.union_in_place(t);

    for sub_t in of_type.iter_with_unpacked_unions(i_s.db) {
        match sub_t {
            Type::Any(_) | Type::TypeVar(_) => {
                // Any can be None or something else.
                if is_eq {
                    truthy.union_in_place(sub_t.clone());
                } else {
                    truthy.union_in_place(singleton.clone());
                }
                add(sub_t.clone());
            }
            Type::Literal(literal1) => match singleton {
                Type::Literal(literal2) if literal1.value(i_s.db) == literal2.value(i_s.db) => {
                    let true_literal = || {
                        let mut new_literal = literal1.clone();
                        new_literal.implicit = false;
                        Type::Literal(new_literal)
                    };
                    truthy.union_in_place(true_literal());
                }
                _ => add(sub_t.clone()),
            },
            _ if singleton == sub_t => truthy.union_in_place(singleton.clone()),
            _ => {
                if let Type::Literal(literal2) = singleton {
                    if let Some((tr, fa)) =
                        maybe_split_bool_from_literal(i_s.db, sub_t, &literal2.kind)
                    {
                        truthy.union_in_place(tr);
                        add(fa);
                        continue;
                    }
                    if has_custom_eq(i_s, sub_t) {
                        truthy.union_in_place(sub_t.clone());
                        add(sub_t.clone());
                        continue;
                    }
                    if sub_t.is_simple_super_type_of(i_s, singleton).bool() {
                        truthy.union_in_place(singleton.clone())
                    } else if let Type::Enum(e) = sub_t
                        && matches!(e.kind(i_s), EnumKind::IntEnum | EnumKind::StrEnum)
                    {
                        truthy.union_in_place(sub_t.clone());
                    }
                }
                add(sub_t.clone())
            }
        }
    }
    (truthy, falsey)
}

fn narrow_is_or_eq(
    i_s: &InferenceState,
    key: FlowKey,
    checking_t: &Type,
    other_t: &Type,
    is_eq: bool,
) -> Option<(Frame, Frame)> {
    let split_singleton = |key: FlowKey| {
        let (truthy, falsey) = split_off_singleton(i_s, checking_t, other_t, is_eq);
        (
            Frame::from_type(key.clone(), truthy),
            Frame::from_type(key, falsey),
        )
    };

    match other_t {
        Type::None if !is_eq => {
            // Mypy makes it possible to narrow None against a bare TypeVar.
            Some(if matches!(checking_t, Type::TypeVar(_)) {
                (
                    Frame::from_type(key.clone(), Type::None),
                    Frame::from_type(key, checking_t.clone()),
                )
            } else {
                split_singleton(key)
            })
        }
        Type::None => {
            let (_, falsey) = split_off_singleton(i_s, checking_t, &Type::None, is_eq);
            Some((Frame::new_conditional(), Frame::from_type(key, falsey)))
        }
        Type::EnumMember(member) if member.implicit => {
            let mut new_member = member.clone();
            new_member.implicit = false;
            narrow_is_or_eq(i_s, key, checking_t, &Type::EnumMember(new_member), is_eq)
        }
        Type::EnumMember(member) if !member.implicit => {
            let (truthy, falsey) = split_off_enum_member(i_s, checking_t, member, is_eq)?;
            let result = (
                Frame::from_type(key.clone(), truthy),
                Frame::from_type(key, falsey),
            );
            Some(result)
        }
        Type::Enum(enum_) if enum_.members.len() == 1 => {
            // Enums with a single item can be compared to that item.
            narrow_is_or_eq(
                i_s,
                key,
                checking_t,
                &Type::EnumMember(EnumMember::new(enum_.clone(), 0, false)),
                is_eq,
            )
        }
        // Mypy does only want to narrow if there are explicit literals on one side. See also
        // comments around testNarrowingEqualityFlipFlop.
        Type::Literal(literal1)
            if is_eq
                && (!literal1.implicit
                    || key.is_simple_name() && !i_s.db.mypy_compatible()
                    || has_explicit_literal(i_s.db, checking_t))
                || !is_eq && matches!(literal1.kind, LiteralKind::Bool(_)) =>
        {
            let (true_type, false_type) = split_off_singleton(i_s, checking_t, other_t, is_eq);
            Some((
                Frame::from_type(key.clone(), true_type),
                Frame::from_type(key, false_type),
            ))
        }
        /* Originally enabled in 566ee94f6, but had issues...
        Type::Literal(_) if is_eq && !has_custom_eq(i_s, left_t) => Some((
            Frame::new_unreachable(),
            Frame::from_type(key, left_t.clone()),
        )),
        */
        Type::Class(c) if c.link == i_s.db.python_state.ellipsis_link() => {
            Some(split_singleton(key))
        }
        _ => match checking_t {
            Type::Union(_) => {
                // Remove None from the checking side, if the other side matches everything except None.
                if checking_t
                    .iter_with_unpacked_unions(i_s.db)
                    .any(|t| matches!(t, Type::None))
                {
                    let (_, falsey) = split_off_singleton(i_s, checking_t, &Type::None, is_eq);
                    if falsey.is_simple_sub_type_of(i_s, other_t).bool()
                        || falsey.is_simple_super_type_of(i_s, other_t).bool()
                    {
                        return Some((Frame::from_type(key, falsey), Frame::new_conditional()));
                    }
                }
                None
            }
            _ => None,
        },
    }
}

fn maybe_split_bool_from_literal(
    db: &Database,
    t: &Type,
    literal: &LiteralKind,
) -> Option<(Type, Type)> {
    if let Type::Class(class) = t
        && let LiteralKind::Bool(b) = literal
        && class.link == db.python_state.bool_node_ref().as_link()
    {
        return Some((
            Type::Literal(Literal::new(LiteralKind::Bool(*b))),
            Type::Literal(Literal::new(LiteralKind::Bool(!*b))),
        ));
    }
    None
}

fn split_truthy_and_falsey(i_s: &InferenceState, inf: &TruthyInferred) -> Option<(Type, Type)> {
    if inf.has_partial_container(i_s.db) {
        None // Do not narrow here for now. The truthy side could be narrowed to Never.
    } else {
        match inf {
            TruthyInferred::Simple {
                inf,
                truthiness: None,
            } => split_truthy_and_falsey_t(i_s, &inf.as_cow_type(i_s)),
            TruthyInferred::Simple {
                inf,
                truthiness: Some(true),
            } => Some((inf.as_type(i_s), Type::Never(NeverCause::Other))),
            TruthyInferred::Simple {
                inf,
                truthiness: Some(false),
            } => Some((Type::Never(NeverCause::Other), inf.as_type(i_s))),
            TruthyInferred::Union(infs) => {
                let mut truthy = Type::Never(NeverCause::Other);
                let mut falsey = Type::Never(NeverCause::Other);
                for inf in infs {
                    if let Some((t, f)) = split_truthy_and_falsey(i_s, inf) {
                        truthy.union_in_place(t);
                        falsey.union_in_place(f);
                    } else {
                        truthy.union_in_place(inf.as_cow_type(i_s).into_owned());
                        falsey.union_in_place(inf.as_cow_type(i_s).into_owned());
                    }
                }
                Some((truthy, falsey))
            }
        }
    }
}

fn split_truthy_and_falsey_t(i_s: &InferenceState, t: &Type) -> Option<(Type, Type)> {
    let split_truthy_and_falsey_single = |t: &Type| {
        let check = |condition| {
            if condition {
                Some((t.clone(), Type::Never(NeverCause::Other)))
            } else {
                Some((Type::Never(NeverCause::Other), t.clone()))
            }
        };
        let check_literal = |literal: &Literal| match &literal.kind {
            LiteralKind::Bool(b) => check(*b),
            LiteralKind::Int(i) => check(*i != 0.into()),
            _ => None,
        };
        let narrow_by_return_literal = |l: LookupDetails| {
            let inf = l.lookup.into_maybe_inferred()?;
            Some(match inf.as_cow_type(i_s).maybe_callable(i_s)? {
                CallableLike::Callable(c) => match &c.return_type {
                    Type::Literal(literal) => check_literal(literal),
                    _ => None,
                },
                _ => None,
            })
        };

        let check_enum = |enum_| {
            // By default bool(<Some Enum Member>) is True, but __bool__/__len__ can change that.
            let check_dunder = |name| {
                let l = lookup_on_enum_instance(i_s, &|_| (), enum_, name);
                narrow_by_return_literal(l)
            };
            check_dunder("__bool__")
                .or_else(|| check_dunder("__len__"))
                .unwrap_or_else(|| Some((t.clone(), Type::Never(NeverCause::Other))))
        };
        match t {
            Type::None => Some((Type::Never(NeverCause::Other), Type::None)),
            Type::Literal(literal) => check_literal(literal),
            Type::Tuple(tup) => match &tup.args {
                TupleArgs::ArbitraryLen(t) => Some((
                    Type::Tuple(Tuple::new(TupleArgs::WithUnpack(WithUnpack {
                        before: Arc::new([(**t).clone()]),
                        unpack: TupleUnpack::ArbitraryLen((**t).clone()),
                        after: Arc::new([]),
                    }))),
                    Type::Tuple(Tuple::new_fixed_length(Arc::new([]))),
                )),
                _ => None,
            },
            Type::Class(c) => maybe_split_bool_from_literal(i_s.db, t, &LiteralKind::Bool(true))
                .or_else(|| {
                    let class = c.class(i_s.db);
                    let narrow_class_by_return_literal = |name| {
                        let l = class.lookup(i_s, name, ClassLookupOptions::new(&|_| ()));
                        narrow_by_return_literal(l)
                    };

                    if c.link == i_s.db.python_state.int_link() {
                        Some((
                            t.clone(),
                            Type::Literal(Literal::new(LiteralKind::Int(0.into()))),
                        ))
                    } else if c.link == i_s.db.python_state.str_link() {
                        Some((
                            t.clone(),
                            Type::Literal(Literal::new(LiteralKind::String(DbString::Static("")))),
                        ))
                    } else if c.link == i_s.db.python_state.bytes_link() {
                        Some((
                            t.clone(),
                            Type::Literal(Literal::new(LiteralKind::Bytes(DbBytes::Static(b"")))),
                        ))
                    } else if let Some(maybe_specific_bool) =
                        narrow_class_by_return_literal("__bool__")
                    {
                        maybe_specific_bool
                    } else if let Some(nt) = class.maybe_named_tuple_base(i_s.db) {
                        check_literal(&Literal::new(LiteralKind::Int(nt.params().len().into())))
                    } else if let Some(maybe_specific_len) =
                        narrow_class_by_return_literal("__len__")
                    {
                        maybe_specific_len
                    } else if class.use_cached_class_infos(i_s.db).is_final {
                        Some((t.clone(), Type::Never(NeverCause::Other)))
                    } else {
                        None
                    }
                }),
            Type::EnumMember(member) => check_enum(&member.enum_),
            Type::Enum(enum_) => check_enum(enum_),
            Type::TypedDict(td) if td.has_required_members(i_s.db) => {
                Some((t.clone(), Type::NEVER))
            }
            _ => None,
        }
    };

    match t {
        Type::Union(union) => {
            let mut truthy = Type::Never(NeverCause::Other);
            let mut falsey = Type::Never(NeverCause::Other);
            let mut had_split = false;
            for t in union.iter() {
                let result = split_truthy_and_falsey_t(i_s, t);
                had_split |= result.is_some();
                let (new_true, new_false) = result.unwrap_or_else(|| (t.clone(), t.clone()));
                truthy.union_in_place(new_true);
                falsey.union_in_place(new_false);
            }
            had_split.then_some((truthy, falsey))
        }
        Type::Never(cause) => Some((Type::Never(*cause), Type::Never(*cause))),
        _ => split_truthy_and_falsey_single(t),
    }
}

impl<'file> Inference<'_, 'file, '_> {
    pub fn is_unreachable(&self) -> bool {
        FLOW_ANALYSIS.with(|fa| fa.is_unreachable())
    }

    pub fn allow_redefinitions_in_specific_scope(&self) -> bool {
        self.flags().allow_redefinition || FLOW_ANALYSIS.with(|fa| fa.in_pattern_matching.get() > 0)
    }

    pub fn in_type_checking_only_block(&self) -> bool {
        FLOW_ANALYSIS.with(|fa| fa.in_type_checking_only_block.get())
    }

    pub fn in_conditional(&self) -> bool {
        FLOW_ANALYSIS.with(|fa| {
            let frames = fa.frames.borrow();
            let Some(last) = frames.last() else {
                //recoverable_error!("in_conditional should not have empty frames");
                // TODO This should probably not happen, because we are not sure if we are in a
                // conditional
                return false;
            };
            matches!(last.kind, FrameKind::Conditional)
        })
    }

    pub fn is_initialized(&self, first_index: NodeIndex) -> bool {
        let key = FlowKey::Name(PointLink::new(self.file.file_index, first_index));
        FLOW_ANALYSIS.with(|fa| fa.lookup_entry(self.i_s.db, key).is_some())
    }

    pub fn mark_current_frame_unreachable(&self) {
        FLOW_ANALYSIS.with(|fa| fa.mark_current_frame_unreachable())
    }

    #[inline]
    pub fn add_initial_name_definition(&self, name: NameDef) {
        FLOW_ANALYSIS.with(|fa| {
            fa.add_initial_name_definition(
                self.i_s.db,
                PointLink::new(self.file.file_index, name.name_index()),
            )
        })
    }

    pub fn maybe_lookup_narrowed_name(
        &self,
        original_name_index: NodeIndex,
        name_link: PointLink,
    ) -> Option<Inferred> {
        let (result, deleted) = FLOW_ANALYSIS
            .with(|fa| fa.lookup_narrowed_key_and_deleted(self.i_s.db, FlowKey::Name(name_link)));
        if deleted {
            self.add_issue(original_name_index, IssueKind::ReadingDeletedVariable);
            return Some(Inferred::new_any_from_error());
        }
        let result = result?;
        debug!(
            "Use narrowed {} as {}",
            NodeRef::from_link(self.i_s.db, name_link).as_code(),
            result.format_short(self.i_s)
        );
        Some(result)
    }

    pub fn maybe_lookup_narrowed_primary(&self, primary: Primary) -> Option<Inferred> {
        self.maybe_has_primary_entry(primary).map(|x| x.1)
    }

    pub fn maybe_lookup_narrowed_primary_target(
        &self,
        primary_target: PrimaryTarget,
    ) -> Option<Inferred> {
        let key = self.key_from_primary_target(primary_target)?;
        FLOW_ANALYSIS
            .with(|fa| fa.lookup_narrowed_key_and_deleted(self.i_s.db, key))
            .0
    }

    pub fn flow_analysis_for_assert(&self, assert_stmt: AssertStmt) {
        let (expr, message_expr) = assert_stmt.unpack();
        if expr
            .maybe_tuple()
            .is_some_and(|tup| tup.iter().next().is_some())
        {
            self.add_issue(
                expr.index(),
                IssueKind::AssertionAlwaysTrueBecauseOfParentheses,
            );
        }

        let (_, true_frame, false_frame) = self.find_guards_in_expr(expr);

        FLOW_ANALYSIS.with(|fa| {
            if let Some(message_expr) = message_expr {
                fa.with_frame(false_frame, || {
                    self.infer_expression(message_expr);
                });
            }

            let assert_point = self.point(assert_stmt.index());
            if assert_point.calculated() && assert_point.specific() == Specific::AssertAlwaysFails {
                fa.mark_current_frame_unreachable()
            }
            fa.overwrite_frame(self.i_s.db, true_frame)
        })
    }

    pub fn narrow_or_widen_name_target(
        &self,
        first_name_link: PointLink,
        declaration_t: &Type,
        new_t: &Type,
        check_for_error: impl FnOnce() -> RedefinitionResult,
    ) {
        self.narrow_or_widen_target(
            FlowKey::Name(first_name_link),
            declaration_t,
            new_t,
            check_for_error,
        )
    }

    fn narrow_or_widen_target(
        &self,
        key: FlowKey,
        declaration_t: &Type,
        new_t: &Type,
        check_for_error: impl FnOnce() -> RedefinitionResult,
    ) {
        let new_t = match declaration_t.could_be_a_literal() {
            CouldBeALiteral::Yes { .. } => Cow::Borrowed(new_t),
            _ => new_t.avoid_implicit_literal_cow(self.i_s.db),
        };
        self.narrow_or_widen_target_internal(key, declaration_t, &new_t, check_for_error)
    }

    fn narrow_or_widen_target_internal(
        &self,
        key: FlowKey,
        declaration_t: &Type,
        new_t: &Type,
        check_for_error: impl FnOnce() -> RedefinitionResult,
    ) {
        let widens = false;
        // It seems like explicit Any is treated in a special way, see tests
        // testIsinstanceNarrowAnyExplicit and testIsinstanceNarrowAnyImplicit
        if let Type::Any(AnyCause::Explicit) = declaration_t {
            // Still check for stuff like Final reassignments
            check_for_error();
            // Remove the key
            FLOW_ANALYSIS.with(|fa| {
                fa.remove_key(self.i_s, &key);
                if let Some(mut tos_frame) = fa.maybe_tos_frame() {
                    invalidate_child_entries(&mut tos_frame.entries, self.i_s.db, &key);
                }
            });
            return;
        }
        let error_result = if new_t.is_any() && !declaration_t.is_any_or_any_in_union(self.i_s.db) {
            if self.allow_redefinitions_in_specific_scope()
                && matches!(key, FlowKey::Name(_))
                && matches!(check_for_error(), RedefinitionResult::RedefinitionAllowed)
            {
                RedefinitionResult::RedefinitionAllowed
            } else {
                if declaration_t.is_none_or_none_in_union(self.i_s.db) {
                    // This is a special case like
                    //
                    //     def foo(x: int | None) -> None:
                    //         if x is None:
                    //             x = assign_with_untyped_function()
                    //             reveal_type(x) # Revealed type is "Union[builtins.int, Any]"
                    //         reveal_type(x)     # Revealed type is "Union[builtins.int, Any]"
                    //
                    // This special case is important, because a lot of the time when Any is returned
                    // people actually remove None from the union.
                    self.save_narrowed(
                        key,
                        declaration_t
                            .remove_none(self.i_s.db)
                            .into_owned()
                            .union(new_t.clone()),
                        widens,
                    )
                } else {
                    // Any should not be narrowed if it is not part of a union with any.
                    FLOW_ANALYSIS.with(|fa| fa.remove_key_if_modifies_ancestors(self.i_s, &key));
                }
                return;
            }
        } else {
            check_for_error()
        };
        let allow_redefinition = match error_result {
            RedefinitionResult::TypeMismatch(true) => return,
            RedefinitionResult::TypeMismatch(false) => false,
            RedefinitionResult::RedefinitionAllowed => true,
        };
        self.save_narrowed(key, new_t.clone(), allow_redefinition);
    }

    pub fn narrow_or_widen_self_target(
        &self,
        primary_target: PrimaryTarget,
        declaration_t: &Type,
        new_t: &Type,
        check_for_error: impl FnOnce() -> RedefinitionResult,
    ) {
        if let Some(key) = self.key_from_primary_target(primary_target) {
            self.narrow_or_widen_target(key, declaration_t, new_t, check_for_error)
        }
    }

    pub fn save_narrowed_primary_target(&self, primary_target: PrimaryTarget, t: &Type) {
        if let Some(key) = self.key_from_primary_target(primary_target) {
            self.save_narrowed(key, t.clone(), false)
        }
    }

    pub fn save_narrowed_partial(&self, origin: PrimaryOrAtom, type_: Type) {
        let key = match origin {
            PrimaryOrAtom::Primary(p) => self.key_from_primary(p).key,
            PrimaryOrAtom::Atom(atom) => self.key_from_atom(atom),
        }
        .unwrap();
        self.save_narrowed(key, type_, false)
    }

    pub fn save_narrowed_partial_primary_target_or_atom(
        &self,
        origin: PrimaryTargetOrAtom,
        type_: Type,
    ) {
        self.save_narrowed(
            self.key_from_primary_target_or_atom(origin).unwrap(),
            type_,
            false,
        )
    }

    pub fn save_narrowed_partial_target(&self, target: &Target, type_: Type) {
        self.save_narrowed(
            match target {
                Target::Name(n) => self.key_from_name_def(*n),
                Target::NameExpression(primary_target, name) => {
                    let base_key = self
                        .key_from_primary_target_or_atom(primary_target.first())
                        .unwrap();
                    self.key_from_attribute(base_key, name.name())
                }
                _ => unreachable!(),
            },
            type_,
            false,
        )
    }

    fn save_narrowed(&self, key: FlowKey, type_: Type, widens: bool) {
        FLOW_ANALYSIS.with(|fa| {
            fa.overwrite_entry(
                self.i_s,
                Entry {
                    key,
                    type_: EntryKind::Type(type_),
                    modifies_ancestors: true,
                    deleted: false,
                    widens,
                },
            )
        })
    }

    pub(crate) fn self_lookup_with_flow_analysis(
        &self,
        c: Class,
        self_symbol: NodeIndex,
        add_issue: &dyn Fn(IssueKind),
    ) -> Result<Option<Inferred>, FunctionDef<'file>> {
        let name_node_ref = NodeRef::new(self.file, self_symbol);
        let name_def_node_ref = name_node_ref.name_def_ref_of_name();
        let c = Class::with_self_generics(self.i_s.db, c.node_ref);
        let func_def = func_of_self_symbol(self.file, self_symbol);
        let func = Function::new(NodeRef::new(self.file, func_def.index()), Some(c));
        let i_s = &self.i_s.with_func_context(&func);
        let recheck_if_on_actual_self = || {
            // We cache all potential self assignments while name binding. Here we recheck that
            // this is an assignment on self and not on cls or a staticmethod param.

            // TODO We need to recheck all following symbols to the self symbol, because there
            // might be a valid assignment in there.
            matches!(func.first_param_kind(self.i_s), FirstParamKind::Self_)
        };
        if !name_node_ref.point().needs_flow_analysis() {
            let assignment = name_node_ref
                .expect_name()
                .maybe_self_assignment_name_on_self_like()
                .expect("Expected an assignment, because self type var without flow analysis");
            match assignment.unpack() {
                AssignmentContent::WithAnnotation(_, annotation, right_side) => {
                    func.ensure_cached_func(&InferenceState::from_class(self.i_s.db, &c));
                    if !recheck_if_on_actual_self() {
                        return Ok(None);
                    }
                    let inference = self.file.inference(i_s);
                    inference.ensure_cached_annotation(annotation, right_side.is_some());
                    if !matches!(
                        self.file.points.get(annotation.index()).specific(),
                        Specific::AnnotationOrTypeCommentClassVar
                            | Specific::AnnotationOrTypeCommentFinal
                    ) {
                        return Ok(Some(inference.use_cached_annotation(annotation)));
                    }
                }
                _ => unreachable!("For now we don't support something like this"),
            }
        }
        let p = name_def_node_ref.point();
        if p.calculating() {
            debug!(
                "The symbol {} is already calculating",
                name_def_node_ref.as_code()
            );
            return Err(func_def);
        }
        if !p.calculated() {
            if !recheck_if_on_actual_self() {
                return Ok(None);
            }
            let result = FLOW_ANALYSIS.with(|fa| {
                // The class should have self generics within the functions
                self.ensure_func_diagnostics_for_self_attribute(fa, func)
            });
            if result.is_err() {
                // It is possible that the self variable is defined in a super class and we are
                // accessing it before definition in the current class, so use the one from the
                // super class.
                if let Some(inf) = c
                    .instance()
                    .lookup(
                        self.i_s,
                        name_def_node_ref.as_code(),
                        // It seems like this is not necessary, because it is added anyway
                        InstanceLookupOptions::new(add_issue)
                            .with_skip_first_of_mro(self.i_s.db, &c)
                            .with_no_check_dunder_getattr(),
                    )
                    .lookup
                    .into_maybe_inferred()
                {
                    return Ok(Some(inf));
                }
                return Err(func_def);
            }
        }
        Ok(Some(
            self.file
                .inference(i_s)
                .infer_name_of_definition_by_index(self_symbol),
        ))
    }

    fn ensure_func_diagnostics_for_self_attribute(
        &self,
        fa: &FlowAnalysis,
        function: Function,
    ) -> Result<(), ()> {
        let mut function = function; // lifetime issues?!
        if let Some(class) = function.class.as_mut() {
            let result = class.ensure_calculated_diagnostics_for_class(self.i_s.db);
            if result.is_err() {
                debug!(
                    "The class {:?} could not be calculated for func {:?} diagnostics",
                    class.name(),
                    function.name()
                );
            }
            result?
        }

        fa.with_new_empty_and_delay_further(self.i_s.db, || self.ensure_func_diagnostics(function))
    }

    pub fn flow_analysis_for_ternary(
        &self,
        t: Ternary,
        result_context: &mut ResultContext,
    ) -> Inferred {
        let (if_, condition, else_) = t.unpack();
        let (_, true_frame, false_frame) = self.find_guards_in_expr_part(condition, result_context);
        FLOW_ANALYSIS.with(|fa| {
            let mut if_inf = None;
            let mut else_inf = None;
            let if_backup = self.file.points.backup(if_.index()..condition.index());
            let true_frame_backup = true_frame.clone();

            let mut use_else_context = false;
            let mut needs_recalculation = false;
            let mut true_frame = fa.with_frame(true_frame, || {
                if result_context.has_explicit_type() {
                    if_inf = Some(self.infer_expression_part_with_context(if_, result_context));
                    return;
                }
                let (inf, had_error) = self.i_s.avoid_errors_within(|i_s| {
                    self.file
                        .inference(i_s)
                        .infer_expression_part_with_context(if_, result_context)
                });
                use_else_context = inf
                    .as_cow_type(self.i_s)
                    .has_any_with_unknown_type_params(self.i_s.db);
                needs_recalculation = use_else_context || had_error;
                if_inf = Some(inf);
            });

            let false_frame = fa.with_frame(false_frame, || {
                else_inf = Some(
                    if let Some(if_inf) = if_inf
                        .as_ref()
                        .filter(|_| !use_else_context && !result_context.has_explicit_type())
                    {
                        // Mypy passes the context without literals here.
                        self.infer_expression_with_context(
                            else_,
                            &mut ResultContext::new_known(
                                &if_inf.as_type(self.i_s).avoid_implicit_literal(self.i_s.db),
                            ),
                        )
                    } else {
                        self.infer_expression_with_context(else_, result_context)
                    },
                );
            });
            if needs_recalculation {
                self.file.points.reset_from_backup(&if_backup);
                true_frame = fa.with_frame(true_frame_backup, || {
                    if_inf = Some(
                        if let Some(else_inf) = else_inf.as_ref().filter(|_| use_else_context) {
                            // Mypy passes the context without literals here.
                            self.infer_expression_part_with_context(
                                if_,
                                &mut ResultContext::new_known(
                                    &else_inf
                                        .as_type(self.i_s)
                                        .avoid_implicit_literal(self.i_s.db),
                                ),
                            )
                        } else {
                            self.infer_expression_part_with_context(if_, result_context)
                        },
                    );
                });
            }

            fa.merge_conditional(self.i_s, true_frame, false_frame);
            if_inf
                .unwrap()
                .simplified_union(self.i_s, else_inf.unwrap())
        })
    }

    pub(crate) fn flow_analysis_for_if_stmt(
        &self,
        if_stmt: IfStmt,
        class: Option<Class>,
        func: Option<&Function>,
    ) {
        self.process_ifs(if_stmt.iter_blocks(), class, func)
    }

    pub(crate) fn flow_analysis_for_while_stmt(
        &self,
        while_stmt: WhileStmt,
        class: Option<Class>,
        func: Option<&Function>,
    ) {
        let (condition, block, else_block) = while_stmt.unpack();
        self.process_loop(Some(condition), block, else_block, class, func, || ())
    }

    fn process_loop(
        &self,
        if_expr: Option<NamedExpression>,
        block: Block,
        else_block: Option<ElseBlock>,
        class: Option<Class>,
        func: Option<&Function>,
        assign_for_stmt_names: impl FnOnce(),
    ) {
        FLOW_ANALYSIS.with(|fa| {
            let (true_frame, false_frame) = if let Some(if_expr) = if_expr {
                let (_, truthy, falsey) = self.find_guards_in_named_expr(if_expr);
                (truthy, falsey)
            } else {
                (Frame::new_conditional(), Frame::new_conditional())
            };
            let (mut after_frame, loop_details) = fa.with_new_loop_frame(true_frame, || {
                assign_for_stmt_names();
                self.calc_block_diagnostics(block, class, func);
            });
            for continue_frame in loop_details.continue_frames {
                after_frame = fa.merge_or(self.i_s, after_frame, continue_frame, false);
            }
            if if_expr.is_some() {
                after_frame = merge_and(self.i_s, after_frame, false_frame.clone());
            }
            // When we have a loop we need to merge with the statements before, because the
            // loop is not guaranteed to start.
            after_frame = fa.merge_or(self.i_s, false_frame, after_frame, false);
            if let Some(else_block) = else_block {
                after_frame = fa.with_frame(after_frame, || {
                    self.calc_block_diagnostics(else_block.block(), class, func)
                });
            }
            for break_frame in loop_details.break_frames {
                after_frame = fa.merge_or(self.i_s, after_frame, break_frame, false);
            }
            fa.merge_conditional(self.i_s, after_frame, Frame::new_unreachable());
        })
    }

    pub fn flow_analysis_for_break_stmt(&self, while_stmt: BreakStmt) {
        FLOW_ANALYSIS.with(|fa| {
            let mut loop_details = fa.loop_details.borrow_mut();
            let Some(loop_details) = loop_details.as_mut() else {
                self.add_issue(while_stmt.index(), IssueKind::BreakOutsideLoop);
                return;
            };
            loop_details
                .break_frames
                .push(fa.merge_frames_for_index(self.i_s.db, loop_details.loop_frame_index));
            fa.mark_current_frame_unreachable();
        });
    }

    pub fn flow_analysis_for_continue_stmt(&self, while_stmt: ContinueStmt) {
        FLOW_ANALYSIS.with(|fa| {
            let mut loop_details = fa.loop_details.borrow_mut();
            let Some(loop_details) = loop_details.as_mut() else {
                self.add_issue(while_stmt.index(), IssueKind::ContinueOutsideLoop);
                return;
            };
            loop_details
                .continue_frames
                .push(fa.merge_frames_for_index(self.i_s.db, loop_details.loop_frame_index));
            fa.mark_current_frame_unreachable();
        });
    }

    pub(crate) fn flow_analysis_for_for_stmt(
        &self,
        for_stmt: ForStmt,
        class: Option<Class>,
        func: Option<&Function>,
        is_async: bool,
    ) {
        let (star_targets, star_exprs, block, else_block) = for_stmt.unpack();
        self.process_loop(None, block, else_block, class, func, || {
            self.cache_for_stmt_names(star_targets, star_exprs, is_async)
        })
    }

    fn process_ifs(
        &self,
        mut if_blocks: IfBlockIterator,
        class: Option<Class>,
        func: Option<&Function>,
    ) {
        let Some(if_block) = if_blocks.next() else {
            return;
        };
        let name_binder_check = self
            .point(if_block.first_leaf_index())
            .maybe_calculated_and_specific();
        if name_binder_check == Some(Specific::IfBranchAfterAlwaysReachableInNameBinder) {
            return self.process_ifs(if_blocks, class, func);
        }

        match if_block {
            IfBlockType::If(if_expr, block) => {
                let (_, true_frame, false_frame) = self.find_guards_in_named_expr(if_expr);
                match name_binder_check {
                    Some(Specific::IfBranchAlwaysReachableInTypeCheckingBlock) => {
                        FLOW_ANALYSIS.with(|fa| {
                            fa.with_in_type_checking_only_block(|| {
                                self.calc_block_diagnostics(block, class, func);
                            })
                        });
                        self.process_ifs(if_blocks, class, func)
                    }
                    Some(Specific::IfBranchAlwaysReachableInNameBinder) => {
                        self.calc_block_diagnostics(block, class, func);
                        self.process_ifs(if_blocks, class, func)
                    }
                    Some(Specific::IfBranchAlwaysUnreachableInNameBinder) => {
                        self.process_ifs(if_blocks, class, func)
                    }
                    _ => {
                        FLOW_ANALYSIS.with(|fa| {
                            let true_frame = fa.with_frame(true_frame, || {
                                self.calc_block_diagnostics(block, class, func)
                            });
                            let false_frame = fa.with_frame(false_frame, || {
                                self.process_ifs(if_blocks, class, func)
                            });

                            fa.merge_conditional(self.i_s, true_frame, false_frame);
                        });
                    }
                }
            }
            IfBlockType::Else(else_block) => {
                self.calc_block_diagnostics(else_block.block(), class, func)
            }
        }
    }

    pub fn flow_analysis_for_comprehension_with_comp_ifs<T>(
        &self,
        for_if_clauses: ForIfClauseIterator,
        mut comp_ifs: CompIfIterator,
        item_callable: impl FnOnce() -> T,
    ) -> T {
        if let Some(comp_if) = comp_ifs.next() {
            let (_, true_frame, _) = self
                .find_guards_in_expr_part(comp_if.expression_part(), &mut ResultContext::Unknown);
            FLOW_ANALYSIS.with(|fa| {
                fa.with_frame_and_result(true_frame, || {
                    self.flow_analysis_for_comprehension_with_comp_ifs(
                        for_if_clauses,
                        comp_ifs,
                        item_callable,
                    )
                })
                .1
            })
        } else {
            self.infer_comprehension_recursively(for_if_clauses, item_callable)
        }
    }

    pub fn flow_analysis_for_conjunction(&self, and: Conjunction) -> Inferred {
        self.check_conjunction(and).0.into_inferred(self.i_s)
    }

    pub fn flow_analysis_for_del_stmt(&self, del_targets: DelTargets) {
        debug!(
            r#"Flow analysis for "del {}" {}"#,
            del_targets.as_code(),
            NodeRef::new(self.file, del_targets.index()).debug_info(self.i_s.db)
        );
        let _indent = debug_indent();
        for del_target in del_targets.iter() {
            match del_target {
                DelTarget::Target(target) => self.flow_analysis_for_del_target(target),
                DelTarget::DelTargets(del_targets) => self.flow_analysis_for_del_stmt(del_targets),
            }
        }
    }

    pub fn delete_name(&self, name_def: NameDef) {
        FLOW_ANALYSIS.with(|fa| {
            fa.overwrite_entry(
                self.i_s,
                Entry {
                    key: self.key_from_name_def(name_def),
                    type_: EntryKind::Type(Type::ERROR),
                    modifies_ancestors: true,
                    deleted: true,
                    widens: false,
                },
            )
        })
    }

    pub fn flow_analysis_for_del_target(&self, target: Target) {
        match target {
            Target::Name(name_def) => {
                if self.infer_name_target(name_def, true).is_none() {
                    debug!("Name not found for del stmt");
                    self.add_issue(
                        name_def.index(),
                        IssueKind::NameError {
                            name: name_def.as_code().into(),
                            note: None,
                        },
                    );
                    self.assign_any_to_target(target, NodeRef::new(self.file, name_def.index()));
                } else {
                    debug!("Assigned deleted variable {}", name_def.as_code());
                    // TODO this should be something like Specific::DeletedVariable
                    NodeRef::new(self.file, name_def.index())
                        .set_point(Point::new_specific(Specific::AnyDueToError, Locality::Todo))
                }
                self.delete_name(name_def);
            }
            Target::NameExpression(primary_target, name_def) => {
                // We do a normal lookup to check that the attribute is there.
                let inf = self.infer_primary_target_or_atom(primary_target.first());
                inf.run_after_lookup_on_each_union_member(
                    self.i_s,
                    self.file,
                    name_def.as_code(),
                    LookupKind::Normal,
                    &|issue| self.add_issue(primary_target.index(), issue),
                    &mut |on_t, details| {
                        if matches!(details.lookup, LookupResult::None) {
                            add_attribute_error(
                                self.i_s,
                                NodeRef::new(self.file, primary_target.index()),
                                &inf.as_cow_type(self.i_s),
                                on_t,
                                name_def.as_code(),
                            );
                        }
                        // TODO this should still be implemented for all cases
                        if details.attr_kind.is_read_only_property() {
                            let named_tuple_attr_cannot_be_deleted = || {
                                self.add_issue(
                                    primary_target.index(),
                                    IssueKind::NamedTupleAttributeCannotBeDeleted,
                                )
                            };
                            if let Some(cls) = on_t.maybe_class(self.i_s.db)
                                && cls.maybe_named_tuple_base(self.i_s.db).is_some()
                            {
                                named_tuple_attr_cannot_be_deleted()
                            }
                            if let Type::NamedTuple(_) = on_t {
                                named_tuple_attr_cannot_be_deleted()
                            }
                        }
                    },
                );
            }
            Target::IndexExpression(primary_target) => {
                let base = self.infer_primary_target_or_atom(primary_target.first());
                let PrimaryContent::GetItem(s) = primary_target.second() else {
                    unreachable!()
                };
                let slice_type = SliceType::new(self.file, primary_target.index(), s);
                let node_ref = slice_type.as_node_ref();
                base.lookup(self.i_s, node_ref, "__delitem__", LookupKind::OnlyType)
                    .into_inferred()
                    .execute_with_details(
                        self.i_s,
                        &slice_type.as_args(*self.i_s),
                        &mut ResultContext::ExpectUnused,
                        OnTypeError::new(&on_argument_type_error),
                    );
            }
            Target::Tuple(_) | Target::Starred(_) => unreachable!(),
        }
    }

    pub(crate) fn flow_analysis_for_try_stmt(
        &self,
        try_stmt: TryStmt,
        class: Option<Class>,
        func: Option<&Function>,
    ) {
        let mut except_bodies = 0;
        let mut finally_block = None;
        for b in try_stmt.iter_blocks() {
            match b {
                TryBlockType::Except(_) => except_bodies += 1,
                TryBlockType::Finally(block) => {
                    finally_block = Some(block);
                }
                _ => (),
            }
        }

        let (after_ok, after_exception) =
            self.flow_analysis_for_try_stmt_without_finally(try_stmt, class, func, except_bodies);

        FLOW_ANALYSIS.with(|fa| {
            fa.merge_conditional(self.i_s, after_ok, after_exception);
            let old_unreachable = fa.is_unreachable();
            // TODO this if is wrong and should not be here. Please remove once we recheck finally
            if old_unreachable {
                fa.tos_frame().unreachable = false;
            }
            if let Some(finally_block) = finally_block {
                self.calc_block_diagnostics(finally_block.block(), class, func)
            }
            if old_unreachable {
                fa.tos_frame().unreachable = old_unreachable;
            }
        })
    }

    fn flow_analysis_for_try_stmt_without_finally(
        &self,
        try_stmt: TryStmt,
        class: Option<Class>,
        func: Option<&Function>,
        except_bodies: usize,
    ) -> (Frame, Frame) {
        FLOW_ANALYSIS.with(|fa| {
            let mut try_frame_for_except = Frame::new_conditional();
            let mut try_frame = None;
            let mut after_ok = Frame::new_unreachable();
            let mut after_exception = Frame::new_unreachable();
            let mut nth_except_body = 0;
            let ignores_attribute_error = try_stmt.iter_blocks().any(|b| match b {
                TryBlockType::Except(b) => {
                    let (Some(except_expr), _) = b.unpack() else {
                        return false;
                    };
                    let attribute_error = self.i_s.db.python_state.attribute_error_link();
                    match except_expr.unpack() {
                        ExceptExpressionContent::WithNameDef(expr, _) => {
                            let inf = self.infer_expression(expr);
                            inf.maybe_saved_link() == Some(attribute_error)
                        }
                        ExceptExpressionContent::Expressions(expressions) => {
                            expressions.iter().any(|expr| {
                                let inf = self.infer_expression(expr);
                                inf.maybe_saved_link() == Some(attribute_error)
                            })
                        }
                    }
                }
                _ => false,
            });
            for b in try_stmt.iter_blocks() {
                let mut check_block = |except_expr: Option<ExceptExpression>, block, is_star| {
                    nth_except_body += 1;
                    let exception_frame = if nth_except_body == except_bodies {
                        try_frame_for_except.take()
                    } else {
                        try_frame_for_except.clone()
                    };
                    let mut name_def = None;
                    let (exception_frame, except_type) =
                        fa.with_frame_and_result(exception_frame, || {
                            let except_type = if let Some(except_expr) = except_expr {
                                match except_expr.unpack() {
                                    ExceptExpressionContent::WithNameDef(expr, n) => {
                                        let inf = self.infer_expression(expr);
                                        let inf_t = inf.as_cow_type(self.i_s);
                                        let instantiated = match is_star {
                                            false => instantiate_except(self.i_s, &inf_t),
                                            true => self.instantiate_except_star(n, &inf_t),
                                        };
                                        let name_index = n.name_index();
                                        let first = first_defined_name(self.file, name_index);
                                        if first == name_index {
                                            Inferred::from_type(instantiated).maybe_save_redirect(
                                                self.i_s,
                                                self.file,
                                                n.index(),
                                                false,
                                            );
                                        } else {
                                            self.save_narrowed(
                                                FlowKey::Name(PointLink::new(
                                                    self.file.file_index,
                                                    first,
                                                )),
                                                instantiated,
                                                false,
                                            )
                                        }
                                        name_def = Some(n);
                                        Some(except_type(self.i_s.db, &inf_t, true))
                                    }
                                    ExceptExpressionContent::Expressions(expressions) => {
                                        Some(ExceptType::from_types(
                                            self.i_s.db,
                                            true,
                                            expressions.iter().map(|expr| {
                                                self.infer_expression(expr).as_type(self.i_s)
                                            }),
                                        ))
                                    }
                                }
                            } else {
                                None
                            };
                            self.calc_block_diagnostics(block, class, func);
                            if let Some(name_def) = name_def {
                                self.delete_name(name_def)
                            }
                            except_type
                        });
                    let new_after = after_exception.take();
                    after_exception = fa.merge_or(self.i_s, exception_frame, new_after, false);
                    except_type
                };
                match b {
                    TryBlockType::Try(block) => {
                        try_frame_for_except =
                            fa.with_new_try_frame(ignores_attribute_error, || {
                                try_frame = Some(fa.with_frame(Frame::new_conditional(), || {
                                    self.calc_block_diagnostics(block, class, func)
                                }))
                            })
                    }
                    TryBlockType::Except(b) => {
                        let (except_expr, block) = b.unpack();
                        let except_type = check_block(except_expr, block, false);
                        if !matches!(
                            except_type,
                            None | Some(ExceptType::ContainsOnlyBaseExceptions)
                                | Some(ExceptType::HasExceptionGroup)
                        ) {
                            self.add_issue(
                                except_expr.unwrap().index(),
                                IssueKind::BaseExceptionExpected,
                            );
                        }
                    }
                    TryBlockType::ExceptStar(except_star) => {
                        let (except_expr, block) = except_star.unpack();
                        let except_type = check_block(Some(except_expr), block, true);
                        match except_type {
                            None | Some(ExceptType::ContainsOnlyBaseExceptions) => (),
                            Some(ExceptType::HasExceptionGroup) => {
                                self.add_issue(
                                    except_expr.index(),
                                    IssueKind::ExceptStarIsNotAllowedToBeAnExceptionGroup,
                                );
                            }
                            Some(ExceptType::Invalid) => {
                                self.add_issue(
                                    except_expr.index(),
                                    IssueKind::BaseExceptionExpected,
                                );
                            }
                        }
                    }
                    TryBlockType::Else(b) => {
                        let try_frame = try_frame.take().unwrap();
                        let else_frame = if try_frame.unreachable {
                            Frame::new_unreachable()
                        } else {
                            Frame::new_conditional()
                        };
                        fa.with_frame(try_frame, || {
                            let new_after = after_ok.take();
                            after_ok = fa.merge_or(
                                self.i_s,
                                new_after,
                                fa.with_frame(else_frame, || {
                                    self.calc_block_diagnostics(b.block(), class, func)
                                }),
                                false,
                            );
                        });
                    }
                    TryBlockType::Finally(_) => (),
                }
            }
            if let Some(try_frame) = try_frame {
                after_ok = fa.merge_or(self.i_s, try_frame, after_ok, false);
            }
            (after_ok, after_exception)
        })
    }

    pub fn flow_analysis_for_with_stmt_when_exceptions_maybe_suppressed(
        &self,
        callable: impl FnOnce(),
    ) {
        FLOW_ANALYSIS.with(|fa| {
            let try_frame_for_except = fa.with_new_try_frame(false, || {
                // Create a new frame that is then thrown away. This makes sense if we consider
                // that the end of the with statement might never be reached.
                fa.with_frame(Frame::new_conditional(), callable);
            });
            fa.overwrite_entries(self.i_s.db, try_frame_for_except.entries, false);
        })
    }

    pub fn flow_analysis_for_lambda_body(
        &self,
        expr: Expression,
        result_context: &mut ResultContext,
    ) -> Inferred {
        FLOW_ANALYSIS.with(|fa| {
            fa.with_frame_and_result(Frame::new_conditional(), || {
                self.infer_expression_without_cache(expr, result_context)
            })
            .1
        })
    }

    fn subject_key_named_expr(&self, named_expr: NamedExpression) -> Option<InferredSubject> {
        match named_expr.expression().maybe_unpacked_atom() {
            Some(AtomContent::Tuple(tup)) => self
                .subject_key_tuple(tup.iter())
                .map(InferredSubject::TupleKeys),
            Some(AtomContent::NamedExpression(inner)) => self.subject_key_named_expr(inner),
            _ => Some(InferredSubject::SubjectExprContent(
                self.key_from_namedexpression(named_expr),
            )),
        }
    }

    fn subject_key_tuple(
        &self,
        tuple_items: StarLikeExpressionIterator,
    ) -> Option<Vec<Option<SubjectKey>>> {
        let mut keys = vec![];
        for item in tuple_items {
            keys.push(match item {
                StarLikeExpression::NamedExpression(ne) => match self.subject_key_named_expr(ne) {
                    Some(InferredSubject::SubjectExprContent(r)) => {
                        r.key.map(|key| SubjectKey::Expr {
                            key,
                            parent_unions: r.parent_unions,
                        })
                    }
                    Some(InferredSubject::TupleKeys(keys)) => Some(SubjectKey::Tuple(keys)),
                    None => None,
                },
                StarLikeExpression::StarNamedExpression(_) => return None,
                _ => unreachable!(),
            })
        }
        Some(keys)
    }

    pub(crate) fn flow_analysis_for_match_stmt(
        &self,
        match_stmt: MatchStmt,
        class: Option<Class>,
        func: Option<&Function>,
    ) {
        let (subject_expr, case_blocks) = match_stmt.unpack();
        let (subject_key, inf) = match subject_expr.unpack() {
            SubjectExprContent::NamedExpression(ne) => match self.subject_key_named_expr(ne) {
                Some(InferredSubject::SubjectExprContent(k)) => (
                    k.key.map(|key| SubjectKey::Expr {
                        key,
                        parent_unions: k.parent_unions,
                    }),
                    k.inf,
                ),
                Some(InferredSubject::TupleKeys(keys)) => (
                    Some(SubjectKey::Tuple(keys)),
                    self.infer_named_expression(ne),
                ),
                None => (None, self.infer_named_expression(ne)),
            },
            SubjectExprContent::Tuple(iterator) => (
                self.subject_key_tuple(iterator.clone())
                    .map(SubjectKey::Tuple),
                self.infer_tuple_iterator(iterator, &mut ResultContext::Unknown),
            ),
        };
        let rest = self.process_match_cases_and_return_rest(
            inf,
            subject_key.as_ref(),
            case_blocks,
            class,
            func,
        );
        if self
            .flags()
            .enabled_error_codes
            .iter()
            .any(|enabled| enabled == "exhaustive-match")
        {
            let rest = rest.as_cow_type(self.i_s);
            if !rest.is_never() {
                self.add_issue(
                    subject_expr.index(),
                    IssueKind::NonExhaustiveMatch {
                        unmatched_type: rest.format_short(self.i_s.db),
                    },
                )
            }
        }
    }

    fn narrow_subject(
        &self,
        subject_key: Option<&SubjectKey>,
        frame: &mut Frame,
        for_type: Cow<Type>,
    ) {
        // In this function we make sure that the type accepted by the pattern is narrowed
        // for subject.
        if for_type.is_never() {
            frame.unreachable = true;
            return;
        }
        match subject_key {
            Some(SubjectKey::Expr { key, parent_unions }) => {
                frame.add_entry(self.i_s, Entry::new(key.clone(), for_type.into_owned()));
                self.propagate_parent_unions(frame, parent_unions);
            }
            Some(SubjectKey::Tuple(narrowable)) => {
                if let Type::Tuple(tup) = for_type.as_ref()
                    && let TupleArgs::FixedLen(given) = &tup.args
                {
                    for (given, narrowable) in given.iter().zip(narrowable.iter()) {
                        self.narrow_subject(narrowable.as_ref(), frame, Cow::Borrowed(given))
                    }
                }
            }
            None => (),
        }
    }

    fn process_match_cases_and_return_rest<'x>(
        &self,
        subject: Inferred,
        subject_key: Option<&SubjectKey>,
        mut case_blocks: impl Iterator<Item = CaseBlock<'x>>,
        class: Option<Class>,
        func: Option<&Function>,
    ) -> Inferred {
        let Some(case_block) = case_blocks.next() else {
            return subject;
        };
        let (case_pattern, guard, block) = case_block.unpack();
        FLOW_ANALYSIS.with(|fa| {
            fa.in_pattern_matching.set(fa.in_pattern_matching.get() + 1);
            let (mut truthy_frame, mut frames) = fa
                .with_frame_and_result(Frame::new_conditional(), || {
                    self.find_guards_in_case_pattern(subject.clone(), subject_key, case_pattern)
                });
            // Only enable pattern matching logic for the patterns, the other blocks should be
            // calculated in normal ways
            fa.in_pattern_matching.set(fa.in_pattern_matching.get() - 1);

            let falsey_t = frames.falsey_t.as_cow_type(self.i_s);
            let mut falsey_frame = if let Some(SubjectKey::Expr { key, .. }) = subject_key {
                Frame::from_type(key.clone(), falsey_t.into_owned())
            } else {
                Frame::from_type_without_entry(&falsey_t)
            };
            self.narrow_subject(
                subject_key,
                &mut truthy_frame,
                frames.truthy_t.as_cow_type(self.i_s),
            );

            if let Some(guard) = guard {
                let (guard_truthy, guard_falsey);
                (truthy_frame, (_, guard_truthy, guard_falsey)) = fa
                    .with_frame_and_result(truthy_frame, || {
                        self.find_guards_in_named_expr(guard.named_expr())
                    });

                let mut input_for_next_case_should_be_rewritten = true;

                // If the guard narrowed the subject, copy the narrowed types over
                let (name_def, as_name_def) = case_pattern.maybe_simple_name_assignments();
                for name_def in name_def.into_iter().chain(as_name_def.into_iter()) {
                    let key = self.key_from_name_def(name_def);
                    if let Some(found) = guard_falsey.lookup_entry(self.i_s.db, &key)
                        && let EntryKind::Type(t) = &found.type_
                    {
                        frames.falsey_t = Inferred::from_type(t.clone());
                        input_for_next_case_should_be_rewritten = false;
                    }
                    if let Some(found) = guard_truthy.lookup_entry(self.i_s.db, &key)
                        && let EntryKind::Type(t) = &found.type_
                    {
                        // We need to rerun this, because the types might have changed
                        self.narrow_subject(subject_key, &mut truthy_frame, Cow::Borrowed(t));
                    }
                }

                truthy_frame = merge_and(self.i_s, truthy_frame, guard_truthy);

                falsey_frame = fa.merge_or(self.i_s, falsey_frame, guard_falsey, false);
                if !falsey_frame.unreachable && input_for_next_case_should_be_rewritten {
                    frames.falsey_t = subject;
                }
                self.narrow_subject(
                    subject_key,
                    &mut falsey_frame,
                    frames.falsey_t.as_cow_type(self.i_s),
                );
            }
            let true_frame = fa.with_frame(truthy_frame, || {
                self.calc_block_diagnostics(block, class, func)
            });
            let (false_frame, result) = fa.with_frame_and_result(falsey_frame, || {
                self.process_match_cases_and_return_rest(
                    frames.falsey_t,
                    subject_key,
                    case_blocks,
                    class,
                    func,
                )
            });
            fa.in_pattern_matching.set(fa.in_pattern_matching.get() + 1);
            fa.merge_conditional(self.i_s, true_frame, false_frame);
            fa.in_pattern_matching.set(fa.in_pattern_matching.get() - 1);
            result
        })
    }

    fn check_conjunction(
        &self,
        and: Conjunction,
    ) -> (
        TruthyInferred,
        FramesWithParentUnions,
        FramesWithParentUnions,
    ) {
        let (left, right) = and.unpack();
        match is_expr_part_reachable_for_name_binder(
            &self.i_s.db.project.settings,
            self.flags(),
            left,
        ) {
            Truthiness::True { .. } => {
                let (inf, r) = self.find_guards_in_expression_parts(right);
                return (inf, FramesWithParentUnions::default(), r);
            }
            Truthiness::False => {
                let (inf, l) = self.find_guards_in_expression_parts(left);
                return (inf, l, FramesWithParentUnions::default());
            }
            Truthiness::Unknown => (),
        }

        let (left_inf, mut left_frames) = self.find_guards_in_expression_parts(left);
        let mut right_infos = None;
        if left_frames.truthy.unreachable {
            if self.flags().warn_unreachable {
                self.add_issue(
                    and.index(),
                    IssueKind::RightOperandIsNeverOperated { right: "and" },
                )
            }
        } else {
            self.propagate_parent_unions(&mut left_frames.truthy, &left_frames.parent_unions);
            left_frames.truthy = FLOW_ANALYSIS.with(|fa| {
                fa.with_frame(left_frames.truthy, || {
                    right_infos = Some(self.find_guards_in_expression_parts(right));
                })
            });
        }
        let (inf, right_frames) = if let Some((right_inf, right_frames)) = right_infos {
            let falsey = TruthyInferred::Simple {
                inf: if let Some((_, falsey)) = split_truthy_and_falsey(self.i_s, &left_inf) {
                    Inferred::from_type(falsey)
                } else {
                    left_inf.into_inferred(self.i_s)
                },
                truthiness: Some(false),
            };
            (falsey.combine(right_inf), right_frames)
        } else {
            (left_inf, FramesWithParentUnions::default())
        };
        (inf, left_frames, right_frames)
    }

    pub fn flow_analysis_for_disjunction(
        &self,
        or: Disjunction,
        result_context: &mut ResultContext,
    ) -> Inferred {
        self.check_disjunction(or, result_context)
            .0
            .into_inferred(self.i_s)
    }

    fn check_disjunction(
        &self,
        or: Disjunction,
        result_context: &mut ResultContext,
    ) -> (
        TruthyInferred,
        FramesWithParentUnions,
        FramesWithParentUnions,
    ) {
        let (left, right) = or.unpack();
        match is_expr_part_reachable_for_name_binder(
            &self.i_s.db.project.settings,
            self.flags(),
            left,
        ) {
            Truthiness::False => {
                let (inf, r) = self.find_guards_in_expression_parts(right);
                return (inf, FramesWithParentUnions::default(), r);
            }
            Truthiness::True { .. } => {
                let (inf, l) = self.find_guards_in_expression_parts(left);
                return (inf, l, FramesWithParentUnions::default());
            }
            Truthiness::Unknown => (),
        }

        let (left_inf, mut left_frames) =
            self.find_guards_in_expression_parts_with_context(left, result_context);
        let mut right_infos = None;
        if left_frames.falsey.unreachable {
            if self.flags().warn_unreachable {
                self.add_issue(
                    or.index(),
                    IssueKind::RightOperandIsNeverOperated { right: "or" },
                )
            }
        } else {
            self.propagate_parent_unions(&mut left_frames.falsey, &left_frames.parent_unions);
            left_frames.falsey = FLOW_ANALYSIS.with(|fa| {
                let left_t = left_inf.as_cow_type(self.i_s);
                fa.with_frame(left_frames.falsey, || {
                    right_infos = Some(self.find_guards_in_expression_parts_with_context(
                        right,
                        &mut ResultContext::new_known(&left_t),
                    ));
                })
            });
        }

        let (inf, right_frames) = if let Some((right_inf, right_frames)) = right_infos {
            let truthy = TruthyInferred::Simple {
                inf: if let Some((truthy, _)) = split_truthy_and_falsey(self.i_s, &left_inf) {
                    Inferred::from_type(truthy)
                } else {
                    left_inf.into_inferred(self.i_s)
                },
                truthiness: Some(true),
            };
            (truthy.combine(right_inf), right_frames)
        } else {
            (left_inf, FramesWithParentUnions::default())
        };
        (inf, left_frames, right_frames)
    }

    #[inline]
    fn maybe_propagate_parent_union(
        &self,
        base_union: &UnionType,
        child_entry: &Entry,
    ) -> Option<Type> {
        let replay = |t: &Type| {
            self.i_s.avoid_errors_within(|i_s| match &child_entry.key {
                FlowKey::Member(_, name) => self
                    .file
                    .inference(i_s)
                    .check_attr(t, name.as_str(i_s.db))
                    .into_inferred(),
                FlowKey::Index { node_index, .. } => t.get_item(
                    i_s,
                    None,
                    &SliceType::new(
                        self.file,
                        *node_index,
                        CSTSliceType::from_index(&self.file.tree, *node_index),
                    ),
                    &mut ResultContext::Unknown,
                ),
                FlowKey::Name(_) => unreachable!(),
            })
        };

        let child_t = match &child_entry.type_ {
            EntryKind::Type(t) => t,
            EntryKind::OriginalDeclaration => return None,
        };
        let mut matching_entries = vec![];
        for union_entry in base_union.entries.iter() {
            let (inf, had_error) = replay(&union_entry.type_);
            if had_error {
                return None;
            }
            if inf.as_cow_type(self.i_s).simple_overlaps(self.i_s, child_t) {
                matching_entries.push(union_entry.clone());
            }
        }
        (base_union.entries.len() != matching_entries.len())
            .then(|| Type::from_union_entries(matching_entries, base_union.might_have_type_vars))
    }

    fn propagate_parent_unions(&self, frame: &mut Frame, parent_unions: &[(FlowKey, UnionType)]) {
        for (key, parent_union) in parent_unions.iter().rev() {
            for entry in &frame.entries {
                let (FlowKey::Member(base_key, _) | FlowKey::Index { base_key, .. }) = &entry.key
                else {
                    continue;
                };
                if key.equals(self.i_s.db, base_key)
                    && let Some(type_) = self.maybe_propagate_parent_union(parent_union, entry)
                {
                    frame.add_entry(self.i_s, Entry::new(key.clone(), type_));
                    break;
                }
            }
        }
    }

    fn literal_pattern_to_type(&self, pat: LiteralPattern) -> Type {
        let db = self.i_s.db;
        match pat.unpack() {
            LiteralPatternContent::Strings(strings) => self.strings_to_type(strings),
            LiteralPatternContent::Bytes(bytes) => {
                if let Some(b) = bytes.maybe_single_bytes_literal() {
                    Type::Literal(Literal::new(LiteralKind::Bytes(DbBytes::Link(
                        PointLink::new(self.file.file_index, b.index()),
                    ))))
                } else {
                    db.python_state.bytes_type()
                }
            }
            LiteralPatternContent::SignedNumber(signed_number) => {
                let (number, is_negated) = signed_number.number_and_is_negated();
                match number {
                    UnpackedNumber::Int(int) => {
                        let mut result = int.parse();
                        if is_negated {
                            result = -result
                        }
                        Type::Literal(Literal::new(LiteralKind::Int(result)))
                    }
                    UnpackedNumber::Float(_) => db.python_state.float_type(),
                    UnpackedNumber::Complex(_) => db.python_state.complex_type(),
                }
            }
            LiteralPatternContent::ComplexNumber(_) => db.python_state.complex_type(),
            LiteralPatternContent::None => Type::None,
            LiteralPatternContent::Bool(b) => Type::Literal(Literal::new(LiteralKind::Bool(b))),
        }
    }

    fn find_guards_in_case_pattern(
        &self,
        inf: Inferred,
        subject_key: Option<&SubjectKey>,
        case_pattern: CasePattern,
    ) -> PatternResult {
        match case_pattern {
            CasePattern::Pattern(pattern) => self.find_guards_in_pattern(inf, subject_key, pattern),
            CasePattern::OpenSequencePattern(seq) => {
                debug!(
                    "Check open sequence pattern: {:?} with type {:?}",
                    seq.as_code(),
                    inf.format_short(self.i_s)
                );
                let _indent = debug_indent();
                self.find_guards_in_sequence_pattern(inf, seq.iter())
            }
        }
    }

    fn find_guards_in_pattern(
        &self,
        inf: Inferred,
        subject_key: Option<&SubjectKey>,
        pattern: Pattern,
    ) -> PatternResult {
        debug!(
            "Check pattern: {:?} with type {:?}",
            pattern.as_code(),
            inf.format_short(self.i_s)
        );
        let _indent = debug_indent();
        let (pattern_kind, as_name) = pattern.unpack();
        let result = self.find_guards_in_pattern_kind(inf, subject_key, pattern_kind.clone());
        if let Some(as_name) = as_name {
            self.assign_to_pattern_name(as_name, &result.truthy_t)
        }
        result
    }

    fn assign_to_pattern_name(&self, name_def: NameDef, inf: &Inferred) {
        let from = NodeRef::new(self.file, name_def.index());
        // In almost all cases the point should not have been calculated. A calculated point
        // probably means that the name has been accessed illegally and we therefore do not have to
        // assign.
        if !from.point().calculated() {
            self.assign_to_name_def_simple(name_def, from, inf, AssignKind::Pattern);
        }
    }

    fn find_guards_in_pattern_kind(
        &self,
        inf: Inferred,
        subject_key: Option<&SubjectKey>,
        kind: PatternKind,
    ) -> PatternResult {
        let i_s = self.i_s;
        match kind {
            PatternKind::NameDef(name_def) => {
                self.assign_to_pattern_name(name_def, &inf);
                PatternResult {
                    truthy_t: inf,
                    falsey_t: Inferred::new_never(NeverCause::Other),
                }
            }
            PatternKind::WildcardPattern(_) => PatternResult {
                truthy_t: inf,
                falsey_t: Inferred::new_never(NeverCause::Other),
            },
            PatternKind::DottedName(dotted_name) => {
                let dotted_inf = self.infer_pattern_dotted_name(dotted_name);
                self.split_for_dotted_pattern_name(inf, &dotted_inf.as_cow_type(i_s))
            }
            PatternKind::ClassPattern(class_pattern) => {
                self.find_guards_in_class_pattern(inf, subject_key, class_pattern)
            }
            PatternKind::LiteralPattern(literal_pattern) => {
                let expected = self.literal_pattern_to_type(literal_pattern);
                let of_type = inf.as_cow_type(i_s);
                let (truthy, falsey) = if matches!(expected, Type::Class(_)) {
                    // Floats for example are not literals and can therefore never change the
                    // falsey side and can therefore not be matched as a singleton.
                    (
                        Type::from_union_entries(
                            of_type
                                .iter_with_unpacked_unions(i_s.db)
                                .enumerate()
                                .filter_map(|(format_index, t)| {
                                    match t {
                                        Type::Class(c) if *t == expected => (),
                                        Type::TypeVar(_) | Type::Any(_) => (),
                                        _ => {
                                            if !has_custom_eq(i_s, t) {
                                                return None;
                                            }
                                        }
                                    };
                                    Some(UnionEntry {
                                        format_index,
                                        type_: t.clone(),
                                    })
                                })
                                .collect(),
                            true,
                        ),
                        of_type.into_owned(),
                    )
                } else {
                    split_off_singleton(
                        i_s,
                        &of_type,
                        &expected,
                        !matches!(
                            literal_pattern.unpack(),
                            // The spec says "The singleton literals None, True and False are
                            // compared using the is operator."
                            LiteralPatternContent::Bool(_) | LiteralPatternContent::None
                        ),
                    )
                };
                PatternResult {
                    truthy_t: Inferred::from_type(truthy),
                    falsey_t: Inferred::from_type(falsey),
                }
            }
            PatternKind::GroupPattern(group_pattern) => {
                self.find_guards_in_pattern(inf, subject_key, group_pattern.inner())
            }
            PatternKind::OrPattern(or_pattern) => {
                self.find_guards_in_or_pattern(inf, subject_key, or_pattern.iter())
            }
            PatternKind::SequencePattern(sequence_pattern) => {
                self.find_guards_in_sequence_pattern(inf, sequence_pattern.iter())
            }
            PatternKind::MappingPattern(mapping_pattern) => {
                run_pattern_for_each_type_with_pattern_result(i_s, inf, |t| {
                    match t {
                        Type::TypedDict(td) => {
                            self.find_guards_in_typed_dict_for_mapping_pattern(td, mapping_pattern)
                        }
                        Type::Any(_) => (t.clone(), t),
                        _ => {
                            let key = self.infer_mapping_key(mapping_pattern);
                            let not_found = Cell::new(false);
                            let mut executed = t
                                .lookup(
                                    i_s,
                                    self.file,
                                    "__getitem__",
                                    LookupKind::OnlyType,
                                    &mut ResultContext::Unknown,
                                    &|_| (),
                                    &|_| not_found.set(true),
                                )
                                .into_inferred()
                                .execute_with_details(
                                    i_s,
                                    &KnownArgsWithCustomAddIssue::new(&key, &|_| false),
                                    &mut ResultContext::Unknown,
                                    OnTypeError::new(&|_, _, _, _| ()),
                                );
                            if not_found.get() {
                                // A subclass could always create __getitem__
                                executed = Inferred::new_object(i_s.db)
                            }
                            self.assign_key_value_to_mapping_pattern(t, executed, mapping_pattern)
                        }
                    }
                })
            }
        }
    }

    fn split_for_dotted_pattern_name(&self, inf: Inferred, dotted_t: &Type) -> PatternResult {
        let inf_t = inf.into_type(self.i_s);
        let fallback = |inf_t| {
            let (truthy, mut falsey) = split_and_intersect(self.i_s, &inf_t, dotted_t, |_| {});
            if !truthy.is_singleton(self.i_s.db) {
                falsey.union_in_place(inf_t)
            }
            (truthy, falsey)
        };
        let (truthy, falsey) = match dotted_t {
            Type::EnumMember(member) => {
                let mut member = member.clone();
                member.implicit = false;
                split_off_enum_member(self.i_s, &inf_t, &member, true)
                    .unwrap_or_else(|| fallback(inf_t))
            }
            _ => fallback(inf_t),
        };
        PatternResult {
            truthy_t: Inferred::from_type(truthy),
            falsey_t: Inferred::from_type(falsey),
        }
    }

    fn find_guards_in_or_pattern<'x>(
        &self,
        inf: Inferred,
        subject_key: Option<&SubjectKey>,
        mut patterns: impl Iterator<Item = PatternKind<'x>>,
    ) -> PatternResult {
        let Some(pattern) = patterns.next() else {
            return PatternResult {
                truthy_t: Inferred::new_never(NeverCause::Other),
                falsey_t: inf,
            };
        };
        FLOW_ANALYSIS.with(|fa| {
            let (first_frame, result1) = fa.with_frame_and_result(Frame::new_conditional(), || {
                self.find_guards_in_pattern_kind(inf, subject_key, pattern)
            });
            let (next_frame, result2) = fa.with_frame_and_result(Frame::new_conditional(), || {
                self.find_guards_in_or_pattern(result1.falsey_t, subject_key, patterns)
            });
            fa.merge_conditional(self.i_s, first_frame, next_frame);
            PatternResult {
                truthy_t: result1
                    .truthy_t
                    .simplified_union(self.i_s, result2.truthy_t),
                falsey_t: result2.falsey_t,
            }
        })
    }

    fn find_guards_in_class_pattern(
        &self,
        inf: Inferred,
        subject_key: Option<&SubjectKey>,
        class_pattern: ClassPattern,
    ) -> PatternResult {
        let i_s = self.i_s;
        let (dotted, params) = class_pattern.unpack();
        let inferred_target = self.infer_pattern_dotted_name(dotted);
        let inferred_target = inferred_target.as_cow_type(i_s);
        let target_t = match inferred_target.as_ref() {
            Type::Type(t) => {
                if let Type::Class(c) = &**t
                    && !matches!(
                        c.generics,
                        ClassGenerics::None { .. } | ClassGenerics::NotDefinedYet
                    )
                {
                    self.add_issue(dotted.index(), IssueKind::ClassPatternCannotParametrized);
                    return PatternResult {
                        truthy_t: Inferred::new_never(NeverCause::Other),
                        falsey_t: inf,
                    };
                }
                t.as_ref()
            }
            Type::Any(_) => {
                return PatternResult {
                    truthy_t: inf.clone(),
                    falsey_t: inf,
                };
            }
            t => {
                self.add_issue(
                    dotted.index(),
                    IssueKind::ExpectedTypeInClassPattern {
                        got: t.format_short(i_s.db),
                    },
                );
                return PatternResult {
                    truthy_t: Inferred::new_never(NeverCause::Other),
                    falsey_t: inf,
                };
            }
        };
        let inf_type = inf.as_cow_type(i_s);
        let (truthy, falsey) = split_and_intersect(self.i_s, &inf_type, target_t, |issue| {
            debug!("Intersection for class target not possible: {issue:?}");
        });
        let (mut truthy, falsey_new) = run_pattern_for_each_type(self.i_s, truthy, |t| {
            self.find_guards_in_class_pattern_part2(t, subject_key, params.clone(), target_t)
        });
        if inf_type.is_never() {
            truthy = Type::Never(NeverCause::Other)
        }

        PatternResult {
            truthy_t: Inferred::from_type(truthy),
            falsey_t: Inferred::from_type(falsey.union(falsey_new)),
        }
    }

    fn find_guards_in_class_pattern_part2<'x>(
        &self,
        truthy: Type,
        subject_key: Option<&SubjectKey>,
        params: impl Iterator<Item = ParamPattern<'x>> + Clone,
        target_t: &Type,
    ) -> (Type, Type) {
        let i_s = self.i_s;
        debug!(
            "Check class pattern with intersected type {:?}",
            truthy.format_short(i_s.db)
        );
        let lookup = |t: &Type, name: &str| {
            t.lookup(
                i_s,
                self.file,
                name,
                LookupKind::OnlyType,
                &mut ResultContext::Unknown,
                &|_| (),
                &|_| (),
            )
        };
        let mut added_no_match_args_issue = false;
        //for e in truthy.into_iter_with_unpacked_unions(i_s.db, true) {
        let mut inner_mismatch = false;
        let match_args = OnceCell::new();
        let mut nth_positional = 0;
        let mut find_inner_guards_and_return_unreachable = |node_ref: NodeRef, name: &str, pat| {
            let lookup = lookup(&truthy, name);
            let inf = lookup.into_maybe_inferred().unwrap_or_else(|| {
                node_ref.add_issue(
                    i_s,
                    IssueKind::ClassPatternHasNoAttribute {
                        class: target_t.format(&FormatData::new_reveal_type(i_s.db)),
                        attribute: name.into(),
                    },
                );
                Inferred::new_any_from_error()
            });
            let inner_result = self.find_guards_in_pattern(inf, None, pat);
            inner_mismatch |= inner_result.truthy_t.as_cow_type(i_s).is_never();
            inner_mismatch
        };
        let mut used_keywords: Vec<(&str, bool)> = vec![];
        for param in params.clone() {
            match param {
                ParamPattern::Positional(pat) => {
                    let node_ref = NodeRef::new(self.file, pat.index());
                    if let Some(match_args) = match_args.get_or_init(|| {
                        let lookup = lookup(&truthy, "__match_args__");
                        let name = lookup.maybe_name();
                        lookup.into_maybe_inferred().map(|inf| {
                            let truthy = inf.as_type(i_s);
                            truthy.ensure_dunder_match_args_with_literals(i_s.db, name)
                        })
                    }) {
                        if let Some(tup_entries) = match_args.maybe_fixed_len_tuple() {
                            if let Some(entry) = tup_entries.get(nth_positional) {
                                if let Type::Literal(literal) = entry
                                    && let LiteralKind::String(s) = &literal.kind
                                {
                                    let key = s.as_str(i_s.db);
                                    used_keywords.push((key, false));
                                    if find_inner_guards_and_return_unreachable(
                                        NodeRef::new(self.file, pat.index()),
                                        key,
                                        pat,
                                    ) {
                                        break;
                                    }
                                } else {
                                    // If the type is not a literal, an error should be added
                                    // in diagnostics that __match_args__ is not correct and we
                                    // can simply work with Any here.
                                    self.find_guards_in_pattern(
                                        Inferred::new_any_from_error(),
                                        None,
                                        pat,
                                    );
                                }
                            } else if !added_no_match_args_issue {
                                node_ref.add_issue(
                                    i_s,
                                    IssueKind::TooManyPositionalPatternsForMatchArgs,
                                );
                                // If there are too many positional patterns don't mark the
                                // rest as potentially unreachable, since an error occured.
                                return (Type::Never(NeverCause::Other), truthy);
                            }
                        } else {
                            // If match args are incorrect, we simply assume it's matching, because
                            // an error should have been added at the point of defining the
                            // __match_args__
                            return (truthy.clone(), truthy);
                        }
                    } else if params.clone().count() == 1 && is_self_match_type(i_s.db, &truthy) {
                        self.find_guards_in_pattern(
                            Inferred::from_type(truthy.clone()),
                            subject_key,
                            pat,
                        );
                    } else {
                        if !added_no_match_args_issue {
                            node_ref.add_issue(
                                i_s,
                                IssueKind::ClassHasNoMatchArgs {
                                    class: truthy.format(&FormatData::new_reveal_type(i_s.db)),
                                },
                            );
                        }
                        added_no_match_args_issue = true;
                        self.find_guards_in_pattern(Inferred::new_any_from_error(), None, pat);
                    }
                    nth_positional += 1;
                }
                ParamPattern::Keyword(keyword_pattern) => {
                    let (key_node, pat) = keyword_pattern.unpack();
                    let key = key_node.as_code();
                    for (used, is_kw) in &used_keywords {
                        if key == *used {
                            self.add_issue(
                                key_node.index(),
                                if *is_kw {
                                    IssueKind::DuplicateKeywordPattern { name: key.into() }
                                } else {
                                    IssueKind::DuplicateImplicitKeywordPattern { name: key.into() }
                                },
                            )
                        }
                    }
                    if find_inner_guards_and_return_unreachable(
                        NodeRef::new(self.file, keyword_pattern.index()),
                        key,
                        pat,
                    ) {
                        break;
                    }
                    used_keywords.push((key, true))
                }
            }
        }
        if inner_mismatch {
            (Type::NEVER, truthy)
        } else {
            (truthy, Type::NEVER)
        }
    }

    fn find_guards_in_sequence_pattern<'x>(
        &self,
        inf: Inferred,
        sequence_patterns: impl Iterator<Item = SequencePatternItem<'x>> + Clone,
    ) -> PatternResult {
        let i_s = self.i_s;
        run_pattern_for_each_type_with_pattern_result(i_s, inf, |t| {
            let assign_from_tuple =
                |tup| self.assign_tup_for_sequence_patterns(tup, sequence_patterns.clone());
            match &t {
                Type::Class(c)
                    if c.link == i_s.db.python_state.str_link()
                        || c.link == i_s.db.python_state.bytes_link()
                        || c.link == i_s.db.python_state.bytearray_link() =>
                {
                    (Type::NEVER, t)
                }
                Type::None | Type::Literal(_) | Type::LiteralString { .. } => (Type::NEVER, t),
                Type::Any(_) => (t.clone(), t),
                Type::Tuple(tup) => assign_from_tuple(tup.clone()),
                Type::NamedTuple(nt) => assign_from_tuple(nt.as_tuple()),
                _ => {
                    let maybe_class = t.maybe_class(i_s.db);
                    if let Some(cls) = maybe_class
                        && let Some(tup) = cls.maybe_tuple_base(i_s.db)
                    {
                        return assign_from_tuple(tup);
                    }

                    let sequence_link = i_s.db.python_state.sequence_link();
                    if let Some(cls) = maybe_class
                        && let Some(sequence) =
                            cls.class_in_mro(i_s.db, i_s.db.python_state.sequence_node_ref())
                    {
                        let container_t = sequence.nth_type_argument(i_s.db, 0);
                        let inferred_container =
                            self.assign_sequence_patterns(&container_t, sequence_patterns.clone());
                        if cls.node_ref.as_link() == sequence_link {
                            (new_class!(sequence_link, inferred_container), t)
                        } else {
                            (t.clone(), t)
                        }
                    } else {
                        let obj = i_s.db.python_state.object_type();
                        let inner = self.assign_sequence_patterns(&obj, sequence_patterns.clone());
                        (new_class!(sequence_link, inner), t)
                    }
                }
            }
        })
    }

    fn find_guards_in_typed_dict_for_mapping_pattern(
        &self,
        td: Arc<TypedDict>,
        mapping_pattern: MappingPattern,
    ) -> (Type, Type) {
        let unreachable_pattern = || (Type::NEVER, Type::TypedDict(td.clone()));
        let i_s = self.i_s;
        let fallback_type = || {
            if td.has_extra_items(i_s.db) {
                td.union_of_all_types(i_s)
            } else {
                i_s.db.python_state.object_type()
            }
        };
        let mut unsure = false;
        for item in mapping_pattern.iter() {
            match item {
                MappingPatternItem::Entry(e) => {
                    let (key, value) = e.unpack();
                    let inf_key = match key {
                        KeyEntryInPattern::LiteralPattern(lit) => match lit.unpack() {
                            LiteralPatternContent::Strings(strings) => {
                                Inferred::from_type(self.strings_to_type(strings))
                            }
                            _ => return unreachable_pattern(),
                        },
                        KeyEntryInPattern::DottedName(dotted) => {
                            self.infer_pattern_dotted_name(dotted)
                        }
                    };
                    let value_t = match inf_key.as_cow_type(i_s).as_ref() {
                        Type::Literal(literal) => match &literal.kind {
                            LiteralKind::String(s) => {
                                if let Some(member) = td.find_member(i_s.db, s.as_str(i_s.db)) {
                                    unsure |= !member.required;
                                    member.type_.clone()
                                } else if td.is_closed(i_s.db) {
                                    return unreachable_pattern();
                                } else {
                                    unsure = true;
                                    fallback_type()
                                }
                            }
                            _ => return unreachable_pattern(),
                        },
                        t if t.might_be_string(i_s.db) => {
                            unsure = true;
                            fallback_type()
                        }
                        _ => return unreachable_pattern(),
                    };
                    let inner_result =
                        self.find_guards_in_pattern(Inferred::from_type(value_t), None, value);
                    unsure |= !inner_result.is_falsey_unreachable(i_s);
                }
                MappingPatternItem::Rest(rest) => {
                    let name_def = rest.name_def();
                    self.assign_to_pattern_name(
                        name_def,
                        &Inferred::from_type(new_class!(
                            self.i_s.db.python_state.dict_link(),
                            self.i_s.db.python_state.str_type(),
                            fallback_type()
                        )),
                    )
                }
            }
        }
        // Mypy doesn't support narrowing TypedDicts by its subattributes at the moment
        let falsey = match unsure || i_s.db.mypy_compatible() {
            true => Type::TypedDict(td.clone()),
            false => Type::NEVER,
        };
        (Type::TypedDict(td), falsey)
    }

    fn assign_key_value_to_mapping_pattern(
        &self,
        mapping_type: Type,
        value: Inferred,
        mapping_pattern: MappingPattern,
    ) -> (Type, Type) {
        let db = self.i_s.db;
        for item in mapping_pattern.iter() {
            match item {
                MappingPatternItem::Entry(e) => {
                    let (_, val) = e.unpack();
                    self.find_guards_in_pattern(value.clone(), None, val);
                }
                MappingPatternItem::Rest(rest) => {
                    let name_def = rest.name_def();
                    let key_type = mapping_type
                        .maybe_class(db)
                        .and_then(|cls| {
                            let mapping_node_ref = db.python_state.mapping_node_ref();
                            let mapping = cls.class_in_mro(db, mapping_node_ref)?;
                            Some(mapping.nth_type_argument(db, 0))
                        })
                        .unwrap_or_else(|| db.python_state.object_type());
                    self.assign_to_pattern_name(
                        name_def,
                        &Inferred::from_type(new_class!(
                            db.python_state.dict_link(),
                            key_type,
                            value.as_type(self.i_s),
                        )),
                    );
                }
            }
        }
        (mapping_type.clone(), mapping_type)
    }

    fn infer_mapping_key(&self, mapping_pattern: MappingPattern) -> Inferred {
        Inferred::gather_simplified_union(self.i_s, |gather| {
            for item in mapping_pattern.iter() {
                match item {
                    MappingPatternItem::Entry(e) => {
                        let (key, _) = e.unpack();
                        gather(match key {
                            KeyEntryInPattern::LiteralPattern(lit) => {
                                Inferred::from_type(self.literal_pattern_to_type(lit))
                            }
                            KeyEntryInPattern::DottedName(dotted) => {
                                self.infer_pattern_dotted_name(dotted)
                            }
                        })
                    }
                    MappingPatternItem::Rest(..) => (),
                }
            }
        })
    }

    fn assign_sequence_patterns<'x>(
        &self,
        container_t: &Type,
        iter: impl Iterator<Item = SequencePatternItem<'x>>,
    ) -> Type {
        let mut result = Type::NEVER;
        let i_s = self.i_s;
        for item in iter {
            match item {
                SequencePatternItem::Entry(pattern) => {
                    let r = self.find_guards_in_pattern(
                        Inferred::from_type(container_t.clone()),
                        None,
                        pattern,
                    );
                    result.simplified_union_in_place(i_s, &r.truthy_t.as_cow_type(i_s));
                }
                SequencePatternItem::Rest(star_pattern) => match star_pattern.unpack() {
                    StarPatternContent::NameDef(name_def) => {
                        self.assign_to_pattern_name(
                            name_def,
                            &Inferred::from_type(new_class!(
                                self.i_s.db.python_state.list_link(),
                                container_t.clone()
                            )),
                        );
                    }
                    StarPatternContent::WildcardPattern(_) => (),
                },
            }
        }
        result
    }

    fn assign_tup_for_sequence_patterns<'x>(
        &self,
        tup: Arc<Tuple>,
        sequence_patterns: impl Iterator<Item = SequencePatternItem<'x>> + Clone,
    ) -> (Type, Type) {
        let has_fixed_len_items = match &tup.args {
            TupleArgs::WithUnpack(u) => u.before.len() + u.after.len(),
            TupleArgs::FixedLen(items) => items.len(),
            TupleArgs::ArbitraryLen(t) => {
                self.assign_sequence_patterns(t, sequence_patterns);
                return (Type::Tuple(tup.clone()), Type::Tuple(tup));
            }
        };

        // Calculate first how many items are needed
        let mut normal_patterns = 0;
        let mut after_stars = 0;
        let mut had_starred_pattern = false;
        for item in sequence_patterns.clone() {
            match item {
                SequencePatternItem::Entry(_) => {
                    normal_patterns += 1;
                    if had_starred_pattern {
                        after_stars += 1;
                    }
                }
                SequencePatternItem::Rest(star_pattern) => {
                    if had_starred_pattern {
                        self.add_issue(
                            star_pattern.index(),
                            IssueKind::MultipleStarredExpressionsInAssignment,
                        );
                        self.assign_sequence_patterns(&Type::ERROR, sequence_patterns);
                        return (Type::Tuple(tup.clone()), Type::Tuple(tup));
                    }
                    had_starred_pattern = true;
                }
            }
        }

        if !had_starred_pattern && has_fixed_len_items > normal_patterns
            || has_fixed_len_items < normal_patterns
                && !matches!(&tup.args, TupleArgs::WithUnpack(_))
        {
            return (Type::Never(NeverCause::Other), Type::Tuple(tup));
        }
        let i_s = self.i_s;
        let mut value_iterator = tup.iter();
        let mut truthy_gatherer = TupleGatherer::default();
        let mut falsey_unreachable = true;
        let mut had_star = false;
        for (i, pattern) in sequence_patterns.enumerate() {
            match pattern {
                SequencePatternItem::Entry(pattern) => {
                    let result = self.find_guards_in_pattern(
                        value_iterator.unpack_next_with_customized_after(|with_unpack| {
                            if normal_patterns - i + had_starred_pattern as usize
                                > with_unpack.after.len()
                            {
                                // This mostly for pattern unpacking
                                Some(with_unpack.unpack.fallback_bound(i_s.db))
                            } else {
                                None
                            }
                        }),
                        None,
                        pattern,
                    );
                    if result.truthy_t.is_never(i_s) {
                        return (Type::Never(NeverCause::Other), Type::Tuple(tup));
                    }
                    falsey_unreachable &= result.is_falsey_unreachable(i_s);
                    truthy_gatherer.add(result.truthy_t.into_type(i_s));
                }
                SequencePatternItem::Rest(star_pattern) => {
                    truthy_gatherer
                        .extend_from_inferred_iterator(value_iterator.clone(), after_stars);
                    let (is_empty, mut value) = value_iterator.unpack_starred_and_return_is_empty(
                        i_s,
                        after_stars,
                        false,
                        false,
                    );
                    had_star = true;
                    match star_pattern.unpack() {
                        StarPatternContent::NameDef(name_def) => {
                            if is_empty && self.infer_name_target(name_def, false).is_some() {
                                // The type is already defined, just use any here, because the
                                // list really can be anything.
                                value = Inferred::from_type(i_s.db.python_state.list_of_any.clone())
                            }
                            self.assign_to_pattern_name(name_def, &value);
                        }
                        StarPatternContent::WildcardPattern(_) => (),
                    }
                }
            }
        }
        (
            truthy_gatherer
                .into_tuple(i_s.db, || unreachable!())
                .into_type(i_s),
            if falsey_unreachable && (matches!(&tup.args, TupleArgs::FixedLen(_)) || had_star) {
                Type::Never(NeverCause::Other)
            } else {
                Type::Tuple(tup)
            },
        )
    }

    fn find_guards_in_named_expr(
        &self,
        named_expr: NamedExpression,
    ) -> (TruthyInferred, Frame, Frame) {
        match named_expr.unpack() {
            NamedExpressionContent::Expression(expr) => self.find_guards_in_expr(expr),
            NamedExpressionContent::Walrus(walrus) => {
                let (name_def, expr) = walrus.unpack();
                let (inf, mut truthy, mut falsey) =
                    if let Some(inf) = self.infer_name_target(name_def, false) {
                        self.find_guards_in_expr_with_context(
                            expr,
                            &mut ResultContext::new_known(&inf.as_cow_type(self.i_s)),
                        )
                    } else {
                        self.find_guards_in_expr(expr)
                    };
                FLOW_ANALYSIS.with(|fa| {
                    let (walrus_frame, (narrowing_result, inf)) =
                        fa.with_frame_and_result(Frame::new_conditional(), || {
                            // This can happen in weird closures. I'm not currently sure how we should
                            // best handle that, see avoid_walrus_crash_when_variable_is_used_in_closure
                            if self.point(name_def.index()).calculated() {
                                return (None, inf);
                            }
                            let (narrowing_result, inf) =
                                self.save_walrus(name_def, inf.into_inferred(self.i_s));
                            (narrowing_result, inf.into())
                        });

                    let key = self.key_from_name_def(name_def);
                    if matches!(
                        narrowing_result,
                        Some(RedefinitionResult::TypeMismatch(true))
                    ) {
                        return (
                            Inferred::new_any_from_error().into(),
                            Frame::new_conditional(),
                            Frame::new_conditional(),
                        );
                    } else if let Some((walrus_truthy, walrus_falsey)) =
                        split_truthy_and_falsey(self.i_s, &inf)
                    {
                        debug!(
                            "Narrowed {} to true: {} and false: {}",
                            named_expr.as_code(),
                            walrus_truthy.format_short(self.i_s.db),
                            walrus_falsey.format_short(self.i_s.db)
                        );
                        let widens = walrus_frame
                            .entries
                            .into_iter()
                            .any(|e| e.key.equals(self.i_s.db, &key) && e.widens);
                        truthy.overwrite_entry(
                            self.i_s.db,
                            Entry {
                                widens,
                                modifies_ancestors: true,
                                ..Entry::new(key.clone(), walrus_truthy)
                            },
                        );
                        falsey.overwrite_entry(
                            self.i_s.db,
                            Entry {
                                widens,
                                ..Entry::new(key, walrus_falsey)
                            },
                        );
                    } else {
                        for entry in walrus_frame.entries {
                            truthy.overwrite_entry(self.i_s.db, entry.clone());
                            falsey.overwrite_entry(self.i_s.db, entry);
                        }
                    }
                    (inf, truthy, falsey)
                })
            }
        }
    }

    fn find_guards_in_expr(&self, expr: Expression) -> (TruthyInferred, Frame, Frame) {
        self.find_guards_in_expr_with_context(expr, &mut ResultContext::ValueExpected)
    }

    fn find_guards_in_expr_with_context(
        &self,
        expr: Expression,
        result_context: &mut ResultContext,
    ) -> (TruthyInferred, Frame, Frame) {
        match expr.unpack() {
            ExpressionContent::ExpressionPart(part) => {
                self.find_guards_in_expr_part(part, result_context)
            }
            _ => (
                self.infer_expression(expr).into(),
                Frame::new_conditional(),
                Frame::new_conditional(),
            ),
        }
    }

    fn find_guards_in_expr_part(
        &self,
        part: ExpressionPart,
        result_context: &mut ResultContext,
    ) -> (TruthyInferred, Frame, Frame) {
        let (inf, mut result) =
            self.find_guards_in_expression_parts_with_context(part, result_context);
        self.propagate_parent_unions(&mut result.truthy, &result.parent_unions);
        self.propagate_parent_unions(&mut result.falsey, &result.parent_unions);
        (inf, result.truthy, result.falsey)
    }

    fn find_guards_in_expression_parts(
        &self,
        part: ExpressionPart,
    ) -> (TruthyInferred, FramesWithParentUnions) {
        self.find_guards_in_expression_parts_with_context(part, &mut ResultContext::ValueExpected)
    }

    fn find_guards_in_expression_parts_with_context(
        &self,
        part: ExpressionPart,
        result_context: &mut ResultContext,
    ) -> (TruthyInferred, FramesWithParentUnions) {
        self.find_guards_in_expression_parts_inner(part, result_context)
            .unwrap_or_else(|inf| {
                let inf = inf.into();
                if let Some((truthy, falsey)) = split_truthy_and_falsey(self.i_s, &inf) {
                    let frames = FramesWithParentUnions {
                        truthy: Frame::from_type_without_entry(&truthy),
                        falsey: Frame::from_type_without_entry(&falsey),
                        ..Default::default()
                    };
                    let as_s = |frame: &Frame| match frame.unreachable {
                        true => "unreachable",
                        false => "reachable",
                    };
                    debug!(
                        "Split reachability for {} into true: {} and false: {}",
                        part.as_code(),
                        as_s(&frames.truthy),
                        as_s(&frames.falsey)
                    );
                    (inf, frames)
                } else {
                    (inf, FramesWithParentUnions::default())
                }
            })
    }

    fn find_guards_in_expression_parts_inner(
        &self,
        part: ExpressionPart,
        result_context: &mut ResultContext,
    ) -> Result<(TruthyInferred, FramesWithParentUnions), Inferred> {
        let narrow_from_key = |key: Option<FlowKey>, inf: Inferred, parent_unions| {
            let inf = inf.into();
            if let Some(key) = key
                && let Some((truthy, falsey)) = split_truthy_and_falsey(self.i_s, &inf)
            {
                debug!(
                    "Narrowed {} to true: {} and false: {}",
                    part.as_code(),
                    truthy.format_short(self.i_s.db),
                    falsey.format_short(self.i_s.db)
                );
                return Ok((
                    inf,
                    FramesWithParentUnions {
                        truthy: Frame::from_type(key.clone(), truthy),
                        falsey: Frame::from_type(key, falsey),
                        parent_unions,
                    },
                ));
            }
            Err(inf.into_inferred(self.i_s))
        };
        match part {
            ExpressionPart::Atom(atom) => {
                if let AtomContent::NamedExpression(named_expr) = atom.unpack() {
                    let (inf, truthy, falsey) = self.find_guards_in_named_expr(named_expr);
                    return Ok((
                        inf,
                        FramesWithParentUnions {
                            falsey,
                            truthy,
                            ..Default::default()
                        },
                    ));
                }
                let inf = self.infer_atom(atom, result_context);
                return narrow_from_key(self.key_from_atom(atom), inf, Default::default());
            }
            ExpressionPart::Comparisons(comps) => {
                if let Some(frames) = self.find_guards_in_comparisons(comps) {
                    return Ok((Inferred::new_bool(self.i_s.db).into(), frames));
                }
                return Ok((Inferred::new_bool(self.i_s.db).into(), Default::default()));
            }
            ExpressionPart::Conjunction(and) => {
                let (inf, left, right) = self.check_conjunction(and);

                return FLOW_ANALYSIS
                    .with(|fa| Ok((inf, fa.merge_conjunction(self.i_s, Some(left), right))));
            }
            ExpressionPart::Disjunction(or) => {
                let (inf, left_frames, right_frames) = self.check_disjunction(or, result_context);
                let mut parent_unions = left_frames.parent_unions;
                parent_unions.extend(right_frames.parent_unions);
                return Ok((
                    inf,
                    FLOW_ANALYSIS.with(|fa| FramesWithParentUnions {
                        truthy: fa.merge_or(
                            self.i_s,
                            left_frames.truthy,
                            right_frames.truthy,
                            true,
                        ),
                        falsey: merge_and(self.i_s, left_frames.falsey, right_frames.falsey),
                        parent_unions,
                    }),
                ));
            }
            ExpressionPart::Inversion(inv) => {
                let (_, mut frames) = self.find_guards_in_expression_parts(inv.expression());
                (frames.truthy, frames.falsey) = (frames.falsey, frames.truthy);
                return Ok((Inferred::new_bool(self.i_s.db).into(), frames));
            }
            ExpressionPart::Primary(primary) => match primary.second() {
                PrimaryContent::Execution(arg_details @ ArgumentsDetails::Node(args)) => {
                    let first = self.infer_primary_or_atom(primary.first());
                    match first.maybe_saved_specific(self.i_s.db) {
                        Some(Specific::BuiltinsIsinstance) => {
                            if let Some(frames) =
                                self.find_isinstance_or_issubclass_frames(args, false)
                            {
                                return Ok((Inferred::new_bool(self.i_s.db).into(), frames));
                            }
                        }
                        Some(Specific::BuiltinsIssubclass) => {
                            if let Some(frames) =
                                self.find_isinstance_or_issubclass_frames(args, true)
                            {
                                return Ok((Inferred::new_bool(self.i_s.db).into(), frames));
                            }
                        }
                        _ => {
                            if let Some(saved) = first.maybe_saved_link() {
                                if saved == self.i_s.db.python_state.callable_node_ref().as_link() {
                                    if let Some(frames) = self.guard_callable(args) {
                                        return Ok((
                                            Inferred::new_bool(self.i_s.db).into(),
                                            frames,
                                        ));
                                    }
                                } else if saved
                                    == self.i_s.db.python_state.hasattr_node_ref().as_link()
                                    && let Some(frames) = self.guard_hasattr(args)
                                {
                                    return Ok((Inferred::new_bool(self.i_s.db).into(), frames));
                                }
                            }
                            if let Some(c) = first.maybe_type_guard_callable(self.i_s) {
                                let simple_args = &SimpleArgs::new(
                                    *self.i_s,
                                    self.file,
                                    primary.index(),
                                    arg_details,
                                );
                                if let Some(frames) = self.guard_type_guard(simple_args, args, c) {
                                    return Ok((Inferred::new_bool(self.i_s.db).into(), frames));
                                }
                            }
                        }
                    }
                }
                PrimaryContent::Execution(_) => (),
                _ => {
                    let infos = self.key_from_primary(primary);
                    return narrow_from_key(infos.key, infos.inf, infos.parent_unions);
                }
            },
            _ => (),
        }
        Err(self.infer_expression_part_with_context(part, result_context))
    }

    fn find_guards_in_comparisons(&self, comps: Comparisons) -> Option<FramesWithParentUnions> {
        FLOW_ANALYSIS.with(|fa| {
            let mut frames: Option<FramesWithParentUnions> = None;
            let mut iterator = comps.iter().peekable();
            let mut left_infos = self.comparison_part_infos(iterator.peek().unwrap().left());
            while let Some(comparison) = iterator.next() {
                let mut invert = false;
                let right = comparison.right();
                let mut right_infos = self.comparison_part_infos(right);
                let new = match comparison {
                    ComparisonContent::Equals(..) => {
                        let mut eq_chain = vec![];
                        // `foo == bar == None` needs special handling
                        while let Some(ComparisonContent::Equals(_, _, r)) = iterator.peek() {
                            if eq_chain.is_empty() {
                                eq_chain.push(left_infos.clone());
                                eq_chain.push(right_infos.clone());
                            }
                            eq_chain.push(self.comparison_part_infos(*r));
                            iterator.next();
                        }
                        if eq_chain.is_empty() {
                            find_comparison_guards(self.i_s, &left_infos, &right_infos, true)
                        } else {
                            let result = find_comparison_chain_guards(self.i_s, &eq_chain, true);
                            right_infos = eq_chain.into_iter().last().unwrap();
                            result
                        }
                    }
                    ComparisonContent::NotEquals(..) => {
                        invert = true;
                        find_comparison_guards(self.i_s, &left_infos, &right_infos, true)
                    }
                    ComparisonContent::Is(..) => {
                        let mut is_chain = vec![];
                        // `foo is bar is None` needs special handling
                        while let Some(ComparisonContent::Is(_, _, r)) = iterator.peek() {
                            if is_chain.is_empty() {
                                is_chain.push(left_infos.clone());
                                is_chain.push(right_infos.clone());
                            }
                            is_chain.push(self.comparison_part_infos(*r));
                            iterator.next();
                        }
                        if is_chain.is_empty() {
                            find_comparison_guards(self.i_s, &left_infos, &right_infos, false)
                        } else {
                            let result = find_comparison_chain_guards(self.i_s, &is_chain, false);
                            right_infos = is_chain.into_iter().last().unwrap();
                            result
                        }
                    }
                    ComparisonContent::IsNot(..) => {
                        invert = true;
                        find_comparison_guards(self.i_s, &left_infos, &right_infos, false)
                    }
                    ComparisonContent::In(_, op, _) | ComparisonContent::NotIn(_, op, _) => {
                        if right_infos.inf.is_saved_partial_container(self.i_s.db) {
                            // Mypy simply disables type checking in the case of partials.
                            // Theoretically we could recheck after the partial was finished.
                            // See for example testInferFromEmptyListWhenUsingInWithStrictEquality,
                            // which has a TODO.
                            left_infos = right_infos;
                            continue;
                        }
                        self.guard_of_in_operator(op, &mut left_infos, &right_infos)
                    }
                    ComparisonContent::Ordering(operation) => {
                        let mut result = None;
                        if let Some(ComparisonKey::Len { key, inf }) = &left_infos.key {
                            result = narrow_len(
                                self.i_s,
                                key,
                                inf,
                                &left_infos.parent_unions,
                                &right_infos.inf,
                                LenNarrowing::from_operand(operation.infos.operand),
                            );
                        } else if let Some(ComparisonKey::Len { key, inf }) = &right_infos.key {
                            result = narrow_len(
                                self.i_s,
                                key,
                                inf,
                                &right_infos.parent_unions,
                                &left_infos.inf,
                                LenNarrowing::from_operand(operation.infos.operand).invert(),
                            );
                        }

                        if result.is_some() {
                            result
                        } else {
                            self.infer_comparison_part(
                                comparison,
                                left_infos.inf,
                                &right_infos.inf,
                            );
                            left_infos = right_infos;
                            continue;
                        }
                    }
                };
                if let Some(mut new) = new {
                    if invert {
                        (new.falsey, new.truthy) = (new.truthy, new.falsey);
                    }
                    frames = Some(fa.merge_conjunction(self.i_s, frames, new));
                } else {
                    self.infer_comparison_part(comparison, left_infos.inf, &right_infos.inf);
                }
                left_infos = right_infos
            }
            frames
        })
    }

    fn find_isinstance_or_issubclass_frames(
        &self,
        args: Arguments,
        issubclass: bool,
    ) -> Option<FramesWithParentUnions> {
        let mut iterator = args.iter();
        let Argument::Positional(arg) = iterator.next()? else {
            return None;
        };
        let input = self.key_from_namedexpression(arg);
        let Argument::Positional(type_arg) = iterator.next()? else {
            return None;
        };
        let mut isinstance_type = self.check_isinstance_or_issubclass_type(type_arg, issubclass)?;
        if iterator.next().is_some() {
            return None;
        }
        if isinstance_type.is_any() {
            // Parent unions are not narrowed, because with Any we know essentially nothing
            // about the type and its parents except that it can be anything.
            debug!("The isinstance type is Any, we therefore do not narrow");
            return Some(FramesWithParentUnions {
                truthy: Frame::from_type(input.key?, isinstance_type),
                falsey: Frame::new_conditional(),
                parent_unions: vec![],
            });
        }
        if issubclass && !matches!(isinstance_type, Type::Never(_)) {
            isinstance_type = Type::Type(Arc::new(isinstance_type))
        }

        let (truthy, falsey) = split_and_intersect(
            self.i_s,
            &input.inf.as_cow_type(self.i_s),
            &isinstance_type,
            |issue| {
                if self.flags().warn_unreachable {
                    self.add_issue(args.index(), issue)
                }
            },
        );
        let key = input.key?;
        Some(FramesWithParentUnions {
            truthy: Frame::from_type(key.clone(), truthy),
            falsey: Frame::from_type(key, falsey),
            parent_unions: input.parent_unions,
        })
    }

    fn guard_hasattr(&self, args: Arguments) -> Option<FramesWithParentUnions> {
        let mut iterator = args.iter();
        let Argument::Positional(arg) = iterator.next()? else {
            return None;
        };
        let result = self.key_from_namedexpression(arg);
        let key = result.key?;
        let Argument::Positional(str_arg) = iterator.next()? else {
            return None;
        };
        let attr_inf = self.infer_named_expression(str_arg);
        let attr = attr_inf.maybe_string_literal(self.i_s)?;

        let mut all_have_attr = true;
        let mut attr_t = Type::Never(NeverCause::Other);
        let mut falsey_parent = Type::Never(NeverCause::Other);
        for t in result
            .inf
            .as_cow_type(self.i_s)
            .iter_with_unpacked_unions(self.i_s.db)
        {
            if let Some(inf) = self
                .check_attr(t, attr.as_str(self.i_s.db))
                .into_maybe_inferred()
            {
                attr_t.union_in_place(inf.as_type(self.i_s));
            } else {
                attr_t.union_in_place(Type::Any(AnyCause::Todo));
                falsey_parent.union_in_place(t.clone());
                all_have_attr = false;
            }
        }
        if all_have_attr {
            // It's a bit weird, but in the case where all union parts have an attr, Mypy does not
            // perform any narrowing.
            return None;
        }
        let falsey = match falsey_parent {
            // Frames should not be unreachable, because people might be checking for deleted
            // attributes.
            Type::Never(_) => Frame::new_conditional(),
            _ => Frame::from_type(key.clone(), falsey_parent),
        };
        Some(FramesWithParentUnions {
            truthy: Frame::from_type(FlowKey::Member(Arc::new(key), attr), attr_t),
            falsey,
            parent_unions: ParentUnions::default(),
        })
    }

    fn guard_callable(&self, args: Arguments) -> Option<FramesWithParentUnions> {
        // Guards the builtins `callable(foo)`
        let mut iterator = args.iter();
        let Argument::Positional(arg) = iterator.next()? else {
            return None;
        };
        let result = self.key_from_namedexpression(arg);
        let key = result.key?;

        let mut callable_t = Type::Never(NeverCause::Other);
        let mut other_side = Type::Never(NeverCause::Other);
        let input_t = result.inf.as_cow_type(self.i_s);
        for t in input_t.iter_with_unpacked_unions(self.i_s.db) {
            let mut add_t = |t: &Type| {
                if t.is_any() {
                    callable_t.union_in_place(t.clone());
                    other_side.union_in_place(t.clone());
                } else if let Some(callable_like) = t.maybe_callable(self.i_s) {
                    if !callable_like.is_typed(false) {
                        other_side.union_in_place(t.clone());
                    }
                    callable_t.union_in_place(t.clone());
                } else {
                    other_side.union_in_place(t.clone());
                }
            };
            match t {
                Type::Type(inner) => match inner.as_ref() {
                    Type::Union(union) => {
                        for inner in union.iter() {
                            add_t(&Type::Type(Arc::new(inner.clone())));
                        }
                    }
                    _ => add_t(t),
                },
                _ => add_t(t),
            }
        }
        let falsey = if matches!(callable_t, Type::Never(_)) {
            callable_t = Type::Intersection(Intersection::new(Arc::new([
                Type::Callable(self.i_s.db.python_state.any_callable_from_error.clone()),
                input_t.into_owned(),
            ])));
            Frame::new_conditional()
        } else {
            Frame::from_type(key.clone(), other_side)
        };
        Some(FramesWithParentUnions {
            truthy: Frame::from_type(key, callable_t),
            falsey,
            parent_unions: ParentUnions::default(),
        })
    }

    fn guard_type_guard(
        &self,
        simple_args: &SimpleArgs,
        args: Arguments,
        might_have_guard: CallableLike,
    ) -> Option<FramesWithParentUnions> {
        match &might_have_guard {
            CallableLike::Callable(c) => self.check_type_guard_callable(simple_args, args, c, None),
            CallableLike::Overload(o) => {
                // Only check if there is a guard in there.
                if !o.iter_functions().any(|c| c.guard.is_some()) {
                    return None;
                }
                let overload = OverloadedFunction::new(o, None);
                debug!(
                    "Check overloaded TypeGuard/TypeIs {}",
                    overload.name(self.i_s.db)
                );
                let had_non_guard_match = Cell::new(false);
                let union_guard_result = Cell::<Option<FramesWithParentUnions>>::new(None);

                let _indent = debug_indent();
                let matching = overload.find_matching_function(
                    self.i_s,
                    simple_args,
                    false,
                    None,
                    false,
                    &mut ResultContext::ValueExpected,
                    None,
                    OnTypeError::new(&on_argument_type_error),
                    &|c, calculated_type_args| {
                        let Some(guard) = &c.content.guard else {
                            had_non_guard_match.set(true);
                            return Type::Never(NeverCause::Other);
                        };
                        let resolved_t = calculated_type_args
                            .into_return_type(self.i_s, &guard.type_, None, &|| None)
                            .as_type(self.i_s);
                        if let Some(y) = self.check_type_guard_callable(
                            simple_args,
                            args,
                            c.content,
                            Some(resolved_t),
                        ) {
                            union_guard_result.set(Some(
                                if let Some(found) = union_guard_result.take() {
                                    FLOW_ANALYSIS.with(|fa| FramesWithParentUnions {
                                        truthy: fa.merge_or(
                                            self.i_s,
                                            found.truthy,
                                            y.truthy,
                                            false,
                                        ),
                                        falsey: {
                                            // TODO this merging is a bit weird, because it
                                            // should not merge TypeGuard/TypeIn combinations,
                                            // but use a common_sub_type when it's two TypeIn
                                            // narrowing the same values. This should probably
                                            // hold for 99.999% of cases.
                                            if found.falsey.entries.is_empty()
                                                || y.falsey.entries.is_empty()
                                            {
                                                Frame::new_conditional()
                                            } else {
                                                merge_and(self.i_s, found.falsey, y.falsey)
                                            }
                                        },
                                        //falsey: merge_and(self.i_s, found.falsey, y.falsey),
                                        parent_unions: Default::default(),
                                    })
                                } else {
                                    y
                                },
                            ));
                        } else {
                            had_non_guard_match.set(true);
                        }
                        Type::Never(NeverCause::Other)
                    },
                );
                match matching {
                    OverloadResult::Single(c) => {
                        self.check_type_guard_callable(simple_args, args, c.content, None)
                    }
                    OverloadResult::Union(_) => {
                        if had_non_guard_match.get() {
                            return Some(Default::default());
                        }
                        union_guard_result.into_inner()
                    }
                    // Return the default, because the overload was already typechecked and
                    // doesn't need to be typechecked anymore
                    OverloadResult::NotFound => Some(Default::default()),
                }
            }
        }
    }

    fn check_type_guard_callable(
        &self,
        simple_args: &SimpleArgs,
        args: Arguments,
        callable: &CallableContent,
        guard_t: Option<Type>,
    ) -> Option<FramesWithParentUnions> {
        let guard = callable.guard.as_ref()?;
        let find_arg = || {
            let CallableParams::Simple(c_params) = &callable.params else {
                return None;
            };
            let first_param = c_params.iter().next()?;
            for arg in args.iter() {
                match arg {
                    Argument::Positional(arg) => return Some(self.key_from_namedexpression(arg)),
                    Argument::Keyword(kwarg) => {
                        let first_param_name = first_param.name.as_ref()?;
                        let (name, expr) = kwarg.unpack();
                        if name.as_code() == first_param_name.as_str(self.i_s.db) {
                            return Some(self.key_from_expression(expr));
                        }
                    }
                    _ => return None,
                }
            }
            None
        };

        let infos = find_arg()?;
        let key = infos.key?;

        let resolved_inf: Inferred;
        let resolved_guard_t = if let Some(g) = guard_t {
            Cow::Owned(g)
        } else {
            resolved_inf = Callable::new(callable, self.i_s.current_class())
                .execute_for_custom_return_type(
                    self.i_s,
                    simple_args,
                    false,
                    &guard.type_,
                    OnTypeError::new(&on_argument_type_error),
                    &mut ResultContext::ValueExpected,
                    None,
                );
            resolved_inf.as_cow_type(self.i_s)
        };
        let (truthy, falsey) = if guard.from_type_is {
            let (truthy, falsey) = split_and_intersect(
                self.i_s,
                &infos.inf.as_cow_type(self.i_s),
                &resolved_guard_t,
                |issue| {
                    if self.flags().warn_unreachable {
                        self.add_issue(args.index(), issue)
                    }
                },
            );
            (
                Frame::from_type(key.clone(), truthy),
                Frame::from_type(key, falsey),
            )
        } else {
            (
                Frame::from_type(key, resolved_guard_t.into_owned()),
                Frame::new_conditional(),
            )
        };
        Some(FramesWithParentUnions {
            truthy,
            falsey,
            parent_unions: infos.parent_unions,
        })
    }

    fn guard_of_in_operator(
        &self,
        op: Operand,
        left: &mut ComparisonPartInfos,
        right: &ComparisonPartInfos,
    ) -> Option<FramesWithParentUnions> {
        // This is needed, because the operator can also be `not in`
        let maybe_invert = |truthy, falsey, parent_unions| {
            self.infer_in_operator(NodeRef::new(self.file, op.index()), &left.inf, &right.inf);
            if op.as_code() == "in" {
                Some(FramesWithParentUnions {
                    truthy,
                    falsey,
                    parent_unions,
                })
            } else {
                Some(FramesWithParentUnions {
                    truthy: falsey,
                    falsey: truthy,
                    parent_unions,
                })
            }
        };
        let db = self.i_s.db;
        if let Some(ComparisonKey::Normal(left_key)) = &left.key {
            let right = &right.inf.as_cow_type(self.i_s);
            if let Some(entries) = right.maybe_fixed_len_tuple() {
                let left_t = left.inf.as_cow_type(self.i_s);
                let initial = Some((Frame::new_unreachable(), Frame::new_conditional()));
                if let Some((truthy, falsey)) = entries.iter().fold(initial, |initial, t| {
                    let initial = initial?;
                    let new = narrow_is_or_eq(self.i_s, left_key.clone(), &left_t, t, true)?;
                    Some(FLOW_ANALYSIS.with(|fa| {
                        let truthy = fa.merge_or(self.i_s, initial.0, new.0, false);
                        let falsey = merge_and(self.i_s, initial.1, new.1);
                        (truthy, falsey)
                    }))
                }) {
                    return maybe_invert(truthy, falsey, left.parent_unions.take());
                }
            }
            if let Some(container_item) = stdlib_container_item(db, right) {
                let left_t = left.inf.as_cow_type(self.i_s);
                if !container_item
                    .iter_with_unpacked_unions(db)
                    .any(|t| t == &Type::None)
                    && left_t.simple_overlaps(self.i_s, &container_item)
                    && let Some(t) = removed_optional(db, &left_t)
                {
                    return maybe_invert(
                        Frame::from_type(left_key.clone(), t),
                        Frame::new_conditional(),
                        left.parent_unions.take(),
                    );
                }
            }
        }
        // The right side can currently only be narrowed with TypedDicts
        let right_t = right.inf.as_cow_type(self.i_s);
        if right_t
            .iter_with_unpacked_unions(db)
            .any(|t| matches!(t, Type::TypedDict(_)))
            && let Some(ComparisonKey::Normal(right_key)) = &right.key
        {
            let left_t = left.inf.as_cow_type(self.i_s);
            let str_literals: Vec<_> = left_t
                .iter_with_unpacked_unions(db)
                .filter_map(|t| match t {
                    Type::Literal(Literal {
                        kind: LiteralKind::String(s),
                        ..
                    }) => Some(s.as_str(db)),
                    _ => None,
                })
                .collect();
            if !str_literals.is_empty() {
                let mut true_types = Type::Never(NeverCause::Other);
                let false_types = right_t.retain_in_union(|t| match t {
                    Type::TypedDict(td) => {
                        let mut true_only_count = 0;
                        let mut false_only_count = 0;
                        for str_literal in &str_literals {
                            // TODO extra_items: handle?
                            if let Some(m) = td.find_member(db, str_literal) {
                                if m.required {
                                    true_only_count += 1;
                                }
                            } else {
                                false_only_count += 1;
                            }
                        }
                        if true_only_count == str_literals.len() {
                            true_types.union_in_place(t.clone());
                            return false;
                        } else if !td.is_final || false_only_count != str_literals.len() {
                            true_types.union_in_place(t.clone());
                        }
                        true
                    }
                    _ => {
                        true_types.union_in_place(t.clone());
                        true
                    }
                });
                return maybe_invert(
                    Frame::from_type(right_key.clone(), true_types),
                    Frame::from_type(right_key.clone(), false_types),
                    // Taking it here is fine, because we don't want these to be duplicated
                    // entries from different comparisons
                    std::mem::take(&mut right.parent_unions.borrow_mut()),
                );
            }
        }
        None
    }

    fn key_from_name_def(&self, name_def: NameDef) -> FlowKey {
        let name_index = name_def.name_index();
        FlowKey::Name(PointLink::new(
            self.file.file_index,
            first_defined_name(self.file, name_index),
        ))
    }

    fn key_from_atom(&self, atom: Atom) -> Option<FlowKey> {
        match atom.unpack() {
            AtomContent::Name(name) => {
                return Some(FlowKey::Name(name_def_link(self.i_s.db, self.file, name)?));
            }
            AtomContent::NamedExpression(named_expr) => {
                if let NamedExpressionContent::Walrus(walrus) = named_expr.unpack() {
                    return Some(self.key_from_name_def(walrus.unpack().0));
                }
            }
            _ => (),
        };
        None
    }

    fn key_from_primary(&self, primary: Primary) -> KeyWithParentUnions {
        let second = primary.second();
        if matches!(second, PrimaryContent::Execution(_)) {
            return KeyWithParentUnions::new(
                self.infer_primary(primary, &mut ResultContext::ValueExpected),
                None,
            );
        }

        let mut base = match primary.first() {
            PrimaryOrAtom::Primary(primary) => self.key_from_primary(primary),
            PrimaryOrAtom::Atom(atom) => KeyWithParentUnions::new(
                self.infer_atom(atom, &mut ResultContext::ValueExpected),
                self.key_from_atom(atom),
            ),
        };
        let old_inf = base.inf;
        let old_base_key = base.key.take();
        let maybe_union = || {
            old_inf
                .as_cow_type(self.i_s)
                .maybe_union_like(self.i_s.db)
                .map(|u| u.into_owned())
        };

        if let Some((key, inf)) = self.maybe_has_primary_entry(primary) {
            let mut parent_unions = base.parent_unions;
            if let Some(union_type) = maybe_union() {
                parent_unions.push((old_base_key.unwrap(), union_type));
            }
            return KeyWithParentUnions {
                inf,
                key: Some(key.clone()),
                parent_unions,
            };
        }

        base.inf = self.infer_primary_or_primary_t_content(
            &old_inf,
            primary.index(),
            second,
            false,
            &mut ResultContext::ValueExpected,
        );
        match second {
            PrimaryContent::Attribute(attr) => {
                if let Some(base_key) = &old_base_key {
                    base.key = Some(self.key_from_attribute(base_key.clone(), attr));
                }
            }
            PrimaryContent::GetItem(slice_type) => {
                if let Some(index_key) = self.key_from_slice_type(slice_type)
                    && let Some(base_key) = &old_base_key
                {
                    base.key = Some(FlowKey::Index {
                        base_key: Arc::new(base_key.clone()),
                        match_index: index_key,
                        node_index: slice_type.index(),
                    });
                }
            }
            PrimaryContent::Execution(_) => unreachable!(),
        }
        if let Some(base_key) = old_base_key {
            // Only in case of valid keys we want to add the unions.
            if base.key.is_some()
                && let Some(union_type) = maybe_union()
            {
                base.parent_unions.push((base_key.clone(), union_type))
            }
        }
        base
    }

    fn key_from_expr_part(&self, expr_part: ExpressionPart) -> KeyWithParentUnions {
        match expr_part {
            ExpressionPart::Atom(atom) => KeyWithParentUnions::new(
                self.infer_atom(atom, &mut ResultContext::ValueExpected),
                self.key_from_atom(atom),
            ),
            ExpressionPart::Primary(primary) => self.key_from_primary(primary),
            _ => KeyWithParentUnions::new(self.infer_expression_part(expr_part), None),
        }
    }

    fn key_from_expression(&self, expr: Expression) -> KeyWithParentUnions {
        match expr.unpack() {
            ExpressionContent::ExpressionPart(part) => self.key_from_expr_part(part),
            _ => KeyWithParentUnions::new(self.infer_expression(expr), None),
        }
    }

    fn key_from_namedexpression(&self, named_expr: NamedExpression) -> KeyWithParentUnions {
        match named_expr.unpack() {
            NamedExpressionContent::Expression(expr) => self.key_from_expression(expr),
            NamedExpressionContent::Walrus(walrus) => KeyWithParentUnions {
                key: Some(self.key_from_name_def(walrus.name_def())),
                inf: self.infer_walrus(walrus, None),
                parent_unions: ParentUnions::default(),
            },
        }
    }

    fn key_from_slice_type(&self, slice_type: CSTSliceType) -> Option<FlowKeyIndex> {
        if let CSTSliceType::NamedExpression(ne) = slice_type {
            match self
                .infer_expression(ne.expression())
                .maybe_literal(self.i_s.db)
            {
                UnionValue::Single(Literal {
                    kind: LiteralKind::Int(i),
                    ..
                }) => Some(FlowKeyIndex::Int(i.try_into().ok()?)),
                UnionValue::Single(Literal {
                    kind: LiteralKind::String(s),
                    ..
                }) => Some(FlowKeyIndex::Str(s.as_str(self.i_s.db).into())),
                _ => None,
            }
        } else {
            None
        }
    }

    fn key_from_primary_target_or_atom(&self, p: PrimaryTargetOrAtom) -> Option<FlowKey> {
        match p {
            PrimaryTargetOrAtom::PrimaryTarget(t) => self.key_from_primary_target(t),
            PrimaryTargetOrAtom::Atom(atom) => self.key_from_atom(atom),
        }
    }

    fn key_from_attribute(&self, base_key: FlowKey, n: Name) -> FlowKey {
        FlowKey::Member(
            Arc::new(base_key),
            DbString::StringSlice(StringSlice::from_name(self.file.file_index, n)),
        )
    }

    fn key_from_primary_target(&self, primary_target: PrimaryTarget) -> Option<FlowKey> {
        let base_key = self.key_from_primary_target_or_atom(primary_target.first())?;
        match primary_target.second() {
            PrimaryContent::Attribute(n) => Some(self.key_from_attribute(base_key, n)),
            PrimaryContent::Execution(_) => None,
            PrimaryContent::GetItem(slice_type) => {
                self.key_from_slice_type(slice_type)
                    .map(|match_index| FlowKey::Index {
                        base_key: Arc::new(base_key),
                        node_index: slice_type.index(),
                        match_index,
                    })
            }
        }
    }

    fn maybe_has_primary_entry(&self, primary: Primary) -> Option<(FlowKey, Inferred)> {
        FLOW_ANALYSIS.with(|fa| {
            for frame in fa.frames.borrow().iter().rev() {
                for entry in &frame.entries {
                    if self.matches_primary_entry(primary, &entry.key) {
                        debug!(
                            "Use narrowed {} as {}",
                            primary.as_code(),
                            entry.debug_format_type(self.i_s.db)
                        );
                        return match &entry.type_ {
                            EntryKind::Type(t) => {
                                Some((entry.key.clone(), Inferred::from_type(t.clone())))
                            }
                            EntryKind::OriginalDeclaration => None,
                        };
                    }
                }
                // If an entry in the current frame overwrites entries further up the stack, it
                // invalidates any further lookup and we need to return without narrowing.
                if frame.entries.iter().any(|entry| {
                    entry.modifies_ancestors && self.matches_ancestor(primary, &entry.key)
                }) {
                    return None;
                }
            }
            None
        })
    }

    fn matches_ancestor(&self, p: Primary, key: &FlowKey) -> bool {
        let first = p.first();
        if let PrimaryOrAtom::Primary(earlier) = first
            && self.matches_ancestor(earlier, key)
        {
            return true;
        }
        self.match_primary_first_part(first, key)
    }

    fn match_primary_first_part(&self, pr: PrimaryOrAtom, key: &FlowKey) -> bool {
        match pr {
            PrimaryOrAtom::Primary(primary) => self.matches_primary_entry(primary, key),
            PrimaryOrAtom::Atom(atom) => {
                let FlowKey::Name(check_link) = key else {
                    return false;
                };
                let AtomContent::Name(name) = atom.unpack() else {
                    return false;
                };
                name_def_link(self.i_s.db, self.file, name) == Some(*check_link)
            }
        }
    }

    fn matches_primary_entry(&self, primary: Primary, key: &FlowKey) -> bool {
        // This method is only needed, because we want to avoid creating a FlowKey each time with
        // Rc allocations.
        match key {
            FlowKey::Member(base_key, right) => {
                if !self.match_primary_first_part(primary.first(), base_key) {
                    return false;
                }
                match primary.second() {
                    PrimaryContent::Attribute(attr) => attr.as_code() == right.as_str(self.i_s.db),
                    _ => false,
                }
            }
            FlowKey::Index {
                base_key,
                match_index,
                ..
            } => match primary.second() {
                PrimaryContent::GetItem(slice_type) => {
                    if !self.match_primary_first_part(primary.first(), base_key) {
                        return false;
                    }
                    self.key_from_slice_type(slice_type)
                        .is_some_and(|other_index_key| match_index == &other_index_key)
                }
                _ => false,
            },
            FlowKey::Name(_) => false,
        }
    }

    fn comparison_part_infos(&self, expr_part: ExpressionPart) -> ComparisonPartInfos {
        let check_for_call = || {
            let ExpressionPart::Primary(primary) = expr_part else {
                return None;
            };
            let PrimaryContent::Execution(ArgumentsDetails::Node(args)) = primary.second() else {
                return None;
            };
            let mut args_iterator = args.iter();
            let Argument::Positional(first_arg) = args_iterator.next().unwrap() else {
                return None;
            };
            if args_iterator.next().is_some() {
                return None;
            }

            let pre_exec = self.infer_primary_or_atom(primary.first());
            let db = self.i_s.db;
            let as_infos = |is_len| {
                let with_key = self.key_from_namedexpression(first_arg);
                with_key.key.map(|key| {
                    let full_inf = self.infer_expression_part(expr_part);
                    let inf = with_key.inf;
                    ComparisonPartInfos {
                        key: Some(match is_len {
                            false => ComparisonKey::TypeOf { key, inf },
                            true => ComparisonKey::Len { key, inf },
                        }),
                        inf: full_inf,
                        parent_unions: RefCell::new(with_key.parent_unions),
                    }
                })
            };
            if pre_exec.maybe_saved_specific(db) == Some(Specific::BuiltinsType) {
                as_infos(false)
            } else if pre_exec.maybe_saved_link() == Some(db.python_state.len_node_ref().as_link())
            {
                as_infos(true)
            } else {
                None
            }
        };
        check_for_call().unwrap_or_else(|| {
            let k = self.key_from_expr_part(expr_part);
            ComparisonPartInfos {
                key: k.key.map(ComparisonKey::Normal),
                inf: k.inf,
                parent_unions: RefCell::new(k.parent_unions),
            }
        })
    }

    fn check_attr(&self, t: &Type, attr: &str) -> LookupResult {
        t.lookup(
            self.i_s,
            self.file,
            attr,
            LookupKind::Normal,
            &mut ResultContext::ValueExpected,
            &|_| (),
            &|_| (), // OnLookupError is irrelevant for us here.
        )
    }

    pub fn has_frames(&self) -> bool {
        !FLOW_ANALYSIS.with(|f| f.frames.borrow().is_empty())
    }

    pub fn add_star_import_to_base_narrowing(&self, name_def: NameDef, original: Inferred) {
        // This is a bit weird and probably only correct in most cases, not in all
        FLOW_ANALYSIS.with(|fa| {
            let mut frames = fa.frames.borrow_mut();
            if frames.len() > 1
                && let Some(frame) = frames.first_mut()
            {
                let key = self.key_from_name_def(name_def);
                if frame.lookup_entry(self.i_s.db, &key).is_none() {
                    let mut entry = Entry::new(key, original.as_type(self.i_s));
                    entry.widens = true;
                    frame.entries.push(entry)
                }
            }
        })
    }
}

fn run_pattern_for_each_type(
    i_s: &InferenceState,
    t: Type,
    callback: impl Fn(Type) -> (Type, Type),
) -> (Type, Type) {
    fn run(
        i_s: &InferenceState,
        mut iterator: std::iter::Peekable<impl Iterator<Item = Type>>,
        callback: impl Fn(Type) -> (Type, Type),
    ) -> (Frame, Type, Type) {
        let Some(t) = iterator.next() else {
            return (
                Frame::new_conditional(),
                Type::Never(NeverCause::Other),
                Type::Never(NeverCause::Other),
            );
        };
        FLOW_ANALYSIS.with(|fa| {
            let (first_frame, (truthy1, falsey1)) =
                fa.with_frame_and_result(Frame::new_conditional(), || callback(t));
            if iterator.peek().is_none() {
                return (first_frame, truthy1, falsey1);
            }
            let (next_frame, truthy2, falsey2) = run(i_s, iterator, callback);
            (
                fa.merge_or(i_s, first_frame, next_frame, false),
                truthy1.simplified_union(i_s, &truthy2),
                falsey1.union(falsey2),
            )
        })
    }

    let iterator = t
        .into_iter_with_unpacked_unions(i_s.db, true)
        .map(|e| e.type_)
        .peekable();
    let (frame, truthy1, falsey1) = run(i_s, iterator, callback);
    FLOW_ANALYSIS.with(|fa| fa.merge_conditional(i_s, frame, Frame::new_conditional()));
    (truthy1, falsey1)
}

fn run_pattern_for_each_type_with_pattern_result(
    i_s: &InferenceState,
    inf: Inferred,
    callback: impl Fn(Type) -> (Type, Type),
) -> PatternResult {
    let (truthy, falsey) = run_pattern_for_each_type(i_s, inf.into_type(i_s), callback);
    PatternResult {
        truthy_t: Inferred::from_type(truthy),
        falsey_t: Inferred::from_type(falsey),
    }
}

fn is_self_match_type(db: &Database, t: &Type) -> bool {
    let py = &db.python_state;
    match t {
        Type::Class(c) => {
            c.link == py.int_link()
                || c.link == py.int_link()
                || c.link == py.float_link()
                || c.link == py.bool_link()
                || c.link == py.str_link()
                || c.link == py.bytes_link()
                || c.link == py.bytearray_link()
                || c.link == py.list_link()
                || c.link == py.dict_link()
                || c.link == py.set_link()
                || c.link == py.frozenset_link()
                || c.link == py.int_link()
        }
        Type::Literal(l) => is_self_match_type(db, &l.fallback_type(db)),
        Type::Tuple(_) => true,
        _ => false,
    }
}

#[derive(Debug)]
struct PatternResult {
    truthy_t: Inferred,
    falsey_t: Inferred,
}

impl PatternResult {
    fn is_falsey_unreachable(&self, i_s: &InferenceState) -> bool {
        self.falsey_t.is_never(i_s)
    }
}

enum TruthyInferred {
    Simple {
        inf: Inferred,
        truthiness: Option<bool>,
    },
    Union(Vec<Self>),
}

impl TruthyInferred {
    fn has_partial_container(&self, db: &Database) -> bool {
        match self {
            Self::Simple { inf, .. } => inf
                .maybe_saved_specific(db)
                .is_some_and(|specific| specific.is_partial_container()),
            Self::Union(infs) => infs.iter().any(|inf| inf.has_partial_container(db)),
        }
    }

    fn as_cow_type<'slf>(&'slf self, i_s: &InferenceState<'slf, '_>) -> Cow<'slf, Type> {
        match self {
            Self::Simple { inf, .. } => inf.as_cow_type(i_s),
            Self::Union(infs) => Cow::Owned(Type::simplified_union_from_iterators(
                i_s,
                infs.iter().map(|inf| inf.as_cow_type(i_s)),
            )),
        }
    }

    fn combine(self, other: Self) -> Self {
        let other_iterator = match other {
            Self::Union(infs) => EitherIterator::Left(infs.into_iter()),
            inf => EitherIterator::Right(std::iter::once(inf)),
        };
        match self {
            Self::Union(mut infs) => {
                infs.extend(other_iterator);
                Self::Union(infs)
            }
            inf => Self::Union(std::iter::once(inf).chain(other_iterator).collect()),
        }
    }

    fn into_inferred<'slf>(self, i_s: &InferenceState<'slf, '_>) -> Inferred {
        match self {
            Self::Simple { inf, .. } => inf,
            Self::Union { .. } => Inferred::from_type(self.as_cow_type(i_s).into_owned()),
        }
    }
}

impl From<Inferred> for TruthyInferred {
    fn from(inf: Inferred) -> Self {
        Self::Simple {
            inf,
            truthiness: None,
        }
    }
}

enum InferredSubject {
    SubjectExprContent(KeyWithParentUnions),
    TupleKeys(Vec<Option<SubjectKey>>),
}

enum SubjectKey {
    Expr {
        key: FlowKey,
        parent_unions: ParentUnions,
    },
    Tuple(Vec<Option<SubjectKey>>),
}

impl Type {
    pub fn ensure_dunder_match_args_with_literals(
        self,
        db: &Database,
        name: Option<PointLink>,
    ) -> Self {
        let Some(name) = name else { return self };
        if let Some(tup_entries) = self.maybe_fixed_len_tuple() {
            for entry in tup_entries {
                if let Type::Class(_) = entry {
                    let name_ref = NodeRef::from_link(db, name);
                    if let Some(name) = name_ref.maybe_name()
                        && let Some(assignment) = name.maybe_assignment_definition_name()
                        && let Some((_, _, expr)) =
                            assignment.maybe_simple_type_expression_assignment()
                        && let Some(tuple) = expr.maybe_tuple()
                        && let Some(t) = NodeRef::new(name_ref.file, tuple.index()).maybe_type()
                    {
                        return t.clone();
                    }
                }
            }
        }
        self
    }
}

#[derive(Copy, Clone, Debug)]
pub(crate) enum RedefinitionResult {
    RedefinitionAllowed,
    TypeMismatch(bool),
}

fn name_def_link(db: &Database, file: &PythonFile, name: Name) -> Option<PointLink> {
    let p = file.points.get(name.index());
    if p.calculated() {
        if p.kind() != PointKind::Redirect {
            // For example Any due to an unresolved name.
            return None;
        }
        let def = p.node_index();
        let file = db.loaded_python_file(p.file_index());
        Some(PointLink::new(
            p.file_index(),
            first_defined_name(file, def),
        ))
    } else {
        // This happens for example with builtins
        None
    }
}

#[derive(Clone)]
struct KeyWithParentUnions {
    key: Option<FlowKey>,
    inf: Inferred,
    parent_unions: ParentUnions,
}

impl KeyWithParentUnions {
    fn new(inf: Inferred, key: Option<FlowKey>) -> Self {
        Self {
            key,
            inf,
            parent_unions: vec![],
        }
    }
}

#[derive(Clone, Debug)]
enum ComparisonKey {
    Normal(FlowKey),
    TypeOf { key: FlowKey, inf: Inferred }, // For type(x) == int
    Len { key: FlowKey, inf: Inferred },    // For len(x) == 2
}

#[derive(Clone)]
struct ComparisonPartInfos {
    key: Option<ComparisonKey>,
    inf: Inferred,
    // This is a RefCell to be able to take it out of the comparison part infos easily
    parent_unions: RefCell<ParentUnions>,
}

struct FramesWithParentUnions {
    truthy: Frame,
    falsey: Frame,
    parent_unions: ParentUnions,
}

impl Default for FramesWithParentUnions {
    fn default() -> Self {
        Self {
            truthy: Frame::new_conditional(),
            falsey: Frame::new_conditional(),
            parent_unions: ParentUnions::default(),
        }
    }
}

fn stdlib_container_item(db: &Database, t: &Type) -> Option<Type> {
    // Returns int for a list[int] or other containers. This is used for narrowing in. However
    // we can only do this if we know how __contains__ works.
    let item = match t {
        Type::Class(c) => {
            let class = c.class(db);
            if let Some(nt) = class.maybe_named_tuple_base(db) {
                return stdlib_container_item(db, &Type::Tuple(nt.as_tuple()));
            } else {
                let s = &db.python_state;
                if [
                    s.list_node_ref(),
                    s.dict_node_ref(),
                    s.set_node_ref(),
                    s.frozenset_node_ref(),
                    s.keys_view_node_ref(),
                    s._collections_abc_dict_keys_node_ref(),
                ]
                .contains(&class.node_ref)
                {
                    class.nth_type_argument(db, 0)
                } else {
                    return None;
                }
            }
        }
        Type::Tuple(tup) => tup.fallback_type(db).clone(),
        Type::NamedTuple(named_tup) => {
            return stdlib_container_item(db, &Type::Tuple(named_tup.as_tuple()));
        }
        Type::TypedDict(_) => db.python_state.str_type(),
        _ => return None,
    };
    if matches!(item, Type::Any(_)) {
        return None;
    }
    if matches!(&item, Type::Class(c) if c.class(db).is_object_class(db)) {
        return None;
    }
    Some(item)
}

fn removed_optional(db: &Database, full: &Type) -> Option<Type> {
    for t in full.iter_with_unpacked_unions(db) {
        if matches!(t, Type::None) {
            return Some(full.retain_in_union(|t| !matches!(t, Type::None)));
        }
    }
    None
}

fn find_comparison_guards(
    i_s: &InferenceState,
    left: &ComparisonPartInfos,
    right: &ComparisonPartInfos,
    is_eq: bool,
) -> Option<FramesWithParentUnions> {
    if let Some(result) = check_for_comparison_guard(i_s, left, &right.inf, is_eq) {
        return Some(result);
    }
    if let Some(result) = check_for_comparison_guard(i_s, right, &left.inf, is_eq) {
        return Some(result);
    }
    None
}

fn find_comparison_chain_guards(
    i_s: &InferenceState,
    chain: &[ComparisonPartInfos],
    is_eq: bool,
) -> Option<FramesWithParentUnions> {
    FLOW_ANALYSIS.with(|fa| {
        let mut frames = None;
        let mut type_of_count = 0;
        'outer: for (i, part1) in chain.iter().enumerate() {
            type_of_count += matches!(part1.key, Some(ComparisonKey::TypeOf { .. })) as usize;
            for (k, part2) in chain.iter().enumerate() {
                if i == k {
                    continue;
                }
                if let Some(new) = check_for_comparison_guard(i_s, part1, &part2.inf, is_eq) {
                    frames = Some(fa.merge_conjunction(i_s, frames, new));
                    continue 'outer;
                }
            }
        }
        if type_of_count > 0 && type_of_count + 1 != chain.len() {
            return None;
        }
        frames
    })
}

fn check_for_comparison_guard(
    i_s: &InferenceState,
    checking_side: &ComparisonPartInfos,
    other_side_inf: &Inferred,
    is_eq: bool,
) -> Option<FramesWithParentUnions> {
    match checking_side.key.as_ref()? {
        ComparisonKey::Normal(key) => {
            // Narrow Foo in `Foo is None` or `Foo == None`
            let (truthy, falsey) = narrow_is_or_eq(
                i_s,
                key.clone(),
                &checking_side.inf.as_cow_type(i_s),
                &other_side_inf.as_cow_type(i_s),
                is_eq,
            )?;
            Some(FramesWithParentUnions {
                truthy,
                falsey,
                parent_unions: std::mem::take(&mut checking_side.parent_unions.borrow_mut()),
            })
        }
        ComparisonKey::TypeOf { key, inf } => {
            if let Type::Type(base_truthy) = other_side_inf.as_cow_type(i_s).as_ref() {
                if matches!(base_truthy.as_ref(), Type::Any(_)) {
                    // Narrowing to Any has no value and will only worsen type information.
                    return None;
                }
                let mut truthy = (**base_truthy).clone();
                let is_final = match &truthy {
                    Type::Class(c) => {
                        if c.class(i_s.db).is_metaclass(i_s.db) {
                            // For now ignore this, Mypy has only very few tests about this.
                            return None;
                        }
                        c.class(i_s.db).use_cached_class_infos(i_s.db).is_final
                    }
                    _ => false,
                };
                let inf_t = inf.as_cow_type(i_s);
                if !truthy.is_simple_sub_type_of(i_s, &inf_t).bool() {
                    truthy = Type::Never(NeverCause::Other);
                }
                Some(FramesWithParentUnions {
                    truthy: Frame::from_type(key.clone(), truthy),
                    falsey: match is_final {
                        true => Frame::from_type(
                            key.clone(),
                            inf_t.retain_in_union(|t| {
                                !t.is_simple_same_type(i_s, base_truthy).bool()
                            }),
                        ),
                        false => Frame::new_conditional(),
                    },
                    parent_unions: std::mem::take(&mut checking_side.parent_unions.borrow_mut()),
                })
            } else {
                None
            }
        }
        ComparisonKey::Len { key, inf } => Some(narrow_len(
            i_s,
            key,
            inf,
            &checking_side.parent_unions,
            other_side_inf,
            LenNarrowing::Equals,
        )?),
    }
}

#[derive(Copy, Clone)]
enum LenNarrowing {
    Equals, // NotEquals will be done by inverting in a separate place
    GreaterThan,
    LowerThan,
    GreaterEquals,
    LowerEquals,
}

impl LenNarrowing {
    fn from_operand(operand: &str) -> Self {
        match operand {
            ">" => LenNarrowing::GreaterThan,
            "<" => LenNarrowing::LowerThan,
            ">=" => LenNarrowing::GreaterEquals,
            "<=" => LenNarrowing::LowerEquals,
            _ => unreachable!(),
        }
    }

    fn invert(self) -> Self {
        match self {
            Self::Equals => Self::Equals,
            Self::GreaterThan => Self::LowerThan,
            Self::LowerThan => Self::GreaterThan,
            Self::GreaterEquals => Self::LowerEquals,
            Self::LowerEquals => Self::GreaterEquals,
        }
    }
}

fn narrow_len(
    i_s: &InferenceState,
    key: &FlowKey,
    inferred_type_param: &Inferred,
    parent_unions: &RefCell<ParentUnions>,
    other_inf: &Inferred,
    kind: LenNarrowing,
) -> Option<FramesWithParentUnions> {
    if let Type::Literal(Literal {
        kind: LiteralKind::Int(n),
        ..
    }) = other_inf.as_cow_type(i_s).as_ref()
        && let Ok(n) = n.try_into()
    {
        let inf_t = inferred_type_param.as_cow_type(i_s);
        let retain = |full: &Type, negative| {
            let mut out = Type::Never(NeverCause::Other);
            for part_t in full.iter_with_unpacked_unions(i_s.db) {
                match part_t {
                    Type::Tuple(tup) => {
                        if narrow_len_for_tuples(n, &tup.args, negative, kind, |t| {
                            out.union_in_place(t)
                        }) {
                            continue;
                        }
                    }
                    Type::NamedTuple(nt) => {
                        if matches_fixed_len_namedtuple_len(nt, n, kind) == negative {
                            continue;
                        }
                    }
                    Type::Class(c) => {
                        if let Some(nt) = c.class(i_s.db).maybe_named_tuple_base(i_s.db)
                            && matches_fixed_len_namedtuple_len(&nt, n, kind) == negative
                        {
                            continue;
                        }
                    }
                    _ => (),
                }
                out.union_in_place(part_t.clone())
            }
            out
        };
        let truthy = retain(&inf_t, false);
        let falsey = retain(&inf_t, true);
        return Some(FramesWithParentUnions {
            truthy: Frame::from_type(key.clone(), truthy),
            falsey: Frame::from_type(key.clone(), falsey),
            parent_unions: std::mem::take(&mut parent_unions.borrow_mut()),
        });
    }
    None
}

fn matches_fixed_len_namedtuple_len(nt: &NamedTuple, n: usize, kind: LenNarrowing) -> bool {
    let TupleArgs::FixedLen(ts) = &nt.as_tuple_ref().args else {
        unreachable!();
    };
    matches_fixed_len_tuple_len(ts, n, kind)
}

fn matches_fixed_len_tuple_len(ts: &[Type], n: usize, kind: LenNarrowing) -> bool {
    let len = ts.len();
    match kind {
        LenNarrowing::Equals => len == n,
        LenNarrowing::GreaterThan => len > n,
        LenNarrowing::LowerThan => len < n,
        LenNarrowing::GreaterEquals => len >= n,
        LenNarrowing::LowerEquals => len <= n,
    }
}

fn narrow_len_for_tuples(
    n: usize,
    tuple_args: &TupleArgs,
    negative: bool,
    kind: LenNarrowing,
    mut add_type: impl FnMut(Type),
) -> bool {
    let mut invert = false;
    let mut lower_than = || match kind {
        LenNarrowing::Equals => None,
        LenNarrowing::GreaterThan => {
            invert = true;
            Some(n + 1)
        }
        LenNarrowing::LowerThan => Some(n),
        LenNarrowing::GreaterEquals => {
            invert = true;
            Some(n)
        }
        LenNarrowing::LowerEquals => Some(n + 1),
    };
    match tuple_args {
        TupleArgs::FixedLen(ts) => {
            if matches_fixed_len_tuple_len(ts, n, kind) == negative {
                return true;
            }
        }
        TupleArgs::ArbitraryLen(t) => {
            let as_repeated_t =
                |t: &Type, n| std::iter::repeat_with(|| t.clone()).take(n).collect();
            let mut add_tuple_of_len = |n| {
                add_type(Type::Tuple(Tuple::new_fixed_length(as_repeated_t(t, n))));
            };
            if n <= MAX_PRECISE_TUPLE_SIZE {
                if let Some(lower_than) = lower_than() {
                    if lower_than > 0 {
                        if invert == negative {
                            for i in 0..lower_than {
                                add_tuple_of_len(i);
                            }
                        } else {
                            add_type(Type::Tuple(Tuple::new(TupleArgs::WithUnpack(WithUnpack {
                                before: as_repeated_t(t, lower_than),
                                unpack: TupleUnpack::ArbitraryLen((**t).clone()),
                                after: Arc::new([]),
                            }))));
                        }
                        return true;
                    } else if invert == negative {
                        // This leads to unreachable, because the
                        // len(...) < 0 does never exist.
                        return true;
                    }
                } else if negative == invert {
                    add_tuple_of_len(n);
                    return true;
                }
            }
        }
        TupleArgs::WithUnpack(with_unpack) => {
            let min_len = with_unpack.before.len() + with_unpack.after.len();
            let lower_than = lower_than();
            if (lower_than.unwrap_or_else(|| n + 1) <= min_len) && invert == negative {
                // This is unreachable, so no type is added.
                return true;
            }
            if lower_than.unwrap_or(n) > MAX_PRECISE_TUPLE_SIZE {
                return false;
            }
            let middle = match &with_unpack.unpack {
                TupleUnpack::ArbitraryLen(t) => t,
                TupleUnpack::TypeVarTuple(_) => return false,
            };
            let middle_iter = |middle_len| std::iter::repeat_with(|| middle).take(middle_len);
            let mut add_fixed_len_tuple = |middle_len| {
                add_type(Type::Tuple(Tuple::new_fixed_length(
                    with_unpack
                        .before
                        .iter()
                        .chain(middle_iter(middle_len))
                        .chain(with_unpack.after.iter())
                        .cloned()
                        .collect(),
                )));
            };
            if let Some(lower_than) = lower_than {
                if invert == negative {
                    for i in 0..(lower_than - min_len) {
                        add_fixed_len_tuple(i);
                    }
                } else {
                    add_type(Type::Tuple(Tuple::new(TupleArgs::WithUnpack(WithUnpack {
                        before: with_unpack
                            .before
                            .iter()
                            .chain(middle_iter(lower_than - min_len))
                            .cloned()
                            .collect(),
                        unpack: with_unpack.unpack.clone(),
                        after: with_unpack.after.clone(),
                    }))));
                }
                return true;
            } else if !negative {
                add_fixed_len_tuple(n - min_len);
                return true;
            }
        }
    }
    false
}

fn split_and_intersect(
    i_s: &InferenceState,
    original_t: &Type,
    isinstance_type: &Type,
    mut add_issue: impl Fn(IssueKind),
) -> (Type, Type) {
    // Please listen to "Red Hot Chili Peppers - Otherside" here.
    let mut true_type = Type::Never(NeverCause::Other);
    let mut other_side = Type::Never(NeverCause::Other);
    let matcher = &mut Matcher::with_ignored_promotions();
    let mut type_var_split = false;
    for t in original_t.iter_with_unpacked_unions(i_s.db) {
        let mut split = |t: &Type| {
            let mut matched = false;
            let mut matched_with_any = true;
            let mut had_any = None;
            for isinstance_t in isinstance_type.iter_with_unpacked_unions(i_s.db) {
                // dict is not a super type of TypedDict, because both are mutable, but we still
                // want isinstance to separate it when used with isinstance
                if matches!(t, Type::TypedDict(_))
                    && isinstance_t
                        .maybe_class(i_s.db)
                        .is_some_and(|c| c.node_ref == i_s.db.python_state.dict_node_ref())
                {
                    matched = true;
                    matched_with_any = false;
                    continue;
                }
                if isinstance_t.is_any() {
                    had_any = Some(isinstance_t.clone());
                    continue;
                }
                match isinstance_t.is_super_type_of(i_s, matcher, t) {
                    Match::True { with_any: true, .. } => {
                        matched = true;
                    }
                    Match::True { .. } => {
                        matched_with_any = false;
                        matched = true;
                    }
                    Match::False { .. } => {
                        if isinstance_t.is_sub_type_of(i_s, matcher, t).bool() {
                            true_type.simplified_union_in_place(i_s, isinstance_t);
                        }
                    }
                }
            }
            if matched {
                if matched_with_any {
                    true_type.simplified_union_in_place(i_s, isinstance_type);
                    other_side.union_in_place(t.clone());
                } else {
                    // This used to just use union_in_place. However this caused problems with bool
                    // | int, which could not be added to complex. I'm still not sure what's
                    // correct here. This feels like a very weird consequence of type promotions.
                    // This caused issues when type checking Mypy.
                    true_type.simplified_union_in_place(i_s, t);
                }
            } else {
                other_side.union_in_place(t.clone())
            }
            if let Some(any) = had_any {
                // This piece of code is completely weird and only needed because of the weird
                // Any ordering.
                if matches!(isinstance_type, Type::Union(u) if u.entries.first().unwrap().format_index > 0)
                {
                    true_type = any.union(true_type.clone());
                } else {
                    true_type.union_in_place(any);
                }
            }
        };
        match t {
            Type::Type(inner) => match inner.as_ref() {
                Type::Union(union) => {
                    for inner in union.iter() {
                        split(&Type::Type(Arc::new(inner.clone())))
                    }
                }
                _ => split(t),
            },
            Type::Any(_) => {
                true_type = isinstance_type.clone();
                other_side.union_in_place(t.clone())
            }
            Type::TypeVar(tv) if matches!(tv.type_var.kind(i_s.db), TypeVarKind::Unrestricted) => {
                if let Some(new) = intersect(i_s, t, isinstance_type, &mut add_issue) {
                    type_var_split = true;
                    true_type = new.into_owned();
                    other_side.union_in_place(t.clone())
                } else {
                    split(t)
                }
            }
            _ => split(t),
        }
    }
    if true_type.is_never() {
        if original_t.overlaps(i_s, matcher, isinstance_type) {
            true_type = isinstance_type.clone();
        } else {
            for t in original_t.iter_with_unpacked_unions(i_s.db) {
                if let Some(new) = intersect(i_s, t, isinstance_type, &mut add_issue) {
                    true_type.simplified_union_in_place(i_s, &new);
                }
            }
        }
    }
    // Handle int/float/complex promotions
    {
        if let Type::Class(c) = isinstance_type {
            let is_non_promotable = |for_class| {
                original_t
                    .iter_with_unpacked_unions(i_s.db)
                    .any(|t| match t {
                        Type::Class(c) => {
                            c.link == for_class
                                && matches!(
                                    &c.generics,
                                    ClassGenerics::None {
                                        might_be_promoted: false
                                    }
                                )
                        }
                        _ => false,
                    })
            };
            let complex = i_s.db.python_state.complex_link();
            let float = i_s.db.python_state.float_link();
            if c.link == float {
                if !is_non_promotable(float) {
                    // This is a special case. Promotion makes it so a float is not always an int.
                    // We therefore making the other side an int.
                    if let Some(new) =
                        replace_promoted(i_s, &other_side, PromotionReplacementFor::Float)
                    {
                        other_side = new.union(i_s.db.python_state.int_type())
                    } else {
                        let int_t = i_s.db.python_state.int_type();
                        if !type_var_split
                            && !other_side.is_simple_super_type_of(i_s, &int_t).bool()
                        {
                            other_side = other_side.union(int_t)
                        }
                    }
                }
            } else if c.link == i_s.db.python_state.int_link() {
                if let Some(new) = replace_promoted(i_s, &other_side, PromotionReplacementFor::Int)
                {
                    other_side = new
                }
            } else if c.link == complex {
                if other_side.is_never() && !is_non_promotable(complex) {
                    other_side = i_s.db.python_state.float_type()
                }
            }
        }
    }
    debug!(
        "Narrowed because of isinstance or TypeIs to {} and other side to {}",
        true_type.format_short(i_s.db),
        other_side.format_short(i_s.db)
    );
    (true_type, other_side)
}

#[derive(Copy, Clone)]
enum PromotionReplacementFor {
    Int,
    Float,
}

fn replace_promoted(
    i_s: &InferenceState,
    t: &Type,
    replacement: PromotionReplacementFor,
) -> Option<Type> {
    let db = i_s.db;
    match t {
        Type::Class(c) => {
            let new_non_promoted = |link| {
                Type::Class(GenericClass {
                    link,
                    generics: ClassGenerics::None {
                        might_be_promoted: false,
                    },
                })
            };
            let complex = db.python_state.complex_link();
            match replacement {
                PromotionReplacementFor::Int => {
                    let float = db.python_state.float_link();
                    if c.link == float {
                        return Some(new_non_promoted(float));
                    } else {
                        if c.link == complex {
                            return Some(new_non_promoted(float).union(new_non_promoted(complex)));
                        }
                    }
                }
                PromotionReplacementFor::Float => {
                    if c.link == complex {
                        return Some(new_non_promoted(complex));
                    }
                }
            }
        }
        Type::Union(u) => {
            if !u.iter().any(|t| matches!(t, Type::Class(c) if c.link == db.python_state.float_link() || c.link == db.python_state.complex_link())) {
                return None
            }
            return Some(Type::simplified_union_from_iterators(
                i_s,
                u.iter()
                    .map(|t| replace_promoted(i_s, t, replacement).unwrap_or_else(|| t.clone())),
            ));
        }
        _ => (),
    }
    None
}

fn intersect<'x>(
    i_s: &InferenceState,
    t1: &'x Type,
    t2: &'x Type,
    add_issue: &mut dyn FnMut(IssueKind),
) -> Option<Cow<'x, Type>> {
    Some(if t2.is_simple_sub_type_of(i_s, t1).bool() {
        Cow::Borrowed(t2)
    } else if t2.is_simple_super_type_of(i_s, t1).bool() {
        Cow::Borrowed(t1)
    } else {
        Cow::Owned(Intersection::new_instance_intersection(i_s, t1, t2, add_issue).ok()?)
    })
}

#[derive(PartialEq)]
enum ExceptType {
    ContainsOnlyBaseExceptions,
    HasExceptionGroup,
    Invalid,
}

impl ExceptType {
    fn from_types<'x, B: Borrow<Type>>(
        db: &Database,
        allow_tuple: bool,
        types: impl Iterator<Item = B>,
    ) -> Self {
        let mut result = ExceptType::ContainsOnlyBaseExceptions;
        for t in types {
            match except_type(db, t.borrow(), allow_tuple) {
                ExceptType::ContainsOnlyBaseExceptions => (),
                x @ ExceptType::HasExceptionGroup => result = x,
                ExceptType::Invalid => return ExceptType::Invalid,
            }
        }
        result
    }
}

fn except_type(db: &Database, t: &Type, allow_tuple: bool) -> ExceptType {
    match t {
        Type::Type(t) => {
            if let Some(cls) = t.maybe_class(db).or_else(|| match t.as_ref() {
                Type::Dataclass(dc) => Some(dc.class(db)),
                _ => None,
            }) {
                if cls.is_base_exception_group(db) {
                    return ExceptType::HasExceptionGroup;
                } else if cls.is_base_exception(db) {
                    return ExceptType::ContainsOnlyBaseExceptions;
                }
            }
            ExceptType::Invalid
        }
        Type::Any(_) => ExceptType::ContainsOnlyBaseExceptions,
        Type::Tuple(content) if allow_tuple => match &content.args {
            TupleArgs::FixedLen(ts) => ExceptType::from_types(db, false, ts.iter()),
            TupleArgs::ArbitraryLen(t) => except_type(db, t, false),
            TupleArgs::WithUnpack(w) => match &w.unpack {
                TupleUnpack::TypeVarTuple(_) => ExceptType::Invalid,
                TupleUnpack::ArbitraryLen(t) => ExceptType::from_types(
                    db,
                    false,
                    w.before
                        .iter()
                        .chain(w.after.iter())
                        .chain(std::iter::once(t)),
                ),
            },
        },
        Type::Union(union) => {
            let mut result = ExceptType::ContainsOnlyBaseExceptions;
            for t in union.iter() {
                match except_type(db, t, allow_tuple) {
                    ExceptType::ContainsOnlyBaseExceptions => (),
                    x @ ExceptType::HasExceptionGroup => result = x,
                    ExceptType::Invalid => return ExceptType::Invalid,
                }
            }
            result
        }
        _ => ExceptType::Invalid,
    }
}

pub fn process_unfinished_partials(db: &Database, partials: impl IntoIterator<Item = PointLink>) {
    for partial in partials.into_iter() {
        let node_ref = NodeRef::from_link(db, partial);
        let point = node_ref.point();
        if let Some(specific) = point.maybe_specific()
            && specific.is_partial()
        {
            node_ref.finish_partial_with_annotation_needed(db);
        }
    }
}

fn verify_constraint(db: &Database, verify: Box<DelayedConstraintVerification>) {
    let add_issue_at = NodeRef::from_link(db, verify.add_issue_at);
    let i_s = &InferenceState::new(db, add_issue_at.file);
    match verify.type_var.kind(db) {
        TypeVarKind::Unrestricted => unreachable!(),
        TypeVarKind::Bound(bound) => {
            if !bound.is_simple_super_type_of(i_s, &verify.actual).bool() {
                add_issue_at.add_issue(
                    i_s,
                    IssueKind::TypeVarBoundViolation {
                        actual: verify.actual.format_short(db),
                        of: verify.of_name.as_str(db).into(),
                        expected: bound.format_short(db),
                    },
                );
            }
        }
        TypeVarKind::Constraints(mut constraints) => {
            if let Type::TypeVar(usage) = &verify.actual
                && let TypeVarKind::Constraints(mut constraints2) = usage.type_var.kind(db)
                && constraints2.all(|t2| {
                    constraints
                        .clone()
                        .any(|t| t.is_simple_super_type_of(i_s, t2).bool())
                })
            {
                // The provided type_var2 is a subset of the type_var constraints.
                return;
            }
            if !constraints.any(|t| t.is_simple_same_type(i_s, &verify.actual).bool()) {
                add_issue_at.add_issue(
                    i_s,
                    IssueKind::InvalidTypeVarValue {
                        type_var_name: Box::from(verify.type_var.name(db)),
                        of: format!("\"{}\"", verify.of_name.as_str(db)).into(),
                        actual: verify.actual.format_short(db),
                    },
                );
            }
        }
    }
}
