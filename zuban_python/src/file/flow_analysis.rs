use std::{
    cell::{Cell, RefCell, RefMut},
    rc::Rc,
};

use parsa_python_cst::{
    Argument, Arguments, ArgumentsDetails, AssertStmt, Atom, AtomContent, Block, BreakStmt,
    CompIfIterator, ComparisonContent, Comparisons, Conjunction, ContinueStmt, DelTarget,
    DelTargets, Disjunction, ElseBlock, ExceptExpression, Expression, ExpressionContent,
    ExpressionPart, ForIfClauseIterator, ForStmt, IfBlockIterator, IfBlockType, IfStmt, Name,
    NameDefinition, NamedExpression, NamedExpressionContent, NodeIndex, Operand, Primary,
    PrimaryContent, PrimaryOrAtom, PrimaryTarget, PrimaryTargetOrAtom, SliceType as CSTSliceType,
    Target, Ternary, TryBlockType, TryStmt, WhileStmt,
};

use crate::{
    arguments::SimpleArgs,
    database::{ClassKind, Database, PointKind, PointLink, Specific},
    debug,
    diagnostics::IssueKind,
    getitem::SliceType,
    inference_state::InferenceState,
    inferred::{Inferred, UnionValue},
    matching::{Generic, LookupKind, Match, Matcher, OnTypeError, ResultContext},
    node_ref::NodeRef,
    type_::{
        simplified_union_from_iterators, AnyCause, CallableContent, CallableLike, CallableParams,
        ClassGenerics, DbString, EnumMember, Intersection, Literal, LiteralKind, LookupResult,
        NamedTuple, NeverCause, StringSlice, Tuple, TupleArgs, TupleUnpack, Type, TypeVarKind,
        UnionType, WithUnpack,
    },
    type_helpers::{Callable, Class, ClassLookupOptions, Function},
    utils::join_with_commas,
};

use super::{
    first_defined_name, first_defined_name_of_multi_def,
    inference::{instantiate_except, instantiate_except_star, Inference},
    name_binder::{is_expr_part_reachable_for_name_binder, Truthiness},
    on_argument_type_error, PythonFile,
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
    Member(Rc<FlowKey>, DbString),
    Index {
        base_key: Rc<FlowKey>,
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
}

#[derive(Debug, Clone, PartialEq)]
enum FlowKeyIndex {
    Int(usize),
    Str(String),
}

#[derive(Debug, Clone)]
struct Entry {
    key: FlowKey,
    type_: Option<Type>,
    modifies_ancestors: bool,
    deleted: bool, // e.g. after a `del foo`
    widens: bool,  // e.g. if a type is defined as None and later made an optional.
}

impl Entry {
    fn new(key: FlowKey, type_: Type) -> Self {
        Entry {
            key,
            type_: Some(type_),
            modifies_ancestors: false,
            deleted: false,
            widens: false,
        }
    }

    fn with_declaration(&self) -> Self {
        Entry {
            key: self.key.clone(),
            type_: None,
            modifies_ancestors: self.modifies_ancestors,
            deleted: self.deleted,
            widens: self.widens,
        }
    }

    #[inline]
    fn simplified_union(&self, i_s: &InferenceState, other: &Self) -> Option<Type> {
        self.type_
            .as_ref()
            .zip(other.type_.as_ref())
            .map(|(t1, t2)| t1.simplified_union(i_s, t2))
    }

    #[inline]
    fn union(&mut self, i_s: &InferenceState, other: &Self, invert_type: bool) {
        if invert_type {
            self.type_ = other.simplified_union(i_s, self);
        } else {
            self.type_ = self.simplified_union(i_s, other);
        }
        self.modifies_ancestors |= other.modifies_ancestors;
        self.deleted |= other.deleted;
        self.widens |= other.widens;
    }

    fn union_of_refs(&self, i_s: &InferenceState, other: &Self) -> Self {
        Self {
            key: self.key.clone(),
            type_: self.simplified_union(i_s, other),
            modifies_ancestors: self.modifies_ancestors | other.modifies_ancestors,
            deleted: self.deleted | other.deleted,
            widens: self.widens | other.widens,
        }
    }

    fn common_sub_type(&self, i_s: &InferenceState, other: &Self) -> Option<Option<Type>> {
        let Some(t1) = self.type_.as_ref() else {
            return Some(other.type_.clone());
        };
        let Some(t2) = other.type_.as_ref() else {
            return Some(Some(t1.clone()));
        };
        t1.common_sub_type(i_s, t2).map(|t| Some(t))
    }

    fn debug_format_type(&self, db: &Database) -> Box<str> {
        match self.type_.as_ref() {
            Some(t) => t.format_short(db),
            None => "<widened back to declaration>".into(),
        }
    }
}

#[derive(Debug, Default, Clone)]
struct Frame {
    entries: Entries,
    unreachable: bool,
    reported_unreachable: bool,
}

impl Frame {
    fn new(entries: Entries) -> Self {
        Self {
            entries,
            unreachable: false,
            reported_unreachable: false,
        }
    }

    fn new_unreachable() -> Self {
        Self {
            entries: Default::default(),
            unreachable: true,
            reported_unreachable: false,
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

    fn add_entry_from_type(&mut self, i_s: &InferenceState, key: FlowKey, type_: Type) {
        self.add_entry(i_s, Entry::new(key, type_))
    }

    fn from_type_without_entry(t: Type) -> Self {
        match t {
            Type::Never(_) => Self::new_unreachable(),
            _ => Self::default(),
        }
    }

    fn lookup_entry(&self, db: &Database, key: &FlowKey) -> Option<&Entry> {
        self.entries.iter().find(|entry| entry.key.equals(db, key))
    }

    fn from_type(key: FlowKey, type_: Type) -> Self {
        match type_ {
            Type::Never(_) => Self::new_unreachable(),
            type_ => Self::new(vec![Entry::new(key, type_)]),
        }
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

#[derive(Debug, Default)]
pub struct FlowAnalysis {
    frames: RefCell<Vec<Frame>>,
    try_frames: RefCell<Vec<Entries>>,
    loop_details: RefCell<Option<LoopDetails>>,
    partials_in_module: RefCell<Vec<PointLink>>,
    in_type_checking_only_block: Cell<bool>, // For stuff like if TYPE_CHECKING:
    accumulating_types: Cell<usize>, // Can accumulate nested and thereore use this counter like a stack
}

impl FlowAnalysis {
    fn lookup_narrowed_key_and_deleted(
        &self,
        db: &Database,
        lookup_key: FlowKey,
    ) -> Option<(Inferred, bool)> {
        let frames = self.frames.borrow();
        let entry = frames
            .iter()
            .rev()
            .find_map(|frame| frame.lookup_entry(db, &lookup_key))?;
        Some((
            Inferred::from_type(entry.type_.as_ref()?.clone()),
            entry.deleted,
        ))
    }

    pub fn in_conditional(&self) -> bool {
        self.frames.borrow().len() > 1
    }

    pub fn is_unreachable(&self) -> bool {
        self.frames.borrow().last().unwrap().unreachable
    }

    #[inline]
    fn top_frame(&self) -> RefMut<Frame> {
        RefMut::map(self.frames.borrow_mut(), |frames| {
            frames.last_mut().unwrap()
        })
    }

    pub fn enable_reported_unreachable_in_top_frame(&self) {
        self.top_frame().reported_unreachable = true;
    }

    pub fn report_unreachable_if_not_reported_before(&self, callback: impl FnOnce()) {
        let mut top_frame = self.top_frame();
        if !top_frame.reported_unreachable {
            top_frame.reported_unreachable = true;
            callback()
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
                self.overwrite_entries(i_s.db, false_frame.entries)
            } else if !true_frame.unreachable {
                self.overwrite_entries(i_s.db, true_frame.entries)
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
                        // Assign false to make sure it is not handled again from the other side.
                        other_entry.modifies_ancestors = false;

                        self.overwrite_entry(i_s, other_entry.union_of_refs(i_s, first_entry));
                        continue 'outer;
                    }
                }
                if first_entry.widens {
                    let declaration_t = Type::None;
                    let mut entry = first_entry.clone();
                    entry.type_ = Some(entry.type_.unwrap().union(declaration_t));
                    self.overwrite_entry(i_s, entry)
                } else {
                    self.overwrite_entry(
                        i_s,
                        self.merge_key_with_ancestor_assignment(i_s, first_entry),
                    )
                }
            }
        }
    }

    fn overwrite_entry(&self, i_s: &InferenceState, new_entry: Entry) {
        for entries in self.try_frames.borrow_mut().iter_mut() {
            invalidate_child_entries(entries, i_s.db, &new_entry.key);
            // We don't want to add entries if they are already overwritten in the same frame.
            if entries
                .iter()
                .any(|e| new_entry.key.is_child_of(i_s.db, &e.key))
            {
                continue;
            }

            let mut add_entry_to_try_frame = |new_entry: &Entry| {
                for entry in &mut *entries {
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
                entries.push(new)
            }
        }

        let mut top_frame = self.top_frame();
        invalidate_child_entries(&mut top_frame.entries, i_s.db, &new_entry.key);
        let entries = &mut top_frame.entries;
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
            // not be able to know if the entry would invalidate entries further up the stack.
            .unwrap_or_else(|| search_for.with_declaration())
    }

    fn remove_key_if_modifies_ancestors(&self, i_s: &InferenceState, key: &FlowKey) {
        self.top_frame()
            .entries
            .retain(|entry| !entry.modifies_ancestors || !entry.key.equals(i_s.db, key))
    }

    fn overwrite_entries(&self, db: &Database, new_entries: Entries) {
        let mut top_frame = self.top_frame();

        for entry in &new_entries {
            invalidate_child_entries(&mut top_frame.entries, db, &entry.key);
        }

        let entries = &mut top_frame.entries;
        'outer: for new_entry in new_entries {
            for entry in &mut *entries {
                if entry.key.equals(db, &new_entry.key) {
                    *entry = new_entry;
                    continue 'outer;
                }
            }
            entries.push(new_entry)
        }
    }

    fn overwrite_frame(&self, db: &Database, new_frame: Frame) {
        self.overwrite_entries(db, new_frame.entries);
        self.top_frame().unreachable |= new_frame.unreachable;
    }

    pub fn with_new_frame_and_return_unreachable(&self, callable: impl FnOnce()) -> bool {
        self.frames.borrow_mut().push(Frame::default());
        callable();
        let frame = self.frames.borrow_mut().pop().unwrap();
        frame.unreachable
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

    fn with_new_try_frame(&self, callable: impl FnOnce()) -> Frame {
        self.try_frames.borrow_mut().push(vec![]);
        callable();
        Frame {
            entries: self.try_frames.borrow_mut().pop().unwrap(),
            ..Frame::default()
        }
    }

    fn with_new_loop_frame(&self, frame: Frame, callable: impl FnOnce()) -> (Frame, LoopDetails) {
        let old = self.loop_details.borrow_mut().replace(LoopDetails {
            break_frames: vec![],
            continue_frames: vec![],
            loop_frame_index: self.frames.borrow().len(),
        });
        let after_frame = self.with_frame(frame, || callable());
        let mut loop_details = self.loop_details.borrow_mut();
        let result = loop_details.take().unwrap();
        *loop_details = old;
        (after_frame, result)
    }

    fn merge_frames_for_index(&self, db: &Database, frame_index: usize) -> Frame {
        let mut result = Frame::default();
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
        self.top_frame().unreachable = true
    }

    pub fn add_partial(&self, defined_at: PointLink) {
        self.partials_in_module.borrow_mut().push(defined_at)
    }

    pub fn check_for_unfinished_partials(&self, i_s: &InferenceState) {
        let mut partials = self.partials_in_module.borrow_mut();
        for partial in partials.iter() {
            let node_ref = NodeRef::from_link(i_s.db, *partial);
            if let Some(specific) = node_ref.point().maybe_specific() {
                if specific.is_partial() {
                    node_ref.add_need_type_annotation_issue(i_s, specific)
                }
            }
        }
        partials.clear()
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
        Frame::new(new_entries)
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
                    x_entry.type_ = Some(Type::Never(NeverCause::Other));
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
        Type::TypeVar(tv) => match &tv.type_var.kind {
            TypeVarKind::Bound(bound) => has_explicit_literal(db, bound),
            _ => false,
        },
        _ => false,
    })
}

pub fn has_custom_special_method(i_s: &InferenceState, t: &Type, method: &str) -> bool {
    t.iter_with_unpacked_unions(i_s.db).any(|t| {
        let cls = match t {
            Type::Class(c) => c.class(i_s.db),
            Type::Dataclass(dc) => dc.class(i_s.db),
            Type::Enum(enum_) => enum_.class(i_s.db),
            Type::EnumMember(member) => member.enum_.class(i_s.db),
            Type::Type(t) => {
                if let Some(link) = t
                    .maybe_class(i_s.db)
                    .and_then(|c| c.maybe_metaclass(i_s.db))
                {
                    Class::from_non_generic_link(i_s.db, link)
                } else {
                    return false;
                }
            }
            _ => return false,
        };
        let details = cls.lookup(i_s, method, ClassLookupOptions::new(&|_| ()));
        details.lookup.is_some() && !details.class.originates_in_builtins_or_typing(i_s.db)
    })
}

fn has_custom_eq(i_s: &InferenceState, t: &Type) -> bool {
    has_custom_special_method(i_s, t, "__eq__") || has_custom_special_method(i_s, t, "__ne__")
}

fn split_off_singleton(
    i_s: &InferenceState,
    t: &Type,
    split_off: &Type,
    abort_on_custom_eq: bool,
) -> Option<(Type, Type)> {
    let matches_singleton = |t: &_| match split_off {
        Type::EnumMember(member1) => match t {
            Type::EnumMember(member2) => member1.is_same_member(member2),
            _ => false,
        },
        _ => split_off == t,
    };
    let mut other_return = Type::Never(NeverCause::Other);
    let mut left = Type::Never(NeverCause::Other);
    let mut add = |t| left.union_in_place(t);
    for sub_t in t.iter_with_unpacked_unions(i_s.db) {
        match sub_t {
            Type::Any(_) => {
                // Any can be None or something else.
                other_return = split_off.clone();
                add(sub_t.clone());
            }
            Type::Enum(enum_) => {
                if abort_on_custom_eq && has_custom_eq(i_s, t) {
                    return None;
                }
                if let Type::EnumMember(split) = split_off {
                    if enum_.defined_at == split.enum_.defined_at {
                        for (i, _) in enum_.members.iter().enumerate() {
                            let new_member =
                                Type::EnumMember(EnumMember::new(enum_.clone(), i, false));
                            if i == split.member_index {
                                other_return.union_in_place(new_member)
                            } else {
                                add(new_member)
                            }
                        }
                        continue;
                    }
                }
                add(sub_t.clone())
            }
            _ if matches_singleton(sub_t) => other_return = split_off.clone(),
            _ => {
                if abort_on_custom_eq && has_custom_eq(i_s, t) {
                    return None;
                }
                add(sub_t.clone())
            }
        }
    }
    Some((left, other_return))
}

fn narrow_is_or_eq(
    i_s: &InferenceState,
    key: FlowKey,
    left_t: &Type,
    right_t: &Type,
    is_eq: bool,
) -> Option<(Frame, Frame)> {
    let split = |key: FlowKey| {
        let (rest, none) = split_off_singleton(i_s, left_t, right_t, is_eq)?;
        let result = (
            Frame::from_type(key.clone(), none),
            Frame::from_type(key, rest),
        );
        Some(result)
    };

    match right_t {
        Type::EnumMember(member) if member.implicit => {
            let mut new_member = member.clone();
            new_member.implicit = false;
            narrow_is_or_eq(i_s, key, left_t, &Type::EnumMember(new_member), is_eq)
        }
        Type::None if !is_eq => split(key),
        Type::EnumMember(member) if !is_eq || !member.implicit => split(key),
        Type::Enum(enum_) if enum_.members.len() == 1 => {
            // Enums with a single item can be compared to that item.
            narrow_is_or_eq(
                i_s,
                key,
                left_t,
                &Type::EnumMember(EnumMember::new(enum_.clone(), 0, false)),
                is_eq,
            )
        }
        // Mypy does only want to narrow if there are explicit literals on one side. See also
        // comments around testNarrowingEqualityFlipFlop.
        Type::Literal(literal1)
            if is_eq && (!literal1.implicit || has_explicit_literal(i_s.db, left_t))
                || !is_eq && matches!(literal1.kind, LiteralKind::Bool(_)) =>
        {
            let mut true_type = Type::Never(NeverCause::Other);
            let mut false_type = Type::Never(NeverCause::Other);
            let true_literal = || {
                let mut new_literal = literal1.clone();
                new_literal.implicit = false;
                Type::Literal(new_literal)
            };
            for sub_t in left_t.iter_with_unpacked_unions(i_s.db) {
                match sub_t {
                    Type::Literal(literal2) if literal1.value(i_s.db) == literal2.value(i_s.db) => {
                        true_type.union_in_place(true_literal())
                    }
                    _ => {
                        if let Some((truthy, falsey)) =
                            maybe_split_bool_from_literal(i_s.db, sub_t, &literal1.kind)
                        {
                            true_type.union_in_place(truthy);
                            false_type.union_in_place(falsey);
                            continue;
                        }
                        if has_custom_eq(i_s, sub_t) {
                            return None;
                        }
                        if sub_t.is_simple_super_type_of(i_s, right_t).bool() {
                            true_type.union_in_place(right_t.clone())
                        }
                        false_type.union_in_place(sub_t.clone())
                    }
                }
            }
            Some((
                Frame::from_type(key.clone(), true_type),
                Frame::from_type(key, false_type),
            ))
        }
        /* Originally enabled in 566ee94f6, but had issues...
        Type::Literal(literal1) if is_eq && !has_custom_eq(i_s, left_t) => Some((
            Frame::new_unreachable(),
            Frame::from_type(key, left_t.clone()),
        )),
        */
        Type::Class(c) if c.link == i_s.db.python_state.ellipsis_link() => split(key),
        _ => match left_t {
            left_t @ Type::Union(union) => {
                // Remove None from left, if the right types match everything except None.
                if left_t
                    .iter_with_unpacked_unions(i_s.db)
                    .any(|t| matches!(t, Type::None))
                {
                    let (new_left, _) = split_off_singleton(i_s, left_t, &Type::None, is_eq)?;
                    if new_left.is_simple_sub_type_of(i_s, right_t).bool()
                        || new_left.is_simple_super_type_of(i_s, right_t).bool()
                    {
                        return Some((Frame::from_type(key, new_left), Frame::default()));
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
    if let Type::Class(class) = t {
        if let LiteralKind::Bool(b) = literal {
            if class.link == db.python_state.bool_node_ref().as_link() {
                return Some((
                    Type::Literal(Literal::new(LiteralKind::Bool(*b))),
                    Type::Literal(Literal::new(LiteralKind::Bool(!*b))),
                ));
            }
        }
    }
    None
}

fn split_truthy_and_falsey(i_s: &InferenceState, t: &Type) -> Option<(Type, Type)> {
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
            LiteralKind::Int(i) => check(*i != 0),
            _ => None,
        };
        let falsey = || Some((Type::Never(NeverCause::Other), t.clone()));
        match t {
            Type::None => Some((Type::Never(NeverCause::Other), Type::None)),
            Type::Literal(literal) => check_literal(literal),
            Type::Tuple(tup) => match &tup.args {
                TupleArgs::ArbitraryLen(t) => Some((
                    Type::Tuple(Tuple::new(TupleArgs::WithUnpack(WithUnpack {
                        before: Rc::new([(**t).clone()]),
                        unpack: TupleUnpack::ArbitraryLen((**t).clone()),
                        after: Rc::new([]),
                    }))),
                    Type::Tuple(Tuple::new_fixed_length(Rc::new([]))),
                )),
                _ => None,
            },
            Type::Class(c) => maybe_split_bool_from_literal(i_s.db, t, &LiteralKind::Bool(true))
                .or_else(|| {
                    let class = c.class(i_s.db);
                    let class_lookup =
                        class.lookup(i_s, "__bool__", ClassLookupOptions::new(&|_| ()));
                    let Some(CallableLike::Callable(callable)) = class_lookup
                        .lookup
                        .into_maybe_inferred()
                        .filter(|_| !class_lookup.class.is_object(i_s.db))
                        .and_then(|inf| inf.as_cow_type(i_s).maybe_callable(i_s))
                    else {
                        if let Some(nt) = class.maybe_named_tuple_base(i_s.db) {
                            if nt.params().is_empty() {
                                todo!()
                            } else {
                                return Some((t.clone(), Type::Never(NeverCause::Other)));
                            }
                        }
                        return None;
                    };
                    match &callable.return_type {
                        Type::Literal(literal) => check_literal(literal),
                        _ => None,
                    }
                }),
            _ => None,
        }
    };

    match t {
        Type::Union(union) => {
            let mut truthy = Type::Never(NeverCause::Other);
            let mut falsey = Type::Never(NeverCause::Other);
            let mut had_split = false;
            for t in union.iter() {
                let result = split_truthy_and_falsey(i_s, t);
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

impl Inference<'_, '_, '_> {
    pub fn is_unreachable(&self) -> bool {
        FLOW_ANALYSIS.with(|fa| fa.is_unreachable())
    }

    pub fn in_type_checking_only_block(&self) -> bool {
        FLOW_ANALYSIS.with(|fa| fa.in_type_checking_only_block.get())
    }

    pub fn mark_current_frame_unreachable(&self) {
        FLOW_ANALYSIS.with(|fa| fa.mark_current_frame_unreachable())
    }

    pub fn maybe_lookup_narrowed_name(
        &self,
        original_name_index: NodeIndex,
        name_link: PointLink,
    ) -> Option<Inferred> {
        let (result, deleted) = FLOW_ANALYSIS
            .with(|fa| fa.lookup_narrowed_key_and_deleted(self.i_s.db, FlowKey::Name(name_link)))?;
        if deleted {
            self.add_issue(original_name_index, IssueKind::ReadingDeletedVariable)
        }
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

            let assert_point = self.file.points.get(assert_stmt.index());
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
        current_t: &Type,
        check_for_error: impl FnOnce() -> bool,
    ) {
        let mut widens = false;
        if matches!(declaration_t, Type::None) && !matches!(current_t, Type::None) {
            widens = true;
        } else if current_t.is_any() && !declaration_t.is_any_or_any_in_union(self.i_s.db) {
            // Any should not be narrowed if it is not part of a union with any.
            FLOW_ANALYSIS.with(|fa| {
                fa.remove_key_if_modifies_ancestors(self.i_s, &FlowKey::Name(first_name_link))
            });
            return;
        } else if check_for_error() {
            return; // There was an error so return and don't narrow.
        }
        self.assign_type_for_node_index(first_name_link, current_t.clone(), widens)
    }

    pub fn maybe_lookup_narrowed_primary_target(
        &self,
        primary_target: PrimaryTarget,
    ) -> Option<Inferred> {
        let key = self.key_from_primary_target(primary_target)?;
        Some(
            FLOW_ANALYSIS
                .with(|fa| fa.lookup_narrowed_key_and_deleted(self.i_s.db, key))?
                .0,
        )
    }

    pub fn save_narrowed_primary_target(&self, primary_target: PrimaryTarget, t: &Type) {
        if let Some(key) = self.key_from_primary_target(primary_target) {
            self.save_narrowed(key, t.clone(), false)
        }
    }

    pub fn assign_type_for_node_index(&self, first_name_link: PointLink, t: Type, widens: bool) {
        self.save_narrowed(FlowKey::Name(first_name_link), t, widens);
    }

    fn save_narrowed(&self, key: FlowKey, type_: Type, widens: bool) {
        FLOW_ANALYSIS.with(|fa| {
            fa.overwrite_entry(
                self.i_s,
                Entry {
                    key,
                    type_: Some(type_),
                    modifies_ancestors: true,
                    deleted: false,
                    widens,
                },
            )
        })
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
                    .has_never_from_inference(self.i_s.db);
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
                            &mut ResultContext::Known(
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
                                &mut ResultContext::Known(
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
            let Some(if_inf) = if_inf else {
                return else_inf.unwrap_or_else(|| todo!("This is probably unlikely to happen"));
            };
            let Some(else_inf) = else_inf else {
                return if_inf;
            };

            if_inf.simplified_union(self.i_s, else_inf)
        })
    }

    pub fn flow_analysis_for_if_stmt(
        &self,
        if_stmt: IfStmt,
        class: Option<Class>,
        func: Option<&Function>,
    ) {
        self.process_ifs(if_stmt.iter_blocks(), class, func)
    }

    pub fn flow_analysis_for_while_stmt(
        &self,
        while_stmt: WhileStmt,
        class: Option<Class>,
        func: Option<&Function>,
    ) {
        let (condition, block, else_block) = while_stmt.unpack();
        self.process_loop(Some(condition), block, else_block, class, func)
    }

    fn process_loop(
        &self,
        if_expr: Option<NamedExpression>,
        block: Block,
        else_block: Option<ElseBlock>,
        class: Option<Class>,
        func: Option<&Function>,
    ) {
        FLOW_ANALYSIS.with(|fa| {
            let (true_frame, false_frame) = if let Some(if_expr) = if_expr {
                let (_, truthy, falsey) = self.find_guards_in_named_expr(if_expr);
                (truthy, falsey)
            } else {
                (Frame::default(), Frame::default())
            };
            let (mut after_frame, loop_details) = fa.with_new_loop_frame(true_frame, || {
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

    pub fn flow_analysis_for_for_stmt(
        &self,
        for_stmt: ForStmt,
        class: Option<Class>,
        func: Option<&Function>,
        is_async: bool,
    ) {
        let (star_targets, star_exprs, block, else_block) = for_stmt.unpack();
        self.cache_for_stmt_names(star_targets, star_exprs, is_async);
        self.process_loop(None, block, else_block, class, func)
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
            .file
            .points
            .get(if_block.first_leaf_index())
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
        self.check_conjunction(and).0
    }

    pub fn flow_analysis_for_del_stmt(&self, del_targets: DelTargets) {
        for del_target in del_targets.iter() {
            match del_target {
                DelTarget::Target(target) => self.flow_analysis_for_del_target(target),
                DelTarget::DelTargets(del_targets) => self.flow_analysis_for_del_stmt(del_targets),
            }
        }
    }

    pub fn delete_name(&self, name_def: NameDefinition) {
        FLOW_ANALYSIS.with(|fa| {
            fa.overwrite_entry(
                self.i_s,
                Entry {
                    key: self.key_from_name_def(name_def),
                    type_: Some(Type::Any(AnyCause::FromError)),
                    modifies_ancestors: true,
                    deleted: true,
                    widens: true,
                },
            )
        })
    }

    pub fn flow_analysis_for_del_target(&self, target: Target) {
        match target {
            Target::Name(name_def) => {
                if let Some(first_index) =
                    first_defined_name_of_multi_def(self.file, name_def.name_index())
                {
                    self.infer_name_target(name_def, true);
                } else {
                    self.add_issue(
                        name_def.index(),
                        IssueKind::NameError {
                            name: name_def.as_code().into(),
                        },
                    );
                }
                self.delete_name(name_def)
            }
            Target::NameExpression(primary_target, name_def) => {
                // TODO this should still be implemented
                //self.infer_single_target(target);
                let node_ref = NodeRef::new(self.file, name_def.index());
                // We do a normal lookup to check that the attribute is there.
                self.infer_primary_target_or_atom(primary_target.first())
                    .lookup(self.i_s, node_ref, name_def.as_code(), LookupKind::Normal);
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

    pub fn flow_analysis_for_try_stmt(
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
                fa.top_frame().unreachable = false;
            }
            if let Some(finally_block) = finally_block {
                self.calc_block_diagnostics(finally_block.block(), class, func)
            }
            if old_unreachable {
                fa.top_frame().unreachable = old_unreachable;
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
            let mut try_frame_for_except = Frame::default();
            let mut try_frame = None;
            let mut after_ok = Frame::new_unreachable();
            let mut after_exception = Frame::new_unreachable();
            let mut nth_except_body = 0;
            for b in try_stmt.iter_blocks() {
                let mut check_block = |except_expr: Option<ExceptExpression>, block, is_star| {
                    let mut name_def = None;
                    let except_type = if let Some(except_expr) = except_expr {
                        let expr;
                        (expr, name_def) = except_expr.unpack();
                        let inf = self.infer_expression(expr);
                        let inf_t = inf.as_cow_type(self.i_s);
                        if let Some(name_def) = name_def {
                            let instantiated = match is_star {
                                false => instantiate_except(self.i_s, &inf_t),
                                true => instantiate_except_star(self.i_s, &inf_t),
                            };
                            let name_index = name_def.name_index();
                            let first = first_defined_name(self.file, name_index);
                            if first == name_index {
                                Inferred::from_type(instantiated).maybe_save_redirect(
                                    self.i_s,
                                    self.file,
                                    name_def.index(),
                                    false,
                                );
                            } else {
                                self.assign_type_for_node_index(
                                    PointLink::new(self.file_index, first),
                                    instantiated,
                                    false,
                                )
                            }
                        }
                        Some(except_type(self.i_s, &inf_t, true))
                    } else {
                        None
                    };
                    nth_except_body += 1;
                    let mut exception_frame = if nth_except_body == except_bodies {
                        std::mem::take(&mut try_frame_for_except)
                    } else {
                        try_frame_for_except.clone()
                    };
                    exception_frame = fa.with_frame(exception_frame, || {
                        self.calc_block_diagnostics(block, class, func)
                    });
                    let new_after = std::mem::take(&mut after_exception);
                    after_exception = fa.merge_or(self.i_s, exception_frame, new_after, false);
                    if let Some(name_def) = name_def {
                        self.delete_name(name_def)
                    }
                    except_type
                };
                match b {
                    TryBlockType::Try(block) => {
                        try_frame_for_except = fa.with_new_try_frame(|| {
                            try_frame = Some(fa.with_frame(Frame::default(), || {
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
                            Frame::default()
                        };
                        fa.with_frame(try_frame, || {
                            let new_after = std::mem::take(&mut after_ok);
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
                    TryBlockType::Finally(b) => (),
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
            let try_frame_for_except = fa.with_new_try_frame(|| {
                // Create a new frame that is then thrown away. This makes sense if we consider
                // that the end of the with statement might never be reached.
                fa.with_new_frame_and_return_unreachable(|| callable());
            });
            fa.overwrite_entries(self.i_s.db, try_frame_for_except.entries);
        })
    }

    pub fn flow_analysis_for_lambda_body(
        &self,
        expr: Expression,
        result_context: &mut ResultContext,
    ) -> Inferred {
        FLOW_ANALYSIS.with(|fa| {
            fa.with_frame_and_result(Frame::default(), || {
                self.infer_expression_without_cache(expr, result_context)
            })
            .1
        })
    }

    fn check_conjunction(
        &self,
        and: Conjunction,
    ) -> (Inferred, FramesWithParentUnions, FramesWithParentUnions) {
        let (left, right) = and.unpack();
        match is_expr_part_reachable_for_name_binder(self.flags(), left) {
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
        let had_first_left_entry = !left_frames.falsey.entries.is_empty();
        if left_frames.truthy.unreachable {
            if self.flags().warn_unreachable {
                self.add_issue(
                    and.index(),
                    IssueKind::RightOperandIsNeverOperated { right: "and" },
                )
            }
        } else {
            left_frames.truthy = FLOW_ANALYSIS.with(|fa| {
                fa.with_frame(left_frames.truthy, || {
                    right_infos = Some(self.find_guards_in_expression_parts(right));
                })
            });
        }
        let (inf, right_frames) = if let Some((right_inf, right_frames)) = right_infos {
            let left_t = left_inf.as_cow_type(self.i_s);
            (
                Inferred::from_type(
                    split_truthy_and_falsey(self.i_s, &left_t)
                        .map(|(_, falsey)| falsey)
                        .unwrap_or_else(|| left_t.into_owned()),
                )
                .simplified_union(self.i_s, right_inf),
                right_frames,
            )
        } else {
            (left_inf, FramesWithParentUnions::default())
        };
        (inf, left_frames, right_frames)
    }

    pub fn flow_analysis_for_disjunction(&self, or: Disjunction) -> Inferred {
        self.check_disjunction(or).0
    }

    fn check_disjunction(
        &self,
        or: Disjunction,
    ) -> (Inferred, FramesWithParentUnions, FramesWithParentUnions) {
        let (left, right) = or.unpack();
        match is_expr_part_reachable_for_name_binder(self.flags(), left) {
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

        let (left_inf, mut left_frames) = self.find_guards_in_expression_parts(left);
        let mut right_infos = None;
        if left_frames.falsey.unreachable {
            if self.flags().warn_unreachable {
                self.add_issue(
                    or.index(),
                    IssueKind::RightOperandIsNeverOperated { right: "or" },
                )
            }
        } else {
            left_frames.falsey = FLOW_ANALYSIS.with(|fa| {
                fa.with_frame(left_frames.falsey, || {
                    right_infos = Some(self.find_guards_in_expression_parts(right));
                })
            });
        }

        let (inf, right_frames) = if let Some((right_inf, right_frames)) = right_infos {
            let left_t = left_inf.as_cow_type(self.i_s);
            (
                Inferred::from_type(
                    split_truthy_and_falsey(self.i_s, &left_t)
                        .map(|(truthy, _)| truthy)
                        .unwrap_or_else(|| left_t.into_owned()),
                )
                .simplified_union(self.i_s, right_inf),
                right_frames,
            )
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

        let child_t = child_entry.type_.as_ref()?;
        let mut matching_entries = vec![];
        for union_entry in base_union.entries.iter() {
            let (inf, had_error) = replay(&union_entry.type_);
            if had_error {
                return None;
            }
            if inf
                .as_cow_type(self.i_s)
                .simple_overlaps(self.i_s, &child_t)
            {
                matching_entries.push(union_entry.clone());
            }
        }
        (base_union.entries.len() != matching_entries.len())
            .then(|| Type::from_union_entries(matching_entries))
    }

    fn propagate_parent_unions(&self, frame: &mut Frame, parent_unions: &[(FlowKey, UnionType)]) {
        for (key, parent_union) in parent_unions.iter().rev() {
            for entry in &frame.entries {
                let (FlowKey::Member(base_key, _) | FlowKey::Index { base_key, .. }) = &entry.key
                else {
                    continue;
                };
                if key.equals(self.i_s.db, base_key) {
                    if let Some(type_) = self.maybe_propagate_parent_union(parent_union, entry) {
                        frame.add_entry(self.i_s, Entry::new(key.clone(), type_));
                        break;
                    }
                }
            }
        }
    }

    fn find_guards_in_named_expr(&self, named_expr: NamedExpression) -> (Inferred, Frame, Frame) {
        match named_expr.unpack() {
            NamedExpressionContent::Expression(expr) => self.find_guards_in_expr(expr),
            NamedExpressionContent::Walrus(walrus) => {
                let (name_def, expr) = walrus.unpack();
                let (inf, mut truthy, mut falsey) =
                    if let Some(inf) = self.infer_name_target(name_def, false) {
                        self.find_guards_in_expr_with_context(
                            expr,
                            &mut ResultContext::Known(&inf.as_cow_type(self.i_s)),
                        )
                    } else {
                        self.find_guards_in_expr(expr)
                    };
                FLOW_ANALYSIS.with(|fa| {
                    let (walrus_frame, inf) = fa.with_frame_and_result(Frame::default(), || {
                        self.save_walrus(name_def, inf)
                    });
                    if let Some((walrus_truthy, walrus_falsey)) =
                        split_truthy_and_falsey(self.i_s, &inf.as_cow_type(self.i_s))
                    {
                        debug!(
                            "Narrowed {} to true: {} and false: {}",
                            named_expr.as_code(),
                            walrus_truthy.format_short(self.i_s.db),
                            walrus_falsey.format_short(self.i_s.db)
                        );
                        let key = self.key_from_name_def(name_def);
                        truthy.add_entry_from_type(self.i_s, key.clone(), walrus_truthy);
                        falsey.add_entry_from_type(self.i_s, key, walrus_falsey);
                    }
                    for entry in walrus_frame.entries {
                        truthy.overwrite_entry(self.i_s.db, entry.clone());
                        falsey.overwrite_entry(self.i_s.db, entry);
                    }
                    (inf, truthy, falsey)
                })
            }
        }
    }

    fn find_guards_in_expr(&self, expr: Expression) -> (Inferred, Frame, Frame) {
        self.find_guards_in_expr_with_context(expr, &mut ResultContext::Unknown)
    }

    fn find_guards_in_expr_with_context(
        &self,
        expr: Expression,
        result_context: &mut ResultContext,
    ) -> (Inferred, Frame, Frame) {
        match expr.unpack() {
            ExpressionContent::ExpressionPart(part) => {
                self.find_guards_in_expr_part(part, result_context)
            }
            _ => (
                self.infer_expression(expr),
                Frame::default(),
                Frame::default(),
            ),
        }
    }

    fn find_guards_in_expr_part(
        &self,
        part: ExpressionPart,
        result_context: &mut ResultContext,
    ) -> (Inferred, Frame, Frame) {
        let (inf, mut result) =
            self.find_guards_in_expression_parts_with_context(part, result_context);
        self.propagate_parent_unions(&mut result.truthy, &result.parent_unions);
        self.propagate_parent_unions(&mut result.falsey, &result.parent_unions);
        (inf, result.truthy, result.falsey)
    }

    fn find_guards_in_expression_parts(
        &self,
        part: ExpressionPart,
    ) -> (Inferred, FramesWithParentUnions) {
        self.find_guards_in_expression_parts_with_context(part, &mut ResultContext::Unknown)
    }

    fn find_guards_in_expression_parts_with_context(
        &self,
        part: ExpressionPart,
        result_context: &mut ResultContext,
    ) -> (Inferred, FramesWithParentUnions) {
        self.find_guards_in_expression_parts_inner(part, result_context)
            .unwrap_or_else(|inf| {
                if let Some((truthy, falsey)) =
                    split_truthy_and_falsey(self.i_s, &inf.as_cow_type(self.i_s))
                {
                    let frames = FramesWithParentUnions {
                        truthy: Frame::from_type_without_entry(truthy),
                        falsey: Frame::from_type_without_entry(falsey),
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
    ) -> Result<(Inferred, FramesWithParentUnions), Inferred> {
        let narrow_from_key = |key: Option<FlowKey>, inf: Inferred, parent_unions| {
            if let Some(key) = key {
                if let Some((truthy, falsey)) =
                    split_truthy_and_falsey(self.i_s, &inf.as_cow_type(self.i_s))
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
            }
            Err(inf)
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
                    return Ok((Inferred::new_bool(self.i_s.db), frames));
                }
                return Ok((
                    Inferred::new_bool(self.i_s.db),
                    FramesWithParentUnions::default(),
                ));
            }
            ExpressionPart::Conjunction(and) => {
                let (inf, left, right) = self.check_conjunction(and);

                return FLOW_ANALYSIS
                    .with(|fa| Ok((inf, fa.merge_conjunction(self.i_s, Some(left), right))));
            }
            ExpressionPart::Disjunction(or) => {
                let (inf, left_frames, right_frames) = self.check_disjunction(or);
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
                let (inf, mut frames) = self.find_guards_in_expression_parts(inv.expression());
                (frames.truthy, frames.falsey) = (frames.falsey, frames.truthy);
                return Ok((inf, frames));
            }
            ExpressionPart::Primary(primary) => match primary.second() {
                PrimaryContent::Execution(arg_details @ ArgumentsDetails::Node(args)) => {
                    let first = self.infer_primary_or_atom(primary.first());
                    match first.maybe_saved_specific(self.i_s.db) {
                        Some(Specific::BuiltinsIsinstance) => {
                            if let Some(frames) =
                                self.find_isinstance_or_issubclass_frames(args, false)
                            {
                                return Ok((Inferred::new_bool(self.i_s.db), frames));
                            }
                        }
                        Some(Specific::BuiltinsIssubclass) => {
                            if let Some(frames) =
                                self.find_isinstance_or_issubclass_frames(args, true)
                            {
                                return Ok((Inferred::new_bool(self.i_s.db), frames));
                            }
                        }
                        _ => {
                            if let Some(saved) = first.maybe_saved_link() {
                                if saved == self.i_s.db.python_state.callable_node_ref().as_link() {
                                    if let Some(frames) = self.guard_callable(args) {
                                        return Ok((Inferred::new_bool(self.i_s.db), frames));
                                    }
                                } else if saved
                                    == self.i_s.db.python_state.hasattr_node_ref().as_link()
                                {
                                    if let Some(frames) = self.guard_hasattr(args) {
                                        return Ok((Inferred::new_bool(self.i_s.db), frames));
                                    }
                                }
                            }
                            if let Some(c) = first.maybe_type_guard_callable(self.i_s) {
                                if let Some(frames) = self.guard_type_guard(arg_details, args, c) {
                                    return Ok((Inferred::new_bool(self.i_s.db), frames));
                                }
                            }
                        }
                    }
                }
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
                    ComparisonContent::In(left, op, _) | ComparisonContent::NotIn(left, op, _) => {
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
        let key = input.key?;
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
            debug!("The isinstance type is Any and there is therefore no narrowing");
            return Some(FramesWithParentUnions {
                truthy: Frame::from_type(key, isinstance_type),
                falsey: Frame::default(),
                parent_unions: vec![],
            });
        }
        if issubclass && !matches!(isinstance_type, Type::Never(_)) {
            isinstance_type = Type::Type(Rc::new(isinstance_type))
        }

        split_and_intersect(
            self.i_s,
            &input.inf.as_cow_type(self.i_s),
            key,
            input.parent_unions,
            &isinstance_type,
            |issue| {
                if self.flags().warn_unreachable {
                    self.add_issue(args.index(), issue)
                }
            },
        )
    }

    pub fn check_isinstance_or_issubclass_type(
        &self,
        arg: NamedExpression,
        issubclass: bool,
    ) -> Option<Type> {
        let isinstance_type = self.isinstance_or_issubclass_type(arg, issubclass)?;
        for t in isinstance_type.iter_with_unpacked_unions(self.i_s.db) {
            let cannot_use_with = |with| {
                self.add_issue(
                    arg.index(),
                    IssueKind::CannotUseIsinstanceWith {
                        func: match issubclass {
                            false => "isinstance",
                            true => "issubclass",
                        },
                        with,
                    },
                )
            };
            match t {
                Type::TypedDict(_) => cannot_use_with("TypedDict"),
                Type::NewType(_) => cannot_use_with("NewType"),
                _ => (),
            }
            if let Some(cls) = t.maybe_class(self.i_s.db) {
                let class_infos = cls.use_cached_class_infos(self.i_s.db);
                if matches!(class_infos.class_kind, ClassKind::Protocol) {
                    if !class_infos.is_runtime_checkable {
                        self.add_issue(arg.index(), IssueKind::ProtocolNotRuntimeCheckable)
                    }
                    if issubclass {
                        let non_method_protocol_members =
                            cls.non_method_protocol_members(self.i_s.db);
                        if !non_method_protocol_members.is_empty() {
                            self.add_issue(
                                arg.index(),
                                IssueKind::IssubcclassWithProtocolNonMethodMembers {
                                    protocol: cls.name().into(),
                                    non_method_members: join_with_commas(
                                        non_method_protocol_members.into_iter(),
                                    )
                                    .into(),
                                },
                            )
                        }
                    }
                }
            }
        }
        Some(isinstance_type)
    }

    fn isinstance_or_issubclass_type(
        &self,
        arg: NamedExpression,
        issubclass: bool,
    ) -> Option<Type> {
        let expr = match arg.unpack() {
            NamedExpressionContent::Expression(expr) => expr,
            NamedExpressionContent::Walrus(_) => todo!(),
        };

        // One might think that we could just use type computation here for isinstance types. This
        // is however not really working, because the types can also be inferred like
        //
        //     isinstance(foo, type(bar))

        match expr.unpack() {
            ExpressionContent::ExpressionPart(part) => {
                self.isinstance_or_issubclass_type_for_expr_part(part, issubclass)
            }
            _ => None,
        }
    }

    fn isinstance_or_issubclass_type_for_expr_part(
        &self,
        part: ExpressionPart,
        issubclass: bool,
    ) -> Option<Type> {
        let cannot_use_with = |with| {
            self.add_issue(
                part.index(),
                IssueKind::CannotUseIsinstanceWith {
                    func: match issubclass {
                        false => "isinstance",
                        true => "issubclass",
                    },
                    with,
                },
            );
            Some(Type::Any(AnyCause::FromError))
        };
        match part {
            ExpressionPart::BitwiseOr(disjunction) => {
                let (first, second) = disjunction.unpack();
                let t1 = self.isinstance_or_issubclass_type_for_expr_part(first, issubclass)?;
                let t2 = self.isinstance_or_issubclass_type_for_expr_part(second, issubclass)?;
                Some(t1.union(t2))
            }
            _ => {
                let inf = self.infer_expression_part(part);
                match inf.maybe_saved_specific(self.i_s.db) {
                    Some(Specific::TypingAny) => {
                        return cannot_use_with("Any");
                    }
                    Some(Specific::TypingType) => {
                        if issubclass {
                            todo!()
                        } else {
                            return Some(inf.as_type(self.i_s));
                        }
                    }
                    _ => (),
                }

                self.process_isinstance_type(part, &inf.as_cow_type(self.i_s))
            }
        }
    }

    fn process_isinstance_type(&self, part: ExpressionPart, t: &Type) -> Option<Type> {
        match t {
            Type::Tuple(tup) => match &tup.args {
                TupleArgs::FixedLen(ts) => {
                    let ts: Option<Vec<Type>> = ts
                        .iter()
                        .map(|t| self.process_isinstance_type(part, t))
                        .collect();
                    let ts = ts?;
                    Some(match ts.len() {
                        0 => Type::Never(NeverCause::Other),
                        1 => ts.into_iter().next().unwrap(),
                        _ => simplified_union_from_iterators(self.i_s, ts.iter()),
                    })
                }
                TupleArgs::ArbitraryLen(t) => self.process_isinstance_type(part, t),
                TupleArgs::WithUnpack(_) => todo!(),
            },
            Type::Type(t) => {
                if let Type::Class(cls) = t.as_ref() {
                    if !matches!(
                        &cls.generics,
                        ClassGenerics::NotDefinedYet | ClassGenerics::None
                    ) {
                        self.add_issue(
                            part.index(),
                            IssueKind::CannotUseIsinstanceWithParametrizedGenerics,
                        );
                        return Some(Type::Any(AnyCause::FromError));
                    }
                }
                Some((**t).clone())
            }
            Type::Any(cause) => Some(Type::Any(*cause)),
            /*
            Type::Literal(l) => {
                cannot_use_with(self, "Literal")
            }
            */
            _ => None,
        }
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
            Type::Never(_) => Frame::default(),
            _ => Frame::from_type(key.clone(), falsey_parent),
        };
        Some(FramesWithParentUnions {
            truthy: Frame::from_type(FlowKey::Member(Rc::new(key), attr), attr_t),
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
                            add_t(&Type::Type(Rc::new(inner.clone())));
                        }
                    }
                    _ => add_t(t),
                },
                _ => add_t(t),
            }
        }
        let falsey = if matches!(callable_t, Type::Never(_)) {
            callable_t = Type::Intersection(Intersection::new(Rc::new([
                Type::Callable(self.i_s.db.python_state.any_callable_from_error.clone()),
                input_t.into_owned(),
            ])));
            Frame::default()
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
        args_details: ArgumentsDetails,
        args: Arguments,
        might_have_guard: CallableLike,
    ) -> Option<FramesWithParentUnions> {
        match &might_have_guard {
            CallableLike::Callable(c) => {
                self.check_type_guard_callable(args_details, args, c, false)
            }
            CallableLike::Overload(o) => {
                for c in o.iter_functions() {
                    if let y @ Some(_) = self.check_type_guard_callable(args_details, args, c, true)
                    {
                        return y;
                    }
                }
                None
            }
        }
    }

    fn check_type_guard_callable(
        &self,
        args_details: ArgumentsDetails,
        args: Arguments,
        callable: &CallableContent,
        from_overload: bool,
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

        let had_error = Cell::new(false);
        let resolved_guard_t = Callable::new(callable, self.i_s.current_class().copied())
            .execute_for_custom_return_type(
                self.i_s,
                &SimpleArgs::new(*self.i_s, self.file, args.index(), args_details),
                false,
                &guard.type_,
                OnTypeError::new(&|i_s, error_text, arg, types| {
                    if from_overload {
                        had_error.set(true)
                    } else {
                        on_argument_type_error(i_s, error_text, arg, types)
                    }
                }),
                &mut ResultContext::Unknown,
                None,
            );
        if had_error.get() {
            return None;
        }
        let resolved_guard_t = resolved_guard_t.as_cow_type(self.i_s);
        if guard.from_type_is {
            split_and_intersect(
                self.i_s,
                &infos.inf.as_cow_type(self.i_s),
                key,
                infos.parent_unions,
                &resolved_guard_t,
                |issue| {
                    if self.flags().warn_unreachable {
                        self.add_issue(args.index(), issue)
                    }
                },
            )
        } else {
            Some(FramesWithParentUnions {
                truthy: Frame::from_type(key, resolved_guard_t.into_owned()),
                falsey: Frame::default(),
                parent_unions: infos.parent_unions,
            })
        }
    }

    fn guard_of_in_operator(
        &self,
        op: Operand,
        left: &mut ComparisonPartInfos,
        right: &ComparisonPartInfos,
    ) -> Option<FramesWithParentUnions> {
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
        if let Some(item) = stdlib_container_item(db, &right.inf.as_cow_type(self.i_s)) {
            if !item.iter_with_unpacked_unions(db).any(|t| t == &Type::None) {
                if let Some(ComparisonKey::Normal(left_key)) = &left.key {
                    let left_t = left.inf.as_cow_type(self.i_s);
                    if left_t.simple_overlaps(self.i_s, &item) {
                        if let Some(t) = removed_optional(db, &left_t) {
                            return maybe_invert(
                                Frame::from_type(left_key.clone(), t),
                                Frame::default(),
                                left.parent_unions.take(),
                            );
                        }
                    }
                }
            }
        }
        // The right side can currently only be narrowed with TypedDicts
        let right_t = right.inf.as_cow_type(self.i_s);
        if right_t
            .iter_with_unpacked_unions(db)
            .any(|t| matches!(t, Type::TypedDict(_)))
        {
            if let Some(ComparisonKey::Normal(right_key)) = &right.key {
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
                                if let Some(m) = td
                                    .members(db)
                                    .iter()
                                    .find(|m| m.name.as_str(db) == *str_literal)
                                {
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
        }
        None
    }

    fn key_from_name_def(&self, name_def: NameDefinition) -> FlowKey {
        let name_index = name_def.name_index();
        FlowKey::Name(PointLink::new(
            self.file_index,
            first_defined_name(self.file, name_index),
        ))
    }

    fn key_from_atom(&self, atom: Atom) -> Option<FlowKey> {
        match atom.unpack() {
            AtomContent::Name(name) => {
                return Some(FlowKey::Name(name_definition_link(
                    self.i_s.db,
                    self.file,
                    name,
                )?))
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
                self.infer_primary(primary, &mut ResultContext::Unknown),
                None,
            );
        }

        let mut base = match primary.first() {
            PrimaryOrAtom::Primary(primary) => self.key_from_primary(primary),
            PrimaryOrAtom::Atom(atom) => KeyWithParentUnions::new(
                self.infer_atom(atom, &mut ResultContext::Unknown),
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
            &mut ResultContext::Unknown,
        );
        match second {
            PrimaryContent::Attribute(attr) => {
                if let Some(base_key) = &old_base_key {
                    base.key = Some(FlowKey::Member(
                        Rc::new(base_key.clone()),
                        DbString::StringSlice(StringSlice::from_name(self.file_index, attr)),
                    ));
                }
            }
            PrimaryContent::GetItem(slice_type) => {
                if let Some(index_key) = self.key_from_slice_type(slice_type) {
                    if let Some(base_key) = &old_base_key {
                        base.key = Some(FlowKey::Index {
                            base_key: Rc::new(base_key.clone()),
                            match_index: index_key,
                            node_index: slice_type.index(),
                        });
                    }
                }
            }
            PrimaryContent::Execution(_) => unreachable!(),
        }
        if let Some(base_key) = old_base_key {
            // Only in case of valid keys we want to add the unions.
            if base.key.is_some() {
                if let Some(union_type) = maybe_union() {
                    base.parent_unions.push((base_key.clone(), union_type))
                }
            }
        }
        base
    }

    fn key_from_expr_part(&self, expr_part: ExpressionPart) -> KeyWithParentUnions {
        match expr_part {
            ExpressionPart::Atom(atom) => KeyWithParentUnions::new(
                self.infer_atom(atom, &mut ResultContext::Unknown),
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

    fn key_from_primary_target(&self, primary_target: PrimaryTarget) -> Option<FlowKey> {
        let base_key = match primary_target.first() {
            PrimaryTargetOrAtom::PrimaryTarget(t) => self.key_from_primary_target(t),
            PrimaryTargetOrAtom::Atom(atom) => self.key_from_atom(atom),
        }?;
        match primary_target.second() {
            PrimaryContent::Attribute(n) => Some(FlowKey::Member(
                Rc::new(base_key),
                DbString::StringSlice(StringSlice::from_name(self.file_index, n)),
            )),
            PrimaryContent::Execution(_) => None,
            PrimaryContent::GetItem(slice_type) => {
                //self.key_from_slice_type(slice_type).map(|match_index| FlowKey::Index { base_key: Rc::new(base_key), node_index: slice_type.index(), match_index })
                None
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
                        return Some((
                            entry.key.clone(),
                            Inferred::from_type(entry.type_.clone()?),
                        ));
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
        if let PrimaryOrAtom::Primary(earlier) = first {
            if self.matches_ancestor(earlier, key) {
                return true;
            }
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
                name_definition_link(self.i_s.db, self.file, name) == Some(*check_link)
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
            if pre_exec.maybe_saved_specific(db) == Some(Specific::TypingType) {
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
            self.file_index,
            attr,
            LookupKind::Normal,
            &mut ResultContext::Unknown,
            &|_| todo!(),
            &|_| (), // OnLookupError is irrelevant for us here.
        )
    }
}

fn name_definition_link(db: &Database, file: &PythonFile, name: Name) -> Option<PointLink> {
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

#[derive(Default)]
struct FramesWithParentUnions {
    truthy: Frame,
    falsey: Frame,
    parent_unions: ParentUnions,
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
                    let generics = class.generics();
                    let Some(Generic::TypeArg(item)) = generics.iter(db).next() else {
                        unreachable!()
                    };
                    item.into_owned()
                } else {
                    return None;
                }
            }
        }
        Type::Tuple(tup) => tup.fallback_type(db).clone(),
        Type::NamedTuple(named_tup) => {
            return stdlib_container_item(db, &Type::Tuple(named_tup.as_tuple()))
        }
        Type::TypedDict(td) => db.python_state.str_type(),
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
            // Narrow Foo in `Foo is None`
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
                let mut truthy = (**base_truthy).clone();
                if matches!(base_truthy.as_ref(), Type::Any(_)) {
                    // Narrowing to Any has no value and will only worsen type information.
                    return None;
                }
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
                        false => Frame::default(),
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
    {
        if let Ok(n) = (*n).try_into() {
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
                            if let Some(nt) = c.class(i_s.db).maybe_named_tuple_base(i_s.db) {
                                if matches_fixed_len_namedtuple_len(&nt, n, kind) == negative {
                                    continue;
                                }
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
                                after: Rc::new([]),
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
            if (lower_than.unwrap_or(n) <= min_len) && invert == negative {
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
    key: FlowKey,
    parent_unions: ParentUnions,
    isinstance_type: &Type,
    mut add_issue: impl Fn(IssueKind),
) -> Option<FramesWithParentUnions> {
    // Please listen to "Red Hot Chili Peppers - Otherside" here.
    let mut true_type = Type::Never(NeverCause::Other);
    let mut other_side = Type::Never(NeverCause::Other);
    let matcher = &mut Matcher::with_ignored_promotions();
    for t in original_t.iter_with_unpacked_unions(i_s.db) {
        let mut split = |t: &Type| {
            let mut matched = false;
            let mut matched_with_any = true;
            let mut had_any = None;
            for (i, isinstance_t) in isinstance_type
                .iter_with_unpacked_unions(i_s.db)
                .enumerate()
            {
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
                    Match::False { .. } => (),
                }
            }
            if matched {
                if matched_with_any {
                    true_type.simplified_union_in_place(i_s, isinstance_type);
                } else {
                    true_type.union_in_place(t.clone());
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
                        split(&Type::Type(Rc::new(inner.clone())))
                    }
                }
                _ => split(t),
            },
            Type::Any(_) => {
                true_type = isinstance_type.clone();
                other_side.union_in_place(t.clone())
            }
            _ => split(t),
        }
    }
    if matches!(true_type, Type::Never(_)) {
        if original_t.overlaps(i_s, matcher, isinstance_type) {
            true_type = isinstance_type.clone();
        } else {
            for t in original_t.iter_with_unpacked_unions(i_s.db) {
                if isinstance_type.is_simple_sub_type_of(i_s, t).bool() {
                    true_type.simplified_union_in_place(i_s, isinstance_type);
                } else if isinstance_type.is_simple_super_type_of(i_s, t).bool() {
                    true_type.simplified_union_in_place(i_s, t);
                } else {
                    match Intersection::new_instance_intersection(
                        i_s,
                        t,
                        isinstance_type,
                        &mut add_issue,
                    ) {
                        Ok(new_t) => true_type.simplified_union_in_place(i_s, &new_t),
                        Err(()) => (),
                    }
                }
            }
        }
    }
    debug!(
        "Narrowed because of isinstance or TypeIs to {} and other side to {}",
        true_type.format_short(i_s.db),
        other_side.format_short(i_s.db)
    );
    Some(FramesWithParentUnions {
        truthy: Frame::from_type(key.clone(), true_type),
        falsey: Frame::from_type(key, other_side),
        parent_unions,
    })
}

enum ExceptType {
    ContainsOnlyBaseExceptions,
    HasExceptionGroup,
    Invalid,
}

fn except_type(i_s: &InferenceState, t: &Type, allow_tuple: bool) -> ExceptType {
    match t {
        Type::Type(t) => {
            let db = i_s.db;
            if let Some(cls) = t.maybe_class(i_s.db) {
                if cls.is_base_exception_group(i_s.db) {
                    return ExceptType::HasExceptionGroup;
                } else if cls.is_base_exception(i_s.db) {
                    return ExceptType::ContainsOnlyBaseExceptions;
                }
            }
            ExceptType::Invalid
        }
        Type::Any(_) => ExceptType::ContainsOnlyBaseExceptions,
        Type::Tuple(content) if allow_tuple => match &content.args {
            TupleArgs::FixedLen(ts) => {
                let mut result = ExceptType::ContainsOnlyBaseExceptions;
                for t in ts.iter() {
                    match except_type(i_s, t, false) {
                        ExceptType::ContainsOnlyBaseExceptions => (),
                        x @ ExceptType::HasExceptionGroup => result = x,
                        ExceptType::Invalid => return ExceptType::Invalid,
                    }
                }
                result
            }
            TupleArgs::ArbitraryLen(t) => except_type(i_s, t, false),
            TupleArgs::WithUnpack(_) => todo!(),
        },
        Type::Union(union) => {
            let mut result = ExceptType::ContainsOnlyBaseExceptions;
            for t in union.iter() {
                match except_type(i_s, t, allow_tuple) {
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
