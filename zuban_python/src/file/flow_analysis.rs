use std::{cell::RefCell, rc::Rc};

use parsa_python_ast::{
    Argument, Arguments, ArgumentsDetails, Atom, AtomContent, ComparisonContent, Expression,
    ExpressionContent, ExpressionPart, IfBlockIterator, IfBlockType, IfStmt, Name, NamedExpression,
    NamedExpressionContent, NodeIndex, Operand, Primary, PrimaryContent, PrimaryOrAtom,
    SliceType as ASTSliceType,
};

use crate::{
    database::{Database, PointLink, PointType, Specific},
    debug,
    diagnostics::{Issue, IssueType},
    getitem::SliceType,
    inference_state::InferenceState,
    inferred::Inferred,
    matching::{Generic, LookupKind, Match, Matcher, ResultContext},
    node_ref::NodeRef,
    type_::{
        AnyCause, ClassGenerics, EnumMember, GenericItem, Literal, LiteralKind, TupleArgs, Type,
        TypeVarKind, UnionType,
    },
    type_helpers::{Class, Function},
};

use super::{first_defined_name, inference::Inference, PythonFile};

type Entries = Vec<Entry>;

thread_local! {
    pub static FLOW_ANALYSIS: FlowAnalysis = FlowAnalysis::default();
}

#[derive(Debug, Clone)]
enum FlowKey {
    Name(PointLink),
    Member(Rc<FlowKey>, *const str),
    Index {
        base_key: Rc<FlowKey>,
        node_index: NodeIndex,
        match_index: FlowKeyIndex,
    },
}

#[derive(Debug, Clone, PartialEq)]
enum FlowKeyIndex {
    Int(usize),
    Str(String),
}

impl PartialEq for FlowKey {
    fn eq(&self, other: &Self) -> bool {
        match self {
            Self::Name(link1) => matches!(other, Self::Name(link2) if link1 == link2),
            Self::Member(key1, s1) => match other {
                Self::Member(key2, s2) => key1 == key2 && unsafe { &**s1 as &str == &**s1 as &str },
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
                } => key1 == key2 && match_index1 == match_index2,
                _ => false,
            },
        }
    }
}

#[derive(Debug)]
struct Entry {
    key: FlowKey,
    type_: Type,
    from_assignment: bool,
}

#[derive(Debug, Default)]
struct Frame {
    entries: Entries,
    unreachable: bool,
}

impl Frame {
    fn new(entries: Entries) -> Self {
        Self {
            entries,
            unreachable: false,
        }
    }

    fn new_unreachable() -> Self {
        Self {
            entries: Default::default(),
            unreachable: true,
        }
    }

    fn add_entry(&mut self, i_s: &InferenceState, entry: Entry) {
        for old_entry in &mut self.entries {
            if old_entry.key == entry.key {
                if let Some(new) = old_entry.type_.common_sub_type(i_s, &entry.type_) {
                    old_entry.type_ = new;
                }
                return;
            }
        }
        self.entries.push(entry)
    }

    fn from_type_without_entry(t: Type) -> Self {
        match t {
            Type::Never => Self::new_unreachable(),
            _ => Self::default(),
        }
    }

    fn from_type(key: FlowKey, type_: Type) -> Self {
        match type_ {
            Type::Never => Self::new_unreachable(),
            type_ => Self::new(vec![Entry {
                key,
                type_,
                from_assignment: false,
            }]),
        }
    }
}

#[derive(Debug, Default)]
pub struct FlowAnalysis {
    frames: RefCell<Vec<Frame>>,
}

impl FlowAnalysis {
    pub fn narrow_name(&self, name_link: PointLink) -> Option<Inferred> {
        for frame in self.frames.borrow().iter().rev() {
            for entry in &frame.entries {
                if entry.key == FlowKey::Name(name_link) {
                    return Some(Inferred::from_type(entry.type_.clone()));
                }
            }
        }
        None
    }

    fn is_unreachable(&self) -> bool {
        self.frames.borrow().last().unwrap().unreachable
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
                self.overwrite_entries(false_frame.entries)
            } else if !true_frame.unreachable {
                self.overwrite_entries(true_frame.entries)
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
        for first_entry in &first_frame.entries {
            if first_entry.from_assignment {
                for other_entry in &mut other_frame.entries {
                    if first_entry.key == other_entry.key {
                        // Assign false to make sure it is not handled again from the other side.
                        other_entry.from_assignment = false;
                        self.overwrite_entry(Entry {
                            key: first_entry.key.clone(),
                            type_: other_entry.type_.simplified_union(i_s, &first_entry.type_),
                            from_assignment: true,
                        })
                    }
                }
            }
        }
    }

    fn overwrite_entry(&self, new_entry: Entry) {
        let mut frames = self.frames.borrow_mut();
        let entries = &mut frames.last_mut().unwrap().entries;
        for entry in &mut *entries {
            if entry.key == new_entry.key {
                *entry = new_entry;
                return;
            }
        }
        entries.push(new_entry)
    }

    fn overwrite_entries(&self, new_entries: Entries) {
        let mut frames = self.frames.borrow_mut();
        let entries = &mut frames.last_mut().unwrap().entries;
        'outer: for new_entry in new_entries {
            for entry in &mut *entries {
                if entry.key == new_entry.key {
                    *entry = new_entry;
                    break 'outer;
                }
            }
            entries.push(new_entry)
        }
    }

    fn overwrite_frame(&self, new_frame: Frame) {
        self.overwrite_entries(new_frame.entries);
        self.frames.borrow_mut().last_mut().unwrap().unreachable |= new_frame.unreachable;
    }

    pub fn with_new_frame(&self, callable: impl FnOnce()) {
        self.frames.borrow_mut().push(Frame::default());
        callable();
        self.frames.borrow_mut().pop().unwrap();
    }

    fn with_frame(&self, db: &Database, frame: Frame, callable: impl FnOnce()) -> Frame {
        if db.project.flags.mypy_compatible && frame.unreachable {
            // Mypy does not analyze frames that are not reachable. However for normal interaction
            // in an IDE yuo typically want to analyze those parts of code, even if they are
            // unreachable.
            return frame;
        }
        self.frames.borrow_mut().push(frame);
        callable();
        self.frames.borrow_mut().pop().unwrap()
    }

    pub fn mark_current_frame_unreachable(&self) {
        self.frames.borrow_mut().last_mut().unwrap().unreachable = true
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
            if &x_entry.key == &y_entry.key {
                if let Some(t) = x_entry.type_.common_sub_type(i_s, &y_entry.type_) {
                    x_entry.type_ = t
                } else {
                    x_entry.type_ = Type::Never;
                    x.unreachable = true;
                }
                continue 'outer;
            }
        }
        x.entries.push(y_entry)
    }
    x
}

fn merge_or(i_s: &InferenceState, x: Frame, y: Frame) -> Frame {
    if x.unreachable {
        return y;
    }
    if y.unreachable {
        return x;
    }
    let mut new_entries = vec![];
    for x_entry in x.entries {
        for y_entry in &y.entries {
            // Only when both sides narrow the same type we actually have learned anything about
            // the expression.
            if &x_entry.key == &y_entry.key {
                new_entries.push(Entry {
                    key: x_entry.key,
                    type_: x_entry.type_.simplified_union(i_s, &y_entry.type_),
                    from_assignment: x_entry.from_assignment || y_entry.from_assignment,
                })
            }
            break;
        }
    }
    Frame::new(new_entries)
}

fn merge_conjunction(
    i_s: &InferenceState,
    old: Option<FramesWithParentUnions>,
    new: FramesWithParentUnions,
) -> FramesWithParentUnions {
    if let Some(old) = old {
        let mut parent_unions = old.parent_unions;
        parent_unions.extend(new.parent_unions);
        FramesWithParentUnions {
            truthy: merge_and(i_s, old.truthy, new.truthy),
            falsey: merge_or(i_s, old.falsey, new.falsey),
            parent_unions,
        }
    } else {
        new
    }
}

fn has_explicit_literal(t: &Type) -> bool {
    t.iter_with_unpacked_unions().any(|t| match t {
        Type::Literal(literal) => !literal.implicit,
        Type::TypeVar(tv) => match &tv.type_var.kind {
            TypeVarKind::Bound(bound) => has_explicit_literal(bound),
            _ => false,
        },
        _ => false,
    })
}

fn has_custom_special_method(i_s: &InferenceState, t: &Type, method: &str) -> bool {
    t.iter_with_unpacked_unions().any(|t| {
        let cls = match t {
            Type::Class(c) => c.class(i_s.db),
            Type::Dataclass(dc) => dc.class(i_s.db),
            Type::Enum(enum_) => enum_.class(i_s.db),
            Type::EnumMember(member) => member.enum_.class(i_s.db),
            _ => return false,
        };
        let details = cls.lookup_without_descriptors_and_custom_add_issue(i_s, method, |_| ());
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
        Type::None => split_off == t,
        Type::EnumMember(member1) => match t {
            Type::EnumMember(member2) => member1.is_same_member(member2),
            _ => false,
        },
        _ => false,
    };
    let mut other_return = Type::Never;
    let mut left = Type::Never;
    let mut add = |t| left.union_in_place(t);
    for sub_t in t.iter_with_unpacked_unions() {
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
        let (rest, none) = split_off_singleton(i_s, &left_t, right_t, is_eq)?;
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
            if is_eq && (!literal1.implicit || has_explicit_literal(left_t))
                || !is_eq && matches!(literal1.kind, LiteralKind::Bool(_)) =>
        {
            let mut true_type = Type::Never;
            let mut false_type = Type::Never;
            let true_literal = || {
                let mut new_literal = literal1.clone();
                new_literal.implicit = false;
                Type::Literal(new_literal)
            };
            for sub_t in left_t.iter_with_unpacked_unions() {
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
            let result = (
                Frame::from_type(key.clone(), true_type),
                Frame::from_type(key, false_type),
            );
            Some(result)
        }
        _ => match left_t {
            left_t @ Type::Union(union) => {
                // Remove None from left, if the right types match everything except None.
                if left_t
                    .iter_with_unpacked_unions()
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

fn split_truthy_and_falsey(db: &Database, t: &Type) -> Option<(Type, Type)> {
    let split_truthy_and_falsey_single = |t: &Type| {
        let check = |condition| {
            if condition {
                Some((t.clone(), Type::Never))
            } else {
                Some((Type::Never, t.clone()))
            }
        };
        let falsey = || Some((Type::Never, t.clone()));
        match t {
            Type::None => Some((Type::Never, Type::None)),
            Type::Literal(literal) => match &literal.kind {
                LiteralKind::Bool(b) => check(*b),
                LiteralKind::Int(i) => check(*i != 0),
                LiteralKind::String(s) => todo!(),
                LiteralKind::Bytes(s) => todo!(),
            },
            Type::Class(c) => maybe_split_bool_from_literal(db, t, &LiteralKind::Bool(true)),
            _ => None,
        }
    };

    match t {
        Type::Union(union) => {
            let mut truthy = Type::Never;
            let mut falsey = Type::Never;
            let mut had_split = false;
            for t in union.iter() {
                let result = split_truthy_and_falsey(db, t);
                had_split |= result.is_some();
                let (new_true, new_false) = result.unwrap_or_else(|| (t.clone(), t.clone()));
                truthy.union_in_place(new_true);
                falsey.union_in_place(new_false);
            }
            had_split.then_some((truthy, falsey))
        }
        _ => split_truthy_and_falsey_single(t),
    }
}

impl Inference<'_, '_, '_> {
    pub fn is_unreachable(&self) -> bool {
        FLOW_ANALYSIS.with(|fa| fa.is_unreachable())
    }

    pub fn flow_analysis_for_assert(&mut self, expr: Expression) {
        let (true_frame, _) = self.find_guards_in_expr(expr);
        FLOW_ANALYSIS.with(|fa| fa.overwrite_frame(true_frame))
    }

    pub fn flow_analysis_for_target(&mut self, first_name_index: NodeIndex, t: &Type) {
        let key = FlowKey::Name(PointLink::new(self.file_index, first_name_index));
        FLOW_ANALYSIS.with(|fa| {
            fa.overwrite_entry(Entry {
                key,
                type_: t.clone(),
                from_assignment: true,
            })
        })
    }

    pub fn flow_analysis_for_if_stmt(
        &mut self,
        if_stmt: IfStmt,
        class: Option<Class>,
        func: Option<&Function>,
    ) {
        self.process_ifs(if_stmt.iter_blocks(), class, func)
    }

    fn process_ifs(
        &mut self,
        mut if_blocks: IfBlockIterator,
        class: Option<Class>,
        func: Option<&Function>,
    ) {
        match if_blocks.next() {
            Some(IfBlockType::If(if_expr, block)) => {
                let (true_frame, false_frame) = self.find_guards_in_named_expr(if_expr);

                let add_unreachable_error = |positions| {
                    if self.i_s.db.project.flags.warn_unreachable {
                        let (start_position, end_position) = positions;
                        self.file.add_issue(
                            self.i_s,
                            Issue {
                                type_: IssueType::UnreachableStatement,
                                start_position,
                                end_position,
                            },
                        )
                    }
                };
                if true_frame.unreachable {
                    add_unreachable_error(block.statements_start_and_end())
                }
                if false_frame.unreachable {
                    // If the if has no else or elif, nothing is "unreachable"
                    if let Some(start_and_end) = if_blocks.next_block_start_and_last_block_end() {
                        add_unreachable_error(start_and_end)
                    }
                }

                FLOW_ANALYSIS.with(|fa| {
                    let true_frame = fa.with_frame(self.i_s.db, true_frame, || {
                        self.calc_block_diagnostics(block, class, func)
                    });
                    let false_frame = fa.with_frame(self.i_s.db, false_frame, || {
                        self.process_ifs(if_blocks, class, func)
                    });

                    fa.merge_conditional(self.i_s, true_frame, false_frame);
                });
            }
            Some(IfBlockType::Else(block)) => self.calc_block_diagnostics(block, class, func),
            None => (),
        }
    }

    #[inline]
    fn maybe_propagate_parent_union(
        &mut self,
        base_union: &UnionType,
        child_entry: &Entry,
    ) -> Option<Type> {
        let replay = |t: &Type| match &child_entry.key {
            FlowKey::Member(_, name) => t
                .lookup(
                    self.i_s,
                    self.file_index,
                    unsafe { &**name },
                    LookupKind::Normal,
                    &mut ResultContext::Unknown,
                    &|_| todo!(),
                    &|_| todo!(),
                )
                .into_inferred(),
            FlowKey::Index { node_index, .. } => t.get_item(
                self.i_s,
                None,
                &SliceType::new(
                    self.file,
                    *node_index,
                    ASTSliceType::from_index(&self.file.tree, *node_index),
                ),
                &mut ResultContext::Unknown,
            ),
            FlowKey::Name(_) => unreachable!(),
        };

        let mut matching_entries = vec![];
        for union_entry in base_union.entries.iter() {
            if replay(&union_entry.type_)
                .as_cow_type(self.i_s)
                .overlaps(self.i_s, &child_entry.type_)
            {
                matching_entries.push(union_entry.clone());
            }
        }
        (base_union.entries.len() != matching_entries.len())
            .then(|| Type::from_union_entries(matching_entries))
    }

    fn propagate_parent_unions(
        &mut self,
        frame: &mut Frame,
        parent_unions: &[(FlowKey, UnionType)],
    ) {
        for (key, parent_union) in parent_unions.iter().rev() {
            for entry in &frame.entries {
                let (FlowKey::Member(base_key, _) | FlowKey::Index{base_key, ..}) = &entry.key else {
                    continue;
                };
                if key == base_key.as_ref() {
                    if let Some(type_) = self.maybe_propagate_parent_union(parent_union, entry) {
                        frame.add_entry(
                            self.i_s,
                            Entry {
                                key: key.clone(),
                                type_,
                                from_assignment: false,
                            },
                        );
                        break;
                    }
                }
            }
        }
    }

    fn find_guards_in_named_expr(&mut self, named_expr: NamedExpression) -> (Frame, Frame) {
        match named_expr.unpack() {
            NamedExpressionContent::Expression(expr) => self.find_guards_in_expr(expr),
            NamedExpressionContent::Definition(name, expr) => {
                debug!("TODO Flow control for walrus");
                self.find_guards_in_expr(expr)
            }
        }
    }

    fn find_guards_in_expr(&mut self, expr: Expression) -> (Frame, Frame) {
        match expr.unpack() {
            ExpressionContent::ExpressionPart(part) => {
                let mut result = self.find_guards_in_expression_parts(part);
                self.propagate_parent_unions(&mut result.truthy, &result.parent_unions);
                self.propagate_parent_unions(&mut result.falsey, &result.parent_unions);
                (result.truthy, result.falsey)
            }
            ExpressionContent::Ternary(_) => todo!(),
            ExpressionContent::Lambda(_) => todo!(),
        }
    }

    fn find_guards_in_expression_parts(&mut self, part: ExpressionPart) -> FramesWithParentUnions {
        match part {
            ExpressionPart::Atom(atom) => {
                if let AtomContent::NamedExpression(named_expr) = atom.unpack() {
                    let (truthy, falsey) = self.find_guards_in_named_expr(named_expr);
                    return FramesWithParentUnions {
                        falsey,
                        truthy,
                        ..Default::default()
                    };
                }
                let inf = self.infer_atom(atom, &mut ResultContext::Unknown);
                if let Some(key) = self.key_from_atom(atom) {
                    if let Some((truthy, falsey)) =
                        split_truthy_and_falsey(self.i_s.db, &inf.as_cow_type(self.i_s))
                    {
                        return FramesWithParentUnions {
                            truthy: Frame::from_type(key.clone(), truthy),
                            falsey: Frame::from_type(key, falsey),
                            ..Default::default()
                        };
                    }
                } else {
                    debug!("maybe use __bool__ for narrowing");
                }
                if let Some((truthy, falsey)) =
                    split_truthy_and_falsey(self.i_s.db, &inf.as_cow_type(self.i_s))
                {
                    return FramesWithParentUnions {
                        truthy: Frame::from_type_without_entry(truthy),
                        falsey: Frame::from_type_without_entry(falsey),
                        ..Default::default()
                    };
                }
            }
            ExpressionPart::Comparisons(comps) => {
                let mut frames: Option<FramesWithParentUnions> = None;
                let mut iterator = comps.iter().peekable();
                let mut left_infos = self.key_from_expr_part(iterator.peek().unwrap().left());
                'outer: while let Some(comparison) = iterator.next() {
                    let mut invert = false;
                    let right = comparison.right();
                    let mut right_infos = self.key_from_expr_part(right);
                    let mut is_eq = false;
                    match comparison {
                        ComparisonContent::Equals(..) => {
                            let mut eq_chain = vec![];
                            // `foo == bar == None` needs special handling
                            is_eq = true;
                            while let Some(ComparisonContent::Equals(_, _, r)) = iterator.peek() {
                                if eq_chain.is_empty() {
                                    eq_chain.push(left_infos.clone());
                                    eq_chain.push(right_infos.clone());
                                }
                                eq_chain.push(self.key_from_expr_part(*r));
                                iterator.next();
                            }
                            if !eq_chain.is_empty() {
                                if let Some(new) =
                                    self.find_comparison_chain_guards(&eq_chain, is_eq)
                                {
                                    frames = Some(merge_conjunction(self.i_s, frames, new));
                                }
                                left_infos = eq_chain.into_iter().last().unwrap();
                                continue 'outer;
                            }
                        }
                        ComparisonContent::NotEquals(..) => {
                            is_eq = true;
                            invert = true;
                        }
                        ComparisonContent::Is(..) => {
                            let mut is_chain = vec![];
                            // `foo is bar is None` needs special handling
                            while let Some(ComparisonContent::Is(_, _, r)) = iterator.peek() {
                                if is_chain.is_empty() {
                                    is_chain.push(left_infos.clone());
                                    is_chain.push(right_infos.clone());
                                }
                                is_chain.push(self.key_from_expr_part(*r));
                                iterator.next();
                            }
                            if !is_chain.is_empty() {
                                if let Some(new) =
                                    self.find_comparison_chain_guards(&is_chain, is_eq)
                                {
                                    frames = Some(merge_conjunction(self.i_s, frames, new));
                                }
                                left_infos = is_chain.into_iter().last().unwrap();
                                continue 'outer;
                            }
                        }
                        ComparisonContent::IsNot(..) => {
                            invert = true;
                        }
                        ComparisonContent::In(left, op, _)
                        | ComparisonContent::NotIn(left, op, _) => {
                            let new = self.guard_of_in_operator(op, left_infos, &mut right_infos);
                            frames = Some(merge_conjunction(self.i_s, frames, new));
                            left_infos = right_infos;
                            continue;
                        }
                        ComparisonContent::Operation(..) => {
                            self.infer_comparison_part(
                                comparison,
                                left_infos.inf,
                                &right_infos.inf,
                            );
                            left_infos = right_infos;
                            continue;
                        }
                    };
                    if let Some(mut new) =
                        self.find_comparison_guards(left_infos, &mut right_infos, is_eq)
                    {
                        if invert {
                            (new.falsey, new.truthy) = (new.truthy, new.falsey);
                        }
                        frames = Some(merge_conjunction(self.i_s, frames, new));
                    }
                    left_infos = right_infos
                }
                if let Some(frames) = frames {
                    return frames;
                }
            }
            ExpressionPart::Conjunction(and) => {
                let (left, right) = and.unpack();
                let mut left_frames = self.find_guards_in_expression_parts(left);
                let mut right_frames = None;
                left_frames.truthy = FLOW_ANALYSIS.with(|fa| {
                    fa.with_frame(self.i_s.db, left_frames.truthy, || {
                        right_frames = Some(self.find_guards_in_expression_parts(right));
                    })
                });
                let right_frames =
                    right_frames.unwrap_or_else(|| FramesWithParentUnions::default());
                return merge_conjunction(self.i_s, Some(left_frames), right_frames);
            }
            ExpressionPart::Disjunction(or) => {
                let (left, right) = or.unpack();
                let mut left_frames = self.find_guards_in_expression_parts(left);
                let mut parent_unions = left_frames.parent_unions;
                let mut right_frames = None;
                left_frames.falsey = FLOW_ANALYSIS.with(|fa| {
                    fa.with_frame(self.i_s.db, left_frames.falsey, || {
                        right_frames = Some(self.find_guards_in_expression_parts(right));
                    })
                });
                let right_frames =
                    right_frames.unwrap_or_else(|| FramesWithParentUnions::default());
                parent_unions.extend(right_frames.parent_unions);
                return FramesWithParentUnions {
                    truthy: merge_or(self.i_s, left_frames.truthy, right_frames.truthy),
                    falsey: merge_and(self.i_s, left_frames.falsey, right_frames.falsey),
                    parent_unions,
                };
            }
            ExpressionPart::Inversion(inv) => {
                let mut frames = self.find_guards_in_expression_parts(inv.expression());
                (frames.truthy, frames.falsey) = (frames.falsey, frames.truthy);
                return frames;
            }
            ExpressionPart::Primary(primary) => {
                match primary.second() {
                    PrimaryContent::Execution(ArgumentsDetails::Node(args)) => {
                        let first = self.infer_primary_or_atom(primary.first());
                        match first.maybe_saved_specific(self.i_s.db) {
                            Some(Specific::BuiltinsIsinstance) => {
                                if let Some(frames) =
                                    self.find_isinstance_or_issubclass_frames(args, false)
                                {
                                    return frames;
                                }
                            }
                            Some(Specific::BuiltinsIssubclass) => {
                                if let Some(frames) =
                                    self.find_isinstance_or_issubclass_frames(args, true)
                                {
                                    return frames;
                                }
                            }
                            _ => (),
                        }
                        if let Some(saved) = first.maybe_saved_link() {
                            if saved == self.i_s.db.python_state.callable_node_ref().as_link() {
                                debug!("TODO callable narrowing")
                            } else if saved == self.i_s.db.python_state.hasattr_node_ref().as_link()
                            {
                                debug!("TODO hasattr narrowing")
                            }
                        }
                    }
                    _ => (),
                }
                self.infer_expression_part(part);
                debug!("TODO primary expressions like foo.bar truthy/falsey")
            }
            _ => {
                self.infer_expression_part(part);
            }
        }
        FramesWithParentUnions::default()
    }

    fn find_isinstance_or_issubclass_frames(
        &mut self,
        args: Arguments,
        issubclass: bool,
    ) -> Option<FramesWithParentUnions> {
        let mut iterator = args.iter();
        let Argument::Positional(arg) = iterator.next()? else {
            return None
        };
        let result = self.key_from_namedexpression(arg);
        let key = result.key?;
        let Argument::Positional(type_arg) = iterator.next()? else {
            return None
        };
        let mut isinstance_type = self.check_isinstance_or_issubclass_type(type_arg, issubclass)?;
        if iterator.next().is_some() {
            return None;
        }
        if issubclass && !matches!(isinstance_type, Type::Never) {
            isinstance_type = Type::Type(Rc::new(isinstance_type))
        }
        // Please listen to "Red Hot Chili Peppers - Otherside" here.
        let mut true_type = Type::Never;
        let mut other_side = Type::Never;
        let matcher = &mut Matcher::with_ignored_promotions();
        for t in result.inf.as_cow_type(self.i_s).iter_with_unpacked_unions() {
            /*
            if matches!(t, Type::Any(_)) {
                true_type.union_in_place(t.clone());
                other_side.union_in_place(t.clone());
            }
            */
            match isinstance_type.is_super_type_of(self.i_s, matcher, t) {
                Match::True { with_any: true, .. } => other_side.union_in_place(t.clone()),
                Match::True {
                    with_any: false, ..
                } => true_type.union_in_place(t.clone()),
                Match::False { .. } => other_side.union_in_place(t.clone()),
            }
        }
        if matches!(true_type, Type::Never)
            || isinstance_type
                .iter_with_unpacked_unions()
                .any(|t| matches!(t, Type::Any(_)))
        {
            true_type = isinstance_type;
        }
        Some(FramesWithParentUnions {
            truthy: Frame::from_type(key.clone(), true_type),
            falsey: Frame::from_type(key, other_side),
            parent_unions: result.parent_unions,
        })
    }

    pub fn check_isinstance_or_issubclass_type(
        &mut self,
        arg: NamedExpression,
        issubclass: bool,
    ) -> Option<Type> {
        let isinstance_type = self.isinstance_or_issubclass_type(arg, issubclass)?;
        for t in isinstance_type.iter_with_unpacked_unions() {
            if matches!(t, Type::TypedDict(_)) {
                self.add_issue(
                    arg.index(),
                    IssueType::CannotUseIsinstanceWith {
                        func: match issubclass {
                            false => "isinstance",
                            true => "issubclass",
                        },
                        with: "TypedDict",
                    },
                )
            }
        }
        Some(isinstance_type)
    }

    fn isinstance_or_issubclass_type(
        &mut self,
        arg: NamedExpression,
        issubclass: bool,
    ) -> Option<Type> {
        let expr = match arg.unpack() {
            NamedExpressionContent::Expression(expr) => expr,
            NamedExpressionContent::Definition(_, _) => todo!(),
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
        &mut self,
        part: ExpressionPart,
        issubclass: bool,
    ) -> Option<Type> {
        let cannot_use_with = |self_: &mut Self, with| {
            self_.add_issue(
                part.index(),
                IssueType::CannotUseIsinstanceWith {
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
                        return cannot_use_with(self, "Any");
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

    fn process_isinstance_type(&mut self, part: ExpressionPart, t: &Type) -> Option<Type> {
        match t {
            Type::Tuple(tup) => match &tup.args {
                TupleArgs::FixedLen(ts) => {
                    let ts: Option<Vec<Type>> = ts
                        .iter()
                        .map(|t| self.process_isinstance_type(part, t))
                        .collect();
                    let ts = ts?;
                    Some(match ts.len() {
                        0 => Type::Never,
                        1 => ts.into_iter().next().unwrap(),
                        _ => Type::Union(UnionType::from_types(ts)),
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
                            IssueType::CannotUseIsinstanceWithParametrizedGenerics,
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

    fn find_comparison_guards(
        &mut self,
        left: KeyWithParentUnions,
        right: &mut KeyWithParentUnions,
        is_eq: bool,
    ) -> Option<FramesWithParentUnions> {
        if let Some(key) = left.key {
            // Narrow Foo in `Foo is None`
            if let Some((truthy, falsey)) = narrow_is_or_eq(
                self.i_s,
                key,
                &left.inf.as_cow_type(self.i_s),
                &right.inf.as_cow_type(self.i_s),
                is_eq,
            ) {
                return Some(FramesWithParentUnions {
                    truthy,
                    falsey,
                    parent_unions: left.parent_unions,
                });
            }
        }
        if let Some(key) = &right.key {
            // Narrow Foo in `None is Foo`
            if let Some((truthy, falsey)) = narrow_is_or_eq(
                self.i_s,
                key.clone(),
                &right.inf.as_cow_type(self.i_s),
                &left.inf.as_cow_type(self.i_s),
                is_eq,
            ) {
                return Some(FramesWithParentUnions {
                    truthy,
                    falsey,
                    // Taking it here is fine, because we don't want these to be duplicated
                    // entries from different comparisons
                    parent_unions: std::mem::take(&mut right.parent_unions),
                });
            }
        }
        None
    }

    fn find_comparison_chain_guards(
        &mut self,
        chain: &[KeyWithParentUnions],
        is_eq: bool,
    ) -> Option<FramesWithParentUnions> {
        let mut frames = None;
        'outer: for (i, part1) in chain.iter().enumerate() {
            for (k, part2) in chain.iter().enumerate() {
                if i == k {
                    continue;
                }
                if let Some(key) = &part1.key {
                    if let Some((truthy, falsey)) = narrow_is_or_eq(
                        self.i_s,
                        key.clone(),
                        &part1.inf.as_cow_type(self.i_s),
                        &part2.inf.as_cow_type(self.i_s),
                        is_eq,
                    ) {
                        let new = FramesWithParentUnions {
                            truthy,
                            falsey,
                            // TODO couldn't we avoid this clone?
                            parent_unions: part1.parent_unions.clone(),
                        };
                        frames = Some(merge_conjunction(self.i_s, frames, new));
                        continue 'outer;
                    }
                }
            }
        }
        frames
    }

    fn guard_of_in_operator(
        &mut self,
        op: Operand,
        left: KeyWithParentUnions,
        right: &mut KeyWithParentUnions,
    ) -> FramesWithParentUnions {
        self.infer_in_operator(NodeRef::new(self.file, op.index()), &left.inf, &right.inf);
        let maybe_invert = |truthy, falsey, parent_unions| {
            if op.as_code() == "in" {
                FramesWithParentUnions {
                    truthy,
                    falsey,
                    parent_unions,
                }
            } else {
                FramesWithParentUnions {
                    truthy: falsey,
                    falsey: truthy,
                    parent_unions,
                }
            }
        };
        let db = self.i_s.db;
        if let Some(item) = stdlib_container_item(db, &right.inf.as_cow_type(self.i_s)) {
            if !item.iter_with_unpacked_unions().any(|t| t == &Type::None) {
                if let Some(left_key) = left.key {
                    let left_t = left.inf.as_cow_type(self.i_s);
                    if left_t.overlaps(self.i_s, &item) {
                        if let Some(t) = removed_optional(&left_t) {
                            return maybe_invert(
                                Frame::from_type(left_key, t),
                                Frame::default(),
                                left.parent_unions,
                            );
                        }
                    }
                }
            }
        }
        // The right side can currently only be narrowed with TypedDicts
        let right_t = right.inf.as_cow_type(self.i_s);
        if right_t
            .iter_with_unpacked_unions()
            .any(|t| matches!(t, Type::TypedDict(_)))
        {
            if let Some(right_key) = &right.key {
                let left_t = left.inf.as_cow_type(self.i_s);
                let str_literals: Vec<_> = left_t
                    .iter_with_unpacked_unions()
                    .filter_map(|t| match t {
                        Type::Literal(Literal {
                            kind: LiteralKind::String(s),
                            ..
                        }) => Some(s.as_str(db)),
                        _ => None,
                    })
                    .collect();
                if !str_literals.is_empty() {
                    let mut true_types = Type::Never;
                    let false_types = right_t.remove_from_union(|t| match t {
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
                                return true;
                            } else if !td.is_final || false_only_count != str_literals.len() {
                                true_types.union_in_place(t.clone());
                            }
                            false
                        }
                        _ => {
                            true_types.union_in_place(t.clone());
                            false
                        }
                    });
                    return maybe_invert(
                        Frame::from_type(right_key.clone(), true_types),
                        Frame::from_type(right_key.clone(), false_types),
                        // Taking it here is fine, because we don't want these to be duplicated
                        // entries from different comparisons
                        std::mem::take(&mut right.parent_unions),
                    );
                }
            }
        }
        FramesWithParentUnions::default()
    }

    fn key_from_atom(&self, atom: Atom) -> Option<FlowKey> {
        match atom.unpack() {
            AtomContent::Name(name) => Some(FlowKey::Name(name_definition_link(
                self.i_s.db,
                self.file,
                name,
            ))),
            _ => None,
        }
    }

    fn key_from_primary(&mut self, primary: Primary) -> KeyWithParentUnions {
        let mut base = match primary.first() {
            PrimaryOrAtom::Primary(primary) => self.key_from_primary(primary),
            PrimaryOrAtom::Atom(atom) => KeyWithParentUnions::new(
                self.infer_atom(atom, &mut ResultContext::Unknown),
                self.key_from_atom(atom),
            ),
        };
        let old_base_key = base.key.take();
        let second = primary.second();
        let old_inf = base.inf;
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
                    base.key = Some(FlowKey::Member(Rc::new(base_key.clone()), attr.as_code()));
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
            PrimaryContent::Execution(_) => (),
        }
        if let Some(base_key) = old_base_key {
            // Only in case of valid keys we want to add the unions.
            if base.key.is_some() && old_inf.is_union(self.i_s) {
                let Type::Union(union_type) = old_inf.as_type(self.i_s) else {
                    unreachable!()
                };
                base.parent_unions.push((base_key.clone(), union_type))
            }
        }
        base
    }

    fn key_from_expr_part(&mut self, expr_part: ExpressionPart) -> KeyWithParentUnions {
        match expr_part {
            ExpressionPart::Atom(atom) => KeyWithParentUnions::new(
                self.infer_atom(atom, &mut ResultContext::Unknown),
                self.key_from_atom(atom),
            ),
            ExpressionPart::Primary(primary) => self.key_from_primary(primary),
            _ => KeyWithParentUnions::new(self.infer_expression_part(expr_part), None),
        }
    }

    fn key_from_expression(&mut self, expr: Expression) -> KeyWithParentUnions {
        match expr.unpack() {
            ExpressionContent::ExpressionPart(part) => self.key_from_expr_part(part),
            _ => KeyWithParentUnions::new(self.infer_expression(expr), None),
        }
    }

    fn key_from_namedexpression(&mut self, named_expr: NamedExpression) -> KeyWithParentUnions {
        match named_expr.unpack() {
            NamedExpressionContent::Expression(expr) => self.key_from_expression(expr),
            NamedExpressionContent::Definition(name_def, expr) => todo!(),
        }
    }

    fn key_from_slice_type(&mut self, slice_type: ASTSliceType) -> Option<FlowKeyIndex> {
        if let ASTSliceType::NamedExpression(ne) = slice_type {
            if let Some(atom) = ne.expression().maybe_unpacked_atom() {
                return match atom {
                    AtomContent::Int(int) => int
                        .parse()
                        .and_then(|i| Some(FlowKeyIndex::Int(i.try_into().ok()?))),
                    AtomContent::Strings(s) => {
                        Some(FlowKeyIndex::Str(s.as_python_string().as_str()?.into()))
                    }
                    _ => None,
                };
            }
        }
        None
    }

    pub fn narrow_primary(&mut self, primary: Primary) -> Option<Inferred> {
        FLOW_ANALYSIS.with(|fa| {
            for frame in fa.frames.borrow().iter().rev() {
                for entry in &frame.entries {
                    if self.matches_primary_entry(primary, &entry.key) {
                        return Some(Inferred::from_type(entry.type_.clone()));
                    }
                }
            }
            None
        })
    }

    fn matches_primary_entry(&mut self, primary: Primary, key: &FlowKey) -> bool {
        let match_primary_first_part = |left: &Rc<_>| match primary.first() {
            PrimaryOrAtom::Primary(primary) => self.matches_primary_entry(primary, left),
            PrimaryOrAtom::Atom(atom) => {
                let FlowKey::Name(check_link) = left.as_ref() else {
                        return false;
                    };
                let AtomContent::Name(name) = atom.unpack() else {
                        return false;
                    };
                name_definition_link(self.i_s.db, self.file, name) == *check_link
            }
        };
        match key {
            FlowKey::Member(left, right) => {
                match primary.second() {
                    PrimaryContent::Attribute(attr) => {
                        if attr.as_code() != unsafe { &**right as &str } {
                            return false;
                        }
                    }
                    _ => return false,
                }
                match primary.first() {
                    PrimaryOrAtom::Primary(primary) => self.matches_primary_entry(primary, left),
                    PrimaryOrAtom::Atom(atom) => {
                        let FlowKey::Name(check_link) = left.as_ref() else {
                            return false;
                        };
                        let AtomContent::Name(name) = atom.unpack() else {
                            return false;
                        };
                        name_definition_link(self.i_s.db, self.file, name) == *check_link
                    }
                }
            }
            FlowKey::Index {
                base_key,
                match_index,
                ..
            } => match primary.second() {
                PrimaryContent::GetItem(slice_type) => {
                    if let Some(other_index_key) = self.key_from_slice_type(slice_type) {
                        return match_index == &other_index_key;
                    }
                    false
                }
                _ => false,
            },
            FlowKey::Name(_) => false,
        }
    }
}

fn name_definition_link(db: &Database, file: &PythonFile, name: Name) -> PointLink {
    let p = file.points.get(name.index());
    if p.calculated() {
        debug_assert_eq!(p.type_(), PointType::Redirect);
        let def = p.node_index();
        let file = db.loaded_python_file(p.file_index());
        PointLink::new(p.file_index(), first_defined_name(file, def).unwrap_or(def))
    } else {
        todo!()
    }
}

#[derive(Clone)]
struct KeyWithParentUnions {
    key: Option<FlowKey>,
    inf: Inferred,
    parent_unions: Vec<(FlowKey, UnionType)>,
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

#[derive(Default)]
struct FramesWithParentUnions {
    truthy: Frame,
    falsey: Frame,
    parent_unions: Vec<(FlowKey, UnionType)>,
}

fn stdlib_container_item(db: &Database, t: &Type) -> Option<Type> {
    // Returns int for a list[int] or other containers. This is used for narrowing in. However
    // we can only do this if we know how __contains__ works.
    let item = match t {
        Type::Class(c) => {
            let class = c.class(db);
            let infos = class.use_cached_class_infos(db);
            if let Some(nt) = infos.maybe_named_tuple() {
                return stdlib_container_item(db, &Type::Tuple(nt.as_tuple()));
            } else {
                let n = class.node_ref;
                let s = &db.python_state;
                if n == s.list_node_ref() || n == s.dict_node_ref() || n == s.set_node_ref() {
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
        Type::Tuple(tup) => {
            let GenericItem::TypeArg(t) = tup.tuple_class_generics(db).nth(0.into()).unwrap() else {
                unreachable!();
            };
            t.clone()
        }
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

fn removed_optional(full: &Type) -> Option<Type> {
    for t in full.iter_with_unpacked_unions() {
        if matches!(t, Type::None) {
            return Some(full.remove_from_union(|t| matches!(t, Type::None)));
        }
    }
    None
}
