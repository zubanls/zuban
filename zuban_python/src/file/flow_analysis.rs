use std::{cell::RefCell, rc::Rc};

use parsa_python_ast::{
    Argument, Arguments, ArgumentsDetails, Atom, AtomContent, ComparisonContent, Expression,
    ExpressionContent, ExpressionPart, IfBlockIterator, IfBlockType, IfStmt, NamedExpression,
    NamedExpressionContent, Primary, PrimaryContent, PrimaryOrAtom, SliceType,
};

use crate::{
    database::{Database, PointLink, PointType},
    debug,
    diagnostics::{Issue, IssueType},
    inference_state::InferenceState,
    inferred::Inferred,
    matching::ResultContext,
    type_::{EnumMember, Type},
    type_helpers::{Class, Function},
};

use super::{first_defined_name, inference::Inference};

type Entries = Vec<Entry>;

thread_local! {
    pub static FLOW_ANALYSIS: FlowAnalysis = FlowAnalysis::default();
}

#[derive(Debug, Clone, PartialEq)]
enum FlowKey {
    Name(PointLink),
    Index(Rc<FlowKey>),
    Member(Rc<FlowKey>, PointLink),
}

#[derive(Debug)]
struct Entry {
    key: FlowKey,
    type_: Type,
    //widens_type: bool,
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

    fn from_type(key: FlowKey, type_: Type) -> Frame {
        match type_ {
            Type::Never => Frame {
                unreachable: true,
                ..Frame::default()
            },
            type_ => Frame::new(vec![Entry { key, type_ }]),
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

    fn overwrite_entries(&self, new_entries: Entries) {
        let mut frames = self.frames.borrow_mut();
        let entries = &mut frames.last_mut().unwrap().entries;
        'outer: for new_entry in new_entries {
            for entry in &mut *entries {
                if entry.key == new_entry.key {
                    entry.type_ = new_entry.type_;
                    break 'outer;
                }
            }
            entries.push(new_entry)
        }
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
                })
            }
            break;
        }
    }
    Frame::new(new_entries)
}

fn merge_conjunction(
    i_s: &InferenceState,
    old: Option<(Frame, Frame)>,
    new: (Frame, Frame),
) -> (Frame, Frame) {
    if let Some(old) = old {
        (merge_and(i_s, old.0, new.0), merge_or(i_s, old.1, new.1))
    } else {
        new
    }
}

fn split_off_singleton(db: &Database, t: &Type, split_off: &Type) -> (Type, Type) {
    let matches_singleton = |t: &_| match split_off {
        Type::None => split_off == t,
        Type::EnumMember(member1) => match t {
            Type::EnumMember(member2) => member1.is_same_member(member2),
            _ => false,
        },
        _ => false,
    };
    let mut other_return = Type::Never;
    let left = Type::gather_union(db, |gather| {
        for sub_t in t.iter_with_unpacked_unions() {
            match sub_t {
                Type::Any(_) => {
                    // Any can be None or something else.
                    other_return = split_off.clone();
                    gather(sub_t.clone());
                }
                Type::Enum(enum_) => {
                    if let Type::EnumMember(split) = split_off {
                        if enum_.defined_at == split.enum_.defined_at {
                            for (i, _) in enum_.members.iter().enumerate() {
                                let new_member =
                                    Type::EnumMember(EnumMember::new(enum_.clone(), i, false));
                                if i == split.member_index {
                                    other_return.union_in_place(db, new_member)
                                } else {
                                    gather(new_member)
                                }
                            }
                            continue;
                        }
                    }
                    gather(sub_t.clone())
                }
                _ if matches_singleton(sub_t) => other_return = split_off.clone(),
                _ => gather(sub_t.clone()),
            }
        }
    });
    (left, other_return)
}

fn narrow_is_or_eq(
    i_s: &InferenceState,
    key: FlowKey,
    left_t: &Type,
    right_t: &Type,
) -> Option<(Frame, Frame)> {
    match right_t {
        Type::EnumMember(member) if member.implicit => {
            let mut new_member = member.clone();
            new_member.implicit = false;
            narrow_is_or_eq(i_s, key, left_t, &Type::EnumMember(new_member))
        }
        Type::None | Type::EnumMember(_) => {
            let (rest, none) = split_off_singleton(i_s.db, &left_t, right_t);
            let result = (
                Frame::from_type(key.clone(), none),
                Frame::from_type(key, rest),
            );
            Some(result)
        }
        Type::Enum(enum_) if enum_.members.len() == 1 => {
            // Enums with a single item can be compared to that item.
            narrow_is_or_eq(
                i_s,
                key,
                left_t,
                &Type::EnumMember(EnumMember::new(enum_.clone(), 0, false)),
            )
        }
        _ => match left_t {
            left_t @ Type::Union(union) => {
                // Remove None from left, if the right types match everything except None.
                if left_t
                    .iter_with_unpacked_unions()
                    .any(|t| matches!(t, Type::None))
                {
                    let (new_left, _) = split_off_singleton(i_s.db, left_t, &Type::None);
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

fn split_truthy_and_falsey(db: &Database, t: &Type) -> Option<(Type, Type)> {
    fn split_truthy_and_falsey_single(t: &Type) -> Option<(Type, Type)> {
        match t {
            Type::None => Some((Type::Never, Type::None)),
            Type::Literal(literal) => todo!(),
            _ => None,
        }
    }

    match t {
        Type::Union(union) => {
            let mut truthy = Type::Never;
            let mut falsey = Type::Never;
            let mut had_split = false;
            for t in union.iter() {
                let result = split_truthy_and_falsey(db, t);
                had_split |= result.is_some();
                let (new_true, new_false) = result.unwrap_or_else(|| (t.clone(), t.clone()));
                truthy.union_in_place(db, new_true);
                falsey.union_in_place(db, new_false);
            }
            had_split.then_some((truthy, falsey))
        }
        _ => split_truthy_and_falsey_single(t),
    }
}

impl Inference<'_, '_, '_> {
    pub fn flow_analysis_for_assert(&mut self, expr: Expression) {
        let (true_frame, _) = self.find_guards_in_expr(expr);
        FLOW_ANALYSIS.with(|fa| {
            let mut frames = fa.frames.borrow_mut();
            let new_frame = merge_and(
                self.i_s,
                std::mem::take(frames.last_mut().unwrap()),
                true_frame,
            );
            *frames.last_mut().unwrap() = new_frame;
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

                    // TODO merge frames properly, this is just a special case
                    if false_frame.unreachable || true_frame.unreachable {
                        if !false_frame.unreachable {
                            fa.overwrite_entries(false_frame.entries)
                        } else if !true_frame.unreachable {
                            fa.overwrite_entries(true_frame.entries)
                        } else {
                            debug!("TODO should probably be unreachable")
                        }
                    }
                });
            }
            Some(IfBlockType::Else(block)) => self.calc_block_diagnostics(block, class, func),
            None => (),
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
            ExpressionContent::ExpressionPart(part) => self.find_guards_in_expression_parts(part),
            ExpressionContent::Ternary(_) => todo!(),
            ExpressionContent::Lambda(_) => todo!(),
        }
    }

    fn find_guards_in_expression_parts(&mut self, part: ExpressionPart) -> (Frame, Frame) {
        match part {
            ExpressionPart::Atom(atom) => {
                let inf = self.infer_atom(atom, &mut ResultContext::Unknown);
                if let Some(key) = self.key_from_atom(atom) {
                    if let Some((truthy, falsey)) =
                        split_truthy_and_falsey(self.i_s.db, &inf.as_cow_type(self.i_s))
                    {
                        return (
                            Frame::from_type(key.clone(), truthy),
                            Frame::from_type(key, falsey),
                        );
                    }
                } else {
                    debug!("maybe use __bool__ for narrowing");
                }
            }
            ExpressionPart::Comparisons(comps) => {
                let mut frames: Option<(Frame, Frame)> = None;
                let mut iterator = comps.iter().peekable();
                let mut left_inf = self.infer_expression_part(iterator.peek().unwrap().left());
                'outer: while let Some(comparison) = iterator.next() {
                    let mut invert = false;
                    let right = comparison.right();
                    let right_inf = self.infer_expression_part(right);
                    match comparison {
                        ComparisonContent::Equals(..) => {
                            let mut eq_chain = vec![];
                            // `foo == bar == None` needs special handling
                            while let Some(ComparisonContent::Equals(_, _, r)) = iterator.peek() {
                                if eq_chain.is_empty() {
                                    eq_chain.push(self.new_inferred_with_key(
                                        left_inf.clone(),
                                        comparison.left(),
                                    ));
                                    eq_chain
                                        .push(self.new_inferred_with_key(right_inf.clone(), right));
                                }
                                let new_inf = self.infer_expression_part(*r);
                                eq_chain.push(self.new_inferred_with_key(new_inf, *r));
                                iterator.next();
                            }
                            if !eq_chain.is_empty() {
                                todo!();
                                left_inf = eq_chain.into_iter().last().unwrap().inf;
                                continue 'outer;
                            }
                        }
                        ComparisonContent::NotEquals(..) => {
                            invert = true;
                        }
                        ComparisonContent::Is(..) => {
                            let mut is_chain = vec![];
                            // `foo is bar is None` needs special handling
                            while let Some(ComparisonContent::Is(_, _, r)) = iterator.peek() {
                                if is_chain.is_empty() {
                                    is_chain.push(self.new_inferred_with_key(
                                        left_inf.clone(),
                                        comparison.left(),
                                    ));
                                    is_chain
                                        .push(self.new_inferred_with_key(right_inf.clone(), right));
                                }
                                let new_inf = self.infer_expression_part(*r);
                                is_chain.push(self.new_inferred_with_key(new_inf, *r));
                                iterator.next();
                            }
                            if !is_chain.is_empty() {
                                if let Some(new) = self.find_comparison_chain_guards(&is_chain) {
                                    frames = Some(merge_conjunction(self.i_s, frames, new));
                                }
                                left_inf = is_chain.into_iter().last().unwrap().inf;
                                continue 'outer;
                            }
                        }
                        ComparisonContent::IsNot(..) => {
                            invert = true;
                        }
                        ComparisonContent::In(..) => {
                            debug!("TODO in");
                            self.infer_comparison_part(comparison, left_inf, &right_inf);
                            return (Frame::default(), Frame::default());
                        }
                        ComparisonContent::NotIn(..) => {
                            debug!("TODO not in");
                            self.infer_comparison_part(comparison, left_inf, &right_inf);
                            return (Frame::default(), Frame::default());
                        }
                        ComparisonContent::Operation(..) => {
                            self.infer_comparison_part(comparison, left_inf.clone(), &right_inf);
                            left_inf = right_inf;
                            continue;
                        }
                    };
                    let left_infos = self.new_inferred_with_key(left_inf, comparison.left());
                    if let Some(mut new) =
                        self.find_comparison_guards(left_infos, &right_inf, right)
                    {
                        if invert {
                            new = (new.1, new.0)
                        }
                        frames = Some(merge_conjunction(self.i_s, frames, new));
                    }
                    left_inf = right_inf
                }
                if let Some(frames) = frames {
                    return frames;
                }
            }
            ExpressionPart::Conjunction(and) => {
                let (left, right) = and.unpack();
                let left_frames = self.find_guards_in_expression_parts(left);
                let right_frames = self.find_guards_in_expression_parts(right);
                return merge_conjunction(self.i_s, Some(left_frames), right_frames);
            }
            ExpressionPart::Disjunction(or) => {
                let (left, right) = or.unpack();
                let (left_true, left_false) = self.find_guards_in_expression_parts(left);
                let (right_true, right_false) = self.find_guards_in_expression_parts(right);
                return (
                    merge_or(self.i_s, left_true, right_true),
                    merge_and(self.i_s, left_false, right_false),
                );
            }
            ExpressionPart::Inversion(inv) => {
                let (true_entries, false_entries) =
                    self.find_guards_in_expression_parts(inv.expression());
                return (false_entries, true_entries);
            }
            ExpressionPart::Primary(primary) => {
                match primary.second() {
                    PrimaryContent::Execution(ArgumentsDetails::Node(args)) => {
                        let first = self.infer_primary_or_atom(primary.first());
                        if let Some(saved) = first.maybe_saved_link() {
                            if saved == self.i_s.db.python_state.isinstance_node_ref().as_link() {
                                if let Some(frames) = self.find_isinstance_frames(args) {
                                    return frames;
                                }
                            } else if saved
                                == self.i_s.db.python_state.issubclass_node_ref().as_link()
                            {
                                debug!("TODO issubclass narrowing")
                            } else if saved
                                == self.i_s.db.python_state.callable_node_ref().as_link()
                            {
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
                debug!("TODO primary guard")
            }
            _ => {
                self.infer_expression_part(part);
            }
        }
        (Frame::default(), Frame::default())
    }

    fn new_inferred_with_key<'a>(
        &mut self,
        inf: Inferred,
        part: ExpressionPart,
    ) -> InferredWithKey {
        InferredWithKey {
            inf,
            key: self.key_from_expr_part(part),
        }
    }

    fn infer_named_expr_with_key(&mut self, n: NamedExpression) -> InferredWithKey {
        InferredWithKey {
            inf: self.infer_named_expression(n),
            key: self.key_from_expression(n.expression()),
        }
    }

    fn find_isinstance_frames(&mut self, args: Arguments) -> Option<(Frame, Frame)> {
        let mut iterator = args.iter();
        let Argument::Positional(arg) = iterator.next()? else {
            return None
        };
        let result = self.infer_named_expr_with_key(arg);
        let key = result.key?;
        let t = self.isinstance_or_issubclass_type(iterator.next()?)?;
        if iterator.next().is_some() {
            return None;
        }
        Some((Frame::from_type(key, t), Frame::default()))
    }

    fn isinstance_or_issubclass_type(&mut self, arg: Argument) -> Option<Type> {
        let Argument::Positional(arg) = arg else {
            return None
        };
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
                self.isinstance_or_issubclass_type_for_expr_part(part)
            }
            _ => None,
        }
    }

    fn isinstance_or_issubclass_type_for_expr_part(
        &mut self,
        part: ExpressionPart,
    ) -> Option<Type> {
        match part {
            ExpressionPart::Disjunction(disjunction) => {
                let (first, second) = disjunction.unpack();
                let t1 = self.isinstance_or_issubclass_type_for_expr_part(first)?;
                let t2 = self.isinstance_or_issubclass_type_for_expr_part(second)?;
                //Some(t1.union(self.i_s.db, t2))
                todo!()
            }
            _ => {
                match self
                    .infer_expression_part(part)
                    .as_cow_type(self.i_s)
                    .as_ref()
                {
                    Type::Type(t) => Some((**t).clone()),
                    _ => None,
                }
            }
        }
    }

    fn find_comparison_guards(
        &mut self,
        left: InferredWithKey,
        right_inf: &Inferred,
        right: ExpressionPart,
    ) -> Option<(Frame, Frame)> {
        if let Some(key) = left.key {
            // Narrow Foo in `Foo is None`
            if let Some(result) = narrow_is_or_eq(
                self.i_s,
                key,
                &left.inf.as_cow_type(self.i_s),
                &right_inf.as_cow_type(self.i_s),
            ) {
                return Some(result);
            }
        }
        if let Some(key) = self.key_from_expr_part(right) {
            // Narrow Foo in `None is Foo`
            if let Some(result) = narrow_is_or_eq(
                self.i_s,
                key,
                &right_inf.as_cow_type(self.i_s),
                &left.inf.as_cow_type(self.i_s),
            ) {
                return Some(result);
            }
        }
        None
    }

    fn find_comparison_chain_guards(
        &mut self,
        chain: &[InferredWithKey],
    ) -> Option<(Frame, Frame)> {
        let mut frames = None;
        'outer: for (i, part1) in chain.iter().enumerate() {
            for (k, part2) in chain.iter().enumerate() {
                if i == k {
                    continue;
                }
                if let Some(key) = &part1.key {
                    if let Some(new) = narrow_is_or_eq(
                        self.i_s,
                        key.clone(),
                        &part1.inf.as_cow_type(self.i_s),
                        &part2.inf.as_cow_type(self.i_s),
                    ) {
                        frames = Some(merge_conjunction(self.i_s, frames, new));
                        continue 'outer;
                    }
                }
            }
        }
        frames
    }

    fn key_from_atom(&self, atom: Atom) -> Option<FlowKey> {
        match atom.unpack() {
            AtomContent::Name(name) => {
                let p = self.file.points.get(name.index());
                if p.calculated() {
                    debug_assert_eq!(p.type_(), PointType::Redirect);
                    let def = p.node_index();
                    let file = self.i_s.db.loaded_python_file(p.file_index());
                    Some(FlowKey::Name(PointLink::new(
                        p.file_index(),
                        first_defined_name(file, def).unwrap_or(def),
                    )))
                } else {
                    todo!()
                }
            }
            _ => None,
        }
    }

    fn key_from_primary(&self, primary: Primary) -> Option<FlowKey> {
        let base = match primary.first() {
            PrimaryOrAtom::Primary(primary) => self.key_from_primary(primary),
            PrimaryOrAtom::Atom(atom) => self.key_from_atom(atom),
        };
        match primary.second() {
            PrimaryContent::Attribute(attr) => {
                debug!("TODO implement primary key");
                None
            }
            PrimaryContent::GetItem(attr) => match attr {
                SliceType::NamedExpression(_) => {
                    debug!("TODO GetItem key");
                    None
                }
                _ => None,
            },
            PrimaryContent::Execution(_) => None,
        }
    }

    fn key_from_expr_part(&self, expr_part: ExpressionPart) -> Option<FlowKey> {
        match expr_part {
            ExpressionPart::Atom(atom) => self.key_from_atom(atom),
            ExpressionPart::Primary(primary) => self.key_from_primary(primary),
            _ => None,
        }
    }

    fn key_from_expression(&self, expression: Expression) -> Option<FlowKey> {
        match expression.unpack() {
            ExpressionContent::ExpressionPart(part) => self.key_from_expr_part(part),
            _ => None,
        }
    }
}

struct InferredWithKey {
    key: Option<FlowKey>,
    inf: Inferred,
}
