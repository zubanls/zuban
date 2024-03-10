use std::{cell::RefCell, rc::Rc};

use parsa_python_ast::{
    Atom, AtomContent, ComparisonContent, Expression, ExpressionContent, ExpressionPart,
    IfBlockIterator, IfBlockType, IfStmt, NamedExpression, NamedExpressionContent, Primary,
    PrimaryContent, PrimaryOrAtom, SliceType,
};

use crate::{
    database::{Database, PointLink, PointType},
    debug,
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

#[derive(Debug)]
enum Frame {
    Reachable { entries: Entries },
    Unreachable,
}

impl Default for Frame {
    fn default() -> Self {
        Self::Reachable {
            entries: Default::default(),
        }
    }
}

impl Frame {
    fn from_type(key: FlowKey, type_: Type) -> Frame {
        match type_ {
            Type::Never => Frame::Unreachable,
            type_ => Frame::Reachable {
                entries: vec![Entry { key, type_ }],
            },
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
            match frame {
                Frame::Reachable { entries } => {
                    for entry in entries {
                        if entry.key == FlowKey::Name(name_link) {
                            return Some(Inferred::from_type(entry.type_.clone()));
                        }
                    }
                }
                Frame::Unreachable => {
                    todo!() //return Some(Inferred::from_type(Type::Never))
                }
            }
        }
        None
    }

    fn overwrite_entries(&self, new_entries: Entries) {
        let mut frames = self.frames.borrow_mut();
        let Frame::Reachable{ entries } = &mut frames.last_mut().unwrap() else {
            unreachable!()
        };
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

    fn with_frame(&self, frame: Frame, callable: impl FnOnce()) -> Frame {
        if matches!(frame, Frame::Unreachable) {
            return frame;
        }
        self.frames.borrow_mut().push(frame);
        callable();
        self.frames.borrow_mut().pop().unwrap()
    }

    pub fn mark_current_frame_unreachable(&self) {
        *self.frames.borrow_mut().last_mut().unwrap() = Frame::Unreachable
    }
}

fn merge_and(i_s: &InferenceState, x: Frame, y: Frame) -> Frame {
    let Frame::Reachable { entries: y_entries } = &y else {
        return Frame::Unreachable
    };
    let Frame::Reachable { entries: mut x_entries } = x else {
        return Frame::Unreachable
    };
    for x_entry in &mut x_entries {
        for y_entry in y_entries {
            if &x_entry.key == &y_entry.key {
                if let Some(t) = x_entry.type_.common_sub_type(i_s, &y_entry.type_) {
                    x_entry.type_ = t
                }
                break;
            }
        }
    }
    Frame::Reachable { entries: x_entries }
}

fn merge_or(i_s: &InferenceState, x: Frame, y: Frame) -> Frame {
    let Frame::Reachable { entries: y_entries } = &y else {
        return x
    };
    let Frame::Reachable { entries: x_entries } = x else {
        return y
    };
    let mut new_entries = vec![];
    for x_entry in x_entries {
        for y_entry in y_entries {
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
    Frame::Reachable {
        entries: new_entries,
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
                FLOW_ANALYSIS.with(|fa| {
                    let true_frame = fa.with_frame(true_frame, || {
                        self.calc_block_diagnostics(block, class, func)
                    });
                    let false_frame =
                        fa.with_frame(false_frame, || self.process_ifs(if_blocks, class, func));

                    // TODO merge frames properly, this is just a special case
                    if matches!(false_frame, Frame::Unreachable)
                        || matches!(true_frame, Frame::Unreachable)
                    {
                        if let Frame::Reachable { entries } = false_frame {
                            fa.overwrite_entries(entries)
                        } else if let Frame::Reachable { entries } = true_frame {
                            fa.overwrite_entries(entries)
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
            ExpressionPart::Comparisons(comparisons) => {
                let mut frames: Option<(Frame, Frame)> = None;
                for comparison in comparisons.iter() {
                    if let Some(new) = self.find_comparison_guards(part, comparison) {
                        frames = Some(if let Some(old) = frames {
                            (
                                merge_and(self.i_s, old.0, new.0),
                                merge_or(self.i_s, old.1, new.1),
                            )
                        } else {
                            new
                        })
                    }
                }
                if let Some(frames) = frames {
                    return frames;
                }
            }
            ExpressionPart::Conjunction(and) => {
                let (left, right) = and.unpack();
                let (left_true, left_false) = self.find_guards_in_expression_parts(left);
                let (right_true, right_false) = self.find_guards_in_expression_parts(right);
                return (
                    merge_and(self.i_s, left_true, right_true),
                    merge_or(self.i_s, left_false, right_false),
                );
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
            ExpressionPart::Primary(_) => {
                self.infer_expression_part(part);
                debug!("TODO primary guard")
            }
            _ => {
                self.infer_expression_part(part);
            }
        }
        (Frame::default(), Frame::default())
    }

    fn find_comparison_guards(
        &mut self,
        part: ExpressionPart,
        comparison: ComparisonContent,
    ) -> Option<(Frame, Frame)> {
        let mut invert = false;
        let (left, right) = match comparison {
            ComparisonContent::Equals(left, _, right) => (left, right),
            ComparisonContent::NotEquals(left, _, right) => {
                invert = true;
                (left, right)
            }
            ComparisonContent::Is(left, _, right) => (left, right),
            ComparisonContent::IsNot(left, _, right) => {
                invert = true;
                (left, right)
            }
            ComparisonContent::In(_, _, _) => {
                debug!("TODO in");
                self.infer_expression_part(part);
                return Some((Frame::default(), Frame::default()));
            }
            ComparisonContent::NotIn(_, _, _) => {
                debug!("TODO not in");
                self.infer_expression_part(part);
                return Some((Frame::default(), Frame::default()));
            }
            ComparisonContent::Operation(_) => {
                self.infer_expression_part(part);
                return Some((Frame::default(), Frame::default()));
            }
        };
        let left_inf = self.infer_expression_part(left);
        let right_inf = self.infer_expression_part(right);
        if let Some(key) = self.key_from_expr_part(left) {
            // Narrow Foo in `Foo is None`
            if let Some(result) = narrow_is_or_eq(
                self.i_s,
                key,
                &left_inf.as_cow_type(self.i_s),
                &right_inf.as_cow_type(self.i_s),
            ) {
                return Some(if invert { (result.1, result.0) } else { result });
            }
        }
        if let Some(key) = self.key_from_expr_part(right) {
            // Narrow Foo in `None is Foo`
            if let Some(result) = narrow_is_or_eq(
                self.i_s,
                key,
                &right_inf.as_cow_type(self.i_s),
                &left_inf.as_cow_type(self.i_s),
            ) {
                return Some(if invert { (result.1, result.0) } else { result });
            }
        }
        None
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
}
