use std::{cell::RefCell, rc::Rc};

use parsa_python_ast::{
    Atom, AtomContent, ComparisonContent, Expression, ExpressionContent, ExpressionPart,
    IfBlockIterator, IfBlockType, IfStmt, NamedExpression, NamedExpressionContent, Primary,
    PrimaryContent, PrimaryOrAtom, SliceType,
};

use crate::{
    database::{Database, PointLink, PointType},
    debug,
    inferred::Inferred,
    matching::ResultContext,
    type_::Type,
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
        for frame in self.frames.borrow().iter() {
            match frame {
                Frame::Reachable { entries } => {
                    for entry in entries {
                        if entry.key == FlowKey::Name(name_link) {
                            return Some(Inferred::from_type(entry.type_.clone()));
                        }
                    }
                }
                Frame::Unreachable => todo!(),
            }
        }
        None
    }

    fn with_new_frame(&self, callable: impl FnOnce()) -> Frame {
        self.frames.borrow_mut().push(Frame::default());
        callable();
        self.frames.borrow_mut().pop().unwrap()
    }

    fn with_frame(&self, frame: Frame, callable: impl FnOnce()) -> Frame {
        self.frames.borrow_mut().push(frame);
        callable();
        self.frames.borrow_mut().pop().unwrap()
    }
}

fn merge_and(x: Frame, y: Frame) -> Frame {
    debug!("TODO implement and");
    x
}

fn merge_or(x: Frame, y: Frame) -> Frame {
    debug!("TODO implement or");
    Frame::default()
}

fn split_off_none(db: &Database, t: &Type) -> (Type, Type) {
    let mut none_return = Type::Never;
    let left = Type::gather_union(db, |gather| {
        for sub_t in t.iter_with_unpacked_unions() {
            if matches!(sub_t, Type::None) {
                none_return = Type::None;
            } else {
                gather(sub_t.clone())
            }
        }
    });
    (left, none_return)
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
                    // TODO merge frames
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
                for comparison in comparisons.iter() {
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
                            return (Frame::default(), Frame::default());
                        }
                        ComparisonContent::NotIn(_, _, _) => {
                            debug!("TODO not in");
                            self.infer_expression_part(part);
                            return (Frame::default(), Frame::default());
                        }
                        ComparisonContent::Operation(_) => {
                            self.infer_expression_part(part);
                            return (Frame::default(), Frame::default());
                        }
                    };
                    let left_inf = self.infer_expression_part(left);
                    if let Some(key) = self.key_from_expr_part(left) {
                        let right = self.infer_expression_part(right);
                        match right.as_cow_type(self.i_s).as_ref() {
                            Type::None => {
                                let (rest, none) =
                                    split_off_none(self.i_s.db, &left_inf.as_cow_type(self.i_s));
                                let result = (
                                    Frame::from_type(key.clone(), none),
                                    Frame::from_type(key, rest),
                                );
                                return if invert { (result.1, result.0) } else { result };
                            }
                            _ => debug!("TODO is"),
                        }
                    }
                    return (Frame::default(), Frame::default());
                }
                todo!()
            }
            ExpressionPart::BitwiseAnd(bitwise_and) => {
                let op = bitwise_and.as_operation();
                let (left_true, left_false) = self.find_guards_in_expression_parts(op.left);
                let (right_true, right_false) = self.find_guards_in_expression_parts(op.right);
                return (
                    merge_and(left_true, right_true),
                    merge_or(left_false, right_false),
                );
            }
            ExpressionPart::BitwiseOr(bitwise_or) => {
                let op = bitwise_or.as_operation();
                let (left_true, left_false) = self.find_guards_in_expression_parts(op.left);
                let (right_true, right_false) = self.find_guards_in_expression_parts(op.right);
                return (
                    merge_or(left_true, right_true),
                    merge_and(left_false, right_false),
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
