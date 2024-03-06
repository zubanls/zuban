use std::{cell::RefCell, rc::Rc};

use parsa_python_ast::{
    Atom, AtomContent, ComparisonContent, Expression, ExpressionContent, ExpressionPart,
    IfBlockIterator, IfBlockType, IfStmt, NamedExpression, NamedExpressionContent, Primary,
    PrimaryContent, PrimaryOrAtom, SliceType,
};

use crate::{
    database::{Database, PointLink, PointType},
    debug,
    matching::ResultContext,
    type_::Type,
    type_helpers::{Class, Function},
};

use super::{first_defined_name, inference::Inference};

type Entries = Vec<Entry>;

thread_local! {
    pub static FLOW_ANALYSIS: FlowAnalysis = FlowAnalysis::default();
}

#[derive(Debug)]
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

fn split_off_none(db: &Database, key: FlowKey, t: &Type) -> (Type, Type) {
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
                debug!("maybe use __bool__ for narrowing");
            }
            ExpressionPart::Comparisons(comparisons) => {
                for comparison in comparisons.iter() {
                    match comparison {
                        ComparisonContent::Equals(_, _, _) => debug!("TODO EQ"),
                        ComparisonContent::NotEquals(_, _, _) => debug!("TODO NEQ"),
                        ComparisonContent::Is(left, _, right) => {
                            let left_inf = self.infer_expression_part(left);
                            if let Some(key) = self.key_from_expr_part(left) {
                                let right = self.infer_expression_part(right);
                                match right.as_cow_type(self.i_s).as_ref() {
                                    Type::None => {
                                        let (left, right) = split_off_none(
                                            self.i_s.db,
                                            key,
                                            &left_inf.as_cow_type(self.i_s),
                                        );
                                        todo!()
                                    }
                                    _ => debug!("TODO is"),
                                }
                            }
                        }
                        ComparisonContent::IsNot(_, _, _) => debug!("TODO is not"),
                        ComparisonContent::In(_, _, _) => debug!("TODO in"),
                        ComparisonContent::NotIn(_, _, _) => debug!("TODO not in"),
                        ComparisonContent::Operation(_) => {
                            self.infer_expression_part(part);
                            return (Frame::default(), Frame::default());
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
                    Some(FlowKey::Name(PointLink::new(
                        self.file_index,
                        first_defined_name(self.file, def).unwrap_or(def),
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
