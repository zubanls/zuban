use std::{cell::RefCell, rc::Rc};

use parsa_python_ast::{
    Atom, AtomContent, ComparisonContent, Expression, ExpressionContent, ExpressionPart,
    IfBlockType, IfStmt, Primary, PrimaryContent, PrimaryOrAtom, SliceType,
};

use crate::{
    database::{Database, PointLink},
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
    fn with_frame(&self, callable: impl FnOnce()) {
        self.frames.borrow_mut().push(Frame::default());
        callable();
        let frame = self.frames.borrow_mut().pop();
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

impl<'db, 'file, 'i_s> Inference<'db, 'file, 'i_s> {
    pub fn flow_analysis_for_if_stmt(
        &mut self,
        if_stmt: IfStmt,
        class: Option<Class>,
        func: Option<&Function>,
    ) {
        for block in if_stmt.iter_blocks() {
            match block {
                IfBlockType::If(if_expr, block) => {
                    self.infer_named_expression(if_expr);
                    self.calc_block_diagnostics(block, class, func)
                }
                IfBlockType::Else(block) => self.calc_block_diagnostics(block, class, func),
            }
        }
    }

    fn with_conditionals(&self, callable: impl FnOnce()) {}

    fn find_guards(&mut self, expr: Expression) -> (Frame, Frame) {
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
                (Frame::default(), Frame::default())
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
                        ComparisonContent::Operation(_) => debug!("TODO comp op"),
                    }
                    return (Frame::default(), Frame::default());
                }
                todo!()
            }
            ExpressionPart::BitwiseAnd(bitwise_and) => {
                let op = bitwise_and.as_operation();
                let (left_true, left_false) = self.find_guards_in_expression_parts(op.left);
                let (right_true, right_false) = self.find_guards_in_expression_parts(op.right);
                (
                    merge_and(left_true, right_true),
                    merge_or(left_false, right_false),
                )
            }
            ExpressionPart::BitwiseOr(bitwise_or) => {
                let op = bitwise_or.as_operation();
                let (left_true, left_false) = self.find_guards_in_expression_parts(op.left);
                let (right_true, right_false) = self.find_guards_in_expression_parts(op.right);
                (
                    merge_or(left_true, right_true),
                    merge_and(left_false, right_false),
                )
            }
            ExpressionPart::Inversion(inv) => {
                let (true_entries, false_entries) =
                    self.find_guards_in_expression_parts(inv.expression());
                (false_entries, true_entries)
            }
            ExpressionPart::Primary(_) => todo!(),
            ExpressionPart::AwaitPrimary(_) => todo!(),
            _ => (Frame::default(), Frame::default()),
        }
    }

    fn key_from_atom(&self, atom: Atom) -> Option<FlowKey> {
        match atom.unpack() {
            AtomContent::Name(name) => Some(FlowKey::Name(PointLink::new(
                self.file_index,
                first_defined_name(self.file, name.index()).unwrap(),
            ))),
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
