use parsa_python_ast::*;

use super::type_computation::{
    assignment_type_node_ref, cache_name_on_class, SpecialType, TypeNameLookup,
};
use crate::database::{Locality, Point, PointLink, PointType};
use crate::diagnostics::IssueType;
use crate::file::file_state::File;
use crate::file::{Inference, PythonFile};
use crate::getitem::{SliceOrSimple, SliceType};
use crate::node_ref::NodeRef;
use crate::type_::{TypeVarIndex, TypeVarLike, TypeVarLikes, TypeVarManager};
use crate::type_helpers::Class;

#[derive(Debug, Clone)]
enum BaseLookup<'file> {
    Module(&'file PythonFile),
    Class(PointLink),
    Protocol,
    Callable,
    Generic,
    Other,
}

pub struct TypeVarFinder<'db, 'file, 'i_s, 'c, 'd> {
    inference: &'c mut Inference<'db, 'file, 'i_s>,
    class: Option<&'c Class<'c>>,
    type_var_manager: TypeVarManager,
    generic_or_protocol_slice: Option<SliceType<'d>>,
    current_generic_or_protocol_index: Option<TypeVarIndex>,
    had_generic_or_protocol_issue: bool,
}

impl<'db, 'file: 'd, 'i_s, 'c, 'd> TypeVarFinder<'db, 'file, 'i_s, 'c, 'd> {
    pub fn find_class_type_vars(
        inference: &'c mut Inference<'db, 'file, 'i_s>,
        class: &'c Class<'d>,
    ) -> TypeVarLikes {
        let mut finder = Self {
            inference,
            class: Some(class),
            type_var_manager: TypeVarManager::default(),
            generic_or_protocol_slice: None,
            current_generic_or_protocol_index: None,
            had_generic_or_protocol_issue: false,
        };

        if let Some(arguments) = class.node().arguments() {
            for argument in arguments.iter() {
                match argument {
                    Argument::Positional(n) => {
                        finder.find_in_expr(n.expression());
                    }
                    Argument::Keyword(_) => (), // Ignore for now -> part of meta class
                    Argument::Star(_) | Argument::StarStar(_) => (), // Nobody probably cares about this
                }
            }
        }
        if let Some(slice_type) = finder.generic_or_protocol_slice {
            if !finder.had_generic_or_protocol_issue {
                finder.check_generic_or_protocol_length(slice_type)
            }
        }
        finder.type_var_manager.into_type_vars()
    }

    pub fn find_alias_type_vars(
        inference: &'c mut Inference<'db, 'file, 'i_s>,
        expr: Expression<'d>,
    ) -> TypeVarLikes {
        let mut finder = Self {
            inference,
            class: None,
            type_var_manager: TypeVarManager::default(),
            generic_or_protocol_slice: None,
            current_generic_or_protocol_index: None,
            had_generic_or_protocol_issue: false,
        };
        finder.find_in_expr(expr);
        finder.type_var_manager.into_type_vars()
    }

    fn find_in_expr(&mut self, expr: Expression<'d>) {
        match expr.unpack() {
            ExpressionContent::ExpressionPart(n) => {
                self.find_in_expression_part(n);
            }
            ExpressionContent::Lambda(_) => todo!(),
            ExpressionContent::Ternary(t) => todo!(),
        };
    }

    fn find_in_expression_part(&mut self, node: ExpressionPart<'d>) {
        match node {
            ExpressionPart::Atom(atom) => {
                self.find_in_atom(atom);
            }
            ExpressionPart::Primary(primary) => {
                self.find_in_primary(primary);
            }
            ExpressionPart::BitwiseOr(bitwise_or) => {
                let (a, b) = bitwise_or.unpack();
                self.find_in_expression_part(a);
                self.find_in_expression_part(b);
            }
            _ => (),
        }
    }

    fn find_in_primary(&mut self, primary: Primary<'d>) -> BaseLookup<'db> {
        let base = self.find_in_primary_or_atom(primary.first());
        match primary.second() {
            PrimaryContent::Attribute(name) => {
                match base {
                    BaseLookup::Module(f) => {
                        // TODO this is a bit weird. shouldn't this just do a goto?
                        if let Some(index) = f.symbol_table.lookup_symbol(name.as_str()) {
                            self.inference.file.points.set(
                                name.index(),
                                Point::new_redirect(f.file_index(), index, Locality::Todo),
                            );
                            self.find_in_name(name)
                        } else {
                            BaseLookup::Other
                        }
                    }
                    BaseLookup::Class(link) => {
                        let cls = Class::from_non_generic_link(self.inference.i_s.db, link);
                        let point_type = cache_name_on_class(cls, self.inference.file, name);
                        if point_type == PointType::Redirect {
                            self.find_in_name(name)
                        } else {
                            BaseLookup::Other
                        }
                    }
                    _ => BaseLookup::Other,
                }
            }
            PrimaryContent::Execution(details) => BaseLookup::Other,
            PrimaryContent::GetItem(slice_type) => {
                let s = SliceType::new(self.inference.file, primary.index(), slice_type);
                match base {
                    BaseLookup::Protocol | BaseLookup::Generic => {
                        if self.generic_or_protocol_slice.is_some() {
                            self.had_generic_or_protocol_issue = true;
                            NodeRef::new(self.inference.file, primary.index()).add_issue(
                                self.inference.i_s,
                                IssueType::EnsureSingleGenericOrProtocol,
                            );
                        }
                        self.generic_or_protocol_slice = Some(SliceType::new(
                            self.inference.file,
                            primary.index(),
                            slice_type,
                        ));
                        for (i, slice_or_simple) in s.iter().enumerate() {
                            self.current_generic_or_protocol_index = Some(i.into());
                            if let SliceOrSimple::Simple(s) = slice_or_simple {
                                self.find_in_expr(s.named_expr.expression())
                            }
                        }
                        self.current_generic_or_protocol_index = None;
                    }
                    BaseLookup::Callable => self.find_in_callable(s),
                    _ => {
                        for slice_or_simple in s.iter() {
                            if let SliceOrSimple::Simple(s) = slice_or_simple {
                                self.find_in_expr(s.named_expr.expression())
                            }
                        }
                    }
                }
                BaseLookup::Other
            }
        }
    }

    fn find_in_atom(&mut self, atom: Atom) -> BaseLookup<'db> {
        match atom.unpack() {
            AtomContent::Name(n) => {
                self.inference.infer_name_reference(n);
                self.find_in_name(n)
            }
            AtomContent::Strings(s_o_b) => match s_o_b.as_python_string() {
                PythonString::Ref(start, s) => {
                    //todo!()
                    BaseLookup::Other
                    //self.compute_forward_reference(start, s.to_owned())
                }
                PythonString::String(start, s) => BaseLookup::Other, // TODO this is wrong
                PythonString::FString => todo!(),
            },
            _ => BaseLookup::Other,
        }
    }

    fn find_in_name(&mut self, name: Name) -> BaseLookup<'db> {
        // TODO this whole check is way too hacky.
        let point = self.inference.file.points.get(name.index());
        if point.calculated() && point.type_() == PointType::Redirect {
            let node_ref = point.as_redirected_node_ref(self.inference.i_s.db);
            if node_ref.file_index() == self.inference.file_index {
                let redirected_name = node_ref.as_name();
                if let TypeLike::Assignment(assignment) = redirected_name.expect_type() {
                    let node_ref = assignment_type_node_ref(self.inference.file, assignment);
                    if node_ref.point().calculating() {
                        // This means that this is probably a recursive type alias being calculated. Just
                        // ignore.
                        return BaseLookup::Other;
                    }
                }
            }
        }
        match self.inference.lookup_type_name(name) {
            TypeNameLookup::Module(f) => BaseLookup::Module(f),
            TypeNameLookup::Class { node_ref } => BaseLookup::Class(node_ref.as_link()),
            TypeNameLookup::TypeVarLike(type_var_like) => {
                if self
                    .class
                    .and_then(|c| {
                        c.maybe_type_var_like_in_parent(self.inference.i_s, &type_var_like)
                    })
                    .is_none()
                {
                    if let TypeVarLike::TypeVarTuple(t) = &type_var_like {
                        if self.type_var_manager.has_type_var_tuples() {
                            NodeRef::new(self.inference.file, name.index()).add_issue(
                                self.inference.i_s,
                                IssueType::MultipleTypeVarTuplesInClassDef,
                            )
                            // TODO this type var tuple should probably not be added
                        }
                    }
                    let old_index = self.type_var_manager.add(type_var_like, None);
                    if let Some(force_index) = self.current_generic_or_protocol_index {
                        if old_index < force_index {
                            NodeRef::new(self.inference.file, name.index())
                                .add_issue(self.inference.i_s, IssueType::DuplicateTypeVar)
                        } else if old_index != force_index {
                            self.type_var_manager.move_index(old_index, force_index);
                        }
                    }
                }
                BaseLookup::Other
            }
            TypeNameLookup::SpecialType(SpecialType::Generic) => BaseLookup::Generic,
            TypeNameLookup::SpecialType(SpecialType::Protocol) => BaseLookup::Protocol,
            TypeNameLookup::SpecialType(SpecialType::Callable) => BaseLookup::Callable,
            _ => BaseLookup::Other,
        }
    }

    fn find_in_primary_or_atom(&mut self, p: PrimaryOrAtom<'d>) -> BaseLookup<'db> {
        match p {
            PrimaryOrAtom::Primary(primary) => self.find_in_primary(primary),
            PrimaryOrAtom::Atom(atom) => self.find_in_atom(atom),
        }
    }

    fn find_in_callable(&mut self, slice_type: SliceType<'d>) {
        if slice_type.iter().count() == 2 {
            let mut iterator = slice_type.iter();
            if let SliceOrSimple::Simple(n) = iterator.next().unwrap() {
                let expression = n.named_expr.expression();
                match expression.maybe_unpacked_atom() {
                    Some(AtomContent::List(list)) => {
                        for i in list.unpack() {
                            if let StarLikeExpression::NamedExpression(n) = i {
                                self.find_in_expr(n.expression());
                            }
                        }
                    }
                    Some(AtomContent::Ellipsis) => (),
                    _ => self.find_in_expr(expression),
                }
            }
            let slice_or_simple = iterator.next().unwrap();
            if let SliceOrSimple::Simple(s) = slice_or_simple {
                self.find_in_expr(s.named_expr.expression())
            }
        }
    }

    fn check_generic_or_protocol_length(&self, slice_type: SliceType) {
        // Reorder slices
        if slice_type.iter().count() < self.type_var_manager.len() {
            slice_type.as_node_ref().add_issue(
                self.inference.i_s,
                IssueType::IncompleteGenericOrProtocolTypeVars,
            )
        }
    }
}
