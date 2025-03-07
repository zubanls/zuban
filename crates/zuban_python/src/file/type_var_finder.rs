use std::borrow::Cow;

use parsa_python_cst::*;
use vfs::FileIndex;

use super::{
    name_resolution::{NameResolution, PointResolution},
    type_computation::cache_name_on_class,
};
use crate::{
    database::{ComplexPoint, PointKind, PointLink, Specific},
    diagnostics::IssueKind,
    file::PythonFile,
    getitem::{SliceOrSimple, SliceType},
    inference_state::InferenceState,
    node_ref::NodeRef,
    type_::{TypeVarIndex, TypeVarLike, TypeVarLikes, TypeVarManager},
    type_helpers::{ClassInitializer, ClassNodeRef},
};

#[derive(Debug, Clone, PartialEq)]
enum BaseLookup {
    Module(FileIndex),
    Class(PointLink),
    Protocol,
    Callable,
    Literal,
    Generic,
    TypeVarLikeClass,
    Other,
}

#[derive(Default)]
struct Infos<'c, 'd> {
    class: Option<&'c ClassNodeRef<'c>>,
    type_var_manager: TypeVarManager<PointLink>,
    generic_or_protocol_slice: Option<SliceType<'d>>,
    current_generic_or_protocol_index: Option<TypeVarIndex>,
    had_generic_or_protocol_issue: bool,
}

pub struct TypeVarFinder<'db, 'file, 'i_s, 'c, 'd, 'e> {
    name_resolution: NameResolution<'db, 'file, 'i_s>,
    infos: &'e mut Infos<'c, 'd>,
}

impl<'db: 'file, 'file, 'i_s> std::ops::Deref for TypeVarFinder<'db, 'file, 'i_s, '_, '_, '_> {
    type Target = NameResolution<'db, 'file, 'i_s>;

    fn deref(&self) -> &Self::Target {
        &self.name_resolution
    }
}

impl<'db, 'file: 'd, 'i_s, 'c, 'd, 'e> TypeVarFinder<'db, 'file, 'i_s, 'c, 'd, 'e> {
    pub fn find_class_type_vars(
        i_s: &'i_s InferenceState<'db, 'i_s>,
        class: &'c ClassNodeRef<'file>,
    ) -> TypeVarLikes {
        let mut infos = Infos {
            class: Some(class),
            ..Default::default()
        };
        let mut finder = TypeVarFinder {
            name_resolution: class.file.name_resolution(i_s),
            infos: &mut infos,
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
        if let Some(slice_type) = finder.infos.generic_or_protocol_slice {
            if !finder.infos.had_generic_or_protocol_issue {
                finder.check_generic_or_protocol_length(slice_type)
            }
        }
        infos.type_var_manager.into_type_vars()
    }

    pub fn find_alias_type_vars(
        i_s: &'i_s InferenceState<'db, 'i_s>,
        file: &'file PythonFile,
        expr: Expression<'d>,
    ) -> TypeVarLikes {
        let mut infos = Infos::default();
        let mut finder = TypeVarFinder {
            name_resolution: file.name_resolution(i_s),
            infos: &mut infos,
        };
        finder.find_in_expr(expr);
        infos.type_var_manager.into_type_vars()
    }

    fn find_in_slice_like(&mut self, slice_like: SliceOrSimple<'d>) {
        match slice_like {
            SliceOrSimple::Simple(s) => self.find_in_expr(s.named_expr.expression()),
            SliceOrSimple::Slice(_) => (),
            SliceOrSimple::Starred(starred) => self.find_in_expr(starred.starred_expr.expression()),
        };
    }

    fn find_in_expr(&mut self, expr: Expression<'d>) {
        // Only expressions are valid in types, lambdas and ternaries are not relevant
        // (though correct syntax)
        if let ExpressionContent::ExpressionPart(n) = expr.unpack() {
            self.find_in_expression_part(n);
        }
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

    fn find_in_primary(&mut self, primary: Primary<'d>) -> BaseLookup {
        let base = self.find_in_primary_or_atom(primary.first());
        match primary.second() {
            PrimaryContent::Attribute(name) => match base {
                BaseLookup::Module(f) => {
                    let mut finder = TypeVarFinder {
                        name_resolution: self
                            .i_s
                            .db
                            .loaded_python_file(f)
                            .name_resolution(self.i_s),
                        infos: self.infos,
                    };
                    finder.find_in_name(name)
                }
                BaseLookup::Class(link) => {
                    let cls = ClassInitializer::from_link(self.i_s.db, link);
                    let point_kind = cache_name_on_class(cls, self.file, name);
                    if point_kind == PointKind::Redirect {
                        self.find_in_name(name)
                    } else {
                        BaseLookup::Other
                    }
                }
                _ => BaseLookup::Other,
            },
            PrimaryContent::Execution(_) => BaseLookup::Other,
            PrimaryContent::GetItem(slice_type) => {
                let s = SliceType::new(self.file, primary.index(), slice_type);
                match base {
                    BaseLookup::Protocol | BaseLookup::Generic => {
                        if self.infos.generic_or_protocol_slice.is_some() {
                            self.infos.had_generic_or_protocol_issue = true;
                            NodeRef::new(self.file, primary.index())
                                .add_issue(self.i_s, IssueKind::EnsureSingleGenericOrProtocol);
                        }
                        self.infos.generic_or_protocol_slice =
                            Some(SliceType::new(self.file, primary.index(), slice_type));
                        for (i, slice_like) in s.iter().enumerate() {
                            self.infos.current_generic_or_protocol_index = Some(i.into());
                            self.find_in_slice_like(slice_like)
                        }
                        self.infos.current_generic_or_protocol_index = None;
                    }
                    BaseLookup::Callable => self.find_in_callable(s),
                    BaseLookup::Literal => (), // Literals can never contain type vars
                    _ => {
                        for slice_like in s.iter() {
                            self.find_in_slice_like(slice_like)
                        }
                    }
                }
                BaseLookup::Other
            }
        }
    }

    fn find_in_atom(&mut self, atom: Atom) -> BaseLookup {
        match atom.unpack() {
            AtomContent::Name(n) => return self.find_in_name(n),
            AtomContent::Strings(s_o_b) => match s_o_b.as_python_string() {
                PythonString::Ref(start, s) => {
                    self.compute_forward_reference(start, Cow::Borrowed(s))
                }
                PythonString::String(start, s) => {
                    self.compute_forward_reference(start, Cow::Owned(s))
                }
                PythonString::FString => (),
            },
            _ => (),
        }
        BaseLookup::Other
    }

    fn find_in_name(&mut self, name: Name) -> BaseLookup {
        let resolved = self.resolve_name_without_narrowing(name);
        self.point_resolution_to_base_lookup(resolved, |kind| {
            NodeRef::new(self.name_resolution.file, name.index())
                .add_issue(self.name_resolution.i_s, kind)
        })
    }

    fn point_resolution_to_base_lookup(
        &mut self,
        resolved: PointResolution,
        add_issue: impl Fn(IssueKind),
    ) -> BaseLookup {
        match resolved {
            PointResolution::NameDef {
                node_ref,
                global_redirect,
            } => {
                let name_def = node_ref.as_name_def();
                match name_def.expect_type() {
                    TypeLike::ClassDef(c) => {
                        return BaseLookup::Class(PointLink::new(node_ref.file_index(), c.index()))
                    }
                    TypeLike::Assignment(assignment) => {
                        if let Some((_, None, expr)) =
                            assignment.maybe_simple_type_expression_assignment()
                        {
                            if self.is_type_var_like_execution(expr) {
                                let inference = node_ref.file.inference(self.i_s);
                                let inf = inference.infer_name_of_definition(name_def.name());
                                if let Some(node_ref) = inf.maybe_saved_node_ref(self.i_s.db) {
                                    if let Some(ComplexPoint::TypeVarLike(tvl)) = node_ref.complex()
                                    {
                                        return self.handle_type_var_like(&tvl, add_issue);
                                    }
                                }
                            }
                        }
                    }
                    TypeLike::ImportFromAsName(from_as_name) => {
                        return self.point_resolution_to_base_lookup(
                            self.resolve_import_from_name_def_without_narrowing(from_as_name),
                            add_issue,
                        )
                    }
                    TypeLike::DottedAsName(dotted_as_name) => {
                        return self.point_resolution_to_base_lookup(
                            self.resolve_import_name_name_def_without_narrowing(dotted_as_name),
                            add_issue,
                        )
                    }
                    _ => (),
                }
            }
            PointResolution::Inferred(inferred) => {
                if let Some(specific) = inferred.maybe_saved_specific(self.i_s.db) {
                    return match specific {
                        Specific::TypingGeneric => BaseLookup::Generic,
                        Specific::TypingProtocol => BaseLookup::Protocol,
                        Specific::TypingCallable => BaseLookup::Callable,
                        Specific::TypingLiteral => BaseLookup::Literal,
                        _ => BaseLookup::Other,
                    };
                } else if let Some(ComplexPoint::TypeVarLike(tvl)) =
                    inferred.maybe_complex_point(self.i_s.db)
                {
                    return self.handle_type_var_like(tvl, add_issue);
                } else if let Some(file) = inferred.maybe_file(self.i_s.db) {
                    return BaseLookup::Module(file);
                }
            }
            _ => (),
        };
        BaseLookup::Other
    }

    fn handle_type_var_like(
        &mut self,
        tvl: &TypeVarLike,
        add_issue: impl Fn(IssueKind),
    ) -> BaseLookup {
        if self
            .infos
            .class
            .and_then(|c| {
                ClassInitializer::from_node_ref(*c).maybe_type_var_like_in_parent(self.i_s.db, &tvl)
            })
            .is_none()
        {
            if matches!(tvl, TypeVarLike::TypeVarTuple(_))
                && self.infos.type_var_manager.has_type_var_tuples()
            {
                if self.infos.class.is_some() {
                    add_issue(IssueKind::MultipleTypeVarTuplesInClassDef);
                }
                return BaseLookup::Other;
            }
            if !tvl.has_default() {
                if let Some(previous) = self.infos.type_var_manager.last() {
                    if previous.has_default() {
                        add_issue(IssueKind::TypeVarDefaultWrongOrder {
                            type_var1: tvl.name(self.i_s.db).into(),
                            type_var2: previous.name(self.i_s.db).into(),
                        });
                    }
                }
            }
            let old_index = self.infos.type_var_manager.add(tvl.clone(), None);
            if let Some(force_index) = self.infos.current_generic_or_protocol_index {
                if old_index < force_index {
                    add_issue(IssueKind::DuplicateTypeVar)
                } else if old_index != force_index {
                    self.infos
                        .type_var_manager
                        .move_index(old_index, force_index);
                }
            }
        }
        BaseLookup::Other
    }

    fn find_in_primary_or_atom(&mut self, p: PrimaryOrAtom<'d>) -> BaseLookup {
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

    fn compute_forward_reference(&mut self, start: CodeIndex, string: Cow<str>) {
        let file = self.file.ensure_annotation_file(self.i_s.db, start, string);
        let mut inner_finder = TypeVarFinder {
            name_resolution: file.name_resolution(self.i_s),
            infos: self.infos,
        };

        let Some(star_exprs) = file.tree.maybe_star_expressions() else {
            return;
        };
        let StarExpressionContent::Expression(expr) = star_exprs.unpack() else {
            return;
        };
        inner_finder.find_in_expr(expr);
    }

    fn is_type_var_like_execution(&mut self, expr: Expression) -> bool {
        let ExpressionContent::ExpressionPart(ExpressionPart::Primary(primary)) = expr.unpack()
        else {
            return false;
        };
        let PrimaryContent::Execution(_) = primary.second() else {
            return false;
        };
        // TODO work on this
        true
        /*
        self.find_in_primary_or_atom(primary.first()) == BaseLookup::TypeVarLikeClass
        */
    }

    fn check_generic_or_protocol_length(&self, slice_type: SliceType) {
        // Reorder slices
        if slice_type.iter().count() < self.infos.type_var_manager.len() {
            slice_type
                .as_node_ref()
                .add_issue(self.i_s, IssueKind::IncompleteGenericOrProtocolTypeVars)
        }
    }
}
