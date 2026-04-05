use std::borrow::Cow;

use parsa_python_cst::*;
use vfs::FileIndex;

use super::{
    ClassInitializer, ClassNodeRef,
    name_resolution::{NameResolution, PointResolution},
};
use crate::{
    database::{ComplexPoint, Point, PointKind, PointLink, Specific},
    debug,
    diagnostics::IssueKind,
    file::PythonFile,
    getitem::{SliceOrSimple, SliceType},
    inference_state::InferenceState,
    node_ref::NodeRef,
    type_::{TypeVarIndex, TypeVarLike, TypeVarLikes, TypeVarManager},
    utils::debug_indent,
};

#[derive(Debug, Clone, PartialEq)]
enum BaseLookup {
    Module(FileIndex),
    Class(PointLink),
    GenericOrProtocol,
    Literal,
    TypeVarLikeClass,
    TypeVarLike(TypeVarLike),
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

pub(crate) struct TypeVarFinder<'db, 'file, 'i_s, 'c, 'd, 'e> {
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
        debug!("Finding type vars for class {:?}", class.name());
        let _indent = debug_indent();
        let mut infos = Infos {
            class: Some(class),
            ..Default::default()
        };
        let mut finder = TypeVarFinder {
            name_resolution: class.file.name_resolution_for_types(i_s),
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
        if let Some(slice_type) = finder.infos.generic_or_protocol_slice
            && !finder.infos.had_generic_or_protocol_issue
        {
            finder.check_generic_or_protocol_length(slice_type)
        }
        let type_vars = infos
            .type_var_manager
            .into_type_vars_after_checking_type_var_tuples(i_s.db, class.file);
        debug!(
            "Found type vars for class {:?}: {:?}",
            class.name(),
            type_vars.debug_info(i_s.db)
        );
        type_vars
    }

    pub(super) fn find_alias_type_vars(
        i_s: &InferenceState,
        file: &PythonFile,
        expr: Expression,
    ) -> TypeVarLikes {
        TypeVarFinder::find_alias_type_vars_with(i_s, file, expr, |slf| slf.find_in_expr(expr))
    }

    pub(super) fn find_named_tuple_or_typed_dict_assignment_type_vars(
        i_s: &InferenceState,
        file: &PythonFile,
        args: ArgumentsDetails,
    ) -> TypeVarLikes {
        if let ArgumentsDetails::Node(n) = args {
            // Skip the name
            if let Some(Argument::Positional(pos)) = n.iter().nth(1) {
                let expr = pos.expression();
                return TypeVarFinder::find_alias_type_vars_with(i_s, file, expr, |slf| {
                    match expr.maybe_unpacked_atom() {
                        Some(AtomContent::List(list)) => {
                            slf.find_in_named_tuple_fields(list.unpack())
                        }
                        Some(AtomContent::Tuple(tup)) => slf.find_in_named_tuple_fields(tup.iter()),
                        Some(AtomContent::Dict(dict)) => {
                            // For TypedDicts
                            for element in dict.iter_elements() {
                                match element {
                                    DictElement::KeyValue(dict_key_value) => {
                                        slf.find_in_expr(dict_key_value.value())
                                    }
                                    DictElement::Star(_) => (),
                                }
                            }
                        }
                        _ => (),
                    }
                });
            }
        }
        i_s.db.python_state.empty_type_var_likes.clone()
    }

    fn find_alias_type_vars_with(
        i_s: &'i_s InferenceState<'db, 'i_s>,
        file: &'file PythonFile,
        expr: Expression<'d>,
        with: impl FnOnce(&mut TypeVarFinder<'db, 'file, 'i_s, 'c, 'd, '_>),
    ) -> TypeVarLikes {
        debug!("Finding type vars in {:?}", expr.as_code());
        let _indent = debug_indent();
        let mut infos = Infos::default();
        let mut finder = TypeVarFinder {
            name_resolution: file.name_resolution_for_types(i_s),
            infos: &mut infos,
        };
        with(&mut finder);
        let type_vars = infos
            .type_var_manager
            .into_type_vars_after_checking_type_var_tuples(i_s.db, file);
        debug!(
            "Found type vars in {:?}: {:?}",
            expr.as_code(),
            type_vars.debug_info(i_s.db)
        );
        type_vars
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
            PrimaryContent::Attribute(name) => {
                let result = match base {
                    BaseLookup::Module(f) => {
                        let file = self.i_s.db.loaded_python_file(f);
                        let Some((resolved, _)) = file
                            .name_resolution_for_types(&InferenceState::new(self.i_s.db, file))
                            .resolve_module_access(name.as_str(), |k| {
                                self.add_issue(name.index(), k)
                            })
                        else {
                            return BaseLookup::Other;
                        };
                        self.point_resolution_to_base_lookup(resolved)
                    }
                    BaseLookup::Class(link) => {
                        let cls = ClassInitializer::from_link(self.i_s.db, link);
                        let Some(pr) = self.lookup_type_name_on_class(cls, name) else {
                            return BaseLookup::Other;
                        };
                        self.point_resolution_to_base_lookup(pr)
                    }
                    _ => BaseLookup::Other,
                };
                if let BaseLookup::TypeVarLike(tvl) = result {
                    self.handle_type_var_like(tvl, primary.index());
                    return BaseLookup::Other;
                }
                result
            }
            PrimaryContent::Execution(_) => BaseLookup::Other,
            PrimaryContent::GetItem(slice_type) => {
                let s = SliceType::new(self.file, primary.index(), slice_type);
                match base {
                    BaseLookup::GenericOrProtocol => {
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

    fn find_in_atom(&mut self, atom: Atom<'d>) -> BaseLookup {
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
            AtomContent::List(list) => {
                for element in list.unpack() {
                    match element {
                        StarLikeExpression::NamedExpression(n) => {
                            self.find_in_expr(n.expression());
                        }
                        StarLikeExpression::StarNamedExpression(s) => {
                            self.find_in_expression_part(s.expression_part());
                        }
                        _ => (),
                    }
                }
            }
            AtomContent::NamedExpression(ne) => self.find_in_expr(ne.expression()),
            _ => (),
        }
        BaseLookup::Other
    }

    fn find_in_named_tuple_fields(&mut self, iterator: StarLikeExpressionIterator<'d>) {
        let mut check_expr = |e: Expression<'d>| {
            if let Some(AtomContent::Tuple(name_and_type)) = e.maybe_unpacked_atom()
                && let Some(StarLikeExpression::NamedExpression(n)) = name_and_type.iter().nth(1)
            {
                self.find_in_expr(n.expression());
            }
        };
        for element in iterator {
            if let StarLikeExpression::NamedExpression(ne) = element {
                check_expr(ne.expression())
            }
        }
    }

    fn find_in_name(&mut self, name: Name) -> BaseLookup {
        match self.lookup_name(name) {
            BaseLookup::TypeVarLike(tvl) => {
                self.handle_type_var_like(tvl, name.index());
                BaseLookup::Other
            }
            l => l,
        }
    }

    fn handle_type_var_like(&mut self, tvl: TypeVarLike, index: NodeIndex) {
        let add_issue = |kind| {
            NodeRef::new(self.name_resolution.file, index).add_issue(self.name_resolution.i_s, kind)
        };
        if self.i_s.find_parent_type_var(&tvl).is_some() {
            debug!(
                "Found bound TypeVar {} in parent scope",
                tvl.name(self.i_s.db)
            );
        } else {
            if let TypeVarLike::TypeVarTuple(tvt) = &tvl
                && let Some(has_tvt) = self.infos.type_var_manager.first_type_var_tuple()
                && has_tvt != tvt
            {
                if self.infos.class.is_some() {
                    add_issue(IssueKind::MultipleTypeVarTuplesInClassDef);
                }
                return;
            }
            debug!("Found unbound TypeVar {}", tvl.name(self.i_s.db));
            let old_index = self.infos.type_var_manager.add(tvl, None, Some(index));
            if let Some(force_index) = self.infos.current_generic_or_protocol_index {
                if old_index < force_index {
                    add_issue(IssueKind::DuplicateTypeVar);
                } else if old_index != force_index {
                    self.infos
                        .type_var_manager
                        .move_index(old_index, force_index);
                }
            }
        }
    }

    fn find_in_primary_or_atom(&mut self, p: PrimaryOrAtom<'d>) -> BaseLookup {
        match p {
            PrimaryOrAtom::Primary(primary) => self.find_in_primary(primary),
            PrimaryOrAtom::Atom(atom) => self.find_in_atom(atom),
        }
    }

    fn compute_forward_reference(&mut self, start: CodeIndex, string: Cow<str>) {
        let file = self
            .file
            .ensure_forward_reference_file(self.i_s.db, start, string);
        let mut inner_finder = TypeVarFinder {
            name_resolution: file.name_resolution_for_types(self.i_s),
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

    fn check_generic_or_protocol_length(&self, slice_type: SliceType) {
        // Reorder slices
        if slice_type.iter().count() < self.infos.type_var_manager.len() {
            slice_type
                .as_node_ref()
                .add_issue(self.i_s, IssueKind::IncompleteGenericOrProtocolTypeVars);
        }
    }
}

impl<'db, 'file> NameResolution<'db, 'file, '_> {
    fn lookup_name(&self, name: Name) -> BaseLookup {
        let resolved = self.resolve_name_without_narrowing(name);
        self.point_resolution_to_base_lookup(resolved)
    }

    fn point_resolution_to_base_lookup(&self, resolved: PointResolution) -> BaseLookup {
        match resolved {
            PointResolution::NameDef {
                node_ref,
                global_redirect: _,
            } => return self.check_name_def(node_ref),
            PointResolution::Inferred(inferred) => {
                if let Some(specific) = inferred.maybe_saved_specific(self.i_s.db) {
                    return match specific {
                        Specific::TypingTypeVarClass
                        | Specific::TypingTypeVarTupleClass
                        | Specific::TypingParamSpecClass => BaseLookup::TypeVarLikeClass,
                        Specific::TypingGeneric | Specific::TypingProtocol => {
                            BaseLookup::GenericOrProtocol
                        }
                        Specific::TypingLiteral => BaseLookup::Literal,
                        _ => BaseLookup::Other,
                    };
                } else if let Some(complex) = inferred.maybe_complex_point(self.i_s.db) {
                    match complex {
                        ComplexPoint::TypeVarLike(tvl) => {
                            return BaseLookup::TypeVarLike(tvl.clone());
                        }
                        ComplexPoint::Class(_) => {
                            return BaseLookup::Class(inferred.maybe_saved_link().unwrap());
                        }
                        _ => (),
                    }
                }
                if let Some(file) = inferred.maybe_file(self.i_s.db) {
                    return BaseLookup::Module(file);
                }
            }
            _ => (),
        };
        BaseLookup::Other
    }

    fn check_name_def(self, node_ref: NodeRef) -> BaseLookup {
        if node_ref.file_index() != self.file.file_index {
            return self.with_new_file(node_ref.file).check_name_def(node_ref);
        }
        let name_def = node_ref.expect_name_def();
        match name_def.expect_type() {
            TypeLike::ClassDef(c) => {
                BaseLookup::Class(PointLink::new(node_ref.file_index(), c.index()))
            }
            TypeLike::Assignment(assignment) => {
                if node_ref.point().calculated() {
                    // This is essentially just a performance optimization to avoid looking
                    // up TypeVar each time.
                    fn follow_potential_inferred(node_ref: NodeRef) -> BaseLookup {
                        let p = node_ref.point();
                        if p.kind() == PointKind::Redirect {
                            if p.file_index() == node_ref.file_index() {
                                let new = NodeRef::new(node_ref.file, p.node_index());
                                follow_potential_inferred(new)
                            } else {
                                BaseLookup::Other
                            }
                        } else if let Some(ComplexPoint::TypeVarLike(tvl)) =
                            node_ref.maybe_complex()
                        {
                            BaseLookup::TypeVarLike(tvl.clone())
                        } else {
                            BaseLookup::Other
                        }
                    }
                    return follow_potential_inferred(node_ref);
                }
                if let Some((_, None, expr)) = assignment.maybe_simple_type_expression_assignment()
                    && self.is_type_var_like_execution(expr)
                {
                    // Now that we know that we have a Typevar-like execution, we can
                    // simply infer the statement and won't cause problems with cycles.
                    let inference = node_ref.file.inference(self.i_s);
                    let inf = inference.infer_name_of_definition(name_def.name());
                    if let Some(node_ref) = inf.maybe_saved_node_ref(self.i_s.db)
                        && let Some(ComplexPoint::TypeVarLike(tvl)) = node_ref.maybe_complex()
                    {
                        return BaseLookup::TypeVarLike(tvl.clone());
                    }
                }
                BaseLookup::Other
            }
            TypeLike::ImportFromAsName(from_as_name) => self.point_resolution_to_base_lookup(
                self.resolve_import_from_name_def_without_narrowing(from_as_name),
            ),
            TypeLike::DottedAsName(dotted_as_name) => self.point_resolution_to_base_lookup(
                self.resolve_import_name_name_def_without_narrowing(dotted_as_name),
            ),
            _ => BaseLookup::Other,
        }
    }

    fn lookup_primary_or_atom(&self, p: PrimaryOrAtom) -> BaseLookup {
        match p {
            PrimaryOrAtom::Primary(primary) => match primary.second() {
                PrimaryContent::Attribute(name) => {
                    match self.lookup_primary_or_atom(primary.first()) {
                        BaseLookup::Module(f) => {
                            let Some((pr, _link_to)) = self
                                .i_s
                                .db
                                .loaded_python_file(f)
                                .name_resolution_for_types(self.i_s)
                                .resolve_module_access(name.as_code(), |_| false)
                            else {
                                return BaseLookup::Other;
                            };
                            // TODO should we use link_to? Probably only if we add the issue
                            self.point_resolution_to_base_lookup(pr)
                        }
                        _ => BaseLookup::Other,
                    }
                }
                _ => BaseLookup::Other,
            },
            PrimaryOrAtom::Atom(atom) => match atom.unpack() {
                AtomContent::Name(n) => self.lookup_name(n),
                _ => BaseLookup::Other,
            },
        }
    }

    fn is_type_var_like_execution(&self, expr: Expression) -> bool {
        let ExpressionContent::ExpressionPart(ExpressionPart::Primary(primary)) = expr.unpack()
        else {
            return false;
        };
        let PrimaryContent::Execution(_) = primary.second() else {
            return false;
        };
        let node_ref = NodeRef::new(self.file, expr.index());
        let p = node_ref.point();
        if p.calculating() {
            return false;
        } else if !p.calculated() {
            // We need to set calculating here, otherwise the lookup below can recurse.
            node_ref.set_point(Point::new_calculating());
        }
        let result = self.lookup_primary_or_atom(primary.first()) == BaseLookup::TypeVarLikeClass;
        if !node_ref.point().calculated() {
            node_ref.set_point(Point::new_uncalculated());
        }
        result
    }
}
