use parsa_python_cst::*;

use super::type_computation::cache_name_on_class;
use crate::{
    database::{ComplexPoint, PointKind, PointLink, Specific},
    diagnostics::IssueKind,
    file::PythonFile,
    getitem::{SliceOrSimple, SliceType},
    inference_state::InferenceState,
    node_ref::NodeRef,
    type_::{TypeVarIndex, TypeVarLike, TypeVarLikes, TypeVarManager},
    type_helpers::Class,
};

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
    i_s: &'i_s InferenceState<'db, 'i_s>,
    file: &'file PythonFile,
    class: Option<&'c Class<'c>>,
    type_var_manager: TypeVarManager<PointLink>,
    generic_or_protocol_slice: Option<SliceType<'d>>,
    current_generic_or_protocol_index: Option<TypeVarIndex>,
    had_generic_or_protocol_issue: bool,
}

impl<'db, 'file: 'd, 'i_s, 'c, 'd> TypeVarFinder<'db, 'file, 'i_s, 'c, 'd> {
    pub fn find_class_type_vars(
        i_s: &'i_s InferenceState<'db, 'i_s>,
        class: &'c Class<'file>,
    ) -> TypeVarLikes {
        let mut finder = Self {
            i_s,
            file: class.node_ref.file,
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
        i_s: &'i_s InferenceState<'db, 'i_s>,
        file: &'file PythonFile,
        expr: Expression<'d>,
    ) -> TypeVarLikes {
        let mut finder = Self {
            i_s,
            file,
            class: None,
            type_var_manager: TypeVarManager::default(),
            generic_or_protocol_slice: None,
            current_generic_or_protocol_index: None,
            had_generic_or_protocol_issue: false,
        };
        finder.find_in_expr(expr);
        finder.type_var_manager.into_type_vars()
    }

    fn find_in_slice_like(&mut self, slice_like: SliceOrSimple<'d>) {
        match slice_like {
            SliceOrSimple::Simple(s) => self.find_in_expr(s.named_expr.expression()),
            SliceOrSimple::Slice(_) => (),
            SliceOrSimple::Starred(starred) => self.find_in_expr(starred.starred_expr.expression()),
        };
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
                        if let Some(link) = f.lookup_global(name.as_str()) {
                            self.file
                                .points
                                .set(name.index(), link.into_point_redirect());
                            self.find_in_name(name)
                        } else {
                            BaseLookup::Other
                        }
                    }
                    BaseLookup::Class(link) => {
                        let cls = Class::from_non_generic_link(self.i_s.db, link);
                        let point_kind = cache_name_on_class(cls, self.file, name);
                        if point_kind == PointKind::Redirect {
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
                let s = SliceType::new(self.file, primary.index(), slice_type);
                match base {
                    BaseLookup::Protocol | BaseLookup::Generic => {
                        if self.generic_or_protocol_slice.is_some() {
                            self.had_generic_or_protocol_issue = true;
                            NodeRef::new(self.file, primary.index())
                                .add_issue(self.i_s, IssueKind::EnsureSingleGenericOrProtocol);
                        }
                        self.generic_or_protocol_slice =
                            Some(SliceType::new(self.file, primary.index(), slice_type));
                        for (i, slice_like) in s.iter().enumerate() {
                            self.current_generic_or_protocol_index = Some(i.into());
                            self.find_in_slice_like(slice_like)
                        }
                        self.current_generic_or_protocol_index = None;
                    }
                    BaseLookup::Callable => self.find_in_callable(s),
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

    fn find_in_atom(&mut self, atom: Atom) -> BaseLookup<'db> {
        match atom.unpack() {
            AtomContent::Name(n) => {
                self.file.inference(self.i_s).infer_name_reference(n);
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
        let point = self.file.points.get(name.index());
        if point.calculated() && point.kind() == PointKind::Redirect {
            let node_ref = point.as_redirected_node_ref(self.i_s.db);
            return match follow_name(self.i_s, node_ref) {
                Ok(type_var_like) => {
                    if self
                        .class
                        .and_then(|c| c.maybe_type_var_like_in_parent(self.i_s.db, &type_var_like))
                        .is_none()
                    {
                        if let TypeVarLike::TypeVarTuple(t) = &type_var_like {
                            if self.type_var_manager.has_type_var_tuples() {
                                if self.class.is_some() {
                                    NodeRef::new(self.file, name.index()).add_issue(
                                        self.i_s,
                                        IssueKind::MultipleTypeVarTuplesInClassDef,
                                    );
                                }
                                return BaseLookup::Other;
                            }
                        }
                        let old_index = self.type_var_manager.add(type_var_like, None);
                        if let Some(force_index) = self.current_generic_or_protocol_index {
                            if old_index < force_index {
                                NodeRef::new(self.file, name.index())
                                    .add_issue(self.i_s, IssueKind::DuplicateTypeVar)
                            } else if old_index != force_index {
                                self.type_var_manager.move_index(old_index, force_index);
                            }
                        }
                    }
                    BaseLookup::Other
                }
                Err(lookup) => lookup,
            };
        }
        BaseLookup::Other
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
            slice_type
                .as_node_ref()
                .add_issue(self.i_s, IssueKind::IncompleteGenericOrProtocolTypeVars)
        }
    }
}

fn follow_name<'db>(
    i_s: &InferenceState<'db, '_>,
    node_ref: NodeRef<'db>,
) -> Result<TypeVarLike, BaseLookup<'db>> {
    let p = node_ref.point();
    if p.calculated() {
        if let Some(specific) = p.maybe_specific() {
            match specific {
                Specific::TypingGeneric => return Err(BaseLookup::Generic),
                Specific::TypingProtocol => return Err(BaseLookup::Protocol),
                Specific::TypingCallable => return Err(BaseLookup::Callable),
                Specific::NameOfNameDef => (),
                _ => return Err(BaseLookup::Other),
            }
        }
    }
    if let Some(name) = node_ref.maybe_name() {
        match name.expect_type() {
            TypeLike::ClassDef(c) => {
                let name_def_node_ref =
                    NodeRef::new(node_ref.file, name.name_def().unwrap().index());
                return Err(BaseLookup::Class(PointLink::new(
                    node_ref.file_index(),
                    c.index(),
                )));
            }
            TypeLike::Assignment(assignment) => {
                let inference = node_ref.file.inference(i_s);
                let inf = inference.infer_name_of_definition(name);
                if let Some(node_ref) = inf.maybe_saved_node_ref(i_s.db) {
                    if let Some(ComplexPoint::TypeVarLike(tvl)) = node_ref.complex() {
                        return Ok(tvl.clone());
                    }
                }
            }
            TypeLike::ImportFromAsName(import_from_as_name) => {
                // TODO this can probably still recurses with module __getattr__
                /*
                node_ref
                    .file
                    .inference(i_s)
                    .cache_import_from(import_from_as_name.import_from());
                */
                let p = node_ref
                    .add_to_node_index(-(NAME_DEF_TO_NAME_DIFFERENCE as i64))
                    .point();
                if p.calculated() && p.kind() == PointKind::Redirect {
                    let new = p.as_redirected_node_ref(i_s.db);
                    if new.maybe_name().is_some() {
                        return follow_name(i_s, new);
                    }
                }
            }
            TypeLike::DottedAsName(d) => {
                let p = node_ref
                    .add_to_node_index(-(NAME_DEF_TO_NAME_DIFFERENCE as i64))
                    .point();
                if p.calculated() {
                    if p.kind() == PointKind::Redirect {
                        let new = p.as_redirected_node_ref(i_s.db);
                        if new.maybe_name().is_some() {
                            return follow_name(i_s, new);
                        }
                    } else if p.kind() == PointKind::FileReference {
                        let file = i_s.db.loaded_python_file(p.file_index());
                        return Err(BaseLookup::Module(file));
                    }
                }
            }
            _ => (),
        }
    }
    Err(BaseLookup::Other)
}
