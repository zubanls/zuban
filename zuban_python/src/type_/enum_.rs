use std::{cell::OnceCell, rc::Rc};

use parsa_python_ast::{
    AtomContent, CodeIndex, DictElement, Expression, ExpressionContent, ExpressionPart,
    StarLikeExpression, StarLikeExpressionIterator,
};

use super::{
    AnyCause, CallableLike, DbString, FormatStyle, Literal, LiteralKind, StringSlice, Type,
};
use crate::{
    arguments::{ArgumentKind, Arguments},
    database::{Database, ParentScope, PointLink},
    diagnostics::IssueType,
    file::File,
    inference_state::InferenceState,
    inferred::Inferred,
    matching::{FormatData, LookupKind, LookupResult, ResultContext},
    node_ref::NodeRef,
    type_helpers::{Class, Instance, TypeOrClass},
};

#[derive(Debug, PartialEq, Clone)]
pub struct EnumMember {
    pub enum_: Rc<Enum>,
    member_index: usize,
    pub(super) implicit: bool,
}

impl EnumMember {
    pub fn new(enum_: Rc<Enum>, member_index: usize, implicit: bool) -> Self {
        Self {
            enum_,
            member_index,
            implicit,
        }
    }

    pub fn name<'x>(&'x self, db: &'x Database) -> &'x str {
        self.enum_.members[self.member_index].name(db)
    }

    pub fn value(&self) -> Option<PointLink> {
        self.enum_.members[self.member_index].value
    }

    pub fn is_same_member(&self, other: &Self) -> bool {
        Rc::ptr_eq(&self.enum_, &other.enum_) && self.member_index == other.member_index
    }

    pub fn format(&self, format_data: &FormatData) -> String {
        let question_mark = match format_data.style {
            FormatStyle::MypyRevealType if self.implicit => "?",
            _ if self.implicit && format_data.hide_implicit_literals => {
                return self.enum_.format(format_data)
            }
            _ => "",
        };
        format!("Literal[{}]{question_mark}", self.format_inner(format_data))
    }

    pub fn format_inner(&self, format_data: &FormatData) -> String {
        format!(
            "{}.{}",
            &self.enum_.format(format_data),
            self.name(format_data.db)
        )
    }
}

#[derive(Debug, PartialEq, Clone)]
pub struct EnumMemberDefinition {
    name: DbString,
    pub value: Option<PointLink>,
}

impl EnumMemberDefinition {
    pub fn new(name: DbString, value: Option<PointLink>) -> Self {
        Self { name, value }
    }

    pub fn name<'x>(&'x self, db: &'x Database) -> &'x str {
        self.name.as_str(db)
    }
}

#[derive(Debug, PartialEq, Clone)]
pub struct Enum {
    pub name: DbString,
    pub class: PointLink,
    defined_at: PointLink,
    parent_scope: ParentScope,
    pub members: Box<[EnumMemberDefinition]>,
    has_customized_new: OnceCell<bool>,
}

impl Enum {
    pub fn new(
        name: DbString,
        class: PointLink,
        defined_at: PointLink,
        parent_scope: ParentScope,
        members: Box<[EnumMemberDefinition]>,
        has_customized_new: OnceCell<bool>,
    ) -> Rc<Self> {
        Rc::new(Self {
            name,
            defined_at,
            parent_scope,
            class,
            members,
            has_customized_new,
        })
    }

    pub fn class<'db>(&self, db: &'db Database) -> Class<'db> {
        Class::from_non_generic_link(db, self.class)
    }

    pub fn lookup(rc: &Rc<Enum>, db: &Database, name: &str, implicit: bool) -> Option<EnumMember> {
        for (index, member) in rc.members.iter().enumerate() {
            if name == member.name(db) {
                return Some(EnumMember::new(rc.clone(), index, implicit));
            }
        }
        None
    }

    pub fn has_customized_new(&self, i_s: &InferenceState) -> bool {
        *self
            .has_customized_new
            .get_or_init(|| self.class(i_s.db).has_customized_enum_new(i_s))
    }

    pub fn format(&self, format_data: &FormatData) -> String {
        let enum_name = self.name.as_str(format_data.db);
        match format_data.style {
            FormatStyle::Short if !format_data.verbose => enum_name.to_string(),
            _ => self.parent_scope.qualified_name(
                format_data.db,
                NodeRef::from_link(format_data.db, self.defined_at),
                enum_name,
            ),
        }
    }
}

pub fn lookup_on_enum_class(
    i_s: &InferenceState,
    from: NodeRef,
    enum_: &Rc<Enum>,
    name: &str,
    result_context: &mut ResultContext,
) -> LookupResult {
    match name {
        "_ignore_" => LookupResult::None,
        _ => lookup_members_on_enum(i_s, enum_, name, result_context).or_else(|| {
            enum_.class(i_s.db).lookup_with_custom_self_type(
                i_s,
                from,
                name,
                LookupKind::Normal,
                || Type::Type(Rc::new(Type::Enum(enum_.clone()))),
            )
        }),
    }
}

pub fn lookup_on_enum_instance(
    i_s: &InferenceState,
    add_issue: impl Fn(IssueType),
    enum_: &Rc<Enum>,
    name: &str,
    result_context: &mut ResultContext,
) -> LookupResult {
    match name {
        "value" | "_value_" => {
            LookupResult::UnknownName(Inferred::gather_simplified_union(i_s, |add| {
                for member in enum_.members.iter() {
                    add(infer_value_on_member(i_s, enum_, member.value))
                }
            }))
        }
        "_ignore_" => LookupResult::None,
        _ => lookup_members_on_enum(i_s, enum_, name, result_context)
            .or_else(|| lookup_on_enum_instance_fallback(i_s, add_issue, enum_, name)),
    }
}

fn lookup_on_enum_instance_fallback(
    i_s: &InferenceState,
    add_issue: impl Fn(IssueType),
    enum_: &Rc<Enum>,
    name: &str,
) -> LookupResult {
    Instance::new(enum_.class(i_s.db), None)
        .lookup_with_explicit_self_binding(i_s, add_issue, name, LookupKind::Normal, 0, || {
            Type::Enum(enum_.clone())
        })
        .1
}

pub fn infer_value_on_member(
    i_s: &InferenceState,
    enum_: &Enum,
    definition: Option<PointLink>,
) -> Inferred {
    match definition {
        // I'm not 100% sure why this is, but Mypy returns Any on all enums that have a __new__
        // defined.
        Some(link) if !enum_.has_customized_new(i_s) => {
            let node_ref = NodeRef::from_link(i_s.db, link);
            let inferred = if let Some(name) = node_ref.maybe_name() {
                node_ref
                    .file
                    .inference(&i_s.with_enum_calculation_mode())
                    .infer_name(name)
            } else {
                let expr = node_ref.as_expression();
                node_ref.file.inference(i_s).infer_expression(expr)
            };
            match inferred.as_cow_type(i_s).as_ref() {
                Type::Class(c) if c.link == i_s.db.python_state.enum_auto_link() => {
                    Inferred::from_type(
                        enum_
                            .class(i_s.db)
                            .lookup(i_s, node_ref, "_generate_next_value_", LookupKind::Normal)
                            .into_maybe_inferred()
                            .and_then(|inf| {
                                // Check We have a proper callable that is not part of the enum module
                                // and overwrites the default of int.
                                if inf.maybe_saved_link().is_some_and(|link| {
                                    link.file == i_s.db.python_state.enum_file().file_index()
                                }) {
                                    return None;
                                }
                                inf.as_cow_type(i_s).maybe_callable(i_s)
                            })
                            .map(|callable| match callable {
                                CallableLike::Callable(c) => c.return_type.clone(),
                                CallableLike::Overload(_) => todo!(),
                            })
                            .unwrap_or(i_s.db.python_state.int_type()),
                    )
                }
                _ => inferred,
            }
        }
        _ => Inferred::new_any(AnyCause::Todo),
    }
}

pub fn lookup_on_enum_member_instance(
    i_s: &InferenceState,
    add_issue: impl Fn(IssueType),
    member: &EnumMember,
    name: &str,
) -> LookupResult {
    let enum_class = member.enum_.class(i_s.db);
    let is_enum = enum_class.mro(i_s.db).any(|(_, base)| match base {
        TypeOrClass::Class(c) => c.node_ref == i_s.db.python_state.enum_node_ref(),
        _ => false,
    });
    // An enum cannot be an Enum, but just an instance of the EnumType metaclass. In that case
    // these specific hardcoded cases don't apply anymore.
    if is_enum {
        match name {
            "name" | "_name_" => {
                return LookupResult::UnknownName(Inferred::from_type(Type::Literal(Literal {
                    implicit: true,
                    kind: LiteralKind::String(DbString::RcStr(member.name(i_s.db).into())),
                })))
            }
            "value" | "_value_" => {
                let value = member.value();
                if value.is_none() {
                    let result = Instance::new(enum_class, None).type_lookup(i_s, add_issue, name);
                    if result.is_some() {
                        return result;
                    }
                }
                return LookupResult::UnknownName(infer_value_on_member(i_s, &member.enum_, value));
            }
            "_ignore_" => return LookupResult::None,
            _ => (),
        }
    }
    lookup_on_enum_instance_fallback(i_s, add_issue, &member.enum_, name)
}

fn lookup_members_on_enum(
    i_s: &InferenceState,
    enum_: &Rc<Enum>,
    name: &str,
    result_context: &mut ResultContext,
) -> LookupResult {
    match Enum::lookup(enum_, i_s.db, name, true) {
        Some(m) => LookupResult::UnknownName(Inferred::from_type(Type::EnumMember(m))),
        None => LookupResult::None,
    }
}

pub(crate) fn execute_functional_enum<'db>(
    i_s: &InferenceState<'db, '_>,
    class: Class,
    args: &dyn Arguments<'db>,
    result_context: &mut ResultContext,
) -> Option<Inferred> {
    let mut name_infos = None;
    let mut fields_infos = None;
    for arg in args.iter() {
        match arg.kind {
            ArgumentKind::Positional { node_ref, .. } => {
                let expr = node_ref.as_named_expression().expression();
                if name_infos.is_none() {
                    name_infos = Some((node_ref, arg.infer(i_s, &mut ResultContext::Unknown)));
                } else if fields_infos.is_none() {
                    fields_infos = Some((node_ref, expr));
                }
                // All the other arguments are not relevant here and were checked by checking
                // EnumMeta.__call__.
            }
            ArgumentKind::Keyword {
                key,
                node_ref,
                expression,
                ..
            } => match key {
                "value" => {
                    name_infos = Some((node_ref, arg.infer(i_s, &mut ResultContext::Unknown)))
                }
                "names" => fields_infos = Some((node_ref, expression)),
                // Keyword names were checked by checking EnumMeta.__call__
                _ => (),
            },
            _ => {
                args.add_issue(
                    i_s,
                    IssueType::EnumUnexpectedArguments {
                        name: class.name().into(),
                    },
                );
                return None;
            }
        }
    }
    let name_infos = name_infos.unwrap();
    let fields_infos = fields_infos.unwrap();

    let Type::Literal(Literal { kind: LiteralKind::String(name), .. }) = name_infos.1.as_type(i_s) else {
        name_infos.0.add_issue(i_s, IssueType::EnumFirstArgMustBeString);
        return None
    };

    let members =
        gather_functional_enum_members(i_s, class, &name, fields_infos.0, fields_infos.1)?;
    if members.len() == 0 {
        fields_infos.0.add_issue(
            i_s,
            IssueType::EnumNeedsAtLeastOneItem {
                name: class.name().into(),
            },
        );
        return None;
    }

    Some(Inferred::from_type(Type::Type(Rc::new(Type::Enum(
        Enum::new(
            name,
            class.node_ref.as_link(),
            args.as_node_ref().as_link(),
            i_s.parent_scope(),
            members,
            class.has_customized_enum_new(i_s).into(),
        ),
    )))))
}

#[derive(Default)]
struct EnumMembers(Vec<EnumMemberDefinition>);

impl EnumMembers {
    fn add_member(
        &mut self,
        i_s: &InferenceState,
        enum_name: &DbString,
        node_ref: NodeRef,
        d: EnumMemberDefinition,
    ) {
        let member_name = d.name(i_s.db);
        if self.0.iter().any(|t| t.name(i_s.db) == member_name) {
            node_ref.add_issue(
                i_s,
                IssueType::EnumReusedMemberName {
                    enum_name: enum_name.as_str(i_s.db).into(),
                    member_name: member_name.into(),
                },
            )
        } else {
            self.0.push(d)
        }
    }

    fn into_boxed_slice(self) -> Box<[EnumMemberDefinition]> {
        self.0.into()
    }
}

fn gather_functional_enum_members(
    i_s: &InferenceState,
    class: Class,
    enum_name: &DbString,
    node_ref: NodeRef,
    expression: Expression,
) -> Option<Box<[EnumMemberDefinition]>> {
    let ExpressionContent::ExpressionPart(ExpressionPart::Atom(atom)) = expression.unpack() else {
        node_ref.add_issue(i_s, IssueType::EnumInvalidSecondArgument);
        return None
    };

    let mut members = EnumMembers::default();

    let get_tuple_like = |mut iterator: StarLikeExpressionIterator| -> Option<StringSlice> {
        let Some(first) = iterator.next() else {
            todo!()
        };
        let Some(second) = iterator.next() else {
            todo!()
        };
        if iterator.next().is_some() {
            return None;
        }
        let StarLikeExpression::NamedExpression(n) = first else {
            todo!()
        };
        StringSlice::from_string_in_expression(node_ref.file.file_index(), n.expression())
    };

    let mut add_from_iterator = |iterator| -> Option<()> {
        for element in iterator {
            let StarLikeExpression::NamedExpression(ne) = element else {
                todo!()
            };
            let expression = ne.expression();
            let name = match expression.maybe_unpacked_atom() {
                // Enums can be defined like Enum("Foo", [('CYAN', 4), ('MAGENTA', 5)])
                Some(AtomContent::List(list)) => get_tuple_like(list.unpack())?,
                Some(AtomContent::Tuple(tup)) => get_tuple_like(tup.iter())?,
                _ => {
                    StringSlice::from_string_in_expression(node_ref.file.file_index(), expression)?
                }
            };
            members.add_member(
                i_s,
                enum_name,
                NodeRef::new(node_ref.file, expression.index()),
                EnumMemberDefinition::new(name.into(), None),
            )
        }
        Some(())
    };

    let mut add_from_iterator_with_error = |iterator| -> Option<()> {
        if add_from_iterator(iterator).is_none() {
            NodeRef::new(node_ref.file, atom.index()).add_issue(
                i_s,
                IssueType::EnumWithTupleOrListExpectsStringPairs {
                    name: class.name().into(),
                },
            );
            None
        } else {
            Some(())
        }
    };
    match atom.unpack() {
        AtomContent::List(list) => {
            add_from_iterator_with_error(list.unpack())?;
        }
        AtomContent::Tuple(tup) => {
            add_from_iterator_with_error(tup.iter())?;
        }
        AtomContent::Strings(s) => {
            match DbString::from_python_string(node_ref.file_index(), s.as_python_string()) {
                Some(s) => split_enum_members(
                    i_s,
                    enum_name,
                    NodeRef::new(node_ref.file, atom.index()),
                    &mut members,
                    &s,
                ),
                _ => todo!(),
            }
        }
        AtomContent::Dict(d) => {
            for element in d.iter_elements() {
                let DictElement::KeyValue(kv) = element else {
                    node_ref.add_issue(i_s, IssueType::EnumWithDictRequiresStringLiterals {
                        name: class.name().into(),
                    });
                    return None
                };
                let key = kv.key();
                let Some(name) = StringSlice::from_string_in_expression(
                    node_ref.file.file_index(),
                    key,
                ) else {
                    node_ref.add_issue(i_s, IssueType::EnumWithDictRequiresStringLiterals {
                        name: class.name().into(),
                    });
                    return None
                };
                members.add_member(
                    i_s,
                    enum_name,
                    NodeRef::new(node_ref.file, key.index()),
                    EnumMemberDefinition::new(
                        name.into(),
                        Some(PointLink::new(
                            node_ref.file.file_index(),
                            kv.value().index(),
                        )),
                    ),
                );
            }
        }
        _ => {
            let inf = node_ref
                .file
                .inference(i_s)
                .infer_atom(atom, &mut ResultContext::Unknown);
            if let Type::Literal(literal) = inf.as_cow_type(i_s).as_ref() {
                if let LiteralKind::String(s) = &literal.kind {
                    split_enum_members(
                        i_s,
                        enum_name,
                        NodeRef::new(node_ref.file, atom.index()),
                        &mut members,
                        s,
                    );
                    return Some(members.into_boxed_slice());
                }
            }
            node_ref.add_issue(i_s, IssueType::EnumInvalidSecondArgument);
            return None;
        }
    };
    Some(members.into_boxed_slice())
}

fn split_enum_members(
    i_s: &InferenceState,
    enum_name: &DbString,
    node_ref: NodeRef,
    members: &mut EnumMembers,
    s: &DbString,
) {
    let mut start = 0;
    for part in s.as_str(i_s.db).split(&[',', ' ']) {
        if part.is_empty() {
            start += 1;
            continue;
        }
        let name = match s {
            DbString::StringSlice(slice) => {
                let start = slice.start + start;
                StringSlice::new(slice.file_index, start, start + part.len() as CodeIndex).into()
            }
            _ => DbString::RcStr(part.into()),
        };
        members.add_member(
            i_s,
            enum_name,
            node_ref,
            EnumMemberDefinition::new(name, None),
        );
        start += part.len() as CodeIndex + 1;
    }
}
