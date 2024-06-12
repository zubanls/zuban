use std::{cell::OnceCell, rc::Rc};

use parsa_python_cst::{
    AtomContent, CodeIndex, DictElement, Expression, StarLikeExpression, StarLikeExpressionIterator,
};

use super::{
    AnyCause, CallableLike, DbString, FormatStyle, Literal, LiteralKind, StringSlice, Type,
};
use crate::{
    arguments::{ArgKind, Args},
    database::{Database, ParentScope, PointLink},
    diagnostics::IssueKind,
    file::File,
    format_data::FormatData,
    inference_state::InferenceState,
    inferred::{AttributeKind, Inferred},
    matching::{LookupKind, LookupResult, ResultContext},
    node_ref::NodeRef,
    type_helpers::{Class, ClassLookupOptions, Instance, LookupDetails, TypeOrClass},
};

#[derive(Debug, PartialEq, Clone)]
pub struct EnumMember {
    pub enum_: Rc<Enum>,
    pub member_index: usize,
    pub implicit: bool,
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
    pub defined_at: PointLink,
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

pub(crate) fn lookup_on_enum_class<'a>(
    i_s: &InferenceState<'a, '_>,
    add_issue: impl Fn(IssueKind),
    enum_: &Rc<Enum>,
    name: &str,
    result_context: &mut ResultContext,
) -> LookupDetails<'a> {
    match name {
        "_ignore_" | "_order_" | "__order__" => LookupDetails::none(),
        _ => LookupDetails::new(
            Type::Enum(enum_.clone()),
            lookup_members_on_enum(i_s, enum_, name, result_context),
            AttributeKind::Attribute,
        )
        .or_else(|| {
            enum_.class(i_s.db).lookup(
                i_s,
                name,
                ClassLookupOptions::new(&add_issue)
                    .with_as_type_type(&|| Type::Type(Rc::new(Type::Enum(enum_.clone())))),
            )
        }),
    }
}

pub(crate) fn lookup_on_enum_instance<'a>(
    i_s: &'a InferenceState,
    add_issue: impl Fn(IssueKind),
    enum_: &'a Rc<Enum>,
    name: &str,
    result_context: &mut ResultContext,
) -> LookupDetails<'a> {
    match name {
        "value" | "_value_" => LookupDetails::new(
            Type::Enum(enum_.clone()),
            LookupResult::UnknownName(Inferred::gather_simplified_union(i_s, |add| {
                for member in enum_.members.iter() {
                    add(infer_value_on_member(i_s, enum_, member.value))
                }
            })),
            AttributeKind::Attribute,
        ),
        "_ignore_" => LookupDetails::none(),
        _ => {
            let lookup = lookup_members_on_enum(i_s, enum_, name, result_context);
            if lookup.is_some() {
                LookupDetails::new(Type::Enum(enum_.clone()), lookup, AttributeKind::Attribute)
            } else {
                lookup_on_enum_instance_fallback(i_s, add_issue, enum_, name)
            }
        }
    }
}

fn lookup_on_enum_instance_fallback<'a>(
    i_s: &'a InferenceState,
    add_issue: impl Fn(IssueKind),
    enum_: &'a Rc<Enum>,
    name: &str,
) -> LookupDetails<'a> {
    Instance::new(enum_.class(i_s.db), None).lookup_with_explicit_self_binding(
        i_s,
        &add_issue,
        name,
        LookupKind::Normal,
        0,
        || Type::Enum(enum_.clone()),
    )
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
            let enum_class = enum_.class(i_s.db);
            let class_i_s = &i_s.with_class_context(&enum_class);
            let inferred = if let Some(name) = node_ref.maybe_name() {
                node_ref
                    .file
                    .inference(&class_i_s.with_enum_calculation_mode())
                    .infer_name_of_definition(name)
            } else {
                let expr = node_ref.as_expression();
                node_ref.file.inference(class_i_s).infer_expression(expr)
            };
            match inferred.as_cow_type(&class_i_s).as_ref() {
                Type::Class(c) if c.link == i_s.db.python_state.enum_auto_link() => {
                    Inferred::from_type(
                        enum_class
                            .simple_lookup(
                                i_s,
                                |issue| node_ref.add_issue(i_s, issue),
                                "_generate_next_value_",
                            )
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

pub(crate) fn lookup_on_enum_member_instance<'a>(
    i_s: &'a InferenceState,
    add_issue: impl Fn(IssueKind),
    member: &'a EnumMember,
    name: &str,
) -> LookupDetails<'a> {
    let enum_class = member.enum_.class(i_s.db);
    enum_class.use_cached_class_infos(i_s.db);
    let is_enum = enum_class.mro(i_s.db).any(|(_, base)| match base {
        TypeOrClass::Class(c) => c.node_ref == i_s.db.python_state.enum_node_ref(),
        _ => false,
    });
    // An enum cannot be an Enum, but just an instance of the EnumType metaclass. In that case
    // these specific hardcoded cases don't apply anymore.
    if is_enum {
        match name {
            "name" | "_name_" => {
                return LookupDetails::new(
                    Type::Enum(member.enum_.clone()),
                    LookupResult::UnknownName(Inferred::from_type(Type::Literal(Literal {
                        implicit: true,
                        kind: LiteralKind::String(DbString::RcStr(member.name(i_s.db).into())),
                    }))),
                    AttributeKind::Attribute,
                )
            }
            "value" | "_value_" => {
                let value = member.value();
                if value.is_none() {
                    let result = Instance::new(enum_class, None).lookup_with_details(
                        i_s,
                        add_issue,
                        name,
                        LookupKind::OnlyType,
                    );
                    if result.lookup.is_some() {
                        return result;
                    }
                }
                return LookupDetails::new(
                    Type::Enum(member.enum_.clone()),
                    LookupResult::UnknownName(infer_value_on_member(i_s, &member.enum_, value)),
                    AttributeKind::DefMethod,
                );
            }
            "_ignore_" => return LookupDetails::none(),
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
    args: &dyn Args<'db>,
    result_context: &mut ResultContext,
) -> Option<Inferred> {
    let mut name_infos = None;
    let mut fields_infos = None;
    for arg in args.iter() {
        match arg.kind {
            ArgKind::Positional(positional) => {
                let expr = positional.node_ref.as_named_expression().expression();
                if name_infos.is_none() {
                    name_infos = Some((
                        positional.node_ref,
                        positional.infer(i_s, &mut ResultContext::Unknown),
                        expr.in_simple_assignment(),
                    ));
                } else if fields_infos.is_none() {
                    fields_infos = Some((positional.node_ref, expr));
                }
                // All the other arguments are not relevant here and were checked by checking
                // EnumMeta.__call__.
            }
            ArgKind::Keyword(kw) => match kw.key {
                "value" => {
                    name_infos = Some((
                        kw.node_ref,
                        kw.infer(i_s, &mut ResultContext::Unknown),
                        kw.expression.in_simple_assignment(),
                    ))
                }
                "names" => fields_infos = Some((kw.node_ref, kw.expression)),
                // Keyword names were checked by checking EnumMeta.__call__
                _ => (),
            },
            _ => {
                args.add_issue(
                    i_s,
                    IssueKind::EnumUnexpectedArguments {
                        name: class.name().into(),
                    },
                );
                return None;
            }
        }
    }
    let name_infos = name_infos.unwrap();
    let fields_infos = fields_infos.unwrap();

    let Type::Literal(Literal {
        kind: LiteralKind::String(name),
        ..
    }) = name_infos.1.as_type(i_s)
    else {
        name_infos
            .0
            .add_issue(i_s, IssueKind::EnumFirstArgMustBeString);
        return None;
    };
    if let Some(name_def) = name_infos.2 {
        let n = name.as_str(i_s.db);
        if name_def.as_code() != n {
            name_infos.0.add_issue(
                i_s,
                IssueKind::VarNameMismatch {
                    class_name: class.qualified_name(i_s.db).into(),
                    string_name: Box::from(n),
                    variable_name: Box::from(name_def.as_code()),
                },
            );
        }
    }

    let members =
        gather_functional_enum_members(i_s, class, &name, fields_infos.0, fields_infos.1)?;
    if members.len() == 0 {
        fields_infos.0.add_issue(
            i_s,
            IssueKind::EnumNeedsAtLeastOneItem {
                name: class.name().into(),
            },
        );
        return None;
    }

    Some(Inferred::from_type(Type::Type(Rc::new(Type::Enum(
        Enum::new(
            name,
            class.node_ref.as_link(),
            name_infos.0.as_link(),
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
        from: NodeRef,
        d: EnumMemberDefinition,
    ) {
        let member_name = d.name(i_s.db);
        if self.0.iter().any(|t| t.name(i_s.db) == member_name) {
            from.add_issue(
                i_s,
                IssueKind::EnumReusedMemberName {
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
            NodeRef::new(node_ref.file, expression.index()).add_issue(
                i_s,
                IssueKind::EnumWithTupleOrListExpectsStringPairs {
                    name: class.name().into(),
                },
            );
            None
        } else {
            Some(())
        }
    };

    match expression.maybe_unpacked_atom() {
        Some(AtomContent::List(list)) => {
            add_from_iterator_with_error(list.unpack())?;
        }
        Some(AtomContent::Tuple(tup)) => {
            add_from_iterator_with_error(tup.iter())?;
        }
        Some(AtomContent::Strings(s)) => {
            match DbString::from_python_string(node_ref.file_index(), s.as_python_string()) {
                Some(s) => split_enum_members(
                    i_s,
                    enum_name,
                    NodeRef::new(node_ref.file, expression.index()),
                    &mut members,
                    &s,
                ),
                _ => todo!(),
            }
        }
        Some(AtomContent::Dict(d)) => {
            for element in d.iter_elements() {
                let DictElement::KeyValue(kv) = element else {
                    node_ref.add_issue(
                        i_s,
                        IssueKind::EnumWithDictRequiresStringLiterals {
                            name: class.name().into(),
                        },
                    );
                    return None;
                };
                let key = kv.key();
                let Some(name) =
                    StringSlice::from_string_in_expression(node_ref.file.file_index(), key)
                else {
                    node_ref.add_issue(
                        i_s,
                        IssueKind::EnumWithDictRequiresStringLiterals {
                            name: class.name().into(),
                        },
                    );
                    return None;
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
            let inf = node_ref.file.inference(i_s).infer_expression(expression);
            if let Type::Literal(literal) = inf.as_cow_type(i_s).as_ref() {
                if let LiteralKind::String(s) = &literal.kind {
                    split_enum_members(
                        i_s,
                        enum_name,
                        NodeRef::new(node_ref.file, expression.index()),
                        &mut members,
                        s,
                    );
                    return Some(members.into_boxed_slice());
                }
            }
            node_ref.add_issue(i_s, IssueKind::EnumInvalidSecondArgument);
            return None;
        }
    };
    Some(members.into_boxed_slice())
}

fn split_enum_members(
    i_s: &InferenceState,
    enum_name: &DbString,
    from: NodeRef,
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
        members.add_member(i_s, enum_name, from, EnumMemberDefinition::new(name, None));
        start += part.len() as CodeIndex + 1;
    }
}
