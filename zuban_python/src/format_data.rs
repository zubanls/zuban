use crate::{
    database::{Database, PointLink},
    matching::{Matcher, MatcherFormatResult},
    node_ref::NodeRef,
    type_::{
        FormatStyle, ParamSpecUsage, RecursiveType, RecursiveTypeOrigin, Type, TypeVarLikeUsage,
        TypeVarName, TypeVarTupleUsage, TypeVarUsage,
    },
    utils::AlreadySeen,
};

#[derive(Clone, Copy, Debug, PartialEq)]
pub enum AvoidRecursionFor<'a> {
    RecursiveType(&'a RecursiveType),
    TypedDict(PointLink),
    NamedTuple(PointLink),
}

type DisplayedRecursive<'a> = AlreadySeen<'a, AvoidRecursionFor<'a>>;

#[derive(Clone, Copy)]
pub enum ParamsStyle {
    CallableParamsInner,
    CallableParams,
    Unreachable,
}

#[derive(Debug, Clone, Copy)]
pub struct FormatData<'db, 'a, 'b, 'c> {
    pub db: &'db Database,
    pub matcher: Option<&'b Matcher<'a>>,
    pub style: FormatStyle,
    pub verbose: bool,
    pub hide_implicit_literals: bool,
    types_that_need_qualified_names: &'a [PointLink],
    displayed_recursive: Option<DisplayedRecursive<'c>>,
}

impl<'db, 'a, 'b, 'c> FormatData<'db, 'a, 'b, 'c> {
    pub fn new_short(db: &'db Database) -> Self {
        Self {
            db,
            matcher: None,
            style: FormatStyle::Short,
            verbose: false,
            hide_implicit_literals: true,
            displayed_recursive: None,
            types_that_need_qualified_names: &[],
        }
    }

    pub fn with_types_that_need_qualified_names(
        db: &'db Database,
        types_that_need_qualified_names: &'a [PointLink],
    ) -> Self {
        Self {
            types_that_need_qualified_names,
            ..Self::new_short(db)
        }
    }

    pub fn new_reveal_type(db: &'db Database) -> Self {
        Self {
            style: FormatStyle::MypyRevealType,
            ..Self::new_short(db)
        }
    }

    pub fn with_matcher(
        db: &'db Database,
        matcher: &'b Matcher<'a>,
        types_that_need_qualified_names: &'a [PointLink],
    ) -> Self {
        Self {
            matcher: Some(matcher),
            types_that_need_qualified_names,
            ..Self::new_short(db)
        }
    }

    pub fn with_seen_recursive_type<'x: 'c>(
        &'x self,
        rec: AvoidRecursionFor<'x>,
    ) -> Result<FormatData<'db, 'a, 'b, 'x>, ()> {
        let displayed_recursive = DisplayedRecursive {
            current: rec,
            previous: self.displayed_recursive.as_ref(),
        };
        if displayed_recursive.is_cycle() {
            Err(())
        } else {
            Ok(Self {
                db: self.db,
                matcher: self.matcher,
                style: self.style,
                verbose: self.verbose,
                hide_implicit_literals: self.hide_implicit_literals,
                displayed_recursive: Some(displayed_recursive),
                types_that_need_qualified_names: self.types_that_need_qualified_names,
            })
        }
    }

    pub fn remove_matcher<'x: 'c>(&'x self) -> Self {
        Self {
            db: self.db,
            matcher: None,
            style: self.style,
            verbose: self.verbose,
            hide_implicit_literals: self.hide_implicit_literals,
            displayed_recursive: self.displayed_recursive,
            types_that_need_qualified_names: self.types_that_need_qualified_names,
        }
    }

    pub fn enable_verbose(&mut self) {
        self.verbose = true;
    }

    pub fn should_format_qualified(&self, link: PointLink) -> bool {
        self.types_that_need_qualified_names.contains(&link)
    }

    pub fn format_type_var(&self, usage: &TypeVarUsage) -> Box<str> {
        match self.format_type_var_like(
            &TypeVarLikeUsage::TypeVar(usage.clone()),
            ParamsStyle::Unreachable,
        ) {
            MatcherFormatResult::Str(s) => s,
            MatcherFormatResult::TypeVarTupleUnknown => unreachable!(),
        }
    }

    pub fn format_type_var_tuple(&self, usage: &TypeVarTupleUsage) -> Option<Box<str>> {
        match self.format_type_var_like(
            &TypeVarLikeUsage::TypeVarTuple(usage.clone()),
            ParamsStyle::Unreachable,
        ) {
            MatcherFormatResult::Str(s) => Some(s),
            MatcherFormatResult::TypeVarTupleUnknown => None,
        }
    }

    pub fn format_param_spec(&self, usage: &ParamSpecUsage, style: ParamsStyle) -> Box<str> {
        match self.format_type_var_like(&TypeVarLikeUsage::ParamSpec(usage.clone()), style) {
            MatcherFormatResult::Str(s) => s,
            MatcherFormatResult::TypeVarTupleUnknown => unreachable!(),
        }
    }

    pub fn format_type_var_like(
        &self,
        type_var_usage: &TypeVarLikeUsage,
        params_style: ParamsStyle,
    ) -> MatcherFormatResult {
        if let Some(matcher) = self.matcher {
            return matcher.format(type_var_usage, self, params_style);
        }
        let mut s = type_var_usage.format_without_matcher(self.db, params_style);
        if type_var_usage
            .name_definition()
            .is_some_and(|link| self.should_format_qualified(link))
        {
            if let Some(func) =
                NodeRef::from_link(self.db, type_var_usage.in_definition()).maybe_function()
            {
                s += "@";
                s += func.name().as_code();
            }
        }
        MatcherFormatResult::Str(s.into())
    }
}

pub fn find_similar_types(db: &Database, types: &[&Type]) -> Vec<PointLink> {
    // Mypy calls this `mypy.messages.find_type_overlaps`
    let mut seen_types = vec![];
    let mut types_with_same_names = vec![];
    for t in types {
        t.find_in_type(db, &mut |t| {
            match t {
                Type::Class(_)
                | Type::RecursiveType(_)
                | Type::NamedTuple(_)
                | Type::TypedDict(_)
                | Type::Enum(_)
                | Type::EnumMember(_)
                | Type::TypeVar(_)
                | Type::NewType(_) => {
                    let Some(name_infos2) = short_type_name_with_link(db, t) else {
                        return false;
                    };
                    if !types_with_same_names.contains(&name_infos2.name_link) {
                        for seen_type in seen_types.iter() {
                            let name_infos1 = short_type_name_with_link(db, seen_type).unwrap();
                            if name_infos1.name == name_infos2.name
                                && name_infos1.name_unique_for != name_infos2.name_unique_for
                            {
                                types_with_same_names.push(name_infos2.name_link);
                                if name_infos1.name_link != name_infos2.name_link {
                                    types_with_same_names.push(name_infos1.name_link);
                                }
                                return false;
                            }
                        }
                        seen_types.push(t.clone());
                    }
                }
                _ => (),
            };
            false
        });
    }
    types_with_same_names
}

struct NameInfos<'x> {
    name: &'x str,
    name_unique_for: PointLink,
    name_link: PointLink,
}

impl<'x> NameInfos<'x> {
    fn new(name: &'x str, link: PointLink) -> Self {
        Self {
            name,
            name_unique_for: link,
            name_link: link,
        }
    }
}

fn short_type_name_with_link<'x>(db: &'x Database, t: &'x Type) -> Option<NameInfos<'x>> {
    Some(match t {
        Type::Class(c) => NameInfos::new(c.class(db).name(), c.link),
        Type::RecursiveType(rec) => NameInfos::new(
            match rec.origin(db) {
                RecursiveTypeOrigin::TypeAlias(alias) => alias.name(db)?,
                RecursiveTypeOrigin::Class(c) => c.name(),
            },
            rec.link,
        ),
        Type::NamedTuple(n) => NameInfos::new(n.name.as_str(db), n.__new__.defined_at),
        Type::TypedDict(td) => NameInfos::new(td.name?.as_str(db), td.defined_at),
        Type::Enum(e) => NameInfos::new(e.name.as_str(db), e.defined_at),
        Type::EnumMember(m) => NameInfos::new(m.enum_.name.as_str(db), m.enum_.defined_at),
        Type::NewType(n) => NameInfos::new(n.name(db), n.name_string),
        Type::TypeVar(tv) => match tv.type_var.name_string {
            TypeVarName::PointLink(link) => NameInfos {
                name: tv.type_var.name(db),
                name_unique_for: tv.in_definition,
                name_link: link,
            },
            TypeVarName::Self_ => return None,
        },
        _ => unreachable!(),
    })
}
