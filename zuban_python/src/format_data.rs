use crate::{
    database::{Database, PointLink},
    matching::{Matcher, MatcherFormatResult},
    type_::{
        FormatStyle, ParamSpecUsage, RecursiveType, RecursiveTypeOrigin, Type, TypeVarLikeUsage,
        TypeVarTupleUsage, TypeVarUsage,
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

#[derive(Debug)]
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
        match self.format_internal(
            &TypeVarLikeUsage::TypeVar(usage.clone()),
            ParamsStyle::Unreachable,
        ) {
            MatcherFormatResult::Str(s) => s,
            MatcherFormatResult::TypeVarTupleUnknown => unreachable!(),
        }
    }

    pub fn format_type_var_tuple(&self, usage: &TypeVarTupleUsage) -> Option<Box<str>> {
        match self.format_internal(
            &TypeVarLikeUsage::TypeVarTuple(usage.clone()),
            ParamsStyle::Unreachable,
        ) {
            MatcherFormatResult::Str(s) => Some(s),
            MatcherFormatResult::TypeVarTupleUnknown => None,
        }
    }

    pub fn format_param_spec(&self, usage: &ParamSpecUsage, style: ParamsStyle) -> Box<str> {
        match self.format_internal(&TypeVarLikeUsage::ParamSpec(usage.clone()), style) {
            MatcherFormatResult::Str(s) => s,
            MatcherFormatResult::TypeVarTupleUnknown => unreachable!(),
        }
    }

    fn format_internal(
        &self,
        type_var_usage: &TypeVarLikeUsage,
        params_style: ParamsStyle,
    ) -> MatcherFormatResult {
        if let Some(matcher) = self.matcher {
            return matcher.format(type_var_usage, self, params_style);
        }
        MatcherFormatResult::Str(type_var_usage.format_without_matcher(self.db, params_style))
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
                | Type::NewType(_) => {
                    let Some((s2, link2)) = short_type_name_with_link(db, t) else {
                        return false;
                    };
                    if !types_with_same_names.contains(&link2) {
                        for seen_type in seen_types.iter() {
                            let (s1, link1) = short_type_name_with_link(db, seen_type).unwrap();
                            if s1 == s2 && link1 != link2 {
                                types_with_same_names.push(link1);
                                types_with_same_names.push(link2);
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

fn short_type_name_with_link<'x>(db: &'x Database, t: &'x Type) -> Option<(&'x str, PointLink)> {
    Some(match t {
        Type::Class(c) => (c.class(db).name(), c.link),
        Type::RecursiveType(rec) => (
            match rec.origin(db) {
                RecursiveTypeOrigin::TypeAlias(alias) => alias.name(db).unwrap_or_else(|| todo!()),
                RecursiveTypeOrigin::Class(c) => c.name(),
            },
            rec.link,
        ),
        Type::NamedTuple(n) => (n.name.as_str(db), n.__new__.defined_at),
        Type::TypedDict(td) => (td.name?.as_str(db), td.defined_at),
        Type::Enum(e) => (e.name.as_str(db), e.defined_at),
        Type::EnumMember(m) => (m.enum_.name.as_str(db), m.enum_.defined_at),
        Type::NewType(n) => (n.name(db), n.name_string),
        _ => unreachable!(),
    })
}
