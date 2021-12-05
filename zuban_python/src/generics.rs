use parsa_python_ast::{
    Expression, ExpressionContent, NameParent, NodeIndex, SliceIterator, SliceType, Slices,
    SlicesContent,
};

use crate::arguments::Arguments;
use crate::database::{
    GenericPart, GenericsList, Locality, Point, PointLink, Specific, TypeVarIndex,
};
use crate::file::PythonFile;
use crate::inference_state::InferenceState;
use crate::inferred::{Inferrable, Inferred};
use crate::value::Function;

#[derive(Debug, Clone)]
pub enum Generics<'db, 'a> {
    Expression(&'db PythonFile, Expression<'db>),
    Slices(&'db PythonFile, Slices<'db>),
    List(&'a GenericsList),
    None,
}

impl<'db, 'a> Generics<'db, 'a> {
    pub fn new_slice(file: &'db PythonFile, slice_type: SliceType<'db>) -> Self {
        match slice_type {
            SliceType::NamedExpression(named) => Self::Expression(file, named.expression()),
            SliceType::Slice(_) => Self::None,
            SliceType::Slices(slices) => Self::Slices(file, slices),
        }
    }

    pub fn nth(&self, i_s: &mut InferenceState<'db, '_>, n: TypeVarIndex) -> Option<Inferred<'db>> {
        match self {
            Self::Expression(file, expr) => {
                if n.is_zero() {
                    Some(file.inference(i_s).infer_annotation_expression(*expr))
                } else {
                    None
                }
            }
            Self::Slices(file, slices) => todo!(),
            Self::List(l) => l.nth(n).map(|g| {
                Inferred::from_generic_class(i_s.database, g).execute_annotation_class(i_s)
            }),
            Self::None => None,
        }
    }

    pub fn iter(&self) -> GenericsIterator<'db, 'a> {
        match self {
            Self::Expression(file, expr) => GenericsIterator::Expression(file, *expr),
            Self::Slices(file, slices) => GenericsIterator::SliceIterator(file, slices.iter()),
            Self::List(l) => GenericsIterator::GenericsList(l.iter()),
            Self::None => GenericsIterator::None,
        }
    }

    pub fn as_generics_list(&self, i_s: &mut InferenceState<'db, '_>) -> Option<GenericsList> {
        match self {
            Self::Expression(file, expr) => {
                todo!()
            }
            Self::Slices(file, slices) => {
                todo!()
            }
            Self::List(_) => {
                todo!()
            }
            Self::None => None,
        }
    }

    pub fn as_str(&self, i_s: &mut InferenceState<'db, '_>) -> String {
        // Returns something like [str] or [List[int], Set[Any]]
        let mut iterator = self.iter();
        let mut strings = vec![];
        while let Some(inf) = iterator.next(i_s) {
            strings.push(inf.internal_run(
                i_s,
                &mut |i_s, v| {
                    v.as_class()
                        .map(|c| c.as_str(i_s))
                        .unwrap_or_else(|| "Unknown".to_owned())
                },
                &|i1, i2| format!("{}|{}", i1, i2),
                &mut |inferred| "Unknown".to_owned(),
            ));
        }
        format!("[{}]", strings.join(", "))
    }
}

pub enum GenericsIterator<'db, 'a> {
    SliceIterator(&'db PythonFile, SliceIterator<'db>),
    GenericsList(std::slice::Iter<'a, GenericPart>),
    Expression(&'db PythonFile, Expression<'db>),
    None,
}

impl<'db> GenericsIterator<'db, '_> {
    pub fn next(&mut self, i_s: &mut InferenceState<'db, '_>) -> Option<Inferred<'db>> {
        match self {
            Self::Expression(file, expr) => {
                let result = file.inference(i_s).infer_expression(*expr);
                *self = GenericsIterator::None;
                Some(result)
            }
            Self::SliceIterator(file, iter) => {
                if let Some(SlicesContent::NamedExpression(s)) = iter.next() {
                    Some(file.inference(i_s).infer_named_expression(s))
                } else {
                    None
                }
            }
            Self::GenericsList(iterator) => iterator
                .next()
                .map(|g| Inferred::from_generic_class(i_s.database, g)),
            GenericsIterator::None => None,
        }
    }
}

pub struct TypeVarMatcher<'db, 'a> {
    function: &'a Function<'db>,
    args: &'a dyn Arguments<'db>,
    skip_first: bool,
    pub calculated_type_vars: Option<GenericsList>,
    matches: bool,
    type_vars: Option<&'a [PointLink]>,
    match_specific: Specific,
}

impl<'db, 'a> TypeVarMatcher<'db, 'a> {
    pub fn new(
        function: &'a Function<'db>,
        args: &'a dyn Arguments<'db>,
        skip_first: bool,
        type_vars: Option<&'a [PointLink]>,
        match_specific: Specific,
    ) -> Self {
        Self {
            function,
            args,
            calculated_type_vars: None,
            skip_first,
            matches: true,
            type_vars,
            match_specific,
        }
    }
    // TODO the structure of this impl looks very weird, strange funcs

    pub fn calculate_and_return(
        i_s: &mut InferenceState<'db, '_>,
        function: &'a Function<'db>,
        args: &'a dyn Arguments<'db>,
        skip_first: bool,
        type_vars: Option<&'db [PointLink]>,
        match_specific: Specific,
    ) -> Option<GenericsList> {
        let mut self_ = Self::new(function, args, skip_first, type_vars, match_specific);
        self_.calculate_type_vars(i_s);
        self_.calculated_type_vars
    }

    fn calculate_type_vars(&mut self, i_s: &mut InferenceState<'db, '_>) {
        // TODO this can be calculated multiple times from different places
        if let Some(type_vars) = self.type_vars {
            if !type_vars.is_empty() {
                self.calculated_type_vars = Some(GenericsList::new_unknown(type_vars.len()));
            }
        }
        self.function.calculated_type_vars(i_s, self.args);
        let mut iter = self
            .function
            .iter_inferrable_params(self.args, self.skip_first);
        while let Some(p) = iter.next() {
            if let Some(annotation) = p.param.annotation() {
                if let ExpressionContent::ExpressionPart(part) = annotation.expression().unpack() {
                    let inferred = self
                        .function
                        .reference
                        .file
                        .inference(i_s)
                        .infer_annotation_expression(annotation.expression());
                    if let Some(point) = inferred.maybe_numbered_type_var() {
                        let generic = p.infer(i_s).as_generic_part(i_s);
                        self.add_type_var_class(i_s, point, generic);
                    } else {
                        let mut maybe_matches = true;
                        inferred.run(
                            i_s,
                            &mut |i_s, v| {
                                let value = p.infer(i_s);
                                v.class(i_s).infer_type_vars(i_s, value, self);
                            },
                            || maybe_matches = false,
                        );
                        self.matches &= maybe_matches;
                    }
                } else {
                    self.matches = false;
                }
            } else if !p.has_argument() {
                self.matches = false;
            }
        }
        if iter.has_unused_argument() {
            self.matches = false
        }
    }

    pub fn nth(&mut self, i_s: &mut InferenceState<'db, '_>, index: TypeVarIndex) -> Inferred<'db> {
        if let Some(type_vars) = &self.calculated_type_vars {
            self.calculated_type_vars
                .as_ref()
                .unwrap()
                .nth(index)
                .map(|g| Inferred::from_generic_class(i_s.database, g))
                .unwrap_or_else(|| todo!())
        } else {
            self.calculate_type_vars(i_s);
            self.nth(i_s, index).execute_annotation_class(i_s)
        }
    }

    pub fn add_type_var(
        &mut self,
        i_s: &mut InferenceState<'db, '_>,
        point: Point,
        value: &Inferred<'db>,
    ) {
        if point.specific() == self.match_specific {
            if let Some(cls) = value.expect_class(i_s) {
                let generic = cls.as_annotation_generic_part(i_s);
                self.add_type_var_class(i_s, point, generic);
            } else {
                todo!(
                    "report pls: {:?} is {:?}",
                    point.type_var_index(),
                    value.description(i_s)
                )
            }
        }
    }

    fn add_type_var_class(
        &mut self,
        i_s: &mut InferenceState<'db, '_>,
        point: Point,
        class: GenericPart,
    ) {
        let index = point.type_var_index();
        self.calculated_type_vars
            .as_mut()
            .unwrap()
            .set_generic(index, class);
    }

    pub fn does_not_match(&mut self) {
        self.matches = false;
    }

    pub fn matches_signature(&mut self, i_s: &mut InferenceState<'db, '_>) -> bool {
        self.calculate_type_vars(i_s);
        self.matches
    }
}

pub fn search_type_vars<'db>(
    i_s: &mut InferenceState<'db, '_>,
    file: &'db PythonFile,
    expression: &Expression<'db>,
    found_callback: &mut dyn FnMut(NodeIndex, PointLink) -> Option<Specific>,
    found_type_vars: &mut Vec<PointLink>,
) {
    for n in expression.search_names() {
        if matches!(n.parent(), NameParent::Atom) {
            let inferred = file.inference(i_s).infer_name_reference(n);
            if let Some(definition) = inferred.maybe_type_var(i_s) {
                let link = definition.as_link();

                if let Some(point_type) = found_callback(n.index(), link) {
                    let i = found_type_vars.iter().position(|&r| r == link);
                    if i.is_none() {
                        found_type_vars.push(link);
                    };
                    let i = i.unwrap_or_else(|| found_type_vars.len() - 1);
                    file.points.set(
                        n.index(),
                        Point::new_numbered_type_var(
                            point_type,
                            TypeVarIndex::new(i),
                            Locality::Stmt,
                        ),
                    );
                }
            }
        }
    }
}
