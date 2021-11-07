use parsa_python_ast::{Expression, ExpressionContent, PrimaryContent, SliceType, Slices};

use crate::arguments::{Arguments, SimpleArguments};
use crate::database::{
    CalculableGenericsList, ComplexPoint, GenericPart, GenericsList, Point, PointLink, PointType,
    Specific, TypeVarIndex,
};
use crate::debug;
use crate::file::PythonFile;
use crate::inference_state::InferenceState;
use crate::inferred::{Inferrable, Inferred, NodeReference};
use crate::value::Function;

#[derive(Debug, Clone)]
pub enum Generics<'db, 'a> {
    Expression(&'db PythonFile, Expression<'db>),
    Slices(Slices<'db>),
    InstanceWithArguments(NodeReference<'db>),
    OnceCell(&'a CalculableGenericsList),
    List(&'a GenericsList),
    None,
}

impl<'db, 'a> Generics<'db, 'a> {
    pub fn new_slice(file: &'db PythonFile, slice_type: SliceType<'db>) -> Self {
        match slice_type {
            SliceType::NamedExpression(named) => Self::Expression(file, named.expression()),
            SliceType::Slice(_) => Self::None,
            SliceType::Slices(slices) => Self::Slices(slices),
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
            Self::Slices(slices) => todo!(),
            Self::InstanceWithArguments(reference) => {
                let class_reference = reference.add_to_node_index(1);
                let point = class_reference.point();
                match point.type_() {
                    PointType::Complex => {
                        if let ComplexPoint::GenericClass(_, generics) =
                            class_reference.get_complex().unwrap()
                        {
                            generics
                                .nth(n)
                                .map(|c| Inferred::from_generic_class(i_s.database, c))
                        } else {
                            unreachable!()
                        }
                    }
                    PointType::Redirect => {
                        let primary = reference.as_primary();
                        let inferred = reference
                            .file
                            .inference(i_s)
                            .infer_primary_or_atom(primary.first());
                        let cls = inferred.expect_class(i_s).unwrap();
                        if let PrimaryContent::Execution(details) = primary.second() {
                            let args = SimpleArguments::from_primary(
                                reference.file,
                                primary,
                                None,
                                Some(&cls),
                            );
                            let init = cls.init_func(i_s, &args);
                            let type_vars = cls.type__vars(i_s);
                            debug!("Inferring instance generics for {}", primary.short_debug());
                            let list = TypeVarMatcher::calculate_and_return(
                                i_s,
                                &init,
                                &args,
                                true,
                                type_vars,
                                Specific::ClassTypeVar,
                            );

                            // After we know the generics we simply replace the old class of
                            // InstanceWithArguments with a complex value that includes generics.
                            class_reference.insert_complex(ComplexPoint::GenericClass(
                                cls.reference.as_link(),
                                list,
                            ));
                            //ComplexPoint::Instance(PointLink, CalculableGenericsList, Box<Execution>),
                            self.nth(i_s, n)
                        } else {
                            unreachable!()
                        }
                    }
                    _ => unreachable!(),
                }
            }
            Self::OnceCell(_) => todo!(),
            Self::List(l) => l
                .nth(n)
                .map(|g| Inferred::from_generic_class(i_s.database, g)),
            Self::None => None,
        }
    }

    pub fn iter(&self) -> GenericsIterator<'db, 'a> {
        match self {
            Self::Expression(file, expr) => GenericsIterator::Expression(file, *expr),
            Self::Slices(slices) => todo!(),
            Self::InstanceWithArguments(_) => todo!(),
            Self::OnceCell(_) => todo!(),
            Self::List(l) => GenericsIterator::GenericsList(l.iter()),
            Self::None => GenericsIterator::None,
        }
    }

    pub fn as_generics_list(&self, i_s: &mut InferenceState<'db, '_>) -> Option<GenericsList> {
        match self {
            Self::Expression(file, expr) => {
                todo!()
            }
            Self::Slices(slices) => {
                todo!()
            }
            Self::InstanceWithArguments(node_ref) => {
                todo!()
            }
            Self::OnceCell(calculable_list) => {
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
                &|inferred| "Unknown".to_owned(),
            ));
        }
        format!("[{}]", strings.join(", "))
    }
}

pub enum GenericsIterator<'db, 'a> {
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
    calculated_type_vars: Option<GenericsList>,
    matches: bool,
    type_vars: &'db [PointLink],
    match_specific: Specific,
}

impl<'db, 'a> TypeVarMatcher<'db, 'a> {
    pub fn new(
        function: &'a Function<'db>,
        args: &'a dyn Arguments<'db>,
        skip_first: bool,
        type_vars: &'db [PointLink],
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

    fn calculate_and_return(
        i_s: &mut InferenceState<'db, '_>,
        function: &'a Function<'db>,
        args: &'a dyn Arguments<'db>,
        skip_first: bool,
        type_vars: &'db [PointLink],
        match_specific: Specific,
    ) -> GenericsList {
        let mut self_ = Self::new(function, args, skip_first, type_vars, match_specific);
        self_.calculate_type_vars(i_s);
        self_.calculated_type_vars.unwrap()
    }

    fn calculate_type_vars(&mut self, i_s: &mut InferenceState<'db, '_>) {
        self.calculated_type_vars = Some(GenericsList::new_unknown(self.type_vars.len()));
        self.function.calculated_type_vars(i_s, self.args);
        for p in self
            .function
            .iter_inferrable_params(self.args, self.skip_first)
        {
            if let Some(annotation) = p.param.annotation() {
                if let ExpressionContent::ExpressionPart(part) = annotation.expression().unpack() {
                    self.function
                        .reference
                        .file
                        .inference(i_s)
                        .infer_annotation_expression(annotation.expression())
                        .run(i_s, &mut |i_s, v| {
                            let value = p.infer(i_s);
                            v.class(i_s).infer_type_vars(i_s, value, self);
                        });
                }
            }
        }
    }

    pub fn nth(&mut self, i_s: &mut InferenceState<'db, '_>, index: TypeVarIndex) -> Inferred<'db> {
        if let Some(type_vars) = &self.calculated_type_vars {
            todo!()
        } else {
            self.calculate_type_vars(i_s);
            self.nth(i_s, index)
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
                let index = point.type_var_index();
                self.calculated_type_vars
                    .as_mut()
                    .unwrap()
                    .set_generic(index, i_s, &cls);
            } else {
                todo!(
                    "report pls: {:?} is {:?}",
                    point.type_var_index(),
                    value.description(i_s)
                )
            }
        }
    }
}
