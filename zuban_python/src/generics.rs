use parsa_python_ast::{
    AtomContent, Expression, ExpressionContent, ExpressionPart, Name, PrimaryContent, SliceType,
    Slices,
};

use crate::arguments::{Argument, Arguments, SimpleArguments};
use crate::database::{
    CalculableGenericsList, ComplexPoint, GenericPart, GenericsList, PointLink, PointType,
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

impl<'db> Generics<'db, '_> {
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
                    Some(file.get_inference(i_s).infer_annotation_expression(*expr))
                } else {
                    None
                }
            }
            Self::Slices(slices) => todo!(),
            Self::InstanceWithArguments(reference) => {
                let point = reference.file.points.get(reference.node_index + 1);
                match point.get_type() {
                    PointType::Complex => {
                        if let ComplexPoint::GenericClass(_, generics) =
                            reference.file.complex_points.get(point.get_complex_index())
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
                            .get_inference(i_s)
                            .infer_primary_or_atom(primary.first());
                        let cls = inferred.expect_class(i_s).unwrap();
                        if let PrimaryContent::Execution(details) = primary.second() {
                            let args = SimpleArguments::from_primary(reference.file, primary, None);
                            let init = cls.get_init_func(i_s, &args);
                            let type_vars = cls.get_type_vars(i_s);
                            debug!("Inferring instance generics for {}", primary.short_debug());
                            let list = TypeVarMatcher::calculate_and_return(
                                i_s,
                                &init,
                                &args,
                                true,
                                type_vars,
                                Specific::ClassTypeVar,
                            );
                            dbg!(list);
                            todo!();
                        } else {
                            unreachable!()
                        }
                        dbg!(cls.description(i_s));
                        dbg!(&i_s.current_execution);
                        use crate::value::*;
                        todo!()
                    }
                    _ => unreachable!(),
                }
            }
            Self::OnceCell(_) => todo!(),
            Self::List(_) => todo!(),
            Self::None => None,
        }
    }

    pub fn iter(&self) -> GenericsIterator<'db> {
        match self {
            Self::Expression(file, expr) => GenericsIterator::Expression(file, *expr),
            Self::Slices(slices) => todo!(),
            Self::InstanceWithArguments(_) => todo!(),
            Self::OnceCell(_) => todo!(),
            Self::List(_) => todo!(),
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

pub enum GenericsIterator<'db> {
    Expression(&'db PythonFile, Expression<'db>),
    None,
}

impl<'db> GenericsIterator<'db> {
    pub fn next(&mut self, i_s: &mut InferenceState<'db, '_>) -> Option<Inferred<'db>> {
        match self {
            Self::Expression(file, expr) => {
                let result = file.get_inference(i_s).infer_expression(*expr);
                *self = GenericsIterator::None;
                Some(result)
            }
            GenericsIterator::None => None,
        }
    }
}

pub struct TypeVarMatcher<'db, 'a> {
    function: &'a Function<'db>,
    args: &'a dyn Arguments<'db>,
    skip_first: bool,
    calculated_type_vars: Option<Box<[GenericPart]>>,
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
    ) -> Box<[GenericPart]> {
        let mut self_ = Self::new(function, args, skip_first, type_vars, match_specific);
        self_.calculate_type_vars(i_s);
        self_.calculated_type_vars.unwrap()
    }

    fn calculate_type_vars(&mut self, i_s: &mut InferenceState<'db, '_>) {
        self.calculated_type_vars = Some(Box::new([]));
        for p in self
            .function
            .iter_inferrable_params(self.args, self.skip_first)
        {
            if let Some(annotation) = p.param.annotation() {
                /*
                // TODO this should be cached
                if let Some(class_foo_list) = self.class_foo_list.as_mut() {
                    let inferred = self
                        .function
                        .file
                        .get_inference(i_s)
                        .infer_annotation_expression(annotation.expression());
                    if inferred.maybe_type_var(i_s).is_some() {
                        todo!()
                    } else {
                        inferred.run(i_s, &mut |i_s, v| {
                            let value = p.infer(i_s);
                            v.class(i_s).infer_type_vars(i_s, value, class_foo_list);
                        });
                        dbg!(class_foo_list);
                        todo!()
                    }
                }
                */
                if let ExpressionContent::ExpressionPart(part) = annotation.expression().unpack() {
                    self.try_to_find(i_s, &part, &p)
                }
            }
        }
    }

    fn try_to_find(
        &mut self,
        i_s: &mut InferenceState<'db, '_>,
        content: &ExpressionPart<'db>,
        inferrable: &dyn Inferrable<'db>,
    ) {
        match content {
            ExpressionPart::Atom(atom) => {
                if let AtomContent::Name(name) = atom.unpack() {
                    if !self.already_in_calculated_type_vars(&name) {
                        let inferred = self.function.file.get_inference(i_s).infer_name(name);
                        if inferred.maybe_type_var(i_s).is_some() {
                            //self.calculated_type_vars
                            //.push((name.as_str(), inferrable.infer(i_s)));
                            todo!()
                        }
                    }
                }
            }
            ExpressionPart::Primary(primary) => match primary.second() {
                PrimaryContent::GetItem(slice_type) => {
                    let inf = self
                        .function
                        .file
                        .get_inference(i_s)
                        .infer_primary_or_atom(primary.first());
                    if let Some(cls) = inf.expect_class(i_s) {
                        let i = inferrable.infer(i_s);
                        //if !self.already_in_calculated_type_vars("foo")  {
                        //dbg!(cls.to_generic_part(i_s));
                        cls.infer_type_vars(
                            i_s,
                            i,
                            self.calculated_type_vars.as_mut().unwrap(),
                            self.match_specific,
                        );
                        //}
                    }
                }
                PrimaryContent::Attribute(name) => {
                    let x = self
                        .function
                        .file
                        .get_inference(i_s)
                        .infer_primary(*primary);
                    todo!()
                }
                PrimaryContent::Execution(_) => (),
            },
            ExpressionPart::BitwiseOr(bitwise_or) => todo!("unions"),
            _ => (),
        }
    }

    fn already_in_calculated_type_vars(&self, name: &Name) -> bool {
        todo!()
        /*
        self.calculated_type_vars
            .as_ref()
            .unwrap()
            .iter()
            .any(|(n, _)| *n == name.as_str())
        */
    }

    pub fn nth(&mut self, i_s: &mut InferenceState<'db, '_>, index: TypeVarIndex) -> Inferred<'db> {
        if let Some(type_vars) = &self.calculated_type_vars {
            todo!()
        } else {
            self.calculate_type_vars(i_s);
            self.nth(i_s, index)
        }
    }

    /*
    fn x(&self) {
        match slice_type {
            SliceType::NamedExpression(named) => {
                let inferred = self.function.file.get_inference(i_s).infer_named_expression(named);
                if inferred.is_type_var(i_s) {
                    todo!()
                } else {
                    todo!()
                }
            }
            SliceType::Slices(slices) => {
                dbg!(slices);
                todo!()
            }
            SliceType::Slice(slice) => {
                // This is an error, the annotation List[foo:bar] makes no sense.
            }
        };
    }
    */

    /*
    fn lookup(&mut self, i_s: &mut InferenceState<'db, '_>, name: &str) -> Option<Inferred<'db>> {
        if let Some(type_vars) = &self.calculated_type_vars {
            if !self.skip_first {
                if let Some(p) = self
                    .function
                    .iter_inferrable_params(self.args, self.skip_first)
                    .next()
                {
                    if let Some(Argument::PositionalFirst(instance)) = p.argument {
                        if let Some(inf) = instance
                            .as_instance()
                            .unwrap_or_else(|| todo!())
                            .lookup_type_var(i_s, name)
                        {
                            return Some(inf);
                        }
                    }
                }
            }
            for (type_var, result) in type_vars {
                if *type_var == name {
                    return Some(result.clone());
                }
            }
            None
        } else {
            self.calculate_type_vars(i_s);
            self.lookup(i_s, name)
        }
    }
    */
}
