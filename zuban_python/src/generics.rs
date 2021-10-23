use parsa_python_ast::{
    AtomContent, Expression, ExpressionContent, ExpressionPart, NodeIndex, PrimaryContent,
    SliceType, Slices,
};

use crate::arguments::{Argument, Arguments};
use crate::file::PythonFile;
use crate::inference_state::InferenceState;
use crate::inferred::{Inferrable, Inferred};
use crate::value::Function;

pub trait TypeVarFinder<'db, 'a> {
    fn lookup(&mut self, i_s: &mut InferenceState<'db, '_>, name: &str) -> Option<Inferred<'db>>;
}

pub fn resolve_type_vars<'db, 'a>(
    i_s: &mut InferenceState<'db, '_>,
    file: &'db PythonFile,
    expr: Expression<'db>,
    type_var_finder: &mut impl TypeVarFinder<'db, 'a>,
) -> Option<Inferred<'db>> {
    let mut i_s = i_s.with_annotation_instance();
    let inferred = file.get_inference(&mut i_s).infer_expression(expr);
    if inferred.is_type_var(&mut i_s) {
        type_var_finder
            .lookup(&mut i_s, expr.get_legacy_node().get_code())
            .or_else(|| todo!())
    } else {
        /*
        if !node.is_leaf() {
            for node in node.iter_children() {
                if node.is_type(Terminal(TerminalType::Name)) {
                    if let Some(resolved_type_var) =
                        resolve_type_vars(&mut i_s, file, node, type_var_finder)
                    {
                        todo!()
                    }
                }
            }
        }
        */
        None
    }
}

#[derive(Debug)]
pub enum Generics<'db> {
    Expression(&'db PythonFile, Expression<'db>),
    Slices(Slices<'db>),
    //Multiple(Box<[&Foo]>),
    None,
}

impl<'db> Generics<'db> {
    pub fn new_slice(file: &'db PythonFile, slice_type: SliceType<'db>) -> Self {
        match slice_type {
            SliceType::NamedExpression(named) => Self::Expression(file, named.expression()),
            SliceType::Slice(_) => Self::None,
            SliceType::Slices(slices) => Self::Slices(slices),
        }
    }

    pub fn get_nth(
        &self,
        i_s: &mut InferenceState<'db, '_>,
        n: usize,
        name: &str,
    ) -> Option<Inferred<'db>> {
        match self {
            Self::Expression(file, expr) => {
                if n == 0 {
                    Some(file.get_inference(i_s).infer_annotation_expression(*expr))
                } else {
                    None
                }
            }
            Self::Slices(slices) => todo!(),
            Self::None => None,
        }
    }

    pub fn iter(&self) -> GenericsIterator<'db> {
        match self {
            Self::Expression(file, expr) => GenericsIterator::Expression(file, *expr),
            Self::Slices(slices) => todo!(),
            Self::None => GenericsIterator::None,
        }
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

/*
pub trait Generics<'db>: std::fmt::Debug {
    fn get_nth(
        &self,
        i_s: &mut InferenceState<'db, '_>,
        n: usize,
        name: &str,
    ) -> Option<Inferred<'db>>;

    fn iter(&self, i_s: &mut InferenceState<'db, '_>) -> std::iter::Empty<Inferred<'db>> {
        todo!();
        std::iter::empty()
    }
}

#[derive(Debug)]
pub struct ExpectNoGenerics();

impl<'db> Generics<'db> for ExpectNoGenerics {
    fn get_nth(
        &self,
        i_s: &mut InferenceState<'db, '_>,
        n: usize,
        name: &str,
    ) -> Option<Inferred<'db>> {
        unreachable!("Should not even ask for generics")
    }
}

#[derive(Debug)]
pub struct NoGenerics();

impl<'db> Generics<'db> for NoGenerics {
    fn get_nth(
        &self,
        i_s: &mut InferenceState<'db, '_>,
        n: usize,
        name: &str,
    ) -> Option<Inferred<'db>> {
        None
    }
}

#[derive(Debug)]
pub struct CalculableGenerics<'db, 'a> {
    init: &'a Function<'db>,
    args: &'a dyn Arguments<'db>,
}

impl<'db, 'a> CalculableGenerics<'db, 'a> {
    pub fn new(init: &'a Function<'db>, args: &'a dyn Arguments<'db>) -> Self {
        Self { init, args }
    }
}

impl<'db> Generics<'db> for CalculableGenerics<'db, '_> {
    fn get_nth(
        &self,
        i_s: &mut InferenceState<'db, '_>,
        n: usize,
        name: &str,
    ) -> Option<Inferred<'db>> {
        FunctionTypeVarFinder::new(self.init, self.args, true).lookup(i_s, name)
    }
}

#[derive(Debug)]
pub struct AnnotationGenerics<'db> {
    slice_type: SliceType<'db>,
}

impl<'db> AnnotationGenerics<'db> {
    pub fn new(slice_type: SliceType<'db>) -> Self {
        Self { slice_type }
    }
}

impl<'db> Generics<'db> for AnnotationGenerics<'db> {
    fn get_nth(
        &self,
        i_s: &mut InferenceState<'db, '_>,
        n: usize,
        name: &str,
    ) -> Option<Inferred<'db>> {
        match self.slice_type {
            SliceType::Simple(simple) => {
                if n == 0 {
                    Some(simple.infer_annotation(i_s))
                } else {
                    None
                }
            }
            SliceType::Slices(slices) => {
                // This is an error, the annotation List[foo:bar] makes no sense.
                dbg!(slices);
                todo!()
            }
            SliceType::Slice(slice) => {
                // This is an error, the annotation List[foo:bar] makes no sense.
                None
            }
        }
    }
}
*/

pub struct FunctionTypeVarFinder<'db, 'a> {
    function: &'a Function<'db>,
    args: &'a dyn Arguments<'db>,
    calculated_type_vars: Option<Vec<(&'db str, Inferred<'db>)>>,
    skip_first: bool,
}

impl<'db, 'a> TypeVarFinder<'db, 'a> for FunctionTypeVarFinder<'db, 'a> {
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
}

impl<'db, 'a> FunctionTypeVarFinder<'db, 'a> {
    pub fn new(
        function: &'a Function<'db>,
        args: &'a dyn Arguments<'db>,
        skip_first: bool,
    ) -> Self {
        Self {
            function,
            args,
            calculated_type_vars: None,
            skip_first,
        }
    }

    fn calculate_type_vars(&mut self, i_s: &mut InferenceState<'db, '_>) {
        self.calculated_type_vars = Some(vec![]);
        for p in self
            .function
            .iter_inferrable_params(self.args, self.skip_first)
        {
            if let Some(annotation) = p.param.annotation() {
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
                    if !self
                        .calculated_type_vars
                        .as_ref()
                        .unwrap()
                        .iter()
                        .any(|(n, _)| *n == name.as_str())
                    {
                        let inferred = self.function.file.get_inference(i_s).infer_name(name);
                        if inferred.is_type_var(i_s) {
                            self.calculated_type_vars
                                .as_mut()
                                .unwrap()
                                .push((name.as_str(), inferrable.infer(i_s)));
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
                    if let Some(cls) = inf.expect_class() {
                        let i = inferrable.infer(i_s);
                        cls.infer_type_vars(i_s, i)
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
}
