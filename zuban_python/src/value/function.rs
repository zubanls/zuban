use parsa_python_ast::{
    FunctionDef, NodeIndex, Param as ASTParam, ParamIterator, ParamType, ReturnAnnotation,
    ReturnOrYield,
};
use std::fmt;
use std::rc::Rc;

use super::{LookupResult, Module, OnTypeError, Value, ValueKind};
use crate::arguments::{Argument, ArgumentIterator, Arguments, SimpleArguments};
use crate::database::{
    CallableContent, CallableParam, ComplexPoint, Database, DbType, Execution, FormatStyle,
    GenericsList, Locality, Overload, Point, TupleContent, TypeVar, TypeVarManager, TypeVarType,
    TypeVarUsage, TypeVars,
};
use crate::debug;
use crate::diagnostics::IssueType;
use crate::file::{PythonFile, TypeComputation};
use crate::getitem::SliceType;
use crate::inference_state::InferenceState;
use crate::inferred::Inferred;
use crate::matching::params::{InferrableParamIterator2, Param};
use crate::matching::{
    calculate_function_type_vars_and_return, ClassLike, Generics, SignatureMatch, Type,
};
use crate::node_ref::NodeRef;
use crate::value::Class;

#[derive(Clone, Copy)]
pub struct Function<'db, 'a> {
    pub node_ref: NodeRef<'db>,
    pub class: Option<Class<'db, 'a>>,
}

impl<'db> fmt::Debug for Function<'db, '_> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        f.debug_struct("Function")
            .field("file", self.node_ref.file)
            .field("node", &self.node())
            .finish()
    }
}

impl<'db, 'a> Function<'db, 'a> {
    // Functions use the following points:
    // - "def" to redirect to the first return/yield
    // - "(" to redirect to save calculated type vars
    pub fn new(node_ref: NodeRef<'db>, class: Option<Class<'db, 'a>>) -> Self {
        Self { node_ref, class }
    }

    pub fn from_execution(
        db: &'db Database,
        execution: &Execution,
        class: Option<Class<'db, 'a>>,
    ) -> Self {
        let f_func = db.loaded_python_file(execution.function.file);
        Function::new(
            NodeRef {
                file: f_func,
                node_index: execution.function.node_index,
            },
            class,
        )
    }

    pub fn node(&self) -> FunctionDef<'db> {
        FunctionDef::by_index(&self.node_ref.file.tree, self.node_ref.node_index)
    }

    pub fn return_annotation(&self) -> Option<ReturnAnnotation<'db>> {
        self.node().return_annotation()
    }

    pub fn iter_inferrable_params<'b>(
        &self,
        args: &'b dyn Arguments<'db>,
        skip_first_param: bool,
    ) -> InferrableParamIterator<'db, 'b> {
        let mut params = self.node().params().iter();
        if skip_first_param {
            params.next();
        }
        InferrableParamIterator::new(self.node_ref.file, params, args.iter_arguments())
    }

    pub fn iter_args_with_params<'b>(
        &self,
        args: &'b dyn Arguments<'db>,
        skip_first_param: bool,
    ) -> InferrableParamIterator2<
        'db,
        'b,
        impl Iterator<Item = FunctionParam<'db, 'b>>,
        FunctionParam<'db, 'b>,
    >
    where
        'a: 'b,
    {
        let mut params = self.iter_params();
        if skip_first_param {
            params.next();
        }
        InferrableParamIterator2::new(params, args.iter_arguments().peekable())
    }

    pub fn infer_param(
        &self,
        i_s: &mut InferenceState<'db, '_>,
        param_name_def_index: NodeIndex,
        args: &dyn Arguments<'db>,
    ) -> Inferred<'db> {
        let func_node =
            FunctionDef::from_param_name_def_index(&self.node_ref.file.tree, param_name_def_index);
        let temporary_args;
        let temporary_func;
        let (check_args, func) = if func_node.index() == self.node_ref.node_index {
            (args, self)
        } else {
            let mut execution = args.outer_execution();
            loop {
                if let Some(exec) = execution {
                    if func_node.index() == exec.function.node_index {
                        // TODO this could be an instance as well
                        // TODO in general check if this code still makes sense
                        temporary_args = SimpleArguments::from_execution(i_s.db, exec);
                        temporary_func = Function::from_execution(i_s.db, exec, None);
                        break (&temporary_args as &dyn Arguments, &temporary_func);
                    }
                    execution = exec.in_.as_deref();
                } else {
                    return Inferred::new_unknown();
                }
            }
        };
        for param in func.iter_inferrable_params(check_args, false) {
            if param.is_at(param_name_def_index) {
                return param.infer(i_s).unwrap_or_else(Inferred::new_unknown);
            }
        }
        unreachable!("{param_name_def_index:?}");
    }

    fn execute_without_annotation(
        &self,
        i_s: &mut InferenceState<'db, '_>,
        args: &dyn Arguments<'db>,
    ) -> Inferred<'db> {
        if self.is_generator() {
            todo!("Maybe not check here, because this could be precalculated and cached");
        }
        let mut inner_i_s = i_s.with_func_and_args(self, args);
        for return_or_yield in self.iter_return_or_yield() {
            match return_or_yield {
                ReturnOrYield::Return(ret) =>
                // TODO multiple returns, this is an early exit
                {
                    if let Some(star_expressions) = ret.star_expressions() {
                        return self
                            .node_ref
                            .file
                            .inference(&mut inner_i_s)
                            .infer_star_expressions(star_expressions)
                            .resolve_function_return(&mut inner_i_s);
                    } else {
                        todo!()
                    }
                }
                ReturnOrYield::Yield(yield_expr) => unreachable!(),
            }
        }
        Inferred::new_none()
    }

    fn iter_return_or_yield(&self) -> ReturnOrYieldIterator<'db> {
        let def_point = self.node_ref.file.points.get(self.node_ref.node_index + 1);
        let first_return_or_yield = def_point.node_index();
        ReturnOrYieldIterator {
            file: self.node_ref.file,
            next_node_index: first_return_or_yield,
        }
    }

    fn is_generator(&self) -> bool {
        for return_or_yield in self.iter_return_or_yield() {
            if let ReturnOrYield::Yield(_) = return_or_yield {
                return true;
            }
        }
        false
    }

    pub fn type_vars(&self, i_s: &mut InferenceState<'db, '_>) -> Option<&'db TypeVars> {
        // To save the generics just use the ( operator's storage.
        // + 1 for def; + 2 for name + 1 for (
        let type_var_reference = self.node_ref.add_to_node_index(4);
        if type_var_reference.point().calculated() {
            if let Some(complex) = type_var_reference.complex() {
                match complex {
                    ComplexPoint::FunctionTypeVars(vars) => return Some(vars),
                    _ => unreachable!(),
                }
            }
            return None;
        }
        let mut type_vars = TypeVarManager::default();
        let func_node = self.node();
        let mut inference = self.node_ref.file.inference(i_s);
        let mut on_type_var = |i_s: &mut InferenceState<'db, '_>, type_var: Rc<TypeVar>, _, _| {
            if let Some(class) = self.class {
                if let Some(usage) = class.type_vars(i_s).and_then(|t| {
                    t.find(
                        type_var.clone(),
                        TypeVarType::Class,
                        class.node_ref.as_link(),
                    )
                }) {
                    return Some(usage);
                }
            }
            let index = type_vars.add(type_var.clone());
            Some(TypeVarUsage {
                type_var,
                index,
                in_definition: self.node_ref.as_link(),
                type_: TypeVarType::Function,
            })
        };
        for param in func_node.params().iter() {
            if let Some(annotation) = param.annotation() {
                TypeComputation::new(&mut inference, &mut on_type_var)
                    .compute_annotation(annotation)
            }
        }
        if let Some(return_annot) = func_node.return_annotation() {
            TypeComputation::new(&mut inference, &mut on_type_var)
                .compute_return_annotation(return_annot);
        }
        let type_vars = type_vars.into_boxed_slice();
        match type_vars.len() {
            0 => type_var_reference.set_point(Point::new_node_analysis(Locality::Todo)),
            _ => type_var_reference
                .insert_complex(ComplexPoint::FunctionTypeVars(type_vars), Locality::Todo),
        }
        debug_assert!(type_var_reference.point().calculated());
        self.type_vars(i_s)
    }

    pub fn as_db_type(&self, i_s: &mut InferenceState<'db, '_>) -> DbType {
        self.type_vars(i_s); // Cache annotation types
        DbType::Callable(CallableContent {
            defined_at: self.node_ref.as_link(),
            params: Some(
                self.iter_params()
                    .map(|p| CallableParam {
                        db_type: p
                            .annotation_type(i_s)
                            .map(|t| t.as_db_type(i_s))
                            .unwrap_or(DbType::Any),
                        param_type: p.param_type(),
                    })
                    .collect(),
            ),
            return_class: Box::new(self.result_type(i_s).as_db_type(i_s)),
        })
    }

    pub fn iter_params(&self) -> impl Iterator<Item = FunctionParam<'db, 'a>> {
        self.node().params().iter().map(|param| FunctionParam {
            file: self.node_ref.file,
            param,
        })
    }

    pub fn param_iterator(&self) -> Option<impl Iterator<Item = FunctionParam<'db, 'a>>> {
        Some(self.iter_params())
    }

    pub(super) fn execute_internal(
        &self,
        i_s: &mut InferenceState<'db, '_>,
        args: &dyn Arguments<'db>,
        on_type_error: OnTypeError<'db, '_>,
        class: Option<&Class<'db, '_>>,
    ) -> Inferred<'db> {
        let return_annotation = self.return_annotation();
        let func_type_vars = return_annotation.and_then(|_| self.type_vars(i_s));
        let calculated_type_vars = calculate_function_type_vars_and_return(
            i_s,
            class,
            *self,
            args,
            false,
            func_type_vars,
            TypeVarType::Function,
            self.node_ref.as_link(),
            Some(on_type_error),
        )
        .1;
        if let Some(return_annotation) = return_annotation {
            let i_s = &mut i_s.with_annotation_instance();
            // We check first if type vars are involved, because if they aren't we can reuse the
            // annotation expression cache instead of recalculating.
            if func_type_vars.is_some()
                || self
                    .class
                    .map(|c| !c.class_infos(i_s).type_vars.is_empty())
                    .unwrap_or(false)
            {
                // TODO this could also be a tuple...
                debug!(
                    "Inferring generics for {}{}",
                    self.class
                        .map(|c| format!("{}.", c.format(i_s, FormatStyle::Short)))
                        .unwrap_or_else(|| "".to_owned()),
                    self.name()
                );
                self.node_ref
                    .file
                    .inference(i_s)
                    .use_cached_return_annotation_type(return_annotation)
                    .execute_and_resolve_type_vars(
                        i_s,
                        self.class.as_ref(),
                        calculated_type_vars.as_ref(),
                    )
            } else {
                self.node_ref
                    .file
                    .inference(i_s)
                    .use_cached_return_annotation(return_annotation)
            }
        } else {
            self.execute_without_annotation(i_s, args)
        }
    }

    pub fn diagnostic_string(&self, class: Option<&Class>) -> Box<str> {
        match class {
            Some(class) => {
                if self.name() == "__init__" {
                    format!("{:?}", class.name()).into()
                } else {
                    format!("{:?} of {:?}", self.name(), self.class.unwrap().name()).into()
                }
            }
            None => format!("{:?}", self.name()).into(),
        }
    }

    pub fn result_type(&self, i_s: &mut InferenceState<'db, '_>) -> Type<'db, 'a> {
        self.return_annotation()
            .map(|a| {
                self.node_ref
                    .file
                    .inference(i_s)
                    .use_cached_return_annotation_type(a)
            })
            .unwrap_or(Type::Any)
    }

    pub fn format(&self, i_s: &mut InferenceState<'db, '_>, style: FormatStyle) -> Box<str> {
        // Make sure annotations/type vars are calculated
        self.type_vars(i_s);

        let return_type = |i_s: &mut InferenceState<'db, '_>, annotation| {
            self.node_ref
                .file
                .inference(i_s)
                .use_cached_return_annotation_type(annotation)
                .format(i_s, self.class.as_ref(), style)
        };
        let node = self.node();
        if matches!(
            style,
            FormatStyle::MypyRevealType | FormatStyle::MypyOverload
        ) {
            let args = self
                .iter_params()
                .enumerate()
                .map(|(i, p)| {
                    let annotation_str = p.annotation_type(i_s).map(|t| t.format(i_s, None, style));
                    let stars = match p.param_type() {
                        ParamType::Starred => "*",
                        ParamType::DoubleStarred => "**",
                        _ => "",
                    };
                    if let Some(annotation_str) = annotation_str {
                        format!("{stars}{}: {annotation_str}", p.name().unwrap())
                    } else if i == 0 && self.class.is_some() && stars.is_empty() {
                        p.name().unwrap().to_owned()
                    } else {
                        format!("{stars}{}: Any", p.name().unwrap())
                    }
                })
                .collect::<Vec<_>>()
                .join(", ");
            let ret = node.return_annotation().map(|a| return_type(i_s, a));
            let name = match style {
                FormatStyle::MypyRevealType => "",
                _ => self.name(),
            };
            let type_var_string = self.type_vars(i_s).map(|type_vars| {
                format!(
                    "[{}] ",
                    type_vars
                        .iter()
                        .map(|t| {
                            let mut s = t.name(i_s.db).to_owned();
                            if let Some(bound) = &t.bound {
                                s += &format!(
                                    " <: {}",
                                    bound.format(i_s.db, None, FormatStyle::Short)
                                );
                            } else if !t.restrictions.is_empty() {
                                s += &format!(
                                    " in ({})",
                                    t.restrictions
                                        .iter()
                                        .map(|t| t.format(i_s.db, None, FormatStyle::Short))
                                        .collect::<Vec<_>>()
                                        .join(", ")
                                );
                            }
                            s
                        })
                        .collect::<Vec<_>>()
                        .join(", "),
                )
            });
            let type_var_str = type_var_string.as_deref().unwrap_or("");
            let result = ret.as_deref().unwrap_or("Any");
            if result == "None" {
                format!("def {type_var_str}{name}({args})").into()
            } else {
                format!("def {type_var_str}{name}({args}) -> {result}").into()
            }
        } else {
            let ret = node.return_annotation().map(|a| return_type(i_s, a));
            let result = format!(
                "Callable[[{}], {}]",
                self.iter_params()
                    .map(|param| {
                        let t = param.annotation_type(i_s).unwrap_or(Type::Any).format(
                            i_s,
                            self.class.as_ref(),
                            style,
                        );
                        match param.param_type() {
                            ParamType::PositionalOnly => t.to_string(),
                            ParamType::PositionalOrKeyword => match param.has_default() {
                                true => format!("DefaultArg({t}, '{}')", param.name().unwrap()),
                                false => format!("Arg({t}, '{}')", param.name().unwrap()),
                            },
                            ParamType::KeywordOnly => {
                                format!("NamedArg({t}, '{}')", param.name().unwrap())
                            }
                            ParamType::Starred => format!("VarArg({t})"),
                            ParamType::DoubleStarred => format!("KwArg({t})"),
                        }
                    })
                    .collect::<Vec<_>>()
                    .join(", "),
                ret.as_deref().unwrap_or("Any"),
            );
            result.into()
        }
    }
}

impl<'db, 'a> Value<'db, 'a> for Function<'db, 'a> {
    fn kind(&self) -> ValueKind {
        ValueKind::Function
    }

    fn name(&self) -> &'db str {
        let func = FunctionDef::by_index(&self.node_ref.file.tree, self.node_ref.node_index);
        func.name().as_str()
    }

    fn lookup_internal(&self, i_s: &mut InferenceState<'db, '_>, name: &str) -> LookupResult<'db> {
        todo!("{name:?}")
    }

    fn execute(
        &self,
        i_s: &mut InferenceState<'db, '_>,
        args: &dyn Arguments<'db>,
        on_type_error: OnTypeError<'db, '_>,
    ) -> Inferred<'db> {
        if let Some(class) = &self.class {
            self.execute_internal(
                &mut i_s.with_class_context(class),
                args,
                on_type_error,
                Some(class),
            )
        } else {
            self.execute_internal(i_s, args, on_type_error, None)
        }
    }

    fn get_item(
        &self,
        i_s: &mut InferenceState<'db, '_>,
        slice_type: &SliceType<'db, '_>,
    ) -> Inferred<'db> {
        slice_type
            .as_node_ref()
            .add_typing_issue(i_s.db, IssueType::OnlyClassTypeApplication);
        Inferred::new_unknown()
    }

    fn class(&self, i_s: &mut InferenceState<'db, '_>) -> ClassLike<'db, 'a> {
        ClassLike::FunctionType(*self)
    }

    fn as_function(&self) -> Option<&Function<'db, 'a>> {
        Some(self)
    }

    fn module(&self, db: &'db Database) -> Module<'db> {
        Module::new(db, self.node_ref.file)
    }
}

struct ReturnOrYieldIterator<'db> {
    file: &'db PythonFile,
    next_node_index: NodeIndex,
}

impl<'db> Iterator for ReturnOrYieldIterator<'db> {
    type Item = ReturnOrYield<'db>;
    fn next(&mut self) -> Option<Self::Item> {
        if self.next_node_index == 0 {
            None
        } else {
            let point = self.file.points.get(self.next_node_index);
            let index = self.next_node_index;
            self.next_node_index = point.node_index();
            Some(ReturnOrYield::by_index(&self.file.tree, index - 1))
        }
    }
}

#[derive(Clone, Copy, Debug)]
pub struct FunctionParam<'db, 'x> {
    file: &'db PythonFile,
    param: ASTParam<'x>,
}

impl<'db, 'x> Param<'db, 'x> for FunctionParam<'db, 'x> {
    fn has_default(&self) -> bool {
        self.param.default().is_some()
    }

    fn name(&self) -> Option<&str> {
        Some(self.param.name_definition().as_code())
    }

    fn annotation_type(&self, i_s: &mut InferenceState<'db, '_>) -> Option<Type<'db, 'x>> {
        self.param.annotation().map(|annotation| {
            self.file
                .inference(i_s)
                .use_cached_annotation_type(annotation)
        })
    }

    fn param_type(&self) -> ParamType {
        self.param.type_()
    }
}

pub struct InferrableParamIterator<'db, 'a> {
    arguments: ArgumentIterator<'db, 'a>,
    params: ParamIterator<'db>,
    file: &'db PythonFile,
    unused_keyword_arguments: Vec<Argument<'db, 'a>>,
}

impl<'db, 'a> InferrableParamIterator<'db, 'a> {
    fn new(
        file: &'db PythonFile,
        params: ParamIterator<'db>,
        arguments: ArgumentIterator<'db, 'a>,
    ) -> Self {
        Self {
            arguments,
            file,
            params,
            unused_keyword_arguments: vec![],
        }
    }

    fn next_argument(&mut self, param: &FunctionParam<'db, 'a>) -> ParamInput<'db, 'a> {
        for (i, unused) in self.unused_keyword_arguments.iter().enumerate() {
            match unused {
                Argument::Keyword(name, reference) => {
                    if *name == param.name().unwrap() {
                        return ParamInput::Argument(self.unused_keyword_arguments.remove(i));
                    }
                }
                _ => unreachable!(),
            }
        }
        match param.param_type() {
            ParamType::PositionalOrKeyword => {
                for argument in &mut self.arguments {
                    match argument {
                        Argument::Keyword(name, reference) => {
                            if name == param.name().unwrap() {
                                return ParamInput::Argument(argument);
                            } else {
                                self.unused_keyword_arguments.push(argument);
                            }
                        }
                        _ => return ParamInput::Argument(argument),
                    }
                }
            }
            ParamType::KeywordOnly => {
                for argument in &mut self.arguments {
                    match argument {
                        Argument::Keyword(name, reference) => {
                            if name == param.name().unwrap() {
                                return ParamInput::Argument(argument);
                            } else {
                                self.unused_keyword_arguments.push(argument);
                            }
                        }
                        _ => todo!(),
                    }
                }
            }
            ParamType::PositionalOnly => todo!(),
            ParamType::Starred => {
                let mut args = vec![];
                for argument in &mut self.arguments {
                    if argument.is_keyword_argument() {
                        self.unused_keyword_arguments.push(argument);
                        break;
                    }
                    args.push(argument)
                }
                return ParamInput::Tuple(args.into_boxed_slice());
            }
            ParamType::DoubleStarred => todo!(),
        }
        for argument in &mut self.arguments {
            // TODO check param type here and make sure that it makes sense.
        }
        ParamInput::None
    }
}

impl<'db, 'a> Iterator for InferrableParamIterator<'db, 'a> {
    type Item = InferrableParam<'db, 'a>;

    fn next(&mut self) -> Option<Self::Item> {
        self.params.next().map(|param| {
            let param = FunctionParam {
                file: self.file,
                param,
            };
            let argument = self.next_argument(&param);
            InferrableParam { param, argument }
        })
    }
}

#[derive(Debug)]
enum ParamInput<'db, 'a> {
    Argument(Argument<'db, 'a>),
    Tuple(Box<[Argument<'db, 'a>]>),
    None,
}

impl ParamInput<'_, '_> {
    fn argument_index(&self) -> String {
        match self {
            Self::Argument(arg) => arg.index(),
            Self::Tuple(_) => todo!(),
            Self::None => todo!(),
        }
    }
}

pub trait ParamWithArgument<'db, 'a> {
    fn argument_index(&self) -> String;
}

#[derive(Debug)]
pub struct InferrableParam<'db, 'a> {
    pub param: FunctionParam<'db, 'a>,
    argument: ParamInput<'db, 'a>,
}

impl<'db> InferrableParam<'db, '_> {
    fn is_at(&self, index: NodeIndex) -> bool {
        self.param.param.name_definition().index() == index
    }

    pub fn has_argument(&self) -> bool {
        !matches!(self.argument, ParamInput::None)
    }

    pub fn infer(&self, i_s: &mut InferenceState<'db, '_>) -> Option<Inferred<'db>> {
        if !matches!(&self.argument, ParamInput::None) {
            debug!("Infer param {:?}", self.param.name());
        }
        match &self.argument {
            ParamInput::Argument(arg) => Some(arg.infer(i_s)),
            ParamInput::Tuple(args) => {
                let mut list = vec![];
                for arg in args.iter() {
                    list.push(arg.infer(i_s).as_db_type(i_s))
                }
                let t = TupleContent {
                    generics: Some(GenericsList::generics_from_vec(list)),
                    arbitrary_length: false,
                };
                Some(Inferred::new_unsaved_complex(ComplexPoint::TypeInstance(
                    Box::new(DbType::Tuple(t)),
                )))
            }
            ParamInput::None => None,
        }
    }
}

impl<'db, 'a> ParamWithArgument<'db, 'a> for InferrableParam<'db, 'a> {
    fn argument_index(&self) -> String {
        self.argument.argument_index()
    }
}

#[derive(Debug)]
pub struct OverloadedFunction<'db, 'a> {
    node_ref: NodeRef<'db>,
    overload: &'a Overload,
    class: Option<Class<'db, 'a>>,
}

impl<'db, 'a> OverloadedFunction<'db, 'a> {
    pub fn new(
        node_ref: NodeRef<'db>,
        overload: &'a Overload,
        class: Option<Class<'db, 'a>>,
    ) -> Self {
        Self {
            node_ref,
            overload,
            class,
        }
    }

    pub(super) fn find_matching_function(
        &self,
        i_s: &mut InferenceState<'db, '_>,
        args: &dyn Arguments<'db>,
        class: Option<&Class<'db, '_>>,
        search_init: bool, // TODO this feels weird, maybe use a callback?
    ) -> Option<(Function<'db, 'a>, Option<GenericsList>)> {
        let has_already_calculated_class_generics =
            search_init && !matches!(class.unwrap().generics(), Generics::None);
        let match_signature =
            |i_s: &mut InferenceState<'db, '_>, function: Function<'db, 'a>| match search_init {
                true => {
                    if has_already_calculated_class_generics {
                        let func_type_vars = function.type_vars(i_s);
                        calculate_function_type_vars_and_return(
                            i_s,
                            class,
                            function,
                            args,
                            true,
                            func_type_vars,
                            TypeVarType::Function,
                            function.node_ref.as_link(),
                            None,
                        )
                    } else {
                        let c = class.unwrap();
                        let type_vars = c.type_vars(i_s);
                        calculate_function_type_vars_and_return(
                            i_s,
                            class,
                            function,
                            args,
                            true,
                            type_vars,
                            TypeVarType::Class,
                            c.node_ref.as_link(),
                            None,
                        )
                    }
                }
                false => {
                    let func_type_vars = function.type_vars(i_s);
                    calculate_function_type_vars_and_return(
                        i_s,
                        class,
                        function,
                        args,
                        false,
                        func_type_vars,
                        TypeVarType::Function,
                        function.node_ref.as_link(),
                        None,
                    )
                }
            };
        let handle_result = |i_s, calculated_type_vars, function| {
            let calculated = if has_already_calculated_class_generics {
                if let Some(class) = class {
                    class.generics.as_generics_list(i_s)
                } else {
                    unreachable!();
                }
            } else {
                calculated_type_vars
            };
            Some((function, calculated))
        };
        let mut first_similar = None;
        let mut multi_any_match = None;
        for link in self.overload.functions.iter() {
            let function = Function::new(NodeRef::from_link(i_s.db, *link), self.class);
            let (matched, calculated_type_vars) = match_signature(i_s, function);
            match matched {
                SignatureMatch::True => {
                    debug!(
                        "Decided overload for {}: {:?}",
                        self.name(),
                        function.node().short_debug()
                    );
                    return handle_result(i_s, calculated_type_vars, function);
                }
                SignatureMatch::TrueWithAny(param_indices) => {
                    // TODO there could be three matches or more?
                    // TODO maybe merge list[any] and list[int]
                    if multi_any_match.is_some() {
                        // If multiple signatures match because of Any, we should just return
                        // without an error message, there is no clear choice, but there should
                        // also not be an error.
                        return None;
                    }
                    multi_any_match = Some((calculated_type_vars, function, param_indices))
                }
                SignatureMatch::FalseButSimilar => {
                    if first_similar.is_none() {
                        first_similar = Some(function)
                    }
                }
                SignatureMatch::False => (),
            }
        }
        if let Some((calculated_type_vars, function, _)) = multi_any_match {
            return handle_result(i_s, calculated_type_vars, function);
        }
        if let Some(function) = first_similar {
            // In case of similar params, we simply use the first similar overload and calculate
            // its diagnostics and return its types.
            // This is also how mypy does it. See `check_overload_call` (9943444c7)
            let (_, calculated_type_vars) = match_signature(i_s, function);
            return handle_result(i_s, calculated_type_vars, function);
        } else {
            let function = Function::new(
                NodeRef::from_link(i_s.db, self.overload.functions[0]),
                self.class,
            );
            args.as_node_ref().add_typing_issue(
                i_s.db,
                IssueType::OverloadMismatch {
                    name: function.diagnostic_string(self.class.as_ref()),
                    args: args.iter_arguments().into_argument_types(i_s),
                    variants: self.variants(i_s),
                },
            );
        }
        None
    }

    fn variants(&self, i_s: &mut InferenceState<'db, '_>) -> Box<[Box<str>]> {
        self.overload
            .functions
            .iter()
            .map(|link| {
                let func = Function::new(NodeRef::from_link(i_s.db, *link), self.class);
                func.format(i_s, FormatStyle::MypyOverload)
            })
            .collect()
    }

    pub(super) fn execute_internal(
        &self,
        i_s: &mut InferenceState<'db, '_>,
        args: &dyn Arguments<'db>,
        on_type_error: OnTypeError<'db, '_>,
        class: Option<&Class<'db, '_>>,
    ) -> Inferred<'db> {
        debug!("Execute overloaded function {}", self.name());
        self.find_matching_function(i_s, args, class, false)
            .map(|(function, _)| function.execute(i_s, args, on_type_error))
            .unwrap_or_else(Inferred::new_unknown)
    }
}

impl<'db, 'a> Value<'db, 'a> for OverloadedFunction<'db, 'a> {
    fn kind(&self) -> ValueKind {
        ValueKind::Function
    }

    fn name(&self) -> &'db str {
        self.node_ref.as_code()
    }

    fn lookup_internal(&self, i_s: &mut InferenceState<'db, '_>, name: &str) -> LookupResult<'db> {
        todo!()
    }

    fn execute(
        &self,
        i_s: &mut InferenceState<'db, '_>,
        args: &dyn Arguments<'db>,
        on_type_error: OnTypeError<'db, '_>,
    ) -> Inferred<'db> {
        self.execute_internal(i_s, args, on_type_error, None)
    }

    fn get_item(
        &self,
        i_s: &mut InferenceState<'db, '_>,
        slice_type: &SliceType<'db, '_>,
    ) -> Inferred<'db> {
        slice_type
            .as_node_ref()
            .add_typing_issue(i_s.db, IssueType::OnlyClassTypeApplication);
        todo!("Please write a test that checks this");
        //Inferred::new_unknown()
    }

    fn as_overloaded_function(&self) -> Option<&OverloadedFunction<'db, 'a>> {
        Some(self)
    }
}
