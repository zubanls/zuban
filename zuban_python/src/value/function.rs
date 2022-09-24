use parsa_python_ast::{
    FunctionDef, NodeIndex, Param as ASTParam, ParamIterator, ParamKind, ReturnAnnotation,
    ReturnOrYield,
};
use std::cell::Cell;
use std::fmt;
use std::rc::Rc;

use super::{LookupResult, Module, OnTypeError, Value, ValueKind};
use crate::arguments::{Argument, ArgumentIterator, ArgumentKind, Arguments, SimpleArguments};
use crate::database::{
    CallableContent, CallableParam, ComplexPoint, Database, DbType, Execution, GenericsList,
    IntersectionType, Locality, Overload, Point, PointLink, StringSlice, TypeVar, TypeVarManager,
    TypeVars,
};
use crate::debug;
use crate::diagnostics::IssueType;
use crate::file::{PythonFile, TypeComputation};
use crate::file_state::File;
use crate::getitem::SliceType;
use crate::inference_state::InferenceState;
use crate::inferred::Inferred;
use crate::matching::params::{InferrableParamIterator2, Param};
use crate::matching::{
    calculate_class_init_type_vars_and_return, calculate_function_type_vars_and_return,
    ArgumentIndexWithParam, FormatData, Generics, ResultContext, SignatureMatch, Type,
    TypeVarMatcher,
};
use crate::node_ref::NodeRef;
use crate::value::Class;

#[derive(Clone, Copy)]
pub struct Function<'db, 'a> {
    pub node_ref: NodeRef<'a>,
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
    pub fn new(node_ref: NodeRef<'a>, class: Option<Class<'db, 'a>>) -> Self {
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

    pub fn node(&self) -> FunctionDef {
        FunctionDef::by_index(&self.node_ref.file.tree, self.node_ref.node_index)
    }

    pub fn return_annotation(&self) -> Option<ReturnAnnotation> {
        self.node().return_annotation()
    }

    pub fn iter_inferrable_params<'b>(
        &self,
        db: &'db Database,
        args: &'b dyn Arguments<'db>,
        skip_first_param: bool,
    ) -> InferrableParamIterator<'db, 'b> {
        let mut params = self.node().params().iter();
        if skip_first_param {
            params.next();
        }
        InferrableParamIterator::new(db, self.node_ref.file, params, args.iter_arguments())
    }

    pub fn iter_args_with_params<'b>(
        &self,
        db: &'db Database,
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
        InferrableParamIterator2::new(db, params, args)
    }

    pub fn infer_param(
        &self,
        i_s: &mut InferenceState<'db, '_>,
        param_name_def_index: NodeIndex,
        args: &dyn Arguments<'db>,
    ) -> Inferred {
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
        for param in func.iter_inferrable_params(i_s.db, check_args, false) {
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
    ) -> Inferred {
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
                            .infer_star_expressions(star_expressions, ResultContext::Unknown)
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
                    ComplexPoint::TypeVars(vars) => return Some(vars),
                    _ => unreachable!(),
                }
            }
            return None;
        }
        let func_node = self.node();
        let mut inference = self.node_ref.file.inference(i_s);
        let in_result_type = Cell::new(false);
        let mut unbound_type_vars = vec![];
        let mut on_type_var = |i_s: &mut InferenceState<'db, '_>,
                               manager: &TypeVarManager,
                               type_var: Rc<TypeVar>,
                               node_ref: NodeRef,
                               current_callable: Option<_>| {
            self.class
                .and_then(|class| {
                    class
                        .type_vars(i_s)
                        .and_then(|t| t.find(type_var.clone(), class.node_ref.as_link()))
                        .map(DbType::TypeVar)
                })
                .or_else(|| {
                    if in_result_type.get()
                        && manager.position(&type_var).is_none()
                        && current_callable.is_none()
                    {
                        unbound_type_vars.push(type_var);
                    }
                    None
                })
        };
        let mut type_computation = TypeComputation::new(
            &mut inference,
            self.node_ref.as_link(),
            Some(&mut on_type_var),
        );
        for param in func_node.params().iter() {
            if let Some(annotation) = param.annotation() {
                type_computation.compute_annotation(annotation);
            }
        }
        if let Some(return_annot) = func_node.return_annotation() {
            in_result_type.set(true);
            type_computation.compute_return_annotation(return_annot);
        }
        let type_vars = type_computation.into_type_vars(|inf, recalculate_type_vars| {
            for param in func_node.params().iter() {
                if let Some(annotation) = param.annotation() {
                    inf.recalculate_annotation_type_vars(annotation.index(), recalculate_type_vars);
                }
            }
            if let Some(return_annot) = func_node.return_annotation() {
                inf.recalculate_annotation_type_vars(return_annot.index(), recalculate_type_vars);
            }
        });
        if !unbound_type_vars.is_empty() {
            if let Some(DbType::TypeVar(t)) = self.result_type(i_s).maybe_db_type() {
                if unbound_type_vars.contains(&t.type_var) {
                    NodeRef::new(
                        self.node_ref.file,
                        func_node.return_annotation().unwrap().expression().index(),
                    )
                    .add_typing_issue(i_s.db, IssueType::TypeVarInReturnButNotArgument);
                }
            }
        }
        match type_vars.len() {
            0 => type_var_reference.set_point(Point::new_node_analysis(Locality::Todo)),
            _ => {
                type_var_reference.insert_complex(ComplexPoint::TypeVars(type_vars), Locality::Todo)
            }
        }
        debug_assert!(type_var_reference.point().calculated());
        self.type_vars(i_s)
    }

    pub fn as_db_type(&self, i_s: &mut InferenceState<'db, '_>, skip_first_param: bool) -> DbType {
        let type_vars = self.type_vars(i_s); // Cache annotation types
        let mut params = self.iter_params();
        if skip_first_param {
            params.next();
        }
        let as_db_type = |i_s: &mut _, t: Type<'db, '_>| {
            t.as_db_type(i_s).replace_type_vars(&mut |usage| {
                if let Some(class) = self.class {
                    if usage.in_definition == class.node_ref.as_link() {
                        return class.generics().nth(i_s, usage.index);
                    }
                }
                DbType::TypeVar(usage.clone())
            })
        };
        let result_type = self.result_type(i_s);
        DbType::Callable(Box::new(CallableContent {
            defined_at: self.node_ref.as_link(),
            params: Some(
                params
                    .map(|p| CallableParam {
                        db_type: p
                            .annotation_type(i_s)
                            .map(|t| as_db_type(i_s, t))
                            .unwrap_or(DbType::Any),
                        has_default: p.has_default(),
                        name: Some({
                            let n = p.param.name_definition();
                            StringSlice::new(self.node_ref.file_index(), n.start(), n.end())
                        }),
                        param_kind: p.kind(i_s.db),
                    })
                    .collect(),
            ),
            type_vars: type_vars.cloned(),
            result_type: as_db_type(i_s, result_type),
        }))
    }

    pub fn iter_params(&self) -> impl Iterator<Item = FunctionParam> {
        self.node().params().iter().map(|param| FunctionParam {
            file: self.node_ref.file,
            param,
        })
    }

    pub fn param_iterator(&self) -> Option<impl Iterator<Item = FunctionParam>> {
        Some(self.iter_params())
    }

    pub(super) fn execute_internal(
        &self,
        i_s: &mut InferenceState<'db, '_>,
        args: &dyn Arguments<'db>,
        on_type_error: OnTypeError<'db, '_>,
        class: Option<&Class<'db, '_>>,
        result_context: ResultContext<'db, '_>,
    ) -> Inferred {
        let return_annotation = self.return_annotation();
        let func_type_vars = return_annotation.and_then(|_| self.type_vars(i_s));
        let calculated_type_vars = calculate_function_type_vars_and_return(
            i_s,
            class,
            *self,
            args,
            false,
            func_type_vars,
            self.node_ref.as_link(),
            result_context,
            Some(on_type_error),
        );
        if let Some(return_annotation) = return_annotation {
            let i_s = &mut i_s.with_annotation_instance();
            // We check first if type vars are involved, because if they aren't we can reuse the
            // annotation expression cache instead of recalculating.
            if func_type_vars.is_some()
                || self
                    .class
                    .map(|c| c.type_vars(i_s).is_some())
                    .unwrap_or(false)
            {
                // TODO this could also be a tuple...
                debug!(
                    "Inferring generics for {}{}",
                    self.class
                        .map(|c| format!("{}.", c.format(&FormatData::new_short(i_s.db))))
                        .unwrap_or_else(|| "".to_owned()),
                    self.name()
                );
                self.node_ref
                    .file
                    .inference(i_s)
                    .use_cached_return_annotation_type(return_annotation)
                    .execute_and_resolve_type_vars(i_s, self.class.as_ref(), &calculated_type_vars)
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
            .unwrap_or_else(|| Type::new(&DbType::Any))
    }

    fn format_overload_variant(
        &self,
        i_s: &mut InferenceState<'db, '_>,
        matcher: Option<&TypeVarMatcher<'db, '_>>,
        is_init: bool,
    ) -> Box<str> {
        // Make sure annotations/type vars are calculated
        self.type_vars(i_s);

        let return_type = |i_s: &mut InferenceState<'db, '_>, annotation| {
            self.node_ref
                .file
                .inference(i_s)
                .use_cached_return_annotation_type(annotation)
                .format(&FormatData::with_matcher(i_s.db, matcher))
        };
        let node = self.node();
        let mut previous_kind = None;
        let mut args = self
            .iter_params()
            .enumerate()
            .map(|(i, p)| {
                let annotation_str = p
                    .annotation_type(i_s)
                    .map(|t| t.format(&FormatData::with_matcher(i_s.db, matcher)));
                let current_kind = p.kind(i_s.db);
                let stars = match current_kind {
                    ParamKind::Starred => "*",
                    ParamKind::DoubleStarred => "**",
                    _ => "",
                };
                let mut out = if i == 0
                    && self.class.is_some()
                    && stars.is_empty()
                    && annotation_str.is_none()
                {
                    p.name(i_s.db).unwrap().to_owned()
                } else {
                    let mut out = if current_kind == ParamKind::PositionalOnly {
                        annotation_str.unwrap_or_else(|| Box::from("Any")).into()
                    } else {
                        format!(
                            "{stars}{}: {}",
                            p.name(i_s.db).unwrap(),
                            annotation_str.as_deref().unwrap_or("Any")
                        )
                    };
                    if previous_kind == Some(ParamKind::PositionalOnly)
                        && current_kind != ParamKind::PositionalOnly
                    {
                        out = format!(" /, {out}")
                    }
                    out
                };
                if p.has_default() {
                    out += " = ...";
                }
                previous_kind = Some(current_kind);
                out
            })
            .collect::<Vec<_>>()
            .join(", ");
        if previous_kind == Some(ParamKind::PositionalOnly) {
            args += ", /";
        }
        let ret = node.return_annotation().map(|a| return_type(i_s, a));
        let name = self.name();
        let type_var_string = self.type_vars(i_s).map(|type_vars| {
            format!(
                "[{}] ",
                type_vars
                    .iter()
                    .map(|t| {
                        let mut s = t.name(i_s.db).to_owned();
                        if let Some(bound) = &t.bound {
                            s += &format!(" <: {}", bound.format(&FormatData::new_short(i_s.db)));
                        } else if !t.restrictions.is_empty() {
                            s += &format!(
                                " in ({})",
                                t.restrictions
                                    .iter()
                                    .map(|t| t.format(&FormatData::new_short(i_s.db)))
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
        if is_init {
            format!("def {type_var_str}{name}({args})").into()
        } else {
            format!("def {type_var_str}{name}({args}) -> {result}").into()
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

    fn lookup_internal(&self, i_s: &mut InferenceState<'db, '_>, name: &str) -> LookupResult {
        todo!("{name:?}")
    }

    fn execute(
        &self,
        i_s: &mut InferenceState<'db, '_>,
        args: &dyn Arguments<'db>,
        result_context: ResultContext<'db, '_>,
        on_type_error: OnTypeError<'db, '_>,
    ) -> Inferred {
        if let Some(class) = &self.class {
            self.execute_internal(
                &mut i_s.with_class_context(class),
                args,
                on_type_error,
                Some(class),
                result_context,
            )
        } else {
            self.execute_internal(i_s, args, on_type_error, None, result_context)
        }
    }

    fn get_item(&self, i_s: &mut InferenceState<'db, '_>, slice_type: &SliceType) -> Inferred {
        slice_type
            .as_node_ref()
            .add_typing_issue(i_s.db, IssueType::OnlyClassTypeApplication);
        Inferred::new_unknown()
    }

    fn as_type(&self, i_s: &mut InferenceState<'db, '_>) -> Type<'a, 'a> {
        Type::owned(self.as_db_type(i_s, false))
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

    fn name(&self, db: &'db Database) -> Option<&str> {
        Some(self.param.name_definition().as_code())
    }

    fn annotation_type(&self, i_s: &mut InferenceState<'db, '_>) -> Option<Type<'db, 'x>> {
        self.param.annotation().map(|annotation| {
            self.file
                .inference(i_s)
                .use_cached_annotation_type(annotation)
        })
    }

    fn func_annotation_link(&self) -> Option<PointLink> {
        self.param
            .annotation()
            .map(|a| PointLink::new(self.file.file_index(), a.index()))
    }

    fn kind(&self, db: &'db Database) -> ParamKind {
        let mut t = self.param.type_();
        if t == ParamKind::PositionalOrKeyword
            && db.python_state.mypy_compatible
            && self.param.name_definition().as_code().starts_with("__")
            && !self.param.name_definition().as_code().ends_with("__")
        {
            // Mypy treats __ params as positional only
            t = ParamKind::PositionalOnly
        }
        t
    }
}

pub struct InferrableParamIterator<'db, 'a> {
    db: &'db Database,
    arguments: ArgumentIterator<'db, 'a>,
    params: ParamIterator<'a>,
    file: &'db PythonFile,
    unused_keyword_arguments: Vec<Argument<'db, 'a>>,
}

impl<'db, 'a> InferrableParamIterator<'db, 'a> {
    fn new(
        db: &'db Database,
        file: &'db PythonFile,
        params: ParamIterator<'a>,
        arguments: ArgumentIterator<'db, 'a>,
    ) -> Self {
        Self {
            db,
            arguments,
            file,
            params,
            unused_keyword_arguments: vec![],
        }
    }

    fn next_argument(&mut self, param: &FunctionParam<'db, 'a>) -> ParamInput<'db, 'a> {
        for (i, unused) in self.unused_keyword_arguments.iter().enumerate() {
            match &unused.kind {
                ArgumentKind::Keyword { key, .. } => {
                    if *key == param.name(self.db).unwrap() {
                        return ParamInput::Argument(self.unused_keyword_arguments.remove(i));
                    }
                }
                _ => unreachable!(),
            }
        }
        match param.kind(self.db) {
            ParamKind::PositionalOrKeyword => {
                for argument in &mut self.arguments {
                    match argument.kind {
                        ArgumentKind::Keyword { key, .. } => {
                            if key == param.name(self.db).unwrap() {
                                return ParamInput::Argument(argument);
                            } else {
                                self.unused_keyword_arguments.push(argument);
                            }
                        }
                        _ => return ParamInput::Argument(argument),
                    }
                }
            }
            ParamKind::KeywordOnly => {
                for argument in &mut self.arguments {
                    match argument.kind {
                        ArgumentKind::Keyword { key, .. } => {
                            if key == param.name(self.db).unwrap() {
                                return ParamInput::Argument(argument);
                            } else {
                                self.unused_keyword_arguments.push(argument);
                            }
                        }
                        _ => todo!(),
                    }
                }
            }
            ParamKind::PositionalOnly => todo!(),
            ParamKind::Starred => {
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
            ParamKind::DoubleStarred => todo!(),
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
    fn human_readable_argument_index(&self) -> String {
        match self {
            Self::Argument(arg) => arg.human_readable_index(),
            Self::Tuple(_) => todo!(),
            Self::None => todo!(),
        }
    }
}

pub trait ParamWithArgument<'db, 'a> {
    fn human_readable_argument_index(&self) -> String;
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

    pub fn infer(&self, i_s: &mut InferenceState<'db, '_>) -> Option<Inferred> {
        if !matches!(&self.argument, ParamInput::None) {
            debug!("Infer param {:?}", self.param.name(i_s.db));
        }
        match &self.argument {
            ParamInput::Argument(arg) => Some(arg.infer(i_s, ResultContext::Unknown)),
            ParamInput::Tuple(args) => {
                todo!();
                /*
                let mut list = vec![];
                for arg in args.iter() {
                    list.push(arg.infer(i_s, ResultContext::Unknown).as_db_type(i_s))
                }
                let t = TupleContent {
                    generics: Some(GenericsList::generics_from_vec(list)),
                    arbitrary_length: false,
                };
                Some(Inferred::new_unsaved_complex(ComplexPoint::TypeInstance(
                    Box::new(DbType::Tuple(t)),
                )))
                */
            }
            ParamInput::None => None,
        }
    }
}

impl<'db, 'a> ParamWithArgument<'db, 'a> for InferrableParam<'db, 'a> {
    fn human_readable_argument_index(&self) -> String {
        self.argument.human_readable_argument_index()
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
        result_context: ResultContext<'db, '_>,
    ) -> Option<(Function<'db, 'a>, Option<GenericsList>)> {
        let match_signature = |i_s: &mut InferenceState<'db, '_>, function: Function<'db, 'a>| {
            let func_type_vars = function.type_vars(i_s);
            if search_init {
                calculate_class_init_type_vars_and_return(
                    i_s,
                    class.unwrap(),
                    function,
                    args,
                    result_context,
                    None,
                )
            } else {
                calculate_function_type_vars_and_return(
                    i_s,
                    class,
                    function,
                    args,
                    false,
                    func_type_vars,
                    function.node_ref.as_link(),
                    result_context,
                    None,
                )
            }
        };
        let has_already_calculated_class_generics =
            search_init && !matches!(class.unwrap().generics(), Generics::None | Generics::Any);
        let handle_result = |i_s: &mut _, calculated_type_vars, function| {
            let calculated = if has_already_calculated_class_generics {
                if let Some(class) = class {
                    let type_vars = class.type_vars(i_s);
                    class.generics.as_generics_list(i_s, type_vars) // TODO why not use generics_as_list
                } else {
                    unreachable!();
                }
            } else {
                calculated_type_vars
            };
            Some((function, calculated))
        };
        let mut first_similar = None;
        let mut multi_any_match: Option<(_, _, Box<_>)> = None;
        for link in self.overload.functions.iter() {
            let function = Function::new(NodeRef::from_link(i_s.db, *link), self.class);
            let calculated_type_args = match_signature(i_s, function);
            match calculated_type_args.matches {
                SignatureMatch::True => {
                    if multi_any_match.is_some() {
                        // This means that there was an explicit any in a param.
                        return None;
                    } else {
                        debug!(
                            "Decided overload for {}: {:?}",
                            self.name(),
                            function.node().short_debug()
                        );
                        return handle_result(i_s, calculated_type_args.type_arguments, function);
                    }
                }
                SignatureMatch::TrueWithAny { argument_indices } => {
                    // TODO there could be three matches or more?
                    // TODO maybe merge list[any] and list[int]
                    if let Some((_, _, ref old_indices)) = multi_any_match {
                        // If multiple signatures match because of Any, we should just return
                        // without an error message, there is no clear choice, i.e. it's ambiguous,
                        // but there should also not be an error.
                        if are_any_arguments_ambiguous_in_overload(
                            i_s,
                            old_indices,
                            &argument_indices,
                        ) {
                            return None;
                        }
                    } else {
                        multi_any_match = Some((
                            calculated_type_args.type_arguments,
                            function,
                            argument_indices,
                        ))
                    }
                }
                SignatureMatch::FalseButSimilar => {
                    if first_similar.is_none() {
                        first_similar = Some(function)
                    }
                }
                SignatureMatch::False => (),
            }
        }
        if let Some((type_arguments, function, _)) = multi_any_match {
            return handle_result(i_s, type_arguments, function);
        }
        if let Some(function) = first_similar {
            // In case of similar params, we simply use the first similar overload and calculate
            // its diagnostics and return its types.
            // This is also how mypy does it. See `check_overload_call` (9943444c7)
            let calculated_type_args = match_signature(i_s, function);
            return handle_result(i_s, calculated_type_args.type_arguments, function);
        } else {
            let function = Function::new(
                NodeRef::from_link(i_s.db, self.overload.functions[0]),
                self.class,
            );
            args.as_node_ref().add_typing_issue(
                i_s.db,
                IssueType::OverloadMismatch {
                    name: function.diagnostic_string(self.class.as_ref()),
                    args: args.iter_arguments().into_argument_types(),
                    variants: self.variants(i_s, search_init),
                },
            );
        }
        None
    }

    fn variants(&self, i_s: &mut InferenceState<'db, '_>, is_init: bool) -> Box<[Box<str>]> {
        self.overload
            .functions
            .iter()
            .map(|link| {
                let func = Function::new(NodeRef::from_link(i_s.db, *link), self.class);
                func.format_overload_variant(i_s, None, is_init)
            })
            .collect()
    }

    fn fallback_type(&self, i_s: &mut InferenceState<'db, '_>) -> Inferred {
        let mut t: Option<DbType> = None;
        for link in self.overload.functions.iter() {
            let func = Function::new(NodeRef::from_link(i_s.db, *link), self.class);
            let f_t = func.result_type(i_s).as_db_type(i_s);
            if let Some(old_t) = t.take() {
                t = Some(old_t.merge_matching_parts(func.result_type(i_s).as_db_type(i_s)))
            } else {
                t = Some(f_t);
            }
        }
        Inferred::execute_db_type(i_s, t.unwrap())
    }

    pub(super) fn execute_internal(
        &self,
        i_s: &mut InferenceState<'db, '_>,
        args: &dyn Arguments<'db>,
        on_type_error: OnTypeError<'db, '_>,
        class: Option<&Class<'db, '_>>,
        result_context: ResultContext<'db, '_>,
    ) -> Inferred {
        debug!("Execute overloaded function {}", self.name());
        self.find_matching_function(i_s, args, class, false, result_context)
            .map(|(function, _)| function.execute(i_s, args, result_context, on_type_error))
            .unwrap_or_else(|| self.fallback_type(i_s))
    }
}

impl<'db, 'a> Value<'db, 'a> for OverloadedFunction<'db, 'a> {
    fn kind(&self) -> ValueKind {
        ValueKind::Function
    }

    fn name(&self) -> &'db str {
        self.node_ref.as_code()
    }

    fn lookup_internal(&self, i_s: &mut InferenceState<'db, '_>, name: &str) -> LookupResult {
        todo!()
    }

    fn execute(
        &self,
        i_s: &mut InferenceState<'db, '_>,
        args: &dyn Arguments<'db>,
        result_context: ResultContext<'db, '_>,
        on_type_error: OnTypeError<'db, '_>,
    ) -> Inferred {
        self.execute_internal(i_s, args, on_type_error, None, result_context)
    }

    fn get_item(&self, i_s: &mut InferenceState<'db, '_>, slice_type: &SliceType) -> Inferred {
        slice_type
            .as_node_ref()
            .add_typing_issue(i_s.db, IssueType::OnlyClassTypeApplication);
        todo!("Please write a test that checks this");
        //Inferred::new_unknown()
    }

    fn as_overloaded_function(&self) -> Option<&OverloadedFunction<'db, 'a>> {
        Some(self)
    }

    fn as_type(&self, i_s: &mut InferenceState<'db, '_>) -> Type<'a, 'a> {
        Type::owned(DbType::Intersection(IntersectionType::new_overload(
            self.overload
                .functions
                .iter()
                .map(|link| {
                    let function = Function::new(NodeRef::from_link(i_s.db, *link), self.class);
                    function.as_db_type(i_s, false)
                })
                .collect(),
        )))
    }
}

fn are_any_arguments_ambiguous_in_overload(
    i_s: &mut InferenceState,
    a: &[ArgumentIndexWithParam],
    b: &[ArgumentIndexWithParam],
) -> bool {
    // This function checks if an argument with an Any (like List[Any]) makes it unclear which
    // overload would need to be chosen. Please have a look at the test
    // `testOverloadWithOverlappingItemsAndAnyArgument4` for more information.
    for p1 in a {
        for p2 in b {
            if p1.argument_index == p2.argument_index {
                let n1 = NodeRef::from_link(i_s.db, p1.param_annotation_link);
                let n2 = NodeRef::from_link(i_s.db, p2.param_annotation_link);
                let t1 = n1
                    .file
                    .inference(i_s)
                    .use_cached_annotation_type(n1.as_annotation())
                    .as_db_type(i_s);
                let t2 = n2
                    .file
                    .inference(i_s)
                    .use_cached_annotation_type(n2.as_annotation())
                    .as_db_type(i_s);
                if t1 != t2 {
                    return true;
                }
            }
        }
    }
    false
}
