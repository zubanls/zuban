use std::rc::Rc;

use parsa_python_ast::*;

use crate::database::{
    CallableContent, ComplexPoint, DbType, GenericsList, Locality, Point, PointType, Specific,
    TupleContent, TypeAlias, TypeVar, TypeVarIndex, TypeVarManager, TypeVarType, TypeVarUsage,
};
use crate::debug;
use crate::diagnostics::IssueType;
use crate::file::{PythonFile, PythonInference};
use crate::file_state::File;
use crate::generics::{Generics, Type};
use crate::getitem::{SliceOrSimple, SliceType, SliceTypeContent};
use crate::inference_state::InferenceState;
use crate::inferred::Inferred;
use crate::node_ref::NodeRef;
use crate::value::{Class, ClassLike, Module, Value};

#[derive(Debug)]
enum SpecialType {
    Union,
    Optional,
    Any,
    Protocol,
    ProtocolWithGenerics,
    Generic,
    GenericWithGenerics,
    Callable,
}

#[derive(Debug)]
enum TypeContent<'db> {
    Module(&'db PythonFile),
    ClassWithoutTypeVar(Inferred<'db>),
    TypeAlias(&'db TypeAlias),
    DbType(DbType),
    SpecialType(SpecialType),
}

enum TypeNameLookup<'db> {
    Module(&'db PythonFile),
    Class(Inferred<'db>),
    TypeVar(Rc<TypeVar>),
    TypeAlias(&'db TypeAlias),
    SpecialType(SpecialType),
    Invalid,
}

pub enum BaseClass {
    DbType(DbType),
    Protocol,
    Generic,
}

impl<'db> TypeContent<'db> {
    fn union(self, i_s: &mut InferenceState<'db, '_>, other: Self) -> Self {
        TypeContent::DbType(match self {
            TypeContent::ClassWithoutTypeVar(inf) => todo!(),
            TypeContent::DbType(t) => t.union(match other {
                TypeContent::ClassWithoutTypeVar(i) => i.as_db_type(i_s),
                TypeContent::DbType(t) => t,
                TypeContent::Module(m) => todo!(),
                TypeContent::TypeAlias(m) => todo!(),
                TypeContent::SpecialType(m) => todo!(),
            }),
            TypeContent::Module(m) => todo!(),
            TypeContent::TypeAlias(m) => todo!(),
            TypeContent::SpecialType(s) => match s {
                // `Any | something` always is Any
                SpecialType::Any => DbType::Any,
                _ => todo!("{:?}", s),
            },
        })
    }
}

pub struct TypeComputation<'db, 'a, 'b, 'c, C> {
    inference: &'c mut PythonInference<'db, 'a, 'b>,
    type_var_callback: &'c mut C,
    errors_already_calculated: bool,
    pub has_type_vars: bool,
}

impl<'db, 'a, 'b, 'c, C: FnMut(Rc<TypeVar>) -> TypeVarUsage> TypeComputation<'db, 'a, 'b, 'c, C> {
    pub fn new(
        inference: &'c mut PythonInference<'db, 'a, 'b>,
        type_var_callback: &'c mut C,
    ) -> Self {
        Self {
            inference,
            type_var_callback,
            errors_already_calculated: false,
            has_type_vars: false,
        }
    }

    // TODO this should not be a string, but probably cow
    fn compute_annotation_string(
        &mut self,
        start: CodeIndex,
        string: String,
    ) -> (&'db PythonFile, TypeContent<'db>) {
        let f: &'db PythonFile =
            self.inference
                .file
                .new_annotation_file(self.inference.i_s.database, start, string);
        if let Some(expr) = f.tree.maybe_expression() {
            let mut comp = TypeComputation {
                inference: &mut f.inference(self.inference.i_s),
                type_var_callback: self.type_var_callback,
                errors_already_calculated: self.errors_already_calculated,
                has_type_vars: false,
            };
            let type_ = comp.compute_type(expr);
            self.has_type_vars |= comp.has_type_vars;
            (f, type_)
        } else {
            debug!("Found non-expression in annotation: {}", f.tree.code());
            todo!()
        }
    }

    pub fn compute_base_class(&mut self, expr: Expression<'db>) -> BaseClass {
        let calculated = self.compute_type(expr);
        match calculated {
            TypeContent::SpecialType(SpecialType::Protocol | SpecialType::ProtocolWithGenerics) => {
                BaseClass::Protocol
            }
            TypeContent::SpecialType(SpecialType::Generic | SpecialType::GenericWithGenerics) => {
                BaseClass::Generic
            }
            _ => BaseClass::DbType(
                self.to_db_type(calculated, NodeRef::new(self.inference.file, expr.index())),
            ),
        }
    }

    pub fn compute_annotation(&mut self, annotation: Annotation<'db>) {
        self.cache_annotation_internal(annotation.index(), annotation.expression());
    }

    pub fn compute_return_annotation(&mut self, annotation: ReturnAnnotation<'db>) {
        self.cache_annotation_internal(annotation.index(), annotation.expression());
    }

    fn add_module_issue(&self, file: &'db PythonFile, node_ref: NodeRef<'db>) {
        node_ref.add_typing_issue(
            self.inference.i_s.database,
            IssueType::ValidType(format!(
                "Module {:?} is not valid as a type",
                Module::new(self.inference.i_s.database, file)
                    .qualified_name(self.inference.i_s.database),
            )),
        );
    }

    #[inline]
    fn cache_annotation_internal(&mut self, annotation_index: NodeIndex, expr: Expression<'db>) {
        let point = self.inference.file.points.get(annotation_index);
        if point.calculated() {
            return;
        }
        debug!(
            "Infer annotation expression class on {:?}: {:?}",
            self.inference.file.byte_to_line_column(expr.start()),
            expr.as_code()
        );

        let type_ = self.compute_type(expr);

        let specific = match type_ {
            TypeContent::ClassWithoutTypeVar(i) => {
                i.save_redirect(self.inference.file, expr.index());
                Specific::AnnotationClassInstance
            }
            TypeContent::DbType(d) => {
                if self.has_type_vars {
                    Inferred::new_unsaved_complex(ComplexPoint::TypeInstance(Box::new(
                        DbType::Type(Box::new(d)),
                    )))
                    .save_redirect(self.inference.file, expr.index());
                    Specific::AnnotationWithTypeVars
                } else {
                    Inferred::new_unsaved_complex(ComplexPoint::TypeInstance(Box::new(d)))
                        .save_redirect(self.inference.file, annotation_index);
                    return;
                }
            }
            TypeContent::Module(m) => {
                self.add_module_issue(m, NodeRef::new(self.inference.file, expr.index()));
                Inferred::new_unsaved_complex(ComplexPoint::TypeInstance(Box::new(
                    DbType::Unknown,
                )))
                .save_redirect(self.inference.file, annotation_index);
                return;
            }
            TypeContent::TypeAlias(m) => {
                if m.type_vars.is_empty() {
                    Inferred::new_unsaved_complex(ComplexPoint::TypeInstance(Box::new(
                        m.db_type.as_ref().clone(),
                    )))
                    .save_redirect(self.inference.file, annotation_index);
                    return;
                } else {
                    todo!()
                }
            }
            TypeContent::SpecialType(s) => match s {
                SpecialType::Any => {
                    Inferred::new_unsaved_complex(ComplexPoint::TypeInstance(Box::new(
                        DbType::Any,
                    )))
                    .save_redirect(self.inference.file, annotation_index);
                    return;
                }
                _ => todo!("{:?}", s),
            },
        };
        self.inference.file.points.set(
            annotation_index,
            Point::new_simple_specific(specific, Locality::Todo),
        );
    }

    fn to_db_type(&mut self, type_: TypeContent<'db>, node_ref: NodeRef<'db>) -> DbType {
        match type_ {
            TypeContent::ClassWithoutTypeVar(i) => i.as_db_type(self.inference.i_s),
            TypeContent::DbType(d) => d,
            TypeContent::Module(m) => {
                self.add_module_issue(m, node_ref);
                DbType::Unknown
            }
            TypeContent::TypeAlias(a) => {
                if a.type_vars.is_empty() {
                    a.db_type.as_ref().clone()
                } else {
                    todo!()
                }
            }
            TypeContent::SpecialType(m) => todo!(),
        }
    }

    fn compute_slice_type(&mut self, slice: SliceOrSimple<'db>) -> TypeContent<'db> {
        match slice {
            SliceOrSimple::Simple(s) => self.compute_type(s.named_expr.expression()),
            SliceOrSimple::Slice(n) => todo!(),
        }
    }

    fn compute_type(&mut self, expr: Expression<'db>) -> TypeContent<'db> {
        match expr.unpack() {
            ExpressionContent::ExpressionPart(n) => self.compute_type_expression_part(n),
            ExpressionContent::Lambda(_) => todo!(),
            ExpressionContent::Ternary(t) => todo!(),
        }
    }

    fn compute_slice_db_type(&mut self, slice: SliceOrSimple<'db>) -> DbType {
        let t = self.compute_slice_type(slice);
        self.to_db_type(t, slice.as_node_ref())
    }

    fn compute_db_type(&mut self, expr: Expression<'db>) -> DbType {
        let t = self.compute_type(expr);
        self.to_db_type(t, NodeRef::new(self.inference.file, expr.index()))
    }

    fn compute_type_expression_part(&mut self, node: ExpressionPart<'db>) -> TypeContent<'db> {
        match node {
            ExpressionPart::Atom(atom) => self.compute_type_atom(atom),
            ExpressionPart::Primary(primary) => self.compute_type_primary(primary),
            ExpressionPart::BitwiseOr(bitwise_or) => {
                let (a, b) = bitwise_or.unpack();
                // TODO this should only merge in annotation contexts
                let other = self.compute_type_expression_part(b);
                self.compute_type_expression_part(a)
                    .union(self.inference.i_s, other)
            }
            _ => todo!("Not handled yet {:?}", node),
        }
    }

    fn compute_type_primary(&mut self, primary: Primary<'db>) -> TypeContent<'db> {
        let base = self.compute_type_primary_or_atom(primary.first());
        match primary.second() {
            PrimaryContent::Attribute(name) => {
                match base {
                    TypeContent::Module(f) => {
                        // TODO this is a bit weird. shouldn't this just do a goto?
                        if let Some(index) = f.symbol_table.lookup_symbol(name.as_str()) {
                            self.inference.file.points.set(
                                name.index(),
                                Point::new_redirect(f.file_index(), index, Locality::Todo),
                            );
                            self.compute_type_name(name)
                        } else {
                            let node_ref = NodeRef::new(self.inference.file, primary.index());
                            if !self.errors_already_calculated {
                                node_ref.add_typing_issue(
                                    self.inference.i_s.database,
                                    IssueType::TypeNotFound,
                                );
                                self.inference.file.points.set(
                                    name.index(),
                                    Point::new_unknown(f.file_index(), Locality::Todo),
                                );
                            }
                            TypeContent::DbType(DbType::Unknown)
                        }
                    }
                    TypeContent::ClassWithoutTypeVar(i) => {
                        let cls = i.maybe_class(self.inference.i_s).unwrap();
                        let node_ref = NodeRef::new(self.inference.file, primary.index());
                        if let Some(index) = cls
                            .class_storage
                            .class_symbol_table
                            .lookup_symbol(name.as_str())
                        {
                            self.inference.file.points.set(
                                name.index(),
                                Point::new_redirect(
                                    cls.reference.file.file_index(),
                                    index,
                                    Locality::Todo,
                                ),
                            );
                            self.compute_type_name(name)
                        } else {
                            todo!()
                        }
                    }
                    TypeContent::DbType(t) => match t {
                        DbType::Class(c) => todo!(),
                        DbType::GenericClass(c, g) => todo!(),
                        //DbType::Any => ComputedType::new(TypeContent::DbType(DbType::Any)),
                        _ => todo!("{:?} {:?}", primary, t),
                    },
                    TypeContent::TypeAlias(m) => todo!(),
                    TypeContent::SpecialType(m) => todo!(),
                }
            }
            PrimaryContent::Execution(details) => {
                todo!("{:?}", primary)
            }
            PrimaryContent::GetItem(slice_type) => {
                let s = SliceType::new(self.inference.file, primary.index(), slice_type);
                match base {
                    TypeContent::ClassWithoutTypeVar(i) => {
                        let cls = i.maybe_class(self.inference.i_s).unwrap();
                        let t = self.compute_type_get_item_on_class(cls, s);
                        if let TypeContent::ClassWithoutTypeVar(i) = t {
                            TypeContent::ClassWithoutTypeVar(
                                i.save_if_unsaved(self.inference.file, primary.index()),
                            )
                        } else {
                            t
                        }
                    }
                    TypeContent::DbType(d) => todo!(),
                    TypeContent::Module(m) => todo!(),
                    TypeContent::TypeAlias(m) => self.compute_type_get_item_on_alias(m, s),
                    TypeContent::SpecialType(special) => match special {
                        SpecialType::Union => todo!(),
                        SpecialType::Optional => match s.unpack() {
                            SliceTypeContent::Simple(simple) => TypeContent::DbType(
                                self.compute_db_type(simple.named_expr.expression())
                                    .union(DbType::None),
                            ),
                            _ => todo!(),
                        },
                        SpecialType::Any => todo!(),
                        SpecialType::Protocol => {
                            self.expect_type_var_args(s);
                            TypeContent::SpecialType(SpecialType::ProtocolWithGenerics)
                        }
                        SpecialType::ProtocolWithGenerics => todo!(),
                        SpecialType::Generic => {
                            self.expect_type_var_args(s);
                            TypeContent::SpecialType(SpecialType::GenericWithGenerics)
                        }
                        SpecialType::GenericWithGenerics => todo!(),
                        SpecialType::Callable => self.compute_type_get_item_on_callable(s),
                    },
                }
            }
        }
    }

    fn compute_type_get_item_on_class(
        &mut self,
        class: Class<'db, '_>,
        slice_type: SliceType<'db>,
    ) -> TypeContent<'db> {
        fn found_simple_generic(file: &PythonFile, primary_index: NodeIndex) -> TypeContent {
            TypeContent::ClassWithoutTypeVar(Inferred::new_unsaved_specific(
                Specific::SimpleGeneric,
            ))
        }
        if matches!(class.generics, Generics::None) {
            if class.reference == self.inference.i_s.database.python_state.tuple() {
                return self.compute_type_get_item_on_tuple(slice_type);
            }
            let expected_count = class.type_vars(self.inference.i_s).len();
            let mut given_count = 1;
            let result = match slice_type.unpack() {
                SliceTypeContent::Simple(s) => match self.compute_type(s.named_expr.expression()) {
                    TypeContent::ClassWithoutTypeVar(_) => {
                        found_simple_generic(self.inference.file, slice_type.primary_index)
                    }
                    TypeContent::DbType(d) => TypeContent::DbType(DbType::GenericClass(
                        class.reference.as_link(),
                        GenericsList::new(Box::new([d])),
                    )),
                    TypeContent::Module(m) => todo!(),
                    TypeContent::TypeAlias(m) => todo!(),
                    TypeContent::SpecialType(m) => todo!(),
                },
                SliceTypeContent::Slice(slice) => todo!(),
                SliceTypeContent::Slices(slices) => {
                    given_count = 0;
                    let mut generics = vec![];
                    for slice_content in slices.iter() {
                        if generics.is_empty() {
                            let t = self.compute_slice_type(slice_content);
                            if !matches!(t, TypeContent::ClassWithoutTypeVar(_)) {
                                for slice_content in slices.iter().take(given_count) {
                                    generics.push(self.compute_slice_db_type(slice_content));
                                }
                                generics.push(self.to_db_type(t, slice_content.as_node_ref()));
                            }
                        } else {
                            generics.push(self.compute_slice_db_type(slice_content))
                        }
                        given_count += 1;
                    }
                    if generics.is_empty() {
                        found_simple_generic(self.inference.file, slice_type.primary_index)
                    } else {
                        TypeContent::DbType(DbType::GenericClass(
                            class.reference.as_link(),
                            GenericsList::from_vec(generics),
                        ))
                    }
                }
            };
            if given_count != expected_count {
                // TODO both the type argument issues and are not implemented for other classlikes
                // like tuple/callable/type, which can also have late bound type vars and too
                // many/few given type vars!
                NodeRef::new(self.inference.file, slice_type.primary_index).add_typing_issue(
                    self.inference.i_s.database,
                    IssueType::TypeArgumentIssue(
                        class.name().to_owned(),
                        expected_count,
                        given_count,
                    ),
                );
            }
            result
        } else {
            todo!()
        }
    }

    fn compute_type_get_item_on_tuple(&mut self, slice_type: SliceType<'db>) -> TypeContent<'db> {
        let content = match slice_type.unpack() {
            SliceTypeContent::Simple(simple) => {
                // TODO if it is a (), it's an empty tuple
                let t = self.compute_db_type(simple.named_expr.expression());
                TupleContent {
                    generics: Some(GenericsList::new(Box::new([t]))),
                    arbitrary_length: false,
                }
            }
            SliceTypeContent::Slice(x) => {
                todo!()
            }
            SliceTypeContent::Slices(slices) => {
                let mut arbitrary_length = false;
                TupleContent {
                    generics: Some(GenericsList::new(
                        slices
                            .iter()
                            .filter_map(|slice_content| {
                                if let SliceOrSimple::Simple(s) = slice_content {
                                    if s.named_expr.is_ellipsis_literal() {
                                        arbitrary_length = true;
                                        return None;
                                    }
                                }
                                Some(self.compute_slice_db_type(slice_content))
                            })
                            .collect(),
                    )),
                    arbitrary_length,
                }
            }
        };
        TypeContent::DbType(DbType::Tuple(content))
    }

    fn compute_type_get_item_on_callable(
        &mut self,
        slice_type: SliceType<'db>,
    ) -> TypeContent<'db> {
        let content = match slice_type.unpack() {
            SliceTypeContent::Simple(simple) => {
                todo!()
            }
            SliceTypeContent::Slice(x) => {
                todo!()
            }
            SliceTypeContent::Slices(slices) => {
                let mut params = Some(vec![]);
                let mut iterator = slices.iter();
                let param_node = iterator.next().map(|slice_content| match slice_content {
                    SliceOrSimple::Simple(n) => {
                        if n.named_expr.as_code() == "..." {
                            params = None
                        } else {
                            let i = n.infer(self.inference.i_s);
                            let mut list = i.iter(self.inference.i_s, slice_type.as_node_ref());
                            while let Some(next) = list.next(self.inference.i_s) {
                                if let Some(params) = &mut params {
                                    params.push(next.as_db_type(self.inference.i_s));
                                }
                            }
                        }
                    }
                    SliceOrSimple::Slice(s) => todo!(),
                });
                let return_class = iterator
                    .next()
                    .map(|slice_content| self.compute_slice_db_type(slice_content))
                    .unwrap_or(DbType::Unknown);
                CallableContent {
                    params: params.map(GenericsList::from_vec),
                    return_class: Box::new(return_class),
                }
            }
        };
        TypeContent::DbType(DbType::Callable(content))
    }

    fn compute_type_get_item_on_alias(
        &mut self,
        alias: &'db TypeAlias,
        slice_type: SliceType<'db>,
    ) -> TypeContent<'db> {
        let expected_count = alias.type_vars.len();
        let mut given_count = 1;
        let mut generics = vec![];
        match slice_type.unpack() {
            SliceTypeContent::Simple(s) => {
                generics.push(self.compute_db_type(s.named_expr.expression()))
            }
            SliceTypeContent::Slice(slice) => todo!(),
            SliceTypeContent::Slices(slices) => {
                given_count = 0;
                for slice_or_simple in slices.iter() {
                    given_count += 1;
                    generics.push(self.compute_slice_db_type(slice_or_simple))
                }
            }
        };
        if given_count != expected_count {
            slice_type.as_node_ref().add_typing_issue(
                self.inference.i_s.database,
                IssueType::TypeAliasArgumentIssue(expected_count, given_count),
            );
            TypeContent::DbType(DbType::Any)
        } else {
            TypeContent::DbType(
                alias
                    .db_type
                    .remap_type_vars(&mut |usage| generics[usage.index.as_usize()].clone()),
            )
        }
    }

    fn expect_type_var_args(&mut self, slice_type: SliceType<'db>) {
        match slice_type.unpack() {
            SliceTypeContent::Simple(n) => match self.compute_type(n.named_expr.expression()) {
                TypeContent::DbType(DbType::TypeVar(_)) => (),
                _ => todo!(),
            },
            SliceTypeContent::Slice(slice) => todo!(),
            SliceTypeContent::Slices(slices) => {
                for s in slices.iter() {
                    match self.compute_slice_type(s) {
                        TypeContent::DbType(DbType::TypeVar(_)) => (),
                        _ => todo!(),
                    }
                }
            }
        }
    }

    fn compute_type_primary_or_atom(&mut self, p: PrimaryOrAtom<'db>) -> TypeContent<'db> {
        match p {
            PrimaryOrAtom::Primary(primary) => self.compute_type_primary(primary),
            PrimaryOrAtom::Atom(atom) => self.compute_type_atom(atom),
        }
    }

    fn compute_type_atom(&mut self, atom: Atom<'db>) -> TypeContent<'db> {
        match atom.unpack() {
            AtomContent::Name(n) => {
                self.inference.infer_name_reference(n);
                self.compute_type_name(n)
            }
            AtomContent::StringsOrBytes(s_o_b) => match s_o_b.as_python_string() {
                Some(PythonString::Ref(start, s)) => {
                    self.compute_annotation_string(start, s.to_owned()).1
                }
                Some(PythonString::String(start, s)) => todo!(),
                Some(PythonString::FString) => todo!(),
                None => todo!(),
            },
            AtomContent::NoneLiteral => TypeContent::DbType(DbType::None),
            _ => todo!("{:?}", atom),
        }
    }

    fn compute_type_name(&mut self, name: Name<'db>) -> TypeContent<'db> {
        match self.inference.lookup_type_name(name) {
            TypeNameLookup::Module(f) => TypeContent::Module(f),
            TypeNameLookup::Class(i) => TypeContent::ClassWithoutTypeVar(i),
            TypeNameLookup::TypeVar(t) => {
                TypeContent::DbType(DbType::TypeVar((self.type_var_callback)(t)))
            }
            TypeNameLookup::TypeAlias(alias) => TypeContent::TypeAlias(alias),
            TypeNameLookup::Invalid => TypeContent::DbType(DbType::Any),
            TypeNameLookup::SpecialType(special) => TypeContent::SpecialType(special),
        }
    }
}

impl<'db, 'a, 'b> PythonInference<'db, 'a, 'b> {
    pub fn compute_type_get_item_on_class(
        &mut self,
        class: Class<'db, '_>,
        slice_type: SliceType<'db>,
    ) -> Inferred<'db> {
        match TypeComputation::new(self, &mut |type_var| TypeVarUsage {
            type_var,
            // TODO this shouldn't be always 0...
            index: TypeVarIndex::new(0),
            type_: TypeVarType::Alias,
        })
        .compute_type_get_item_on_class(class, slice_type)
        {
            TypeContent::ClassWithoutTypeVar(inf) => inf,
            TypeContent::DbType(d) => Inferred::new_saved(
                class.reference.file,
                class.reference.node_index,
                class.reference.point(),
            ),
            _ => todo!(),
        }
    }

    /* TODO remove
    pub fn maybe_compute_param_annotation(&mut self, name: Name<'db>) -> Option<Inferred<'db>> {
        name.maybe_param_annotation()
            .map(|annotation| match name.simple_param_type() {
                SimpleParamType::Normal => self.compute_annotation(annotation),
                SimpleParamType::MultiArgs => {
                    let p = self.annotation_type(annotation).into_db_type(self.i_s);
                    Inferred::new_unsaved_complex(ComplexPoint::TypeInstance(Box::new(
                        DbType::Tuple(TupleContent {
                            generics: Some(GenericsList::new(Box::new([p]))),
                            arbitrary_length: true,
                        }),
                    )))
                }
                SimpleParamType::MultiKwargs => {
                    let p = self.annotation_type(annotation).into_db_type(self.i_s);
                    Inferred::create_instance(
                        self.i_s.database.python_state.builtins_point_link("dict"),
                        Some(&[
                            DbType::Class(
                                self.i_s.database.python_state.builtins_point_link("str"),
                            ),
                            p,
                        ]),
                    )
                }
            })
    }
    */

    pub(super) fn use_cached_annotation(&mut self, annotation: Annotation<'db>) -> Inferred<'db> {
        let point = self.file.points.get(annotation.index());
        if point.type_() == PointType::Specific {
            if point.specific() == Specific::AnnotationClassInstance {
                Inferred::new_saved(self.file, annotation.index(), point)
            } else {
                debug_assert_eq!(point.specific(), Specific::AnnotationWithTypeVars);
                Inferred::new_saved(self.file, annotation.expression().index(), point)
            }
        } else {
            debug_assert_eq!(point.type_(), PointType::Complex, "{:?}", annotation);
            debug_assert!(matches!(
                self.file.complex_points.get(point.complex_index()),
                ComplexPoint::TypeInstance(_)
            ));
            Inferred::new_saved(self.file, annotation.index(), point)
        }
    }

    pub fn use_cached_return_annotation(
        &mut self,
        annotation: ReturnAnnotation<'db>,
    ) -> Inferred<'db> {
        let point = self.file.points.get(annotation.index());
        assert!(point.calculated());
        if point.type_() == PointType::Specific {
            if point.specific() == Specific::AnnotationClassInstance {
                Inferred::new_saved(self.file, annotation.index(), point)
            } else {
                debug_assert_eq!(point.specific(), Specific::AnnotationWithTypeVars);
                todo!()
            }
        } else {
            debug_assert_eq!(point.type_(), PointType::Complex, "{:?}", annotation);
            debug_assert!(matches!(
                self.file.complex_points.get(point.complex_index()),
                ComplexPoint::TypeInstance(_)
            ));
            Inferred::new_saved(self.file, annotation.index(), point)
        }
    }

    pub fn use_cached_return_annotation_type(
        &mut self,
        annotation: ReturnAnnotation<'db>,
    ) -> Type<'db, 'db> {
        self.use_cached_annotation_type_internal(annotation.index(), annotation.expression())
    }

    pub fn use_cached_annotation_type(&mut self, annotation: Annotation<'db>) -> Type<'db, 'db> {
        self.use_cached_annotation_type_internal(annotation.index(), annotation.expression())
    }

    fn use_cached_annotation_type_internal(
        &mut self,
        annotation_index: NodeIndex,
        expr: Expression<'db>,
    ) -> Type<'db, 'db> {
        let point = self.file.points.get(annotation_index);
        assert!(point.calculated());
        let complex_index = if point.type_() == PointType::Specific {
            if point.specific() == Specific::AnnotationClassInstance {
                return Type::ClassLike(ClassLike::Class(
                    self.infer_expression(expr).maybe_class(self.i_s).unwrap(),
                ));
            } else {
                debug_assert_eq!(point.specific(), Specific::AnnotationWithTypeVars);
                self.file.points.get(expr.index()).complex_index()
            }
        } else {
            debug_assert_eq!(point.type_(), PointType::Complex, "{:?}", expr);
            debug_assert!(matches!(
                self.file.complex_points.get(point.complex_index()),
                ComplexPoint::TypeInstance(_)
            ));
            point.complex_index()
        };
        if let ComplexPoint::TypeInstance(db_type) = self.file.complex_points.get(complex_index) {
            Type::from_db_type(self.i_s.database, db_type)
        } else {
            unreachable!()
        }
    }

    fn cache_type_assignment(&mut self, assignment: Assignment<'db>) -> TypeNameLookup<'db> {
        self.cache_assignment_nodes(assignment);
        if let Some(name) = assignment.maybe_simple_type_reassignment() {
            // For very simple cases like `Foo = int`. Not sure yet if this going to stay.
            let node_ref = NodeRef::new(self.file, name.index());
            debug_assert!(node_ref.point().calculated());
            return check_type_name(self.i_s, node_ref, || todo!());
        }
        match assignment.unpack() {
            AssignmentContent::Normal(mut targets, AssignmentRightSide::StarExpressions(right)) => {
                if let StarExpressionContent::Expression(expr) = right.unpack() {
                    let first_target = targets.next().unwrap();
                    if targets.next().is_some() {
                        return TypeNameLookup::Invalid;
                    }
                    let name_def = if let Target::Name(name_def) = first_target {
                        name_def
                    } else {
                        unreachable!()
                    };
                    debug_assert!(self.file.points.get(name_def.index()).calculated());
                    let inferred = self.check_point_cache(name_def.index()).unwrap();
                    let complex = if let Some(tv) = inferred.maybe_type_var(self.i_s) {
                        ComplexPoint::TypeVar(Rc::new(tv))
                    } else {
                        let mut type_vars = TypeVarManager::default();
                        let p = self.file.points.get(expr.index());
                        let mut comp = TypeComputation {
                            inference: self,
                            errors_already_calculated: p.calculated(),
                            type_var_callback: &mut |type_var: Rc<TypeVar>| {
                                let index = type_vars.add(type_var.clone());
                                TypeVarUsage {
                                    type_var,
                                    index,
                                    type_: TypeVarType::Alias,
                                }
                            },
                            has_type_vars: false,
                        };
                        let t = comp.compute_type(expr);
                        if let TypeContent::ClassWithoutTypeVar(i) = t {
                            return TypeNameLookup::Class(i);
                        } else {
                            let node_ref = NodeRef::new(comp.inference.file, expr.index());
                            let db_type = Rc::new(comp.to_db_type(t, node_ref));
                            ComplexPoint::TypeAlias(Box::new(TypeAlias {
                                type_vars: type_vars.into_boxed_slice(),
                                db_type,
                            }))
                        }
                    };
                    let node_ref = NodeRef::new(self.file, name_def.name().index());
                    node_ref.insert_complex(complex, Locality::Todo);
                    load_cached_type(node_ref)
                } else {
                    todo!()
                }
            }
            AssignmentContent::WithAnnotation(target, annotation, right_side) => {
                todo!("{:?}", target)
            }
            _ => todo!(),
        }
    }

    fn lookup_type_name(&mut self, name: Name<'db>) -> TypeNameLookup<'db> {
        let point = self.file.points.get(name.index());
        debug_assert!(self.file.points.get(name.index()).calculated());
        match point.type_() {
            PointType::Specific => todo!(),
            PointType::Redirect => {
                check_type_name(
                    self.i_s,
                    point.as_redirected_node_ref(self.i_s.database),
                    || {
                        let node_ref = NodeRef::new(self.file, name.index());
                        node_ref.add_typing_issue(
                            self.i_s.database,
                            IssueType::ValidType(format!(
                                "Function {:?} is not valid as a type",
                                "m.A".to_owned() //TODO: func.qualified_name(self.i_s.database),
                            )),
                        );
                        node_ref.add_typing_issue(
                            self.i_s.database,
                            IssueType::Note(
                                "Perhaps you need \"Callable[...]\" or a callback protocol?"
                                    .to_owned(),
                            ),
                        );
                    },
                )
            }
            PointType::FileReference => {
                todo!();
                let file = self.i_s.database.loaded_python_file(point.file_index());
                TypeNameLookup::Module(file)
            }
            PointType::Unknown => TypeNameLookup::Invalid,
            _ => todo!("{:?}", point),
        }
    }

    pub(super) fn compute_type_comment(&mut self, start: CodeIndex, string: String) -> DbType {
        let mut on_type_var = |type_var| todo!();
        let mut comp = TypeComputation::new(self, &mut on_type_var);
        let (file, t) = comp.compute_annotation_string(start, string);
        comp.to_db_type(t, NodeRef::new(file, 0))
    }

    pub fn compute_type_var_bound(&mut self, expr: Expression<'db>) -> Option<DbType> {
        let mut on_type_var = |type_var| todo!();
        let mut comp = TypeComputation::new(self, &mut on_type_var);
        let db_type = comp.compute_db_type(expr);
        (!comp.has_type_vars).then(|| db_type)
    }
}

#[inline]
fn check_special_type(point: Point) -> Option<SpecialType> {
    if point.type_() == PointType::Specific {
        Some(match point.specific() {
            Specific::TypingUnion => SpecialType::Union,
            Specific::TypingOptional => SpecialType::Optional,
            Specific::TypingAny => SpecialType::Any,
            Specific::TypingGeneric => SpecialType::Generic,
            Specific::TypingProtocol => SpecialType::Protocol,
            _ => return None,
        })
    } else {
        None
    }
}

fn load_cached_type(node_ref: NodeRef) -> TypeNameLookup {
    if let Some(complex) = node_ref.complex() {
        match complex {
            ComplexPoint::TypeAlias(t) => TypeNameLookup::TypeAlias(t),
            ComplexPoint::TypeVar(t) => TypeNameLookup::TypeVar(t.clone()),
            _ => unreachable!(),
        }
    } else {
        debug_assert_eq!(
            node_ref.point().maybe_specific().unwrap(),
            Specific::TypingCallable
        );
        TypeNameLookup::SpecialType(SpecialType::Callable)
    }
}

fn check_type_name<'db>(
    i_s: &mut InferenceState<'db, '_>,
    name_node_ref: NodeRef<'db>,
    mut on_invalid_function: impl FnMut(),
) -> TypeNameLookup<'db> {
    let point = name_node_ref.point();
    // First check redirects. These are probably one of the following cases:
    //
    // 1. imports
    // 2. Typeshed Aliases (special cases, see python_state.rs)
    // 3. Maybe simple assignments like `Foo = str`, though I'm not sure.
    //
    // It's important to check that it's a name. Otherwise it redirects to some random place.
    if point.calculated() {
        if point.type_() == PointType::Redirect {
            let new = point.as_redirected_node_ref(i_s.database);
            if new.maybe_name().is_some() {
                return check_type_name(i_s, new, on_invalid_function);
            }
        } else if point.type_() == PointType::FileReference {
            let file = i_s.database.loaded_python_file(point.file_index());
            return TypeNameLookup::Module(file);
        }

        if let Some(special) = check_special_type(point) {
            return TypeNameLookup::SpecialType(special);
        }
    }

    let new_name = name_node_ref.as_name();
    match new_name.expect_type() {
        TypeLike::ClassDef(c) => {
            return TypeNameLookup::Class(Inferred::new_saved(
                name_node_ref.file,
                c.index(),
                name_node_ref.file.points.get(c.index()),
            ))
        }
        TypeLike::Assignment(assignment) => {
            // Name must be a NameDefinition
            let name_index = new_name.index();
            let node_ref = NodeRef::new(name_node_ref.file, name_index);
            if node_ref.point().calculated() {
                load_cached_type(node_ref)
            } else {
                name_node_ref
                    .file
                    .inference(i_s)
                    .cache_type_assignment(assignment)
            }
        }
        TypeLike::Function => {
            on_invalid_function();
            TypeNameLookup::Invalid
        }
        TypeLike::Import => {
            if point.calculated() {
                // When an import appears, this means that there's no redirect and the import leads
                // nowhere.
                debug_assert_eq!(point.type_(), PointType::Unknown);
                TypeNameLookup::Invalid
            } else {
                name_node_ref.file.inference(i_s).infer_name(new_name);
                check_type_name(i_s, name_node_ref, on_invalid_function)
            }
        }
        TypeLike::Other => {
            todo!()
        }
    }
}
