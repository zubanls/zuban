use std::fmt;

use parsa_python_cst::{
    Annotation, Assignment, Atom, BytesLiteral, ClassDef, CodeIndex, Expression, Factor,
    FunctionDef, ImportFrom, Int, Name, NameDef, NameImportParent, NamedExpression, NodeIndex,
    Primary, PrimaryTarget, Slices, StarExpression, StarStarExpression, StarredExpression,
    StringLiteral,
};

use crate::{
    database::{
        ClassStorage, ComplexPoint, Database, FileIndex, Locality, Point, PointKind, PointLink,
        Specific, TypeAlias,
    },
    diagnostics::{Diagnostic, Issue, IssueKind},
    file::{File, PythonFile},
    inference_state::InferenceState,
    inferred::Inferred,
    matching::Generics,
    python_state::{NAME_DEF_TO_CLASS_DIFF, NAME_TO_FUNCTION_DIFF},
    type_::Type,
    type_helpers::{Class, Function, Module, CLASS_TO_CLASS_INFO_DIFFERENCE},
};

#[derive(Clone, Copy)]
pub struct NodeRef<'file> {
    pub file: &'file PythonFile,
    pub node_index: NodeIndex,
}

impl<'file> std::cmp::PartialEq for NodeRef<'file> {
    fn eq(&self, other: &Self) -> bool {
        std::ptr::eq(self.file, other.file) && self.node_index == other.node_index
    }
}

impl<'file> NodeRef<'file> {
    #[inline]
    pub fn new(file: &'file PythonFile, node_index: NodeIndex) -> Self {
        Self { file, node_index }
    }

    pub fn from_link(db: &'file Database, point: PointLink) -> Self {
        let file = db.loaded_python_file(point.file);
        Self {
            file,
            node_index: point.node_index,
        }
    }

    pub fn in_module(&self) -> Module<'file> {
        Module::new(self.file)
    }

    #[inline]
    pub fn to_db_lifetime(self, _: &Database) -> NodeRef {
        // This should be safe, because all files are added to the database.
        unsafe { std::mem::transmute(self) }
    }

    #[inline]
    pub fn add_to_node_index(&self, add: i64) -> Self {
        Self::new(self.file, ((self.node_index as i64) + add) as NodeIndex)
    }

    pub fn point(&self) -> Point {
        self.file.points.get(self.node_index)
    }

    pub fn set_point(&self, point: Point) {
        self.file.points.set(self.node_index, point)
    }

    pub fn set_point_redirect_in_same_file(&self, node_index: NodeIndex, locality: Locality) {
        self.file.points.set(
            self.node_index,
            Point::new_redirect(self.file.file_index, node_index, locality),
        )
    }

    pub fn accumulate_types(&self, i_s: &InferenceState, add: &Inferred) {
        let point = self.point();
        if point.calculated() {
            if point.maybe_specific() == Some(Specific::Cycle) {
                return;
            }
            let new = self.expect_inferred(i_s).simplified_union(i_s, add.clone());
            self.set_point(Point::new_uncalculated());
            new.save_redirect(i_s, self.file, self.node_index);
        } else {
            add.clone().save_redirect(i_s, self.file, self.node_index);
        }
    }

    pub fn complex(&self) -> Option<&'file ComplexPoint> {
        let point = self.point();
        if !point.calculated() {
            return None;
        }
        if let PointKind::Complex = point.kind() {
            Some(self.file.complex_points.get(point.complex_index()))
        } else {
            None
        }
    }

    pub fn maybe_alias(&self) -> Option<&'file TypeAlias> {
        match self.complex() {
            Some(ComplexPoint::TypeAlias(alias)) => Some(alias),
            _ => None,
        }
    }

    pub fn insert_complex(&self, complex: ComplexPoint, locality: Locality) {
        self.file
            .complex_points
            .insert(&self.file.points, self.node_index, complex, locality);
    }

    pub fn insert_type(&self, t: Type) {
        self.insert_complex(ComplexPoint::TypeInstance(t), Locality::Todo)
    }

    pub fn as_link(&self) -> PointLink {
        PointLink::new(self.file.file_index, self.node_index)
    }

    pub fn as_expression(&self) -> Expression<'file> {
        Expression::by_index(&self.file.tree, self.node_index)
    }

    pub fn as_star_expression(&self) -> StarExpression<'file> {
        StarExpression::by_index(&self.file.tree, self.node_index)
    }

    pub fn as_slices(&self) -> Slices<'file> {
        Slices::by_index(&self.file.tree, self.node_index)
    }

    pub fn as_primary(&self) -> Primary<'file> {
        Primary::by_index(&self.file.tree, self.node_index)
    }

    pub fn as_name(&self) -> Name<'file> {
        Name::by_index(&self.file.tree, self.node_index)
    }

    pub fn as_name_def(&self) -> NameDef<'file> {
        NameDef::by_index(&self.file.tree, self.node_index)
    }

    pub fn as_annotation(&self) -> Annotation<'file> {
        Annotation::by_index(&self.file.tree, self.node_index)
    }

    pub fn as_bytes_literal(&self) -> BytesLiteral<'file> {
        BytesLiteral::by_index(&self.file.tree, self.node_index)
    }

    pub fn maybe_expression(&self) -> Option<Expression<'file>> {
        Expression::maybe_by_index(&self.file.tree, self.node_index)
    }

    pub fn maybe_name(&self) -> Option<Name<'file>> {
        Name::maybe_by_index(&self.file.tree, self.node_index)
    }

    pub fn maybe_name_def(&self) -> Option<NameDef<'file>> {
        NameDef::maybe_by_index(&self.file.tree, self.node_index)
    }

    pub fn maybe_starred_expression(&self) -> Option<StarredExpression<'file>> {
        StarredExpression::maybe_by_index(&self.file.tree, self.node_index)
    }

    pub fn maybe_double_starred_expression(&self) -> Option<StarStarExpression<'file>> {
        StarStarExpression::maybe_by_index(&self.file.tree, self.node_index)
    }

    pub fn maybe_function(&self) -> Option<FunctionDef<'file>> {
        FunctionDef::maybe_by_index(&self.file.tree, self.node_index)
    }

    pub fn maybe_import_of_name_in_symbol_table(&self) -> Option<NameImportParent> {
        self.as_name().name_def().unwrap().maybe_import()
    }

    pub fn file_index(&self) -> FileIndex {
        self.file.file_index
    }

    pub fn infer_int(&self) -> Option<i64> {
        Int::maybe_by_index(&self.file.tree, self.node_index).and_then(|i| i.as_str().parse().ok())
    }

    pub fn maybe_str(&self) -> Option<StringLiteral<'file>> {
        StringLiteral::maybe_by_index(&self.file.tree, self.node_index)
    }

    pub fn expect_int(&self) -> Int<'file> {
        Int::by_index(&self.file.tree, self.node_index)
    }

    pub fn maybe_class(&self) -> Option<ClassDef<'file>> {
        ClassDef::maybe_by_index(&self.file.tree, self.node_index)
    }

    pub fn maybe_factor(&self) -> Option<Factor<'file>> {
        Factor::maybe_by_index(&self.file.tree, self.node_index)
    }

    pub fn maybe_primary_target(&self) -> Option<PrimaryTarget<'file>> {
        PrimaryTarget::maybe_by_index(&self.file.tree, self.node_index)
    }

    pub fn as_named_expression(&self) -> NamedExpression<'file> {
        NamedExpression::by_index(&self.file.tree, self.node_index)
    }

    pub fn expect_inferred(&self, i_s: &InferenceState) -> Inferred {
        self.file
            .inference(i_s)
            .check_point_cache(self.node_index)
            .unwrap()
    }

    pub fn expect_complex_type(&self) -> &Type {
        let Some(ComplexPoint::TypeInstance(value_t)) = self.complex() else {
            unreachable!("{:?}", self)
        };
        value_t
    }

    pub fn expect_assignment(&self) -> Assignment<'file> {
        Assignment::by_index(&self.file.tree, self.node_index)
    }

    pub fn expect_import_from(&self) -> ImportFrom<'file> {
        ImportFrom::by_index(&self.file.tree, self.node_index)
    }

    pub fn expect_atom(&self) -> Atom<'file> {
        Atom::by_index(&self.file.tree, self.node_index)
    }

    pub fn expect_class_storage(&self) -> &'file ClassStorage {
        let complex = self.complex().unwrap_or_else(|| {
            panic!(
                "Node {:?} ({}:{}) is not a complex class",
                self.file.tree.debug_info(self.node_index),
                self.file_index(),
                self.node_index
            )
        });
        match complex {
            ComplexPoint::Class(c) => c,
            _ => unreachable!("Probably an issue with indexing: {complex:?}"),
        }
    }

    pub fn ensure_cached_class_infos(&self, i_s: &InferenceState) {
        if !self
            .file
            .points
            .get(self.node_index + CLASS_TO_CLASS_INFO_DIFFERENCE as u32)
            .calculated()
        {
            let class_ref = NodeRef::new(self.file, self.node_index);
            let ComplexPoint::Class(cls_storage) = class_ref.complex().unwrap() else {
                unreachable!()
            };

            let class = Class::new(class_ref, cls_storage, Generics::NotDefinedYet, None);
            // Make sure the type vars and MRO are properly pre-calculated
            class.ensure_calculated_class_infos(i_s);
            let name_def = self.add_to_node_index(NAME_DEF_TO_CLASS_DIFF as i64);
            self.file
                .inference(i_s)
                .check_for_redefinition(name_def, |issue| name_def.add_issue(i_s, issue))
        }
    }

    pub fn debug_info(&self, db: &Database) -> String {
        format!(
            "{}: {}, {:?}",
            self.file.file_path(db),
            self.file.tree.debug_info(self.node_index),
            self.point(),
        )
    }

    pub fn compute_new_type_constraint(&self, i_s: &InferenceState) -> Type {
        self.file
            .inference(i_s)
            .compute_new_type_constraint(self.as_expression())
    }

    pub fn as_code(&self) -> &'file str {
        self.file.tree.code_of_index(self.node_index)
    }

    pub(crate) fn add_issue(&self, i_s: &InferenceState, kind: IssueKind) {
        let issue = Issue::from_node_index(&self.file.tree, self.node_index, kind);
        self.file.add_issue(i_s, issue)
    }

    pub(crate) fn issue_to_str(&self, i_s: &InferenceState, kind: IssueKind) -> String {
        let issue = Issue::from_node_index(&self.file.tree, self.node_index, kind);
        Diagnostic::new(i_s.db, self.file, &issue).message(&mut vec![])
    }

    pub(crate) fn add_issue_onto_start_including_decorator(
        &self,
        i_s: &InferenceState,
        kind: IssueKind,
    ) {
        debug_assert!(self.maybe_name().is_some());
        let func_node_ref = self.add_to_node_index(-(NAME_TO_FUNCTION_DIFF as i64));
        if func_node_ref.maybe_function().is_some() {
            Function::new(func_node_ref, None).add_issue_onto_start_including_decorator(i_s, kind)
        } else {
            self.add_issue(i_s, kind)
        }
    }

    pub fn finish_partial_with_annotation_needed(&self, i_s: &InferenceState) {
        let point = self.point();
        let mut partial_flags = point.partial_flags();
        partial_flags.finished = true;
        self.set_point(point.set_partial_flags(partial_flags));
        self.add_need_type_annotation_issue(i_s, point.specific())
    }

    pub fn add_need_type_annotation_issue(&self, i_s: &InferenceState, specific: Specific) {
        let hint = match specific {
            Specific::PartialNone => Some("<type> | None"),
            Specific::PartialList => Some("List[<type>]"),
            Specific::PartialDict => Some("Dict[<type>, <type>]"),
            Specific::PartialSet => Some("Set[<type>]"),
            Specific::PartialDefaultDict
            | Specific::PartialDefaultDictWithList
            | Specific::PartialDefaultDictWithSet => None,
            _ => unreachable!(),
        };
        let point = self.point();
        let mut partial_flags = point.partial_flags();
        if !partial_flags.reported_error && !self.file.flags(i_s.db).allow_untyped_globals {
            partial_flags.reported_error = true;
            self.set_point(point.set_partial_flags(partial_flags));
            self.add_issue(
                i_s,
                IssueKind::NeedTypeAnnotation {
                    for_: self.as_code().into(),
                    hint,
                },
            );
        }
    }

    pub fn maybe_name_of_function(&self) -> Option<FunctionDef<'file>> {
        self.node_index
            .checked_sub(NAME_TO_FUNCTION_DIFF)
            .and_then(|node_index| NodeRef::new(self.file, node_index).maybe_function())
    }

    pub fn node_start_position(self) -> CodeIndex {
        self.file.tree.node_start_position(self.node_index)
    }

    pub fn line(&self) -> usize {
        self.file.byte_to_line_column(self.node_start_position()).0
    }

    pub fn maybe_redirect<'db>(&self, db: &'db Database) -> Option<NodeRef<'db>> {
        let p = self.point();
        debug_assert!(p.calculated());
        (p.kind() == PointKind::Redirect).then(|| p.as_redirected_node_ref(db))
    }
}

impl fmt::Debug for NodeRef<'_> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        let mut s = f.debug_struct("NodeRef");
        s.field("file_index", &self.file.file_index);
        s.field("node_index", &self.node_index);
        s.field(
            "node",
            &self.file.tree.short_debug_of_index(self.node_index),
        );
        let point = self.point();
        s.field("point", &point);
        if let Some(complex_index) = point.maybe_complex_index() {
            s.field("complex", self.file.complex_points.get(complex_index));
        }
        s.finish()
    }
}
