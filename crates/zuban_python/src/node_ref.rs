use std::fmt;

use parsa_python_cst::{
    Annotation, Assignment, BytesLiteral, ClassDef, CodeIndex, Expression, FunctionDef, ImportFrom,
    ImportName, Int, NAME_DEF_TO_NAME_DIFFERENCE, Name, NameDef, NameDefParent, NameImportParent,
    NamedExpression, NodeIndex, Primary, PrimaryTarget, Scope, Slices, StarExpression,
    StarStarExpression, StarredExpression, StringLiteral,
};
use vfs::FileIndex;

use crate::{
    database::{
        ComplexPoint, Database, Locality, Point, PointKind, PointLink, Specific, TypeAlias,
    },
    diagnostics::{Diagnostic, Issue, IssueKind},
    file::{
        CLASS_TO_CLASS_INFO_DIFFERENCE, ClassInitializer, ClassNodeRef, File,
        GLOBAL_NONLOCAL_TO_NAME_DIFFERENCE, OtherDefinitionIterator, PythonFile,
    },
    inference_state::InferenceState,
    inferred::Inferred,
    python_state::{NAME_DEF_TO_CLASS_DIFF, NAME_TO_CLASS_DIFF, NAME_TO_FUNCTION_DIFF},
    type_::{StringSlice, Type},
    type_helpers::Function,
};

#[derive(Clone, Copy)]
pub(crate) struct NodeRef<'file> {
    pub file: &'file PythonFile,
    pub node_index: NodeIndex,
}

impl std::cmp::PartialEq for NodeRef<'_> {
    fn eq(&self, other: &Self) -> bool {
        std::ptr::eq(self.file, other.file) && self.node_index == other.node_index
    }
}

impl<'file> NodeRef<'file> {
    #[inline]
    pub fn new(file: &'file PythonFile, node_index: NodeIndex) -> Self {
        Self { file, node_index }
    }

    pub fn from_link(db: &'file Database, link: PointLink) -> Self {
        let file = db.loaded_python_file(link.file);
        Self {
            file,
            node_index: link.node_index,
        }
    }

    #[inline]
    pub fn to_db_lifetime(self, _: &Database) -> NodeRef<'_> {
        // This should be safe, because all files are added to the database.
        unsafe { std::mem::transmute(self) }
    }

    #[inline]
    pub fn add_to_node_index(&self, add: i64) -> Self {
        Self::new(self.file, ((self.node_index as i64) + add) as NodeIndex)
    }

    #[inline]
    pub fn name_def_ref_of_name(&self) -> Self {
        let n = Self::new(self.file, self.node_index - NAME_DEF_TO_NAME_DIFFERENCE);
        debug_assert!(n.maybe_name_def().is_some());
        n
    }

    #[inline]
    pub fn name_ref_of_name_def(&self) -> Self {
        let n = Self::new(self.file, self.node_index + NAME_DEF_TO_NAME_DIFFERENCE);
        debug_assert!(n.maybe_name().is_some(), "Why is this not a name: {self:?}");
        n
    }

    pub fn global_or_nonlocal_ref(&self) -> Self {
        debug_assert!(self.maybe_name_def().is_some());
        debug_assert!(matches!(
            self.expect_name_def().parent(),
            NameDefParent::GlobalStmt | NameDefParent::NonlocalStmt
        ));
        let node_index =
            self.node_index - GLOBAL_NONLOCAL_TO_NAME_DIFFERENCE + NAME_DEF_TO_NAME_DIFFERENCE;
        Self {
            file: self.file,
            node_index,
        }
    }

    pub fn point(&self) -> Point {
        self.file.points.get(self.node_index)
    }

    pub fn set_point(&self, point: Point) {
        self.file.points.set(self.node_index, point)
    }

    pub fn string_slice(&self) -> StringSlice {
        //self.start()
        StringSlice::new(
            self.file_index(),
            self.node_start_position(),
            self.node_end_position(),
        )
    }

    pub fn as_redirection_point(&self, locality: Locality) -> Point {
        Point::new_redirect(self.file.file_index, self.node_index, locality)
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

    pub fn maybe_complex(&self) -> Option<&'file ComplexPoint> {
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
        match self.maybe_complex() {
            Some(ComplexPoint::TypeAlias(alias)) => Some(alias),
            _ => None,
        }
    }

    pub fn maybe_type(&self) -> Option<&'file Type> {
        self.maybe_complex().and_then(|c| c.maybe_instance())
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

    pub fn expect_expression(&self) -> Expression<'file> {
        Expression::by_index(&self.file.tree, self.node_index)
    }

    pub fn expect_star_expression(&self) -> StarExpression<'file> {
        StarExpression::by_index(&self.file.tree, self.node_index)
    }

    pub fn expect_slices(&self) -> Slices<'file> {
        Slices::by_index(&self.file.tree, self.node_index)
    }

    pub fn expect_primary(&self) -> Primary<'file> {
        Primary::by_index(&self.file.tree, self.node_index)
    }

    pub fn expect_name(&self) -> Name<'file> {
        Name::by_index(&self.file.tree, self.node_index)
    }

    pub fn expect_name_def(&self) -> NameDef<'file> {
        NameDef::by_index(&self.file.tree, self.node_index)
    }

    pub fn expect_annotation(&self) -> Annotation<'file> {
        Annotation::by_index(&self.file.tree, self.node_index)
    }

    pub fn expect_bytes_literal(&self) -> BytesLiteral<'file> {
        BytesLiteral::by_index(&self.file.tree, self.node_index)
    }

    pub fn expect_int(&self) -> Int<'file> {
        Int::by_index(&self.file.tree, self.node_index)
    }

    pub fn expect_named_expression(&self) -> NamedExpression<'file> {
        NamedExpression::by_index(&self.file.tree, self.node_index)
    }

    pub fn expect_assignment(&self) -> Assignment<'file> {
        Assignment::by_index(&self.file.tree, self.node_index)
    }

    pub fn expect_import_from(&self) -> ImportFrom<'file> {
        ImportFrom::by_index(&self.file.tree, self.node_index)
    }

    pub fn expect_import_name(&self) -> ImportName<'file> {
        ImportName::by_index(&self.file.tree, self.node_index)
    }

    pub fn expect_function(&self) -> FunctionDef<'file> {
        FunctionDef::by_index(&self.file.tree, self.node_index)
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

    pub fn maybe_import_from(&self) -> Option<ImportFrom<'file>> {
        ImportFrom::maybe_by_index(&self.file.tree, self.node_index)
    }

    pub fn maybe_import_of_name_in_symbol_table(&self) -> Option<NameImportParent<'file>> {
        self.expect_name().name_def().unwrap().maybe_import()
    }

    pub fn maybe_str(&self) -> Option<StringLiteral<'file>> {
        StringLiteral::maybe_by_index(&self.file.tree, self.node_index)
    }

    pub fn maybe_class(&self) -> Option<ClassDef<'file>> {
        ClassDef::maybe_by_index(&self.file.tree, self.node_index)
    }

    pub fn maybe_primary_target(&self) -> Option<PrimaryTarget<'file>> {
        PrimaryTarget::maybe_by_index(&self.file.tree, self.node_index)
    }

    #[inline]
    pub fn file_index(&self) -> FileIndex {
        self.file.file_index
    }

    pub fn maybe_inferred(&self, i_s: &InferenceState) -> Option<Inferred> {
        self.file.inference(i_s).check_point_cache(self.node_index)
    }

    pub fn expect_inferred(&self, i_s: &InferenceState) -> Inferred {
        self.maybe_inferred(i_s).unwrap()
    }

    pub fn expect_complex_type(&self) -> &Type {
        self.maybe_type()
            .unwrap_or_else(|| unreachable!("{:?}", self))
    }

    pub fn ensure_cached_class_infos(&self, i_s: &InferenceState) {
        if !self
            .file
            .points
            .get(self.node_index + CLASS_TO_CLASS_INFO_DIFFERENCE as u32)
            .calculated()
        {
            let class_ref = ClassNodeRef::new(self.file, self.node_index);
            let ComplexPoint::Class(cls_storage) = class_ref.maybe_complex().unwrap() else {
                unreachable!("{self:?}")
            };

            let class = ClassInitializer::new(class_ref, cls_storage);
            // Make sure the type vars and MRO are properly pre-calculated
            class.ensure_calculated_class_infos(i_s.db);
            let name_def = self.add_to_node_index(NAME_DEF_TO_CLASS_DIFF as i64);
            self.file
                .inference(i_s)
                .check_for_redefinition(name_def, |issue| name_def.add_issue(i_s, issue))
        }
    }

    pub fn debug_info(&self, db: &Database) -> String {
        format!(
            "{}({}):#{}",
            self.file.qualified_name(db),
            self.file_index(),
            self.line_one_based(db),
        )
    }

    pub fn as_code(&self) -> &'file str {
        self.file.tree.code_of_index(self.node_index)
    }

    /// Returns false if the issue was not added
    pub(crate) fn maybe_add_issue(&self, i_s: &InferenceState, kind: IssueKind) -> bool {
        let issue = Issue::from_node_index(&self.file.tree, self.node_index, kind, false);
        self.file.maybe_add_issue(i_s, issue)
    }

    pub(crate) fn add_issue(&self, i_s: &InferenceState, kind: IssueKind) -> bool {
        self.maybe_add_issue(i_s, kind)
    }

    pub(crate) fn add_type_issue(&self, db: &Database, kind: IssueKind) -> bool {
        if kind.is_disabled(self.file.flags(db)) {
            return false;
        }
        let issue = Issue::from_node_index(&self.file.tree, self.node_index, kind, false);
        self.file
            .add_issue_without_checking_for_disabled_error_codes(db, issue)
    }

    pub(crate) fn issue_to_str(&self, i_s: &InferenceState, kind: IssueKind) -> String {
        let issue = Issue::from_node_index(&self.file.tree, self.node_index, kind, false);
        Diagnostic::new(i_s.db, self.file, &issue).message_with_notes(&mut vec![])
    }

    pub(crate) fn add_issue_and_prefer_on_setter_decorator(
        &self,
        i_s: &InferenceState,
        kind: IssueKind,
    ) {
        if self.maybe_name().is_some() {
            // Find @foo.setter for a property foo
            // This is a heuristic, but is probably working well enough. Worst case a
            // diagnostic is not in the same place as in Mypy (but is still valid)
            for n in OtherDefinitionIterator::new(&self.file.points, self.node_index) {
                // Get the next name:
                //
                //     @property
                //     def foo(self) -> int: ...     # We are on foo
                //     @foo.setter                   # We want to land on this decorator
                //     def foo(self, new: int): ...  # The next name is foo
                let func_node_ref = Self::new(self.file, n - NAME_TO_FUNCTION_DIFF);
                if let Some(func) = func_node_ref.maybe_function()
                    && let Some(decorated) = func.maybe_decorated()
                {
                    for decorator in decorated.decorators().iter() {
                        let decorator_expr = decorator.named_expression();
                        if decorator_expr.as_code().ends_with(".setter") {
                            Self::new(self.file, decorator_expr.index()).add_issue(i_s, kind);
                            return;
                        }
                    }
                }
            }
        }
        self.add_issue(i_s, kind);
    }

    pub(crate) fn add_issue_onto_start_including_decorator(
        &self,
        i_s: &InferenceState,
        kind: IssueKind,
    ) {
        let func_node_ref = self.add_to_node_index(-(NAME_TO_FUNCTION_DIFF as i64));
        if func_node_ref.maybe_function().is_some() {
            Function::new(func_node_ref, None).add_issue_onto_start_including_decorator(i_s, kind);
        } else {
            self.add_issue(i_s, kind);
        }
    }

    pub fn finish_partial_with_annotation_needed(&self, db: &Database) {
        let point = self.point();
        let mut partial_flags = point.partial_flags();
        partial_flags.finished = true;
        self.set_point(point.set_partial_flags(partial_flags));
        self.add_need_type_annotation_issue(db, point.specific())
    }

    pub fn add_need_type_annotation_issue(&self, db: &Database, specific: Specific) {
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
        if !partial_flags.reported_error && !self.file.flags(db).allow_untyped_globals {
            partial_flags.reported_error = true;
            self.set_point(point.set_partial_flags(partial_flags));
            if !db.project.flags.allow_incomplete_generics {
                let for_ = self.as_code();
                self.add_type_issue(
                    db,
                    IssueKind::NeedTypeAnnotation {
                        for_: for_.into(),
                        hint,
                    },
                );
            }
        }
    }

    pub fn maybe_name_of_function(&self) -> Option<FunctionDef<'file>> {
        let n = self.node_index.checked_sub(NAME_TO_FUNCTION_DIFF)?;
        NodeRef::new(self.file, n).maybe_function()
    }

    pub fn maybe_name_of_class(&self) -> Option<ClassDef<'file>> {
        let n = self.node_index.checked_sub(NAME_TO_CLASS_DIFF)?;
        NodeRef::new(self.file, n).maybe_class()
    }

    pub fn node_start_position(self) -> CodeIndex {
        self.file.tree.node_start_position(self.node_index)
    }

    pub fn node_end_position(self) -> CodeIndex {
        self.file.tree.node_end_position(self.node_index)
    }

    pub fn node_parent_scope(self) -> Scope<'file> {
        self.file.tree.node_parent_scope(self.node_index)
    }

    pub fn line_one_based(&self, db: &Database) -> usize {
        self.file
            .byte_to_position_infos(db, self.node_start_position())
            .line_one_based()
    }

    pub fn maybe_redirect<'db>(&self, db: &'db Database) -> Option<NodeRef<'db>> {
        let p = self.point();
        debug_assert!(p.calculated());
        (p.kind() == PointKind::Redirect).then(|| p.as_redirected_node_ref(db))
    }

    pub fn is_name_defined_in_module(
        &self,
        db: &Database,
        module_name: &str,
        symbol_name: &str,
    ) -> bool {
        let (name, parent_dir) = self.file.name_and_parent_dir(db);
        if parent_dir.is_some() || name != module_name {
            return false;
        }
        self.maybe_function()
            .is_some_and(|f| f.name().as_code() == symbol_name)
            || self
                .maybe_class()
                .is_some_and(|c| c.name().as_code() == symbol_name)
    }

    pub fn infer_name_of_definition_by_index(&self, i_s: &InferenceState) -> Inferred {
        self.file
            .inference(i_s)
            .infer_name_of_definition_by_index(self.node_index)
    }
}

impl fmt::Debug for NodeRef<'_> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        let mut s = f.debug_struct("NodeRef");
        s.field(
            "node",
            &self.file.tree.short_debug_of_index(self.node_index),
        );
        let point = self.point();
        s.field("point", &point);
        if let Some(complex_index) = point.maybe_complex_index() {
            let complex_point = self.file.complex_points.get(complex_index);
            if matches!(complex_point, ComplexPoint::Class(_)) {
                s.field("complex", &"ClassStorage { .. }");
            } else {
                s.field("complex", complex_point);
            }
        }
        s.field("file_index", &self.file.file_index);
        s.field("node_index", &self.node_index);
        s.finish()
    }
}
