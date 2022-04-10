use parsa_python_ast::{
    Atom, AtomContent, ClassDef, Expression, Name, NamedExpression, NodeIndex, Primary, PyString,
    PythonString,
};

use crate::database::{ComplexPoint, Database, Locality, Point, PointLink, PointType};
use crate::debug;
use crate::diagnostics::{Diagnostic, Issue, IssueType};
use crate::file::PythonFile;
use crate::file_state::File;

#[derive(Debug, Clone, Copy)]
pub struct NodeRef<'db> {
    pub file: &'db PythonFile,
    pub node_index: NodeIndex,
}

impl<'db> std::cmp::PartialEq for NodeRef<'db> {
    fn eq(&self, other: &Self) -> bool {
        std::ptr::eq(self.file, other.file) && self.node_index == other.node_index
    }
}

impl<'db> NodeRef<'db> {
    pub fn new(file: &'db PythonFile, node_index: NodeIndex) -> Self {
        Self { file, node_index }
    }

    pub fn from_link(database: &'db Database, point: PointLink) -> Self {
        let file = database.loaded_python_file(point.file);
        Self {
            file,
            node_index: point.node_index,
        }
    }

    pub fn add_to_node_index(&self, add: NodeIndex) -> Self {
        Self::new(self.file, self.node_index + add)
    }

    pub fn point(&self) -> Point {
        self.file.points.get(self.node_index)
    }

    pub fn set_point(&self, point: Point) {
        self.file.points.set(self.node_index, point)
    }

    pub fn complex(&self) -> Option<&'db ComplexPoint> {
        let point = self.point();
        if let PointType::Complex = point.type_() {
            Some(self.file.complex_points.get(point.complex_index()))
        } else {
            None
        }
    }

    pub fn insert_complex(&self, complex: ComplexPoint, locality: Locality) {
        self.file
            .complex_points
            .insert(&self.file.points, self.node_index, complex, locality);
    }

    pub fn as_link(&self) -> PointLink {
        PointLink::new(self.file.file_index(), self.node_index)
    }

    pub fn as_expression(&self) -> Expression<'db> {
        Expression::by_index(&self.file.tree, self.node_index)
    }

    pub fn as_primary(&self) -> Primary<'db> {
        Primary::by_index(&self.file.tree, self.node_index)
    }

    pub fn as_name(&self) -> Name<'db> {
        Name::by_index(&self.file.tree, self.node_index)
    }

    pub fn infer_int(&self) -> Option<i64> {
        Atom::maybe_by_index(&self.file.tree, self.node_index).and_then(|atom| {
            match atom.unpack() {
                AtomContent::Int(i) => i.as_str().parse().ok(),
                _ => None,
            }
        })
    }

    pub fn infer_str(&self) -> Option<PythonString<'db>> {
        Atom::maybe_by_index(&self.file.tree, self.node_index).and_then(|atom| {
            match atom.unpack() {
                AtomContent::StringsOrBytes(s) => s.as_python_string(),
                _ => None,
            }
        })
    }

    pub fn maybe_str(&self) -> Option<PyString<'db>> {
        PyString::maybe_by_index(&self.file.tree, self.node_index)
    }

    pub fn maybe_class(&self) -> Option<ClassDef<'db>> {
        ClassDef::maybe_by_index(&self.file.tree, self.node_index)
    }

    pub fn as_named_expression(&self) -> NamedExpression<'db> {
        NamedExpression::by_index(&self.file.tree, self.node_index)
    }

    pub fn debug_info(&self, db: &Database) -> String {
        format!(
            "{}: {}",
            self.file.file_path(db),
            self.file.tree.debug_info(self.node_index)
        )
    }

    pub fn add_typing_issue(&self, db: &Database, issue_type: IssueType) {
        let issue = Issue {
            type_: issue_type,
            node_index: self.node_index,
        };
        if self.file.tree.node_has_type_ignore_comment(self.node_index) {
            debug!(
                "New ignored issue: {}",
                Diagnostic::new(db, self.file, &issue).as_string()
            );
            return;
        }
        debug!(
            "New issue: {}",
            Diagnostic::new(db, self.file, &issue).as_string()
        );
        self.file.issues.push(Box::pin(issue));
    }
}
