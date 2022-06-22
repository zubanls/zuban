use parsa_python_ast::{ExpressionContent, ExpressionPart, NodeIndex, TypeLike};
use std::ptr::null;

use crate::database::{Database, Locality, Point, PointLink, PointType, Specific};
use crate::file::PythonFile;
use crate::file_state::File;
use crate::generics::Generics;
use crate::generics::Type;
use crate::node_ref::NodeRef;
use crate::value::{Class, ClassLike};

pub struct PythonState {
    builtins: *const PythonFile,
    typing: *const PythonFile,
    collections: *const PythonFile,
    builtins_object_node_index: NodeIndex,
    builtins_list_index: NodeIndex,
    builtins_tuple_index: NodeIndex,
    builtins_base_exception_index: NodeIndex,
}

impl PythonState {
    pub fn reserve() -> Self {
        Self {
            builtins: null(),
            typing: null(),
            collections: null(),
            builtins_object_node_index: 0,
            builtins_list_index: 0,
            builtins_tuple_index: 0,
            builtins_base_exception_index: 0,
        }
    }

    pub fn initialize(
        db: &mut Database,
        builtins: *const PythonFile,
        typing: *const PythonFile,
        collections: *const PythonFile,
    ) {
        let s = &mut db.python_state;
        s.builtins = builtins;
        s.typing = typing;
        s.collections = collections;
        let builtins = s.builtins();

        let object_name_index = builtins.symbol_table.lookup_symbol("object").unwrap();
        let list_name_index = builtins.symbol_table.lookup_symbol("list").unwrap();
        let tuple_name_index = builtins.symbol_table.lookup_symbol("tuple").unwrap();
        let base_exception_name_index = builtins
            .symbol_table
            .lookup_symbol("BaseException")
            .unwrap();

        s.builtins_object_node_index = s.builtins().points.get(object_name_index - 1).node_index();
        s.builtins_list_index = s.builtins().points.get(list_name_index - 1).node_index();
        s.builtins_tuple_index = s.builtins().points.get(tuple_name_index - 1).node_index();
        s.builtins_base_exception_index = s
            .builtins()
            .points
            .get(base_exception_name_index - 1)
            .node_index();

        // Needed because there's a loop for calculating the type var _T_co, which defines string
        // literal arguments arguments, which means that the class of those is str, which is a sub
        // class of Sequence[_T_co], which uses _T_co again.
        precalculate_type_var_instance(s.typing(), "_T_co");

        typing_changes(s.typing(), s.builtins(), s.collections());
    }

    #[inline]
    pub fn builtins(&self) -> &PythonFile {
        debug_assert!(!self.builtins.is_null());
        unsafe { &*self.builtins }
    }

    #[inline]
    pub fn typing(&self) -> &PythonFile {
        debug_assert!(!self.typing.is_null());
        unsafe { &*self.typing }
    }

    #[inline]
    pub fn collections(&self) -> &PythonFile {
        debug_assert!(!self.collections.is_null());
        unsafe { &*self.collections }
    }

    #[inline]
    pub fn object(&self) -> NodeRef {
        debug_assert!(self.builtins_object_node_index != 0);
        NodeRef::new(self.builtins(), self.builtins_object_node_index)
    }

    pub fn object_class(&self) -> Class {
        Class::from_position(self.object(), Generics::None, None).unwrap()
    }

    #[inline]
    pub fn list(&self) -> NodeRef {
        debug_assert!(self.builtins_list_index != 0);
        NodeRef::new(self.builtins(), self.builtins_list_index)
    }

    #[inline]
    pub fn tuple(&self) -> NodeRef {
        debug_assert!(self.builtins_tuple_index != 0);
        // TODO might be unused???
        NodeRef::new(self.builtins(), self.builtins_tuple_index)
    }

    #[inline]
    fn base_exception(&self) -> NodeRef {
        debug_assert!(self.builtins_base_exception_index != 0);
        NodeRef::new(self.builtins(), self.builtins_base_exception_index)
    }

    pub fn builtins_point_link(&self, name: &str) -> PointLink {
        // TODO I think these should all be available as cached PointLinks
        let builtins = self.builtins();
        let node_index = builtins.symbol_table.lookup_symbol(name).unwrap() - 1;
        let point = builtins.points.get(node_index);
        debug_assert_eq!(point.type_(), PointType::Redirect);
        PointLink::new(builtins.file_index(), point.node_index())
    }

    #[inline]
    pub fn base_exception_type(&self) -> Type {
        Type::ClassLike(ClassLike::Class(
            Class::from_position(self.base_exception(), Generics::None, None).unwrap(),
        ))
    }
}

fn typing_changes(typing: &PythonFile, builtins: &PythonFile, collections: &PythonFile) {
    set_typing_inference(typing, "Protocol", Specific::TypingProtocol);
    set_typing_inference(typing, "Generic", Specific::TypingGeneric);
    set_typing_inference(typing, "ClassVar", Specific::TypingClassVar);

    set_typing_inference(typing, "Union", Specific::TypingUnion);
    set_typing_inference(typing, "Optional", Specific::TypingOptional);
    set_typing_inference(typing, "Any", Specific::TypingAny);
    set_typing_inference(typing, "Callable", Specific::TypingCallable);
    set_typing_inference(typing, "Type", Specific::TypingType);

    set_typing_inference(builtins, "tuple", Specific::TypingTuple);
    set_typing_inference(builtins, "type", Specific::TypingType);

    set_typing_inference(typing, "cast", Specific::TypingCast);

    setup_type_alias(typing, "Tuple", builtins, "tuple");
    setup_type_alias(typing, "List", builtins, "list");
    setup_type_alias(typing, "Dict", builtins, "dict");
    setup_type_alias(typing, "Set", builtins, "set");
    setup_type_alias(typing, "FrozenSet", builtins, "frozenset");

    setup_type_alias(typing, "ChainMap", collections, "ChainMap");
    setup_type_alias(typing, "Counter", collections, "Counter");
    setup_type_alias(typing, "DefaultDict", collections, "defaultdict");
    setup_type_alias(typing, "Deque", collections, "deque");
    setup_type_alias(typing, "OrderedDict", collections, "OrderedDict");

    // TODO this is completely wrong, but for now it's good enough
    setup_type_alias(typing, "SupportsIndex", builtins, "int")
}

fn set_typing_inference(file: &PythonFile, name: &str, specific: Specific) {
    let node_index = file.symbol_table.lookup_symbol(name).unwrap();
    if !["cast", "type", "tuple"].contains(&name) {
        debug_assert!(!file.points.get(node_index).calculated());
        set_assignments_cached(file, node_index);
    }
    file.points.set(
        node_index,
        Point::new_simple_specific(specific, Locality::Stmt),
    );
}

fn setup_type_alias(typing: &PythonFile, name: &str, target_file: &PythonFile, target_name: &str) {
    let node_index = typing.symbol_table.lookup_symbol(name).unwrap();
    debug_assert!(!typing.points.get(node_index).calculated());
    let target_node_index = target_file.symbol_table.lookup_symbol(target_name).unwrap();
    typing.points.set(
        node_index, // Set it on name definition
        Point::new_redirect(target_file.file_index(), target_node_index, Locality::Stmt),
    );
}

fn set_assignments_cached(file: &PythonFile, name_node: NodeIndex) {
    // To avoid getting overwritten we also have to set the assignments to a proper state.
    let name = NodeRef::new(file, name_node).as_name();
    if let TypeLike::Assignment(assignment) = name.expect_type() {
        file.points
            .set(assignment.index(), Point::new_node_analysis(Locality::Stmt));
    } else {
        unreachable!();
    }
}

fn precalculate_type_var_instance(file: &PythonFile, name: &str) {
    let node_index = file.symbol_table.lookup_symbol(name).unwrap();
    let name = NodeRef::new(file, node_index).as_name();
    if let TypeLike::Assignment(assignment) = name.expect_type() {
        if let Some(expr) = assignment.maybe_simple_type_expression_assignment() {
            if let ExpressionContent::ExpressionPart(ExpressionPart::Primary(p)) = expr.unpack() {
                file.points.set(
                    p.index(),
                    Point::new_simple_specific(Specific::InstanceWithArguments, Locality::File),
                )
            }
        } else {
            unreachable!()
        }
    } else {
        unreachable!();
    }
}
