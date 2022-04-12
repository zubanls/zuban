use parsa_python_ast::{NodeIndex, TypeLike};
use std::ptr::null;

use crate::database::{Database, Locality, Point, PointLink, PointType, Specific};
use crate::file::PythonFile;
use crate::file_state::File;
use crate::node_ref::NodeRef;

pub struct PythonState {
    builtins: *const PythonFile,
    typing: *const PythonFile,
    collections: *const PythonFile,
    builtins_object_node_index: NodeIndex,
    builtins_list_index: NodeIndex,
}

impl PythonState {
    pub fn reserve() -> Self {
        Self {
            builtins: null(),
            typing: null(),
            collections: null(),
            builtins_object_node_index: 0,
            builtins_list_index: 0,
        }
    }

    pub fn initialize(
        database: &mut Database,
        builtins: *const PythonFile,
        typing: *const PythonFile,
        collections: *const PythonFile,
    ) {
        let s = &mut database.python_state;
        s.builtins = builtins;
        s.typing = typing;
        s.collections = collections;
        let builtins = s.builtins();

        let object_name_index = builtins.symbol_table.lookup_symbol("object").unwrap();
        let list_name_index = builtins.symbol_table.lookup_symbol("list").unwrap();

        s.builtins_object_node_index = s.builtins().points.get(object_name_index).node_index();
        s.builtins_list_index = s.builtins().points.get(list_name_index).node_index();

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

    #[inline]
    pub fn list(&self) -> NodeRef {
        debug_assert!(self.builtins_list_index != 0);
        NodeRef::new(self.builtins(), self.builtins_list_index)
    }

    pub fn builtins_point_link(&self, name: &str) -> PointLink {
        let builtins = self.builtins();
        let node_index = builtins.symbol_table.lookup_symbol(name).unwrap();
        let point = builtins.points.get(node_index);
        debug_assert_eq!(point.type_(), PointType::Redirect);
        PointLink::new(builtins.file_index(), point.node_index())
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

    // TODO this is completely wrong, but for now it's good enough
    setup_type_alias(builtins, "SupportsIndex", builtins, "int")
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
        node_index - 1, // Set it on name definition
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
