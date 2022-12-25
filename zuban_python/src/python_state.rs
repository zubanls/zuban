use parsa_python_ast::{NodeIndex, TypeLike};
use std::ptr::null;
use std::rc::Rc;

use crate::database::{
    ComplexPoint, Database, DbType, Literal, LiteralKind, Locality, Point, PointLink, PointType,
    Specific, TupleContent,
};
use crate::file::File;
use crate::file::PythonFile;
use crate::matching::Generics;
use crate::node_ref::NodeRef;
use crate::value::{Class, Instance, OverloadedFunction};
use crate::PythonProject;

pub struct PythonState {
    pub project: PythonProject,

    builtins: *const PythonFile,
    typing: *const PythonFile,
    collections: *const PythonFile,
    types: *const PythonFile,
    mypy_extensions: *const PythonFile,
    typing_extensions: *const PythonFile,

    builtins_object_node_index: NodeIndex,
    builtins_list_index: NodeIndex,
    builtins_tuple_index: NodeIndex,
    builtins_function_index: NodeIndex,
    builtins_base_exception_index: NodeIndex,
    builtins_str_index: NodeIndex,
    typing_mapping_index: NodeIndex,
    types_module_type_index: NodeIndex,
    mypy_extensions_arg_func: NodeIndex,
    mypy_extensions_default_arg_func: NodeIndex,
    mypy_extensions_named_arg_func: NodeIndex,
    mypy_extensions_default_named_arg_func: NodeIndex,
    mypy_extensions_kw_arg_func: NodeIndex,
    mypy_extensions_var_arg_func: NodeIndex,
    pub type_of_object: DbType,
    pub type_of_any: DbType,
    pub type_of_arbitrary_tuple: DbType,
}

impl PythonState {
    pub fn reserve(project: PythonProject) -> Self {
        Self {
            project,
            builtins: null(),
            typing: null(),
            collections: null(),
            types: null(),
            mypy_extensions: null(),
            typing_extensions: null(),
            builtins_object_node_index: 0,
            builtins_list_index: 0,
            builtins_tuple_index: 0,
            builtins_function_index: 0,
            builtins_base_exception_index: 0,
            builtins_str_index: 0,
            types_module_type_index: 0,
            typing_mapping_index: 0,
            mypy_extensions_arg_func: 0,
            mypy_extensions_default_arg_func: 0,
            mypy_extensions_named_arg_func: 0,
            mypy_extensions_default_named_arg_func: 0,
            mypy_extensions_kw_arg_func: 0,
            mypy_extensions_var_arg_func: 0,
            type_of_object: DbType::Any, // Will be set later
            type_of_any: DbType::Type(Rc::new(DbType::Any)),
            type_of_arbitrary_tuple: DbType::Type(Rc::new(
                DbType::Tuple(TupleContent::new_empty()),
            )),
        }
    }

    pub fn initialize(
        db: &mut Database,
        builtins: *const PythonFile,
        typing: *const PythonFile,
        collections: *const PythonFile,
        types: *const PythonFile,
        typing_extensions: *const PythonFile,
        mypy_extensions: *const PythonFile,
    ) {
        let s = &mut db.python_state;
        s.builtins = builtins;
        s.typing = typing;
        s.collections = collections;
        s.types = types;
        s.typing_extensions = typing_extensions;
        s.mypy_extensions = mypy_extensions;
        let builtins = s.builtins();
        let typing = s.typing();

        let object_name_index = builtins.symbol_table.lookup_symbol("object").unwrap();
        let list_name_index = builtins.symbol_table.lookup_symbol("list").unwrap();
        let tuple_name_index = builtins.symbol_table.lookup_symbol("tuple").unwrap();
        let str_name_index = builtins.symbol_table.lookup_symbol("str").unwrap();
        let function_name_index = builtins.symbol_table.lookup_symbol("function").unwrap();
        let base_exception_name_index = builtins
            .symbol_table
            .lookup_symbol("BaseException")
            .unwrap();
        let typing_mapping_name_index = typing.symbol_table.lookup_symbol("Mapping").unwrap();
        let module_type_name_index = s.types().symbol_table.lookup_symbol("ModuleType").unwrap();

        s.builtins_object_node_index = s.builtins().points.get(object_name_index - 1).node_index();
        s.builtins_list_index = s.builtins().points.get(list_name_index - 1).node_index();
        s.builtins_tuple_index = s.builtins().points.get(tuple_name_index - 1).node_index();
        s.builtins_function_index = s
            .builtins()
            .points
            .get(function_name_index - 1)
            .node_index();
        s.builtins_base_exception_index = s
            .builtins()
            .points
            .get(base_exception_name_index - 1)
            .node_index();
        s.builtins_str_index = s.builtins().points.get(str_name_index - 1).node_index();

        s.typing_mapping_index = s
            .typing()
            .points
            .get(typing_mapping_name_index - 1)
            .node_index();
        s.types_module_type_index = s
            .types()
            .points
            .get(module_type_name_index - 1)
            .node_index();

        let object_db_type = s.object_db_type();
        s.type_of_object = DbType::Type(Rc::new(object_db_type));

        typing_changes(
            s.typing(),
            s.builtins(),
            s.collections(),
            s.typing_extensions(),
        );

        let mypy_extensions = unsafe { &*s.mypy_extensions };
        let mypy_ext_typed_dict_index = mypy_extensions
            .symbol_table
            .lookup_symbol("TypedDict")
            .unwrap();
        set_specific(
            mypy_extensions,
            mypy_ext_typed_dict_index,
            Specific::TypedDict,
        );
        s.mypy_extensions_arg_func =
            set_mypy_extension_specific(mypy_extensions, "Arg", Specific::MypyExtensionsArg);
        s.mypy_extensions_default_arg_func = set_mypy_extension_specific(
            mypy_extensions,
            "DefaultArg",
            Specific::MypyExtensionsDefaultArg,
        );
        s.mypy_extensions_named_arg_func = set_mypy_extension_specific(
            mypy_extensions,
            "NamedArg",
            Specific::MypyExtensionsNamedArg,
        );
        s.mypy_extensions_default_named_arg_func = set_mypy_extension_specific(
            mypy_extensions,
            "DefaultNamedArg",
            Specific::MypyExtensionsDefaultNamedArg,
        );
        s.mypy_extensions_var_arg_func =
            set_mypy_extension_specific(mypy_extensions, "VarArg", Specific::MypyExtensionsVarArg);
        s.mypy_extensions_kw_arg_func =
            set_mypy_extension_specific(mypy_extensions, "KwArg", Specific::MypyExtensionsKwArg);
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
    pub fn types(&self) -> &PythonFile {
        debug_assert!(!self.types.is_null());
        unsafe { &*self.types }
    }

    #[inline]
    pub fn typing_extensions(&self) -> &PythonFile {
        debug_assert!(!self.typing_extensions.is_null());
        unsafe { &*self.typing_extensions }
    }

    #[inline]
    pub fn mypy_extensions(&self) -> &PythonFile {
        debug_assert!(!self.mypy_extensions.is_null());
        unsafe { &*self.mypy_extensions }
    }

    #[inline]
    pub fn object(&self) -> NodeRef {
        debug_assert!(self.builtins_object_node_index != 0);
        NodeRef::new(self.builtins(), self.builtins_object_node_index)
    }

    #[inline]
    pub fn object_db_type(&self) -> DbType {
        DbType::Class(self.object().as_link(), None)
    }

    #[inline]
    pub fn object_class(&self) -> Class {
        Class::from_position(self.object(), Generics::None, None).unwrap()
    }

    #[inline]
    pub fn list(&self) -> NodeRef {
        debug_assert!(self.builtins_list_index != 0);
        NodeRef::new(self.builtins(), self.builtins_list_index)
    }

    #[inline]
    pub fn tuple(&self) -> Class {
        debug_assert!(self.builtins_tuple_index != 0);
        Class::from_position(
            NodeRef::new(self.builtins(), self.builtins_tuple_index),
            Generics::Any,
            None,
        )
        .unwrap()
    }

    #[inline]
    pub fn str(&self) -> Class {
        Class::from_position(self.str_node_ref(), Generics::None, None).unwrap()
    }

    #[inline]
    pub fn str_node_ref(&self) -> NodeRef {
        debug_assert!(self.builtins_str_index != 0);
        NodeRef::new(self.builtins(), self.builtins_str_index)
    }

    pub fn builtins_point_link(&self, name: &str) -> PointLink {
        // TODO I think these should all be available as cached PointLinks
        let builtins = self.builtins();
        let node_index = builtins.symbol_table.lookup_symbol(name).unwrap() - 1;
        let point = builtins.points.get(node_index);
        debug_assert_eq!(point.type_(), PointType::Redirect);
        PointLink::new(builtins.file_index(), point.node_index())
    }

    pub fn function_point_link(&self) -> PointLink {
        PointLink::new(self.builtins().file_index(), self.builtins_function_index)
    }

    #[inline]
    pub fn base_exception(&self) -> DbType {
        debug_assert!(self.builtins_base_exception_index != 0);
        DbType::Class(
            PointLink::new(
                self.builtins().file_index(),
                self.builtins_base_exception_index,
            ),
            None,
        )
    }

    #[inline]
    pub fn module_type(&self) -> Class {
        debug_assert!(self.types_module_type_index != 0);
        let node_ref = NodeRef::new(self.types(), self.types_module_type_index);
        Class::from_position(node_ref, Generics::None, None).unwrap()
    }

    pub fn mapping_node_ref(&self) -> NodeRef {
        NodeRef::new(self.typing(), self.typing_mapping_index)
    }

    pub fn mypy_extensions_arg_func(&self, specific: Specific) -> OverloadedFunction {
        let node_index = match specific {
            Specific::MypyExtensionsArg => self.mypy_extensions_arg_func,
            Specific::MypyExtensionsDefaultArg => self.mypy_extensions_default_arg_func,
            Specific::MypyExtensionsNamedArg => self.mypy_extensions_named_arg_func,
            Specific::MypyExtensionsDefaultNamedArg => self.mypy_extensions_default_named_arg_func,
            Specific::MypyExtensionsVarArg => self.mypy_extensions_var_arg_func,
            Specific::MypyExtensionsKwArg => self.mypy_extensions_kw_arg_func,
            _ => unreachable!(),
        };
        let node_ref = NodeRef::new(self.mypy_extensions(), node_index);
        let overload = match node_ref.complex().unwrap() {
            ComplexPoint::FunctionOverload(overload) => overload,
            _ => unreachable!(),
        };
        OverloadedFunction::new(node_ref, overload, None)
    }

    pub fn literal_instance<'db>(&self, db: &'db Database, literal: Literal) -> Instance<'db> {
        use crate::inferred::load_builtin_instance_from_str;
        load_builtin_instance_from_str(
            db,
            match literal.kind(db) {
                LiteralKind::Integer => "int",
                LiteralKind::String => todo!(),
                LiteralKind::Boolean => todo!(),
                LiteralKind::Bytes => todo!(),
            },
        )
    }
}

fn typing_changes(
    typing: &PythonFile,
    builtins: &PythonFile,
    collections: &PythonFile,
    typing_extensions: &PythonFile,
) {
    set_typing_inference(typing, "Protocol", Specific::TypingProtocol);
    set_typing_inference(typing, "Generic", Specific::TypingGeneric);
    set_typing_inference(typing, "ClassVar", Specific::TypingClassVar);

    set_typing_inference(typing, "Union", Specific::TypingUnion);
    set_typing_inference(typing, "Optional", Specific::TypingOptional);
    set_typing_inference(typing, "Any", Specific::TypingAny);
    set_typing_inference(typing, "Callable", Specific::TypingCallable);
    set_typing_inference(typing, "Type", Specific::TypingType);
    set_typing_inference(typing, "NewType", Specific::TypingNewType);
    set_typing_inference(typing, "TypeVar", Specific::TypingTypeVarClass);
    set_typing_inference(typing, "TypeVarTuple", Specific::TypingTypeVarTupleClass);
    set_typing_inference(typing, "Concatenate", Specific::TypingConcatenateClass);
    set_typing_inference(typing, "ParamSpec", Specific::TypingParamSpecClass);
    set_typing_inference(typing, "LiteralString", Specific::TypingLiteralString);
    set_typing_inference(typing, "Literal", Specific::TypingLiteral);
    set_typing_inference(typing, "Final", Specific::TypingFinal);
    set_typing_inference(typing, "TypedDict", Specific::TypedDict);
    set_typing_inference(typing, "Unpack", Specific::TypingUnpack);
    set_typing_inference(typing, "TypeAlias", Specific::TypingTypeAlias);

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

    let t = typing_extensions;
    // TODO this is completely wrong, but for now it's good enough
    setup_type_alias(t, "SupportsIndex", builtins, "int");
    set_typing_inference(t, "LiteralString", Specific::TypingLiteralString);
    set_typing_inference(t, "Literal", Specific::TypingLiteral);
    set_typing_inference(t, "Final", Specific::TypingFinal);
    set_typing_inference(t, "TypedDict", Specific::TypedDict);
    set_typing_inference(t, "Unpack", Specific::TypingUnpack);
    set_typing_inference(t, "ParamSpec", Specific::TypingParamSpecClass);
    set_typing_inference(t, "TypeVarTuple", Specific::TypingTypeVarTupleClass);
    set_typing_inference(t, "Concatenate", Specific::TypingConcatenateClass);
    set_typing_inference(t, "TypeAlias", Specific::TypingTypeAlias);
}

fn set_typing_inference(file: &PythonFile, name: &str, specific: Specific) {
    let node_index = file.symbol_table.lookup_symbol(name).unwrap();
    if ![
        "cast",
        "type",
        "tuple",
        "NewType",
        "TypeVar",
        "TypeVarTuple",
        "LiteralString",
        "Concatenate",
        "ParamSpec",
        "Unpack",
        "TypeAlias",
    ]
    .contains(&name)
    {
        let p = file.points.get(node_index).calculated();
        assert!(!p, "{:?}", p);
        set_assignments_cached(file, node_index);
    }
    set_specific(file, node_index, specific)
}

fn set_specific(file: &PythonFile, node_index: NodeIndex, specific: Specific) {
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

fn set_mypy_extension_specific(file: &PythonFile, name: &str, specific: Specific) -> NodeIndex {
    let node_index = file.symbol_table.lookup_symbol(name).unwrap();
    // Act on the name def index and not the name.
    let old_point = file.points.get(node_index);
    file.points.set(
        node_index,
        Point::new_simple_specific(specific, Locality::Stmt),
    );
    debug_assert!(!old_point.calculated());
    node_index - 1
}
