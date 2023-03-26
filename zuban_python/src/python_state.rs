use parsa_python_ast::{NodeIndex, TypeLike};
use std::ptr::null;
use std::rc::Rc;

use crate::database::{
    ComplexPoint, Database, DbType, LiteralKind, Locality, Point, PointLink, Specific, TupleContent,
};
use crate::file::File;
use crate::file::PythonFile;
use crate::matching::Generics;
use crate::node_ref::NodeRef;
use crate::value::{Class, OverloadedFunction};
use crate::{InferenceState, PythonProject};

// This is a bit hacky, but I'm sure the tests will fail somewhere if this constant is
// wrong. Basically it goes three nodes back: name_def class literal and then the actual
// class.
const NAME_TO_CLASS_DIFF: u32 = 3;

macro_rules! builtins_attribute_node_ref {
    ($name:ident, $attr:ident) => {
        #[inline]
        pub fn $name(&self) -> NodeRef {
            debug_assert!(self.$attr != 0);
            NodeRef::new(self.builtins(), self.$attr)
        }
    };
}

macro_rules! node_ref_to_class {
    ($vis:vis $name:ident, $from_node_ref:ident) => {
        #[inline]
        $vis fn $name(&self) -> Class {
            Class::from_position(self.$from_node_ref(), Generics::None, None)
        }
    };
}

pub struct PythonState {
    pub project: PythonProject,

    builtins: *const PythonFile,
    typing: *const PythonFile,
    collections: *const PythonFile,
    types: *const PythonFile,
    mypy_extensions: *const PythonFile,
    typing_extensions: *const PythonFile,

    builtins_object_index: NodeIndex,
    builtins_list_index: NodeIndex,
    builtins_tuple_index: NodeIndex,
    builtins_dict_index: NodeIndex,
    builtins_bool_index: NodeIndex,
    builtins_int_index: NodeIndex,
    builtins_float_index: NodeIndex,
    builtins_complex_index: NodeIndex,
    builtins_function_index: NodeIndex,
    builtins_base_exception_index: NodeIndex,
    builtins_str_index: NodeIndex,
    builtins_bytes_index: NodeIndex,
    builtins_bytearray_index: NodeIndex,
    builtins_memoryview_index: NodeIndex,
    builtins_slice_index: NodeIndex,
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
            builtins_object_index: 0,
            builtins_list_index: 0,
            builtins_tuple_index: 0,
            builtins_dict_index: 0,
            builtins_bool_index: 0,
            builtins_int_index: 0,
            builtins_float_index: 0,
            builtins_complex_index: 0,
            builtins_function_index: 0,
            builtins_base_exception_index: 0,
            builtins_str_index: 0,
            builtins_bytes_index: 0,
            builtins_bytearray_index: 0,
            builtins_memoryview_index: 0,
            builtins_slice_index: 0,
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

        // Set class indexes and calculate the base types.
        // This needs to be done before it gets accessed, because we expect the MRO etc. to be
        // calculated when a class is accessed. Normally this happens on access, but here we access
        // classes randomly via db.python_state. Therefore do the calculation here.
        macro_rules! cache_index {
            ($attr_name:ident, $db:expr, $module_name:ident, $name:literal) => {
                let class_index = db
                    .python_state
                    .$module_name()
                    .symbol_table
                    .lookup_symbol($name)
                    .unwrap()
                    - NAME_TO_CLASS_DIFF;
                $db.python_state.$attr_name = class_index;
                let module = db.python_state.$module_name();
                let class = Class::from_position(
                    NodeRef::new(module, class_index),
                    Generics::NotDefinedYet,
                    None,
                );
                class.ensure_calculated_class_infos(&InferenceState::new(db));
            };
        }
        cache_index!(builtins_object_index, db, builtins, "object");
        cache_index!(builtins_list_index, db, builtins, "list");
        cache_index!(builtins_dict_index, db, builtins, "dict");
        cache_index!(builtins_bool_index, db, builtins, "bool");
        cache_index!(builtins_int_index, db, builtins, "int");
        cache_index!(builtins_float_index, db, builtins, "float");
        cache_index!(builtins_complex_index, db, builtins, "complex");
        cache_index!(builtins_tuple_index, db, builtins, "tuple");
        cache_index!(builtins_function_index, db, builtins, "function");
        cache_index!(builtins_base_exception_index, db, builtins, "BaseException");
        cache_index!(builtins_str_index, db, builtins, "str");
        cache_index!(builtins_bytes_index, db, builtins, "bytes");
        cache_index!(builtins_bytearray_index, db, builtins, "bytearray");
        cache_index!(builtins_memoryview_index, db, builtins, "memoryview");
        cache_index!(builtins_slice_index, db, builtins, "slice");
        cache_index!(typing_mapping_index, db, typing, "Mapping");
        cache_index!(types_module_type_index, db, types, "ModuleType");

        let s = &mut db.python_state;
        let object_db_type = s.object_db_type();
        s.type_of_object = DbType::Type(Rc::new(object_db_type));

        // Set promotions
        s.int()
            .class_storage
            .promote_to
            .set(Some(s.float_node_ref().as_link()));
        s.float()
            .class_storage
            .promote_to
            .set(Some(s.complex_node_ref().as_link()));
        s.memoryview()
            .class_storage
            .promote_to
            .set(Some(s.bytes_node_ref().as_link()));
        s.bytearray()
            .class_storage
            .promote_to
            .set(Some(s.bytes_node_ref().as_link()));
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
    pub fn object_db_type(&self) -> DbType {
        DbType::Class(self.object_node_ref().as_link(), None)
    }

    #[inline]
    pub fn slice_db_type(&self) -> DbType {
        DbType::Class(self.slice_node_ref().as_link(), None)
    }

    #[inline]
    pub fn tuple_class<'db: 'a, 'a>(
        &'db self,
        db: &'db Database,
        tuple: &'a TupleContent,
    ) -> Class<'a> {
        let generics = tuple.tuple_class_generics(db);
        Class::from_position(self.tuple_node_ref(), Generics::List(generics, None), None)
    }

    builtins_attribute_node_ref!(object_node_ref, builtins_object_index);
    builtins_attribute_node_ref!(dict_node_ref, builtins_dict_index);
    builtins_attribute_node_ref!(list_node_ref, builtins_list_index);
    builtins_attribute_node_ref!(tuple_node_ref, builtins_tuple_index);
    builtins_attribute_node_ref!(bool_node_ref, builtins_bool_index);
    builtins_attribute_node_ref!(int_node_ref, builtins_int_index);
    builtins_attribute_node_ref!(float_node_ref, builtins_float_index);
    builtins_attribute_node_ref!(complex_node_ref, builtins_complex_index);
    builtins_attribute_node_ref!(str_node_ref, builtins_str_index);
    builtins_attribute_node_ref!(bytes_node_ref, builtins_bytes_index);
    builtins_attribute_node_ref!(bytearray_node_ref, builtins_bytearray_index);
    builtins_attribute_node_ref!(memoryview_node_ref, builtins_memoryview_index);
    builtins_attribute_node_ref!(slice_node_ref, builtins_slice_index);

    node_ref_to_class!(pub object_class, object_node_ref);
    node_ref_to_class!(pub str, str_node_ref);
    node_ref_to_class!(int, int_node_ref);
    node_ref_to_class!(float, float_node_ref);
    node_ref_to_class!(memoryview, memoryview_node_ref);
    node_ref_to_class!(bytearray, bytearray_node_ref);

    pub fn builtins_point_link(&self, name: &str) -> PointLink {
        // TODO I think these should all be available as cached PointLinks
        let builtins = self.builtins();
        let node_index = builtins.symbol_table.lookup_symbol(name).unwrap();
        PointLink::new(builtins.file_index(), node_index - NAME_TO_CLASS_DIFF)
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
        Class::from_position(node_ref, Generics::None, None)
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

    pub fn literal_class(&self, literal_kind: LiteralKind) -> Class {
        Class::from_position(
            match literal_kind {
                LiteralKind::Int(_) => self.int_node_ref(),
                LiteralKind::String(_) => self.str_node_ref(),
                LiteralKind::Bool(_) => self.bool_node_ref(),
                LiteralKind::Bytes(_) => self.bytes_node_ref(),
            },
            Generics::None,
            None,
        )
    }

    pub fn literal_db_type(&self, literal_kind: LiteralKind) -> DbType {
        DbType::Class(
            match literal_kind {
                LiteralKind::Int(_) => self.int_node_ref(),
                LiteralKind::String(_) => self.str_node_ref(),
                LiteralKind::Bool(_) => self.bool_node_ref(),
                LiteralKind::Bytes(_) => self.bytes_node_ref(),
            }
            .as_link(),
            None,
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
    set_typing_inference(typing, "Self", Specific::TypingSelf);
    set_typing_inference(typing, "Annotated", Specific::TypingAnnotated);
    set_typing_inference(typing, "reveal_type", Specific::RevealTypeFunction);

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
    set_typing_inference(t, "TypeVar", Specific::TypingTypeVarClass);
    set_typing_inference(t, "TypeVarTuple", Specific::TypingTypeVarTupleClass);
    set_typing_inference(t, "Concatenate", Specific::TypingConcatenateClass);
    set_typing_inference(t, "TypeAlias", Specific::TypingTypeAlias);
    set_typing_inference(t, "Self", Specific::TypingSelf);
    set_typing_inference(t, "Annotated", Specific::TypingAnnotated);
    set_typing_inference(t, "reveal_type", Specific::RevealTypeFunction);
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
        "Self",
        "reveal_type",
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
