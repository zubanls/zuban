use parsa_python_ast::{NodeIndex, TypeLike, NAME_DEF_TO_NAME_DIFFERENCE};
use std::ptr::null;
use std::rc::Rc;

use crate::database::{
    BaseClass, CallableContent, ClassGenerics, ComplexPoint, CustomBehavior, Database, DbType,
    GenericItem, GenericsList, LiteralKind, Locality, Point, PointLink, PointType, Specific,
    TupleContent, TypeVarLikes,
};
use crate::file::File;
use crate::file::PythonFile;
use crate::inferred::Inferred;
use crate::matching::{Generics, Type};
use crate::node_ref::NodeRef;
use crate::type_helpers::{dataclasses_replace, Class, Function, Instance};
use crate::{new_class, InferenceState, PythonProject};

// This is a bit hacky, but I'm sure the tests will fail somewhere if this constant is
// wrong. Basically it goes three nodes back: name_def class literal and then the actual
// class.
const NAME_TO_CLASS_DIFF: u32 = 3;
pub const NAME_TO_FUNCTION_DIFF: u32 = 3;

macro_rules! attribute_node_ref {
    ($module_name:ident, $vis:vis $name:ident, $attr:ident) => {
        #[inline]
        $vis fn $name(&self) -> NodeRef {
            debug_assert!(self.$attr != 0);
            NodeRef::new(self.$module_name(), self.$attr)
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

macro_rules! node_ref_to_db_type_class_without_generic {
    ($vis:vis $name:ident, $from_node_ref:ident) => {
        #[inline]
        $vis fn $name(&self) -> DbType {
            DbType::new_class(self.$from_node_ref().as_link(), ClassGenerics::None)
        }
    };
}

pub struct PythonState {
    pub project: PythonProject,

    builtins: *const PythonFile,
    typing: *const PythonFile,
    typeshed: *const PythonFile,
    collections: *const PythonFile,
    types: *const PythonFile,
    abc: *const PythonFile,
    functools: *const PythonFile,
    enum_file: *const PythonFile,
    dataclasses_file: *const PythonFile,
    mypy_extensions: *const PythonFile,
    typing_extensions: *const PythonFile,

    builtins_object_index: NodeIndex,
    builtins_type_index: NodeIndex,
    builtins_list_index: NodeIndex,
    builtins_tuple_index: NodeIndex,
    builtins_dict_index: NodeIndex,
    builtins_set_index: NodeIndex,
    builtins_bool_index: NodeIndex,
    builtins_int_index: NodeIndex,
    builtins_float_index: NodeIndex,
    builtins_complex_index: NodeIndex,
    builtins_function_index: NodeIndex,
    builtins_base_exception_index: NodeIndex,
    builtins_exception_index: NodeIndex,
    builtins_base_exception_group_index: NodeIndex,
    builtins_exception_group_index: NodeIndex,
    builtins_str_index: NodeIndex,
    builtins_bytes_index: NodeIndex,
    builtins_bytearray_index: NodeIndex,
    builtins_memoryview_index: NodeIndex,
    builtins_slice_index: NodeIndex,
    builtins_classmethod_index: NodeIndex,
    builtins_staticmethod_index: NodeIndex,
    builtins_property_index: NodeIndex,
    builtins_ellipsis_index: NodeIndex,
    typeshed_supports_keys_and_get_item_index: NodeIndex,
    typing_namedtuple_index: NodeIndex, // TODO Appears to be unused currently.
    typing_type_var: NodeIndex,
    typing_coroutine_index: NodeIndex,
    typing_iterator_index: NodeIndex,
    typing_iterable_index: NodeIndex,
    typing_generator_index: NodeIndex,
    typing_async_generator_index: NodeIndex,
    typing_async_iterator_index: NodeIndex,
    typing_async_iterable_index: NodeIndex,
    typing_supports_index_index: NodeIndex,
    typing_overload_index: NodeIndex,
    typing_override_index: NodeIndex,
    typing_typed_dict_index: NodeIndex,
    typing_mapping_index: NodeIndex,
    typing_mapping_get_index: NodeIndex,
    pub typing_typed_dict_bases: Box<[BaseClass]>,
    types_module_type_index: NodeIndex,
    types_none_type_index: NodeIndex,
    collections_namedtuple_index: NodeIndex,
    abc_abc_meta_index: NodeIndex,
    abc_abstractmethod_index: NodeIndex,
    abc_abstractproperty_index: NodeIndex,
    functools_cached_property_index: NodeIndex,
    enum_enum_meta_index: NodeIndex,
    enum_enum_index: NodeIndex,
    enum_auto_index: NodeIndex,
    mypy_extensions_arg_func: NodeIndex,
    mypy_extensions_default_arg_func: NodeIndex,
    mypy_extensions_named_arg_func: NodeIndex,
    mypy_extensions_default_named_arg_func: NodeIndex,
    mypy_extensions_kw_arg_func: NodeIndex,
    mypy_extensions_var_arg_func: NodeIndex,
    dataclasses_dataclass_index: NodeIndex,
    dataclasses_kw_only_index: NodeIndex,
    dataclasses_init_var_index: NodeIndex,
    dataclasses_field_index: NodeIndex,
    dataclasses_capital_field_index: NodeIndex,
    dataclasses_replace_index: NodeIndex,
    pub type_of_object: DbType,
    pub type_of_any: DbType,
    pub type_of_self: DbType,
    pub type_of_arbitrary_tuple: DbType,
    pub any_callable: Rc<CallableContent>,
    pub generator_with_any_generics: DbType,
    pub async_generator_with_any_generics: DbType,
    pub empty_type_var_likes: TypeVarLikes,
    pub dataclass_fields_type: DbType,
}

impl PythonState {
    pub fn reserve(project: PythonProject) -> Self {
        let empty_type_var_likes = TypeVarLikes::new(Rc::new([]));
        Self {
            project,
            builtins: null(),
            typing: null(),
            typeshed: null(),
            collections: null(),
            types: null(),
            abc: null(),
            functools: null(),
            enum_file: null(),
            dataclasses_file: null(),
            mypy_extensions: null(),
            typing_extensions: null(),
            builtins_object_index: 0,
            builtins_type_index: 0,
            builtins_list_index: 0,
            builtins_tuple_index: 0,
            builtins_dict_index: 0,
            builtins_set_index: 0,
            builtins_bool_index: 0,
            builtins_int_index: 0,
            builtins_float_index: 0,
            builtins_complex_index: 0,
            builtins_function_index: 0,
            builtins_base_exception_index: 0,
            builtins_exception_index: 0,
            builtins_base_exception_group_index: 0,
            builtins_exception_group_index: 0,
            builtins_str_index: 0,
            builtins_bytes_index: 0,
            builtins_bytearray_index: 0,
            builtins_memoryview_index: 0,
            builtins_slice_index: 0,
            builtins_classmethod_index: 0,
            builtins_staticmethod_index: 0,
            builtins_property_index: 0,
            builtins_ellipsis_index: 0,
            types_module_type_index: 0,
            types_none_type_index: 0,
            typeshed_supports_keys_and_get_item_index: 0,
            typing_namedtuple_index: 0,
            typing_type_var: 0,
            typing_overload_index: 0,
            typing_override_index: 0,
            typing_typed_dict_index: 0,
            typing_mapping_index: 0,
            typing_mapping_get_index: 0,
            typing_coroutine_index: 0,
            typing_iterator_index: 0,
            typing_iterable_index: 0,
            typing_generator_index: 0,
            typing_async_generator_index: 0,
            typing_async_iterator_index: 0,
            typing_async_iterable_index: 0,
            typing_supports_index_index: 0,
            typing_typed_dict_bases: Box::new([]), // Will be set later
            collections_namedtuple_index: 0,
            abc_abc_meta_index: 0,
            abc_abstractmethod_index: 0,
            abc_abstractproperty_index: 0,
            functools_cached_property_index: 0,
            enum_enum_meta_index: 0,
            enum_enum_index: 0,
            enum_auto_index: 0,
            mypy_extensions_arg_func: 0,
            mypy_extensions_default_arg_func: 0,
            mypy_extensions_named_arg_func: 0,
            mypy_extensions_default_named_arg_func: 0,
            mypy_extensions_kw_arg_func: 0,
            mypy_extensions_var_arg_func: 0,
            dataclasses_dataclass_index: 0,
            dataclasses_kw_only_index: 0,
            dataclasses_init_var_index: 0,
            dataclasses_field_index: 0,
            dataclasses_capital_field_index: 0,
            dataclasses_replace_index: 0,
            type_of_object: DbType::Any, // Will be set later
            type_of_any: DbType::Type(Rc::new(DbType::Any)),
            type_of_self: DbType::Type(Rc::new(DbType::Self_)),
            type_of_arbitrary_tuple: DbType::Type(Rc::new(
                DbType::Tuple(TupleContent::new_empty()),
            )),
            any_callable: Rc::new(CallableContent::new_any(empty_type_var_likes.clone())),
            generator_with_any_generics: DbType::Any, // Will be set later
            async_generator_with_any_generics: DbType::Any, // Will be set later
            empty_type_var_likes,
            dataclass_fields_type: DbType::Any, // Will be set later
        }
    }

    pub fn initialize(
        db: &mut Database,
        builtins: *const PythonFile,
        typing: *const PythonFile,
        typeshed: *const PythonFile,
        collections: *const PythonFile,
        types: *const PythonFile,
        abc: *const PythonFile,
        functools: *const PythonFile,
        enum_file: *const PythonFile,
        dataclasses_file: *const PythonFile,
        typing_extensions: *const PythonFile,
        mypy_extensions: *const PythonFile,
    ) {
        let s = &mut db.python_state;
        s.builtins = builtins;
        s.typing = typing;
        s.typeshed = typeshed;
        s.collections = collections;
        s.types = types;
        s.abc = abc;
        s.functools = functools;
        s.enum_file = enum_file;
        s.dataclasses_file = dataclasses_file;
        s.typing_extensions = typing_extensions;
        s.mypy_extensions = mypy_extensions;

        typing_changes(
            s.typing(),
            s.builtins(),
            s.collections(),
            s.dataclasses_file(),
            s.typing_extensions(),
            s.mypy_extensions(),
        );

        let mypy_extensions = unsafe { &*s.mypy_extensions };
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

        db.python_state.dataclasses_dataclass_index = db
            .python_state
            .dataclasses_file()
            .symbol_table
            .lookup_symbol("dataclass")
            .unwrap()
            - NAME_TO_FUNCTION_DIFF;

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
                let class = Class::with_undefined_generics(NodeRef::new(module, class_index));
                class.ensure_calculated_class_infos(
                    &InferenceState::new(db),
                    NodeRef::new(class.node_ref.file, class.node().name_definition().index()),
                );
            };
        }
        cache_index!(builtins_object_index, db, builtins, "object");
        cache_index!(builtins_type_index, db, builtins, "type");
        cache_index!(abc_abc_meta_index, db, abc, "ABCMeta");
        cache_index!(types_module_type_index, db, types, "ModuleType");
        cache_index!(enum_enum_meta_index, db, enum_file, "EnumMeta");
        cache_index!(enum_enum_index, db, enum_file, "Enum");
        cache_index!(enum_auto_index, db, enum_file, "auto");
        cache_index!(builtins_list_index, db, builtins, "list");
        cache_index!(builtins_dict_index, db, builtins, "dict");
        cache_index!(builtins_set_index, db, builtins, "set");
        cache_index!(builtins_bool_index, db, builtins, "bool");
        cache_index!(builtins_int_index, db, builtins, "int");
        cache_index!(builtins_float_index, db, builtins, "float");
        cache_index!(builtins_complex_index, db, builtins, "complex");
        cache_index!(builtins_tuple_index, db, builtins, "tuple");
        cache_index!(builtins_function_index, db, builtins, "function");
        cache_index!(builtins_base_exception_index, db, builtins, "BaseException");
        cache_index!(builtins_exception_index, db, builtins, "Exception");
        cache_index!(
            builtins_base_exception_group_index,
            db,
            builtins,
            "BaseExceptionGroup"
        );
        cache_index!(
            builtins_exception_group_index,
            db,
            builtins,
            "ExceptionGroup"
        );
        cache_index!(builtins_str_index, db, builtins, "str");
        cache_index!(builtins_bytes_index, db, builtins, "bytes");
        cache_index!(builtins_bytearray_index, db, builtins, "bytearray");
        cache_index!(builtins_memoryview_index, db, builtins, "memoryview");
        cache_index!(builtins_slice_index, db, builtins, "slice");
        cache_index!(builtins_classmethod_index, db, builtins, "classmethod");
        cache_index!(builtins_staticmethod_index, db, builtins, "staticmethod");
        cache_index!(builtins_property_index, db, builtins, "property");
        cache_index!(builtins_ellipsis_index, db, builtins, "ellipsis");
        cache_index!(
            typeshed_supports_keys_and_get_item_index,
            db,
            typeshed,
            "SupportsKeysAndGetItem"
        );
        cache_index!(typing_namedtuple_index, db, typing, "NamedTuple");
        cache_index!(typing_type_var, db, typing, "TypeVar");
        cache_index!(typing_coroutine_index, db, typing, "Coroutine");
        cache_index!(typing_iterator_index, db, typing, "Iterator");
        cache_index!(typing_iterable_index, db, typing, "Iterable");
        cache_index!(typing_generator_index, db, typing, "Generator");
        cache_index!(typing_async_generator_index, db, typing, "AsyncGenerator");
        cache_index!(typing_async_iterator_index, db, typing, "AsyncIterator");
        cache_index!(typing_async_iterable_index, db, typing, "AsyncIterable");
        cache_index!(typing_supports_index_index, db, typing, "SupportsIndex");
        cache_index!(typing_typed_dict_index, db, typing, "_TypedDict");
        cache_index!(typing_mapping_index, db, typing, "Mapping");
        cache_index!(types_none_type_index, db, types, "NoneType");
        cache_index!(abc_abstractproperty_index, db, abc, "abstractproperty");
        cache_index!(
            functools_cached_property_index,
            db,
            functools,
            "cached_property"
        );
        cache_index!(dataclasses_kw_only_index, db, dataclasses_file, "KW_ONLY");
        cache_index!(dataclasses_init_var_index, db, dataclasses_file, "InitVar");
        cache_index!(
            dataclasses_capital_field_index,
            db,
            dataclasses_file,
            "Field"
        );
        db.python_state.dataclasses_field_index = db
            .python_state
            .dataclasses_file()
            .symbol_table
            .lookup_symbol("field")
            .unwrap()
            - NAME_TO_FUNCTION_DIFF;
        db.python_state.dataclasses_replace_index = db
            .python_state
            .dataclasses_file()
            .symbol_table
            .lookup_symbol("replace")
            .unwrap()
            - NAME_TO_FUNCTION_DIFF;

        db.python_state.abc_abstractmethod_index = db
            .python_state
            .abc()
            .symbol_table
            .lookup_symbol("abstractmethod")
            .unwrap()
            - NAME_TO_FUNCTION_DIFF;

        db.python_state.collections_namedtuple_index = db
            .python_state
            .collections()
            .symbol_table
            .lookup_symbol("namedtuple")
            .unwrap()
            - NAME_TO_FUNCTION_DIFF;

        db.python_state.typing_overload_index = db
            .python_state
            .typing()
            .symbol_table
            .lookup_symbol("overload")
            .unwrap()
            - NAME_TO_FUNCTION_DIFF;

        db.python_state.typing_override_index = db
            .python_state
            .typing()
            .symbol_table
            .lookup_symbol("override")
            .unwrap()
            - NAME_TO_FUNCTION_DIFF;

        db.python_state.typing_mapping_get_index = db
            .python_state
            .mapping_node_ref()
            .expect_class_storage()
            .class_symbol_table
            .lookup_symbol("get")
            .unwrap()
            - NAME_TO_FUNCTION_DIFF;

        let typed_dict_class = db.python_state.typed_dict_class();
        let mut typed_dict_mro = Vec::from(typed_dict_class.use_cached_class_infos(db).mro.clone());
        for base in typed_dict_mro.iter_mut() {
            base.is_direct_base = false;
        }
        typed_dict_mro.insert(
            0,
            BaseClass {
                type_: typed_dict_class.as_db_type(db),
                is_direct_base: true,
            },
        );

        let s = &mut db.python_state;
        let object_db_type = s.object_db_type();
        s.type_of_object = DbType::Type(Rc::new(object_db_type));
        s.generator_with_any_generics =
            new_class!(s.generator_link(), DbType::Any, DbType::Any, DbType::Any,);
        s.async_generator_with_any_generics =
            new_class!(s.async_generator_link(), DbType::Any, DbType::Any,);

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

        s.dataclass_fields_type = new_class!(
            s.dict_node_ref().as_link(),
            s.str_db_type(),
            new_class!(s.dataclasses_capital_field_link(), DbType::Any,),
        );

        // Cache
        s.typing_typed_dict_bases = typed_dict_mro.into_boxed_slice();
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
    pub fn typeshed(&self) -> &PythonFile {
        debug_assert!(!self.typeshed.is_null());
        unsafe { &*self.typeshed }
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
    pub fn abc(&self) -> &PythonFile {
        debug_assert!(!self.abc.is_null());
        unsafe { &*self.abc }
    }

    pub fn functools(&self) -> &PythonFile {
        debug_assert!(!self.functools.is_null());
        unsafe { &*self.functools }
    }

    #[inline]
    pub fn enum_file(&self) -> &PythonFile {
        debug_assert!(!self.enum_file.is_null());
        unsafe { &*self.enum_file }
    }

    #[inline]
    pub fn dataclasses_file(&self) -> &PythonFile {
        debug_assert!(!self.dataclasses_file.is_null());
        unsafe { &*self.dataclasses_file }
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
    pub fn tuple_class<'db: 'a, 'a>(
        &'db self,
        db: &'db Database,
        tuple: &'a TupleContent,
    ) -> Class<'a> {
        let generics = tuple.tuple_class_generics(db);
        Class::from_position(self.tuple_node_ref(), Generics::List(generics, None), None)
    }

    attribute_node_ref!(builtins, pub object_node_ref, builtins_object_index);
    attribute_node_ref!(builtins, pub bare_type_node_ref, builtins_type_index);
    attribute_node_ref!(builtins, pub list_node_ref, builtins_list_index);
    attribute_node_ref!(builtins, tuple_node_ref, builtins_tuple_index);
    attribute_node_ref!(builtins, pub dict_node_ref, builtins_dict_index);
    attribute_node_ref!(builtins, pub set_node_ref, builtins_set_index);
    attribute_node_ref!(builtins, bool_node_ref, builtins_bool_index);
    attribute_node_ref!(builtins, int_node_ref, builtins_int_index);
    attribute_node_ref!(builtins, float_node_ref, builtins_float_index);
    attribute_node_ref!(builtins, complex_node_ref, builtins_complex_index);
    attribute_node_ref!(builtins, pub str_node_ref, builtins_str_index);
    attribute_node_ref!(builtins, bytes_node_ref, builtins_bytes_index);
    attribute_node_ref!(builtins, bytearray_node_ref, builtins_bytearray_index);
    attribute_node_ref!(builtins, memoryview_node_ref, builtins_memoryview_index);
    attribute_node_ref!(builtins, slice_node_ref, builtins_slice_index);
    attribute_node_ref!(builtins, pub classmethod_node_ref, builtins_classmethod_index);
    attribute_node_ref!(builtins, pub staticmethod_node_ref, builtins_staticmethod_index);
    attribute_node_ref!(builtins, pub property_node_ref, builtins_property_index);
    attribute_node_ref!(builtins, ellipsis_node_ref, builtins_ellipsis_index);
    attribute_node_ref!(builtins, function_node_ref, builtins_function_index);
    attribute_node_ref!(
        builtins,
        pub base_exception_node_ref,
        builtins_base_exception_index
    );
    attribute_node_ref!(builtins, pub exception_node_ref, builtins_exception_index);
    attribute_node_ref!(
        builtins,
        pub base_exception_group_node_ref,
        builtins_base_exception_group_index
    );
    attribute_node_ref!(
        builtins,
        pub exception_group_node_ref,
        builtins_exception_group_index
    );

    attribute_node_ref!(typing, supports_index_node_ref, typing_supports_index_index);
    attribute_node_ref!(typing, typed_dict_node_ref, typing_typed_dict_index);
    attribute_node_ref!(typing, pub mapping_node_ref, typing_mapping_index);
    attribute_node_ref!(typing, mapping_get_node_ref, typing_mapping_get_index);
    attribute_node_ref!(types, none_type_node_ref, types_none_type_index);
    attribute_node_ref!(types, module_node_ref, types_module_type_index);
    attribute_node_ref!(
        typeshed,
        supports_keys_and_get_item_node_ref,
        typeshed_supports_keys_and_get_item_index
    );
    attribute_node_ref!(enum_file, pub enum_node_ref, enum_enum_index);

    node_ref_to_class!(pub object_class, object_node_ref);
    node_ref_to_class!(int, int_node_ref);
    node_ref_to_class!(float, float_node_ref);
    node_ref_to_class!(memoryview, memoryview_node_ref);
    node_ref_to_class!(bytearray, bytearray_node_ref);
    node_ref_to_class!(pub function_class, function_node_ref);
    node_ref_to_class!(pub bare_type_class, bare_type_node_ref);
    node_ref_to_class!(pub typed_dict_class, typed_dict_node_ref);

    node_ref_to_db_type_class_without_generic!(pub object_db_type, object_node_ref);
    node_ref_to_db_type_class_without_generic!(pub slice_db_type, slice_node_ref);
    node_ref_to_db_type_class_without_generic!(pub str_db_type, str_node_ref);
    node_ref_to_db_type_class_without_generic!(pub bytes_db_type, bytes_node_ref);
    node_ref_to_db_type_class_without_generic!(pub int_db_type, int_node_ref);
    node_ref_to_db_type_class_without_generic!(pub bool_db_type, bool_node_ref);
    node_ref_to_db_type_class_without_generic!(pub float_db_type, float_node_ref);
    node_ref_to_db_type_class_without_generic!(pub complex_db_type, complex_node_ref);
    node_ref_to_db_type_class_without_generic!(pub module_db_type, module_node_ref);
    node_ref_to_db_type_class_without_generic!(pub property_db_type, property_node_ref);
    node_ref_to_db_type_class_without_generic!(pub function_db_type, function_node_ref);
    node_ref_to_db_type_class_without_generic!(pub bare_type_db_type, bare_type_node_ref);
    node_ref_to_db_type_class_without_generic!(pub ellipsis_db_type, ellipsis_node_ref);
    node_ref_to_db_type_class_without_generic!(pub typed_dict_db_type, typed_dict_node_ref);

    node_ref_to_db_type_class_without_generic!(pub supports_index_db_type, supports_index_node_ref);

    pub fn none_instance(&self) -> Instance {
        Instance::new(
            Class::from_non_generic_node_ref(self.none_type_node_ref()),
            None,
        )
    }

    pub fn supports_keys_and_get_item_class<'a>(&'a self, db: &'a Database) -> Class<'a> {
        let node_ref = self.supports_keys_and_get_item_node_ref();
        let cls = Class::with_undefined_generics(node_ref);
        cls.ensure_calculated_class_infos(
            &InferenceState::new(db),
            NodeRef::new(node_ref.file, cls.node().name_definition().index()),
        );
        Class::with_self_generics(db, node_ref)
    }

    pub fn type_var_type(&self) -> Type {
        debug_assert!(self.typing_type_var != 0);
        DbType::new_class(
            PointLink::new(self.typing().file_index(), self.typing_type_var),
            ClassGenerics::None,
        )
        .into()
    }

    pub fn collections_namedtuple_function(&self) -> Function {
        Function::new(
            NodeRef::new(self.collections(), self.collections_namedtuple_index),
            None,
        )
    }

    pub fn abc_meta_link(&self) -> PointLink {
        debug_assert!(self.abc_abc_meta_index != 0);
        PointLink::new(self.abc().file_index(), self.abc_abc_meta_index)
    }

    pub fn abstractmethod_link(&self) -> PointLink {
        debug_assert!(self.abc_abstractmethod_index != 0);
        PointLink::new(self.abc().file_index(), self.abc_abstractmethod_index)
    }

    pub fn abstractproperty_link(&self) -> PointLink {
        debug_assert!(self.abc_abstractproperty_index != 0);
        PointLink::new(self.abc().file_index(), self.abc_abstractproperty_index)
    }

    pub fn cached_property_link(&self) -> PointLink {
        debug_assert!(self.functools_cached_property_index != 0);
        PointLink::new(
            self.functools().file_index(),
            self.functools_cached_property_index,
        )
    }

    pub fn enum_meta_link(&self) -> PointLink {
        debug_assert!(self.enum_enum_meta_index != 0);
        PointLink::new(self.enum_file().file_index(), self.enum_enum_meta_index)
    }

    pub fn enum_auto_link(&self) -> PointLink {
        debug_assert!(self.enum_auto_index != 0);
        PointLink::new(self.enum_file().file_index(), self.enum_auto_index)
    }

    pub fn overload_link(&self) -> PointLink {
        debug_assert!(self.typing_overload_index != 0);
        PointLink::new(self.typing().file_index(), self.typing_overload_index)
    }

    pub fn coroutine_link(&self) -> PointLink {
        debug_assert!(self.typing_coroutine_index != 0);
        PointLink::new(self.typing().file_index(), self.typing_coroutine_index)
    }

    pub fn generator_link(&self) -> PointLink {
        debug_assert!(self.typing_generator_index != 0);
        PointLink::new(self.typing().file_index(), self.typing_generator_index)
    }

    pub fn iterator_link(&self) -> PointLink {
        debug_assert!(self.typing_iterator_index != 0);
        PointLink::new(self.typing().file_index(), self.typing_iterator_index)
    }

    pub fn iterable_link(&self) -> PointLink {
        debug_assert!(self.typing_iterable_index != 0);
        PointLink::new(self.typing().file_index(), self.typing_iterable_index)
    }

    pub fn async_generator_link(&self) -> PointLink {
        debug_assert!(self.typing_async_generator_index != 0);
        PointLink::new(
            self.typing().file_index(),
            self.typing_async_generator_index,
        )
    }

    pub fn async_iterator_link(&self) -> PointLink {
        debug_assert!(self.typing_async_iterator_index != 0);
        PointLink::new(self.typing().file_index(), self.typing_async_iterator_index)
    }

    pub fn async_iterable_link(&self) -> PointLink {
        debug_assert!(self.typing_async_iterable_index != 0);
        PointLink::new(self.typing().file_index(), self.typing_async_iterable_index)
    }

    pub fn mapping_get_function<'class>(&self, class: Class<'class>) -> Function<'_, 'class> {
        Function::new(self.mapping_get_node_ref(), Some(class))
    }

    pub fn dataclasses_dataclass(&self) -> PointLink {
        debug_assert!(self.dataclasses_dataclass_index != 0);
        PointLink::new(
            self.dataclasses_file().file_index(),
            self.dataclasses_dataclass_index,
        )
    }

    pub fn dataclasses_kw_only_link(&self) -> PointLink {
        debug_assert!(self.dataclasses_kw_only_index != 0);
        PointLink::new(
            self.dataclasses_file().file_index(),
            self.dataclasses_kw_only_index,
        )
    }

    pub fn dataclasses_init_var_link(&self) -> PointLink {
        debug_assert!(self.dataclasses_init_var_index != 0);
        PointLink::new(
            self.dataclasses_file().file_index(),
            self.dataclasses_init_var_index,
        )
    }

    pub fn dataclasses_field_link(&self) -> PointLink {
        debug_assert!(self.dataclasses_field_index != 0);
        PointLink::new(
            self.dataclasses_file().file_index(),
            self.dataclasses_field_index,
        )
    }

    fn dataclasses_capital_field_link(&self) -> PointLink {
        debug_assert!(self.dataclasses_capital_field_index != 0);
        PointLink::new(
            self.dataclasses_file().file_index(),
            self.dataclasses_capital_field_index,
        )
    }

    pub fn dataclasses_replace(&self) -> Function {
        debug_assert!(self.dataclasses_replace_index != 0);
        Function::new(
            NodeRef::new(self.dataclasses_file(), self.dataclasses_replace_index),
            None,
        )
    }

    pub fn mypy_extensions_arg_func(&self, db: &Database, specific: Specific) -> Inferred {
        let node_index = match specific {
            Specific::MypyExtensionsArg => self.mypy_extensions_arg_func,
            Specific::MypyExtensionsDefaultArg => self.mypy_extensions_default_arg_func,
            Specific::MypyExtensionsNamedArg => self.mypy_extensions_named_arg_func,
            Specific::MypyExtensionsDefaultNamedArg => self.mypy_extensions_default_named_arg_func,
            Specific::MypyExtensionsVarArg => self.mypy_extensions_var_arg_func,
            Specific::MypyExtensionsKwArg => self.mypy_extensions_kw_arg_func,
            _ => unreachable!(),
        };
        Function::new(NodeRef::new(self.mypy_extensions(), node_index), None)
            .decorated(&InferenceState::new(db))
    }

    fn literal_node_ref(&self, literal_kind: &LiteralKind) -> NodeRef {
        match literal_kind {
            LiteralKind::Int(_) => self.int_node_ref(),
            LiteralKind::String(_) => self.str_node_ref(),
            LiteralKind::Bool(_) => self.bool_node_ref(),
            LiteralKind::Bytes(_) => self.bytes_node_ref(),
        }
    }

    pub fn literal_instance(&self, literal_kind: &LiteralKind) -> Instance {
        Instance::new(
            Class::from_non_generic_node_ref(self.literal_node_ref(literal_kind)),
            None,
        )
    }

    pub fn module_instance(&self) -> Instance {
        Instance::new(
            Class::from_non_generic_node_ref(self.module_node_ref()),
            None,
        )
    }

    pub fn literal_type(&self, literal_kind: &LiteralKind) -> Type {
        Type::owned(self.literal_db_type(literal_kind))
    }

    pub fn literal_db_type(&self, literal_kind: &LiteralKind) -> DbType {
        DbType::new_class(
            self.literal_node_ref(literal_kind).as_link(),
            ClassGenerics::None,
        )
    }
}

fn typing_changes(
    typing: &PythonFile,
    builtins: &PythonFile,
    collections: &PythonFile,
    dataclasses: &PythonFile,
    typing_extensions: &PythonFile,
    mypy_extensions: &PythonFile,
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
    set_typing_inference(typing, "NamedTuple", Specific::TypingNamedTuple);
    set_typing_inference(typing, "Unpack", Specific::TypingUnpack);
    set_typing_inference(typing, "TypeAlias", Specific::TypingTypeAlias);
    set_typing_inference(typing, "Self", Specific::TypingSelf);
    set_typing_inference(typing, "Annotated", Specific::TypingAnnotated);
    set_typing_inference(typing, "Required", Specific::TypingRequired);
    set_typing_inference(typing, "NotRequired", Specific::TypingNotRequired);
    set_typing_inference(typing, "reveal_type", Specific::RevealTypeFunction);
    set_typing_inference(typing, "assert_type", Specific::AssertTypeFunction);
    set_typing_inference(
        typing,
        "dataclass_transform",
        Specific::TypingDataclassTransform,
    );

    set_typing_inference(builtins, "tuple", Specific::TypingTuple);
    set_typing_inference(builtins, "type", Specific::TypingType);
    set_typing_inference(builtins, "super", Specific::BuiltinsSuper);

    set_typing_inference(typing, "cast", Specific::TypingCast);

    //set_typing_inference(dataclasses, "replace", Specific::DataclassesReplace);
    set_custom_behavior(
        dataclasses,
        "replace",
        CustomBehavior::new_function(dataclasses_replace),
    );
    set_typing_inference(collections, "namedtuple", Specific::CollectionsNamedTuple);

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
    set_typing_inference(t, "Unpack", Specific::TypingUnpack);
    set_typing_inference(t, "ParamSpec", Specific::TypingParamSpecClass);
    set_typing_inference(t, "TypeVar", Specific::TypingTypeVarClass);
    set_typing_inference(t, "TypeVarTuple", Specific::TypingTypeVarTupleClass);
    set_typing_inference(t, "Concatenate", Specific::TypingConcatenateClass);
    set_typing_inference(t, "TypeAlias", Specific::TypingTypeAlias);
    set_typing_inference(t, "Self", Specific::TypingSelf);
    set_typing_inference(t, "Annotated", Specific::TypingAnnotated);
    set_typing_inference(t, "reveal_type", Specific::RevealTypeFunction);
    set_typing_inference(t, "assert_type", Specific::AssertTypeFunction);
    set_typing_inference(t, "NamedTuple", Specific::TypingNamedTuple);
    set_typing_inference(t, "Protocol", Specific::TypingProtocol);
    set_typing_inference(t, "Required", Specific::TypingRequired);
    set_typing_inference(t, "NotRequired", Specific::TypingNotRequired);
    set_typing_inference(t, "dataclass_transform", Specific::TypingDataclassTransform);

    for module in [typing, mypy_extensions, typing_extensions] {
        set_typing_inference(module, "TypedDict", Specific::TypingTypedDict);
    }
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
        "NamedTuple",
        "namedtuple",
        "TypedDict",
        "Required",
        "NotRequired",
        "LiteralString",
        "Concatenate",
        "ParamSpec",
        "Unpack",
        "TypeAlias",
        "Self",
        "reveal_type",
        "assert_type",
        "dataclass_transform",
        "super",
        "replace",
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

fn set_custom_behavior(file: &PythonFile, name: &str, custom: CustomBehavior) {
    let node_index = file.symbol_table.lookup_symbol(name).unwrap();
    NodeRef::new(file, node_index).insert_complex(
        ComplexPoint::TypeInstance(DbType::CustomBehavior(custom)),
        Locality::Stmt,
    );
}

fn set_custom_behavior_method(
    file: &PythonFile,
    class_name: &str,
    name: &str,
    custom: CustomBehavior,
) {
    let module_node_index = file.symbol_table.lookup_symbol(class_name).unwrap();
    let class_storage =
        NodeRef::new(file, module_node_index - NAME_TO_CLASS_DIFF).expect_class_storage();
    let node_index = class_storage
        .class_symbol_table
        .lookup_symbol(name)
        .unwrap();
    NodeRef::new(file, node_index).insert_complex(
        ComplexPoint::TypeInstance(DbType::CustomBehavior(custom)),
        Locality::Stmt,
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
    let name_def_node_index = node_index - NAME_DEF_TO_NAME_DIFFERENCE;
    // Act on the name def index and not the name.
    let old_point = file.points.get(name_def_node_index);
    file.points.set(
        node_index - 1,
        Point::new_simple_specific(specific, Locality::Stmt),
    );
    debug_assert!(old_point.type_() == PointType::Redirect);
    let result = old_point.node_index();
    debug_assert!(matches!(
        file.points.get(result).maybe_specific(),
        Some(Specific::Function | Specific::DecoratedFunction)
    ));
    result
}
