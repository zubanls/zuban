use std::{ptr::null, rc::Rc};

use parsa_python_ast::{NodeIndex, TypeLike, NAME_DEF_TO_NAME_DIFFERENCE};

use crate::{
    database::{
        BaseClass, ComplexPoint, Database, FileIndex, Locality, Point, PointLink, Specific,
    },
    file::{File, PythonFile},
    inferred::Inferred,
    matching::Generics,
    new_class,
    node_ref::NodeRef,
    type_::{
        dataclasses_replace, AnyCause, CallableContent, CallableParam, CallableParams,
        ClassGenerics, CustomBehavior, FunctionKind, LiteralKind, ParamType, Tuple, Type,
        TypeVarLikes,
    },
    type_helpers::{Class, Function, Instance},
    InferenceState,
};

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

macro_rules! node_ref_to_type_class_without_generic {
    ($vis:vis $name:ident, $from_node_ref:ident) => {
        #[inline]
        $vis fn $name(&self) -> Type {
            Type::new_class(self.$from_node_ref().as_link(), ClassGenerics::None)
        }
    };
}

pub struct PythonState {
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
    builtins_isinstance_index: NodeIndex,
    builtins_issubclass_index: NodeIndex,
    builtins_callable_index: NodeIndex,
    builtins_hasattr_index: NodeIndex,
    builtins_len_index: NodeIndex,
    pub builtins_int_mro: Box<[BaseClass]>,
    pub builtins_bool_mro: Box<[BaseClass]>,
    pub builtins_str_mro: Box<[BaseClass]>,
    pub builtins_bytes_mro: Box<[BaseClass]>,
    typeshed_supports_keys_and_get_item_index: NodeIndex,
    typing_namedtuple_index: NodeIndex,
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
    typing_final_index: NodeIndex,
    typing_typed_dict_index: NodeIndex,
    typing_mapping_index: NodeIndex,
    typing_mapping_get_index: NodeIndex,
    typing_special_form_index: NodeIndex,
    pub typing_typed_dict_bases: Box<[BaseClass]>,
    types_module_type_index: NodeIndex,
    types_none_type_index: NodeIndex,
    types_ellipsis_type_index: NodeIndex,
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
    pub type_of_object: Type, // TODO currently unused
    pub type_of_any: Type,
    pub type_of_self: Type,
    pub type_of_arbitrary_tuple: Type,
    pub list_of_any: Type,
    pub dict_of_any: Type,
    pub set_of_any: Type,
    pub any_callable_from_error: Rc<CallableContent>,
    pub generator_with_any_generics: Type,
    pub async_generator_with_any_generics: Type,
    pub valid_getattr_supertype: Type,
    pub iterable_of_str: Type,
    pub empty_type_var_likes: TypeVarLikes,
    pub dataclass_fields_type: Type,
}

impl PythonState {
    pub fn reserve() -> Self {
        let empty_type_var_likes = TypeVarLikes::new(Rc::new([]));
        Self {
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
            builtins_isinstance_index: 0,
            builtins_issubclass_index: 0,
            builtins_callable_index: 0,
            builtins_hasattr_index: 0,
            builtins_len_index: 0,
            builtins_int_mro: Box::new([]),   // will be set later
            builtins_bool_mro: Box::new([]),  // will be set later
            builtins_str_mro: Box::new([]),   // will be set later
            builtins_bytes_mro: Box::new([]), // will be set later
            types_module_type_index: 0,
            types_none_type_index: 0,
            types_ellipsis_type_index: 0,
            typeshed_supports_keys_and_get_item_index: 0,
            typing_namedtuple_index: 0,
            typing_type_var: 0,
            typing_overload_index: 0,
            typing_override_index: 0,
            typing_final_index: 0,
            typing_typed_dict_index: 0,
            typing_mapping_index: 0,
            typing_mapping_get_index: 0,
            typing_special_form_index: 0,
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
            type_of_object: Type::None, // Will be set later
            type_of_any: Type::Type(Rc::new(Type::Any(AnyCause::Todo))),
            type_of_self: Type::Type(Rc::new(Type::Self_)),
            type_of_arbitrary_tuple: Type::Type(Rc::new(Type::Tuple(
                Tuple::new_arbitrary_length_with_any(),
            ))),
            list_of_any: Type::None, // Will be set later
            dict_of_any: Type::None, // Will be set later
            set_of_any: Type::None,  // Will be set later
            any_callable_from_error: Rc::new(CallableContent::new_any(
                empty_type_var_likes.clone(),
                AnyCause::FromError,
            )),
            generator_with_any_generics: Type::None, // Will be set later
            async_generator_with_any_generics: Type::None, // Will be set later
            valid_getattr_supertype: Type::None,     // Will be set later
            iterable_of_str: Type::None,             // Will be set later
            empty_type_var_likes,
            dataclass_fields_type: Type::None, // Will be set later
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
            .get()
            .unwrap()
            .lookup_symbol("dataclass")
            .unwrap()
            - NAME_TO_FUNCTION_DIFF;

        // Set class indexes and calculate the base types.
        // This needs to be done before it gets accessed, because we expect the MRO etc. to be
        // calculated when a class is accessed. Normally this happens on access, but here we access
        // classes randomly via db.python_state. Therefore do the calculation here.
        macro_rules! cache_index {
            ($attr_name:ident, $module_name:ident, $name:literal) => {
                let class_index = db
                    .python_state
                    .$module_name()
                    .symbol_table
                    .get()
                    .unwrap()
                    .lookup_symbol($name)
                    .unwrap()
                    - NAME_TO_CLASS_DIFF;
                db.python_state.$attr_name = class_index;
                let module = db.python_state.$module_name();
                let class = Class::with_undefined_generics(NodeRef::new(module, class_index));
                class.ensure_calculated_class_infos(
                    &InferenceState::new(db),
                    NodeRef::new(class.node_ref.file, class.node().name_definition().index()),
                );
            };
        }
        macro_rules! cache_func_index {
            ($attr_name:ident, $module_name:ident, $name:literal) => {
                db.python_state.$attr_name = db
                    .python_state
                    .$module_name()
                    .symbol_table
                    .get()
                    .unwrap()
                    .lookup_symbol($name)
                    .unwrap()
                    - NAME_TO_FUNCTION_DIFF;
            };
        }

        // This first block
        cache_index!(builtins_object_index, builtins, "object");
        cache_index!(builtins_type_index, builtins, "type");
        cache_func_index!(typing_final_index, typing, "final");
        cache_index!(abc_abc_meta_index, abc, "ABCMeta");
        cache_index!(types_module_type_index, types, "ModuleType");
        cache_index!(enum_enum_meta_index, enum_file, "EnumMeta");
        cache_index!(enum_enum_index, enum_file, "Enum");
        cache_index!(enum_auto_index, enum_file, "auto");

        cache_index!(builtins_list_index, builtins, "list");
        cache_index!(builtins_dict_index, builtins, "dict");
        cache_index!(builtins_set_index, builtins, "set");
        cache_index!(builtins_bool_index, builtins, "bool");
        cache_index!(builtins_int_index, builtins, "int");
        cache_index!(builtins_float_index, builtins, "float");
        cache_index!(builtins_complex_index, builtins, "complex");
        cache_index!(builtins_tuple_index, builtins, "tuple");
        cache_index!(builtins_function_index, builtins, "function");
        cache_index!(builtins_base_exception_index, builtins, "BaseException");
        cache_index!(builtins_exception_index, builtins, "Exception");
        cache_index!(
            builtins_base_exception_group_index,
            builtins,
            "BaseExceptionGroup"
        );
        cache_index!(builtins_exception_group_index, builtins, "ExceptionGroup");
        cache_index!(builtins_str_index, builtins, "str");
        cache_index!(builtins_bytes_index, builtins, "bytes");
        cache_index!(builtins_bytearray_index, builtins, "bytearray");
        cache_index!(builtins_memoryview_index, builtins, "memoryview");
        cache_index!(builtins_slice_index, builtins, "slice");
        cache_index!(builtins_classmethod_index, builtins, "classmethod");
        cache_index!(builtins_staticmethod_index, builtins, "staticmethod");
        cache_index!(builtins_property_index, builtins, "property");
        cache_index!(
            typeshed_supports_keys_and_get_item_index,
            typeshed,
            "SupportsKeysAndGetItem"
        );
        cache_index!(typing_namedtuple_index, typing, "NamedTuple");
        cache_index!(typing_type_var, typing, "TypeVar");
        cache_index!(typing_coroutine_index, typing, "Coroutine");
        cache_index!(typing_iterator_index, typing, "Iterator");
        cache_index!(typing_iterable_index, typing, "Iterable");
        cache_index!(typing_generator_index, typing, "Generator");
        cache_index!(typing_async_generator_index, typing, "AsyncGenerator");
        cache_index!(typing_async_iterator_index, typing, "AsyncIterator");
        cache_index!(typing_async_iterable_index, typing, "AsyncIterable");
        cache_index!(typing_supports_index_index, typing, "SupportsIndex");
        cache_index!(typing_typed_dict_index, typing, "_TypedDict");
        cache_index!(typing_mapping_index, typing, "Mapping");
        cache_index!(typing_special_form_index, typing, "_SpecialForm");
        cache_index!(types_none_type_index, types, "NoneType");
        cache_index!(types_ellipsis_type_index, types, "EllipsisType");
        cache_index!(abc_abstractproperty_index, abc, "abstractproperty");
        cache_index!(
            functools_cached_property_index,
            functools,
            "cached_property"
        );
        cache_index!(dataclasses_kw_only_index, dataclasses_file, "KW_ONLY");
        cache_index!(dataclasses_init_var_index, dataclasses_file, "InitVar");
        cache_index!(dataclasses_capital_field_index, dataclasses_file, "Field");

        cache_func_index!(builtins_isinstance_index, builtins, "isinstance");
        cache_func_index!(builtins_issubclass_index, builtins, "issubclass");
        cache_func_index!(builtins_callable_index, builtins, "callable");
        cache_func_index!(builtins_hasattr_index, builtins, "hasattr");
        cache_func_index!(builtins_len_index, builtins, "len");

        cache_func_index!(typing_overload_index, typing, "overload");
        cache_func_index!(typing_override_index, typing, "override");

        cache_func_index!(dataclasses_field_index, dataclasses_file, "field");
        cache_func_index!(dataclasses_replace_index, dataclasses_file, "replace");

        cache_func_index!(abc_abstractmethod_index, abc, "abstractmethod");

        cache_func_index!(collections_namedtuple_index, collections, "namedtuple");

        db.python_state.typing_mapping_get_index = db
            .python_state
            .mapping_node_ref()
            .expect_class_storage()
            .class_symbol_table
            .lookup_symbol("get")
            .unwrap()
            - NAME_TO_FUNCTION_DIFF;

        let typed_dict_mro = calculate_mro_for_class(db, db.python_state.typed_dict_class());
        let builtins_int_mro = calculate_mro_for_class(db, db.python_state.int());
        let builtins_bool_mro = calculate_mro_for_class(db, db.python_state.bool());
        let builtins_str_mro = calculate_mro_for_class(db, db.python_state.str());
        let builtins_bytes_mro = calculate_mro_for_class(db, db.python_state.bytes());

        let s = &mut db.python_state;
        let object_type = s.object_type();
        s.type_of_object = Type::Type(Rc::new(object_type));
        s.list_of_any = new_class!(s.list_node_ref().as_link(), Type::Any(AnyCause::FromError));
        s.dict_of_any = new_class!(
            s.dict_node_ref().as_link(),
            Type::Any(AnyCause::FromError),
            Type::Any(AnyCause::FromError)
        );
        s.set_of_any = new_class!(s.set_node_ref().as_link(), Type::Any(AnyCause::FromError));
        s.generator_with_any_generics = new_class!(
            s.generator_link(),
            Type::Any(AnyCause::Internal),
            Type::Any(AnyCause::Internal),
            Type::Any(AnyCause::Internal),
        );
        s.async_generator_with_any_generics = new_class!(
            s.async_generator_link(),
            Type::Any(AnyCause::Internal),
            Type::Any(AnyCause::Internal),
        );
        s.valid_getattr_supertype = Type::Callable(Rc::new(CallableContent {
            name: None,
            class_name: None,
            defined_at: PointLink::new(FileIndex(0), 0),
            kind: FunctionKind::Function {
                had_first_self_or_class_annotation: true,
            },
            type_vars: s.empty_type_var_likes.clone(),
            params: CallableParams::Simple(Rc::new([
                CallableParam::new_anonymous(ParamType::PositionalOnly(Type::Any(
                    AnyCause::Internal,
                ))),
                CallableParam::new_anonymous(ParamType::PositionalOnly(s.str_type())),
            ])),
            return_type: Type::Any(AnyCause::Internal),
        }));
        s.iterable_of_str = new_class!(s.iterable_link(), s.str_type(),);

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
            s.str_type(),
            new_class!(
                s.dataclasses_capital_field_link(),
                Type::Any(AnyCause::Internal),
            ),
        );

        // Cache
        s.typing_typed_dict_bases = typed_dict_mro;
        s.builtins_int_mro = builtins_int_mro;
        s.builtins_bool_mro = builtins_bool_mro;
        s.builtins_str_mro = builtins_str_mro;
        s.builtins_bytes_mro = builtins_bytes_mro;
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
    pub fn tuple_class<'db: 'a, 'a>(&'db self, db: &'db Database, tuple: &'a Tuple) -> Class<'a> {
        let generics = tuple.tuple_class_generics(db);
        Class::from_position(self.tuple_node_ref(), Generics::List(generics, None), None)
    }

    #[inline]
    pub fn tuple_class_with_generics_to_be_defined(&self) -> Class {
        Class::from_position(self.tuple_node_ref(), Generics::NotDefinedYet, None)
    }

    attribute_node_ref!(builtins, pub object_node_ref, builtins_object_index);
    attribute_node_ref!(builtins, pub bare_type_node_ref, builtins_type_index);
    attribute_node_ref!(builtins, pub list_node_ref, builtins_list_index);
    attribute_node_ref!(builtins, tuple_node_ref, builtins_tuple_index);
    attribute_node_ref!(builtins, pub dict_node_ref, builtins_dict_index);
    attribute_node_ref!(builtins, pub set_node_ref, builtins_set_index);
    attribute_node_ref!(builtins, pub bool_node_ref, builtins_bool_index);
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
    attribute_node_ref!(builtins, pub isinstance_node_ref, builtins_isinstance_index);
    attribute_node_ref!(builtins, pub issubclass_node_ref, builtins_issubclass_index);
    attribute_node_ref!(builtins, pub callable_node_ref, builtins_callable_index);
    attribute_node_ref!(builtins, pub hasattr_node_ref, builtins_hasattr_index);
    attribute_node_ref!(builtins, pub len_node_ref, builtins_len_index);
    attribute_node_ref!(builtins, pub function_node_ref, builtins_function_index);
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
    attribute_node_ref!(typing, mapping_node_ref, typing_mapping_index);
    attribute_node_ref!(typing, mapping_get_node_ref, typing_mapping_get_index);
    attribute_node_ref!(typing, pub typing_overload, typing_overload_index);
    attribute_node_ref!(typing, pub typing_override, typing_override_index);
    attribute_node_ref!(typing, pub typing_final, typing_final_index);
    attribute_node_ref!(typing, pub generator_node_ref, typing_generator_index);
    attribute_node_ref!(typing, pub iterable_node_ref, typing_iterable_index);
    attribute_node_ref!(typing, pub typing_named_tuple_node_ref, typing_namedtuple_index);
    attribute_node_ref!(
        typing,
        typing_special_form_node_ref,
        typing_special_form_index
    );
    attribute_node_ref!(types, none_type_node_ref, types_none_type_index);
    attribute_node_ref!(types, module_node_ref, types_module_type_index);
    attribute_node_ref!(types, ellipsis_node_ref, types_ellipsis_type_index);
    attribute_node_ref!(
        typeshed,
        pub supports_keys_and_get_item_node_ref,
        typeshed_supports_keys_and_get_item_index
    );
    attribute_node_ref!(enum_file, pub enum_node_ref, enum_enum_index);

    node_ref_to_class!(pub object_class, object_node_ref);
    node_ref_to_class!(int, int_node_ref);
    node_ref_to_class!(bool, bool_node_ref);
    node_ref_to_class!(str, str_node_ref);
    node_ref_to_class!(bytes, bytes_node_ref);
    node_ref_to_class!(float, float_node_ref);
    node_ref_to_class!(memoryview, memoryview_node_ref);
    node_ref_to_class!(bytearray, bytearray_node_ref);
    node_ref_to_class!(pub function_class, function_node_ref);
    node_ref_to_class!(pub bare_type_class, bare_type_node_ref);
    node_ref_to_class!(pub typed_dict_class, typed_dict_node_ref);
    node_ref_to_class!(pub typing_named_tuple_class, typing_named_tuple_node_ref);

    node_ref_to_type_class_without_generic!(pub object_type, object_node_ref);
    node_ref_to_type_class_without_generic!(pub slice_type, slice_node_ref);
    node_ref_to_type_class_without_generic!(pub str_type, str_node_ref);
    node_ref_to_type_class_without_generic!(pub bytes_type, bytes_node_ref);
    node_ref_to_type_class_without_generic!(pub int_type, int_node_ref);
    node_ref_to_type_class_without_generic!(pub bool_type, bool_node_ref);
    node_ref_to_type_class_without_generic!(pub float_type, float_node_ref);
    node_ref_to_type_class_without_generic!(pub complex_type, complex_node_ref);
    node_ref_to_type_class_without_generic!(pub module_type, module_node_ref);
    node_ref_to_type_class_without_generic!(pub property_type, property_node_ref);
    node_ref_to_type_class_without_generic!(pub function_type, function_node_ref);
    node_ref_to_type_class_without_generic!(pub bare_type_type, bare_type_node_ref);
    node_ref_to_type_class_without_generic!(pub ellipsis_type, ellipsis_node_ref);
    node_ref_to_type_class_without_generic!(pub typed_dict_type, typed_dict_node_ref);
    node_ref_to_type_class_without_generic!(pub typing_named_tuple_type, typing_named_tuple_node_ref);
    node_ref_to_type_class_without_generic!(pub typing_special_form_type, typing_special_form_node_ref);

    node_ref_to_type_class_without_generic!(pub supports_index_type, supports_index_node_ref);

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
        Type::new_class(
            PointLink::new(self.typing().file_index(), self.typing_type_var),
            ClassGenerics::None,
        )
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
        self.typing_overload().as_link()
    }

    pub fn coroutine_link(&self) -> PointLink {
        debug_assert!(self.typing_coroutine_index != 0);
        PointLink::new(self.typing().file_index(), self.typing_coroutine_index)
    }

    pub fn generator_link(&self) -> PointLink {
        self.generator_node_ref().as_link()
    }

    pub fn iterator_link(&self) -> PointLink {
        debug_assert!(self.typing_iterator_index != 0);
        PointLink::new(self.typing().file_index(), self.typing_iterator_index)
    }

    pub fn iterable_link(&self) -> PointLink {
        self.iterable_node_ref().as_link()
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
        Type::new_class(
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
    set_typing_inference(typing, "Never", Specific::TypingNeverOrNoReturn);
    set_typing_inference(typing, "NoReturn", Specific::TypingNeverOrNoReturn);
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
    set_typing_inference(builtins, "isinstance", Specific::BuiltinsIsinstance);
    set_typing_inference(builtins, "issubclass", Specific::BuiltinsIssubclass);

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
    set_typing_inference(t, "Literal", Specific::TypingLiteral);
    set_typing_inference(t, "Final", Specific::TypingFinal);
    set_typing_inference(t, "ParamSpec", Specific::TypingParamSpecClass);
    set_typing_inference(t, "TypeVar", Specific::TypingTypeVarClass);
    set_typing_inference(t, "TypeVarTuple", Specific::TypingTypeVarTupleClass);
    set_typing_inference(t, "Annotated", Specific::TypingAnnotated);
    set_typing_inference(t, "Protocol", Specific::TypingProtocol);
    setup_type_alias(typing_extensions, "final", typing, "final");
    // Not needed, because there's an import?
    //set_typing_inference(t, "Concatenate", Specific::TypingConcatenateClass);
    //set_typing_inference(t, "TypeAlias", Specific::TypingTypeAlias);
    //set_typing_inference(t, "Self", Specific::TypingSelf);
    //set_typing_inference(t, "LiteralString", Specific::TypingLiteralString);
    //set_typing_inference(t, "NamedTuple", Specific::TypingNamedTuple);
    //set_typing_inference(t, "Unpack", Specific::TypingUnpack);
    //set_typing_inference(t, "reveal_type", Specific::RevealTypeFunction);
    //set_typing_inference(t, "assert_type", Specific::AssertTypeFunction);
    //set_typing_inference(t, "NotRequired", Specific::TypingNotRequired);
    //set_typing_inference(t, "Required", Specific::TypingRequired);
    //set_typing_inference(t, "dataclass_transform", Specific::TypingDataclassTransform);

    for module in [typing, mypy_extensions, typing_extensions] {
        set_typing_inference(module, "TypedDict", Specific::TypingTypedDict);
    }
    set_typing_inference(mypy_extensions, "NoReturn", Specific::TypingNeverOrNoReturn);
}

fn set_typing_inference(file: &PythonFile, name: &str, specific: Specific) {
    let node_index = file
        .symbol_table
        .get()
        .unwrap()
        .lookup_symbol(name)
        .unwrap();
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
        "isinstance",
        "issubclass",
        "NoReturn",
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
    file.points
        .set(node_index, Point::new_specific(specific, Locality::Stmt));
}

fn set_custom_behavior(file: &PythonFile, name: &str, custom: CustomBehavior) {
    let node_index = file
        .symbol_table
        .get()
        .unwrap()
        .lookup_symbol(name)
        .unwrap();
    NodeRef::new(file, node_index).insert_complex(
        ComplexPoint::TypeInstance(Type::CustomBehavior(custom)),
        Locality::Stmt,
    );
}

/* TODO remove?
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
        ComplexPoint::TypeInstance(Type::CustomBehavior(custom)),
        Locality::Stmt,
    );
}
*/

fn setup_type_alias(typing: &PythonFile, name: &str, target_file: &PythonFile, target_name: &str) {
    let node_index = typing
        .symbol_table
        .get()
        .unwrap()
        .lookup_symbol(name)
        .unwrap();
    debug_assert!(!typing.points.get(node_index).calculated());
    let target_node_index = target_file
        .symbol_table
        .get()
        .unwrap()
        .lookup_symbol(target_name)
        .unwrap();
    typing.points.set(
        node_index, // Set it on name
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
    let node_index = file
        .symbol_table
        .get()
        .unwrap()
        .lookup_symbol(name)
        .unwrap();
    let name_def_node_index = node_index - NAME_DEF_TO_NAME_DIFFERENCE;
    // Act on the name def index and not the name.
    file.points.set(
        name_def_node_index,
        Point::new_specific(specific, Locality::Stmt),
    );
    let function_index = node_index - NAME_TO_FUNCTION_DIFF;
    debug_assert!(matches!(
        file.points.get(function_index).maybe_specific(),
        Some(Specific::Function | Specific::DecoratedFunction)
    ));
    function_index
}

fn calculate_mro_for_class(db: &Database, class: Class) -> Box<[BaseClass]> {
    let mut mro = Vec::from(class.use_cached_class_infos(db).mro.clone());
    for base in mro.iter_mut() {
        base.is_direct_base = false;
    }
    mro.insert(
        0,
        BaseClass {
            type_: class.as_type(db),
            is_direct_base: true,
        },
    );
    mro.into_boxed_slice()
}
