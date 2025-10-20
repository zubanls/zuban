use std::{ptr::null, sync::Arc};

use config::PythonVersion;
use parsa_python_cst::{FunctionDef, NAME_DEF_TO_NAME_DIFFERENCE, Name, NodeIndex, TypeLike};
use vfs::FileIndex;

use crate::{
    InferenceState,
    database::{BaseClass, Database, Locality, Point, PointLink, Specific},
    file::{ClassInitializer, ClassNodeRef, PythonFile},
    inferred::Inferred,
    matching::Generics,
    new_class,
    node_ref::NodeRef,
    type_::{
        AnyCause, CallableContent, CallableParam, CallableParams, ClassGenerics, CustomBehavior,
        NeverCause, ParamType, Tuple, Type, TypeArgs, TypeVarLikes, dataclasses_replace,
    },
    type_helpers::{Class, FirstParamProperties, Function, Instance, cache_class_name},
};

// This is a bit hacky, but I'm sure the tests will fail somewhere if this constant is
// wrong. Basically it goes three nodes back: name_def class literal and then the actual
// class.
pub const NAME_TO_CLASS_DIFF: u32 = 3;
pub const NAME_DEF_TO_CLASS_DIFF: u32 = NAME_TO_CLASS_DIFF - NAME_DEF_TO_NAME_DIFFERENCE;
// + 1 for def; + 2 for name
pub const NAME_TO_FUNCTION_DIFF: u32 = 3;

macro_rules! attribute_node_ref {
    ($module_name:ident, $vis:vis $name:ident, $attr:ident) => {
        #[inline]
        $vis fn $name(&self) -> NodeRef<'_> {
            debug_assert!(self.$attr != 0);
            NodeRef::new(self.$module_name(), self.$attr)
        }
    };
}

macro_rules! class_node_ref {
    ($module_name:ident, $vis:vis $name:ident, $attr:ident) => {
        #[inline]
        $vis fn $name(&self) -> ClassNodeRef<'_> {
            debug_assert!(self.$attr != 0);
            ClassNodeRef::new(self.$module_name(), self.$attr)
        }
    };
}

macro_rules! optional_class_node_ref {
    ($module_name:ident, $vis:vis $name:ident, $attr:ident) => {
        #[inline]
        $vis fn $name(&self) -> Option<ClassNodeRef<'_>> {
            self.$attr.map(|attr| {
                debug_assert!(attr != 0);
                ClassNodeRef::new(self.$module_name(), attr)
            })
        }
    };
}

macro_rules! optional_attribute_node_ref {
    ($module_name:ident, $vis:vis $name:ident, $attr:ident) => {
        #[inline]
        $vis fn $name(&self) -> Option<NodeRef<'_>> {
            self.$attr.map(|attr| {
                debug_assert!(attr != 0);
                NodeRef::new(self.$module_name(), attr)
            })
        }
    };
}

macro_rules! attribute_link {
    ($module_name:ident, $vis:vis $name:ident, $attr:ident) => {
        #[inline]
        $vis fn $name(&self) -> PointLink {
            debug_assert!(self.$attr != 0);
            NodeRef::new(self.$module_name(), self.$attr).as_link()
        }
    };
}

macro_rules! optional_attribute_link {
    ($module_name:ident, $vis:vis $name:ident, $attr:ident) => {
        #[inline]
        $vis fn $name(&self) -> Option<PointLink> {
            self.$attr.map(|attr| {
                debug_assert!(attr != 0);
                NodeRef::new(self.$module_name(), attr).as_link()
            })
        }
    };
}

macro_rules! node_ref_to_class {
    ($vis:vis $name:ident, $from_node_ref:ident) => {
        #[inline]
        $vis fn $name(&self) -> Class<'_> {
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

macro_rules! link_to_type_class_without_generic {
    ($vis:vis $name:ident, $access:ident) => {
        #[inline]
        $vis fn $name(&self) -> Type {
            debug_assert_ne!(self.$access.node_index, 0);
            Type::new_class(self.$access, ClassGenerics::None)
        }
    };
}

// TODO are these really safe?
unsafe impl Send for PythonState {}
unsafe impl Sync for PythonState {}

#[derive(Clone)]
pub(crate) struct PythonState {
    pub builtins: *const PythonFile,
    pub typing: *const PythonFile,
    pub typeshed: *const PythonFile,
    pub collections: *const PythonFile,
    pub _collections_abc: *const PythonFile,
    pub types: *const PythonFile,
    pub abc: *const PythonFile,
    pub functools: *const PythonFile,
    pub enum_file: *const PythonFile,
    pub dataclasses_file: *const PythonFile,
    pub mypy_extensions: *const PythonFile,
    pub typing_extensions: *const PythonFile,
    pub warnings: *const PythonFile,

    builtins_object_index: NodeIndex,
    builtins_type_index: NodeIndex,
    builtins_list_index: NodeIndex,
    builtins_tuple_index: NodeIndex,
    builtins_dict_index: NodeIndex,
    builtins_set_index: NodeIndex,
    builtins_frozenset_index: NodeIndex,
    builtins_bool_index: NodeIndex,
    builtins_int_index: NodeIndex,
    builtins_float_index: NodeIndex,
    builtins_complex_index: NodeIndex,
    builtins_function_index: NodeIndex,
    builtins_base_exception_index: NodeIndex,
    builtins_exception_index: NodeIndex,
    builtins_base_exception_group_index: Option<NodeIndex>,
    builtins_exception_group_index: Option<NodeIndex>,
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
    builtins_super_index: NodeIndex,
    builtins_callable_index: NodeIndex,
    builtins_hasattr_index: NodeIndex,
    builtins_len_index: NodeIndex,
    builtins_notimplementederror: NodeIndex,
    builtins_notimplemented_type: NodeIndex,
    pub builtins_int_mro: Box<[BaseClass]>,
    pub builtins_bool_mro: Box<[BaseClass]>,
    pub builtins_str_mro: Box<[BaseClass]>,
    pub builtins_bytes_mro: Box<[BaseClass]>,
    typeshed_supports_keys_and_get_item_index: NodeIndex,
    typing_type_var_index: NodeIndex,
    type_var_tuple_link: PointLink,
    param_spec_link: PointLink,
    pub typinglike_namedtuple_link: PointLink,
    new_type_link: PointLink,
    reveal_type_link: PointLink,
    typing_cast_index: NodeIndex,
    typing_coroutine_index: NodeIndex,
    typing_iterator_index: NodeIndex,
    typing_iterable_index: NodeIndex,
    typing_sequence_index: NodeIndex,
    typing_generator_index: NodeIndex,
    typing_async_generator_index: NodeIndex,
    typing_async_iterator_index: NodeIndex,
    typing_async_iterable_index: NodeIndex,
    typing_supports_index_index: NodeIndex,
    typing_overload_index: NodeIndex,
    typing_override_index: Option<NodeIndex>,
    typing_final_index: NodeIndex,
    typing_typed_dict_index: NodeIndex,
    typing_mapping_index: NodeIndex,
    typing_mutable_mapping_index: NodeIndex,
    typing_keys_view_index: NodeIndex,
    typing_runtime_checkable_index: NodeIndex,
    typing_extensions_runtime_checkable_index: NodeIndex,
    typing_container_index: NodeIndex,
    typing_special_form_index: NodeIndex,
    typing_no_type_check_index: NodeIndex,
    pub type_alias_type_link: PointLink,
    pub typing_typed_dict_bases: Box<[BaseClass]>,
    types_module_type_index: NodeIndex,
    types_none_type_index: Option<NodeIndex>,
    types_ellipsis_type_index: Option<NodeIndex>,
    types_union_type_index: Option<NodeIndex>,
    builtins_ellipsis_fallback_index: Option<NodeIndex>,
    collections_namedtuple_index: NodeIndex,
    collections_defaultdict_index: NodeIndex,
    _collections_abc_dict_keys_index: NodeIndex,
    abc_abc_meta_index: NodeIndex,
    abc_abstractmethod_index: NodeIndex,
    abc_abstractproperty_index: NodeIndex,
    functools_cached_property_index: NodeIndex,
    functools_total_ordering_index: NodeIndex,
    enum_enum_meta_index: NodeIndex,
    enum_enum_index: NodeIndex,
    enum_auto_index: NodeIndex,
    mypy_extensions_arg_func: NodeIndex,
    mypy_extensions_default_arg_func: NodeIndex,
    mypy_extensions_named_arg_func: NodeIndex,
    mypy_extensions_default_named_arg_func: NodeIndex,
    mypy_extensions_kw_arg_func: NodeIndex,
    mypy_extensions_var_arg_func: NodeIndex,
    dataclasses_capital_field_index: NodeIndex,
    dataclasses_replace_index: NodeIndex,
    warnings_deprecated_index: Option<NodeIndex>,
    pub type_of_object: Type, // TODO currently unused
    pub type_of_any: Type,
    pub type_of_self: Type,
    pub type_of_arbitrary_tuple: Type,
    pub any_or_none: Type,
    pub list_of_any: Type,
    pub dict_of_any: Type,
    pub set_of_any: Type,
    pub list_of_never: Type,
    pub dict_of_never: Type,
    pub tuple_of_obj: Type,
    pub tuple_of_unannotated_any: Type,
    pub dict_of_str_and_obj: Type,
    pub any_callable_from_error: Arc<CallableContent>,
    pub type_args_from_err: TypeArgs,
    pub generator_with_any_generics: Type,
    pub async_generator_with_any_generics: Type,
    pub valid_getattr_supertype: Type,
    pub iterable_of_str: Type,
    pub empty_type_var_likes: TypeVarLikes,
    pub dataclass_fields_type: Type,
}

impl PythonState {
    pub fn reserve() -> Self {
        let empty_type_var_likes = TypeVarLikes::new(Arc::new([]));
        Self {
            builtins: null(),
            typing: null(),
            typeshed: null(),
            collections: null(),
            _collections_abc: null(),
            types: null(),
            abc: null(),
            functools: null(),
            enum_file: null(),
            dataclasses_file: null(),
            mypy_extensions: null(),
            typing_extensions: null(),
            warnings: null(),
            builtins_object_index: 0,
            builtins_type_index: 0,
            builtins_list_index: 0,
            builtins_tuple_index: 0,
            builtins_dict_index: 0,
            builtins_set_index: 0,
            builtins_frozenset_index: 0,
            builtins_bool_index: 0,
            builtins_int_index: 0,
            builtins_float_index: 0,
            builtins_complex_index: 0,
            builtins_function_index: 0,
            builtins_base_exception_index: 0,
            builtins_exception_index: 0,
            builtins_base_exception_group_index: None,
            builtins_exception_group_index: None,
            builtins_str_index: 0,
            builtins_bytes_index: 0,
            builtins_bytearray_index: 0,
            builtins_memoryview_index: 0,
            builtins_slice_index: 0,
            builtins_classmethod_index: 0,
            builtins_staticmethod_index: 0,
            builtins_property_index: 0,
            builtins_notimplementederror: 0,
            builtins_notimplemented_type: 0,
            builtins_isinstance_index: 0,
            builtins_issubclass_index: 0,
            builtins_super_index: 0,
            builtins_callable_index: 0,
            builtins_hasattr_index: 0,
            builtins_len_index: 0,
            builtins_int_mro: Box::new([]),   // will be set later
            builtins_bool_mro: Box::new([]),  // will be set later
            builtins_str_mro: Box::new([]),   // will be set later
            builtins_bytes_mro: Box::new([]), // will be set later
            types_module_type_index: 0,
            types_none_type_index: None,
            types_ellipsis_type_index: None,
            types_union_type_index: None,
            builtins_ellipsis_fallback_index: None,
            typeshed_supports_keys_and_get_item_index: 0,
            typing_type_var_index: 0,
            type_var_tuple_link: PointLink::new(FileIndex(0), 0),
            param_spec_link: PointLink::new(FileIndex(0), 0),
            typinglike_namedtuple_link: PointLink::new(FileIndex(0), 0),
            new_type_link: PointLink::new(FileIndex(0), 0),
            reveal_type_link: PointLink::new(FileIndex(0), 0),
            type_alias_type_link: PointLink::new(FileIndex(0), 0),
            typing_cast_index: 0,
            typing_overload_index: 0,
            typing_override_index: None,
            typing_final_index: 0,
            typing_typed_dict_index: 0,
            typing_container_index: 0,
            typing_mapping_index: 0,
            typing_mutable_mapping_index: 0,
            typing_keys_view_index: 0,
            typing_runtime_checkable_index: 0,
            typing_extensions_runtime_checkable_index: 0,
            typing_special_form_index: 0,
            typing_no_type_check_index: 0,
            typing_coroutine_index: 0,
            typing_iterator_index: 0,
            typing_iterable_index: 0,
            typing_sequence_index: 0,
            typing_generator_index: 0,
            typing_async_generator_index: 0,
            typing_async_iterator_index: 0,
            typing_async_iterable_index: 0,
            typing_supports_index_index: 0,
            typing_typed_dict_bases: Box::new([]), // Will be set later
            collections_namedtuple_index: 0,
            collections_defaultdict_index: 0,
            _collections_abc_dict_keys_index: 0,
            abc_abc_meta_index: 0,
            abc_abstractmethod_index: 0,
            abc_abstractproperty_index: 0,
            functools_cached_property_index: 0,
            functools_total_ordering_index: 0,
            enum_enum_meta_index: 0,
            enum_enum_index: 0,
            enum_auto_index: 0,
            mypy_extensions_arg_func: 0,
            mypy_extensions_default_arg_func: 0,
            mypy_extensions_named_arg_func: 0,
            mypy_extensions_default_named_arg_func: 0,
            mypy_extensions_kw_arg_func: 0,
            mypy_extensions_var_arg_func: 0,
            dataclasses_capital_field_index: 0,
            dataclasses_replace_index: 0,
            warnings_deprecated_index: None,
            type_of_object: Type::None, // Will be set later
            type_of_any: Type::Type(Arc::new(Type::Any(AnyCause::Todo))),
            type_of_self: Type::Type(Arc::new(Type::Self_)),
            type_of_arbitrary_tuple: Type::Type(Arc::new(Type::Tuple(
                Tuple::new_arbitrary_length_with_any(),
            ))),
            list_of_any: Type::None, // Will be set later
            any_or_none: Type::ERROR.union(Type::None),
            dict_of_any: Type::None,   // Will be set later
            set_of_any: Type::None,    // Will be set later
            list_of_never: Type::None, // Will be set later
            dict_of_never: Type::None, // Will be set later
            tuple_of_obj: Type::None,  // Will be set later
            tuple_of_unannotated_any: Type::Tuple(Tuple::new_arbitrary_length(Type::Any(
                AnyCause::Unannotated,
            ))),
            dict_of_str_and_obj: Type::None, // Will be set later
            any_callable_from_error: Arc::new(CallableContent::new_any(
                empty_type_var_likes.clone(),
                AnyCause::FromError,
            )),
            type_args_from_err: TypeArgs::new_arbitrary_from_error(),
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
        _collections_abc: *const PythonFile,
        types: *const PythonFile,
        abc: *const PythonFile,
        functools: *const PythonFile,
        enum_file: *const PythonFile,
        dataclasses_file: *const PythonFile,
        typing_extensions: *const PythonFile,
        mypy_extensions: *const PythonFile,
        warnings: *const PythonFile,
    ) {
        let s = &mut db.python_state;
        s.builtins = builtins;
        s.typing = typing;
        s.typeshed = typeshed;
        s.collections = collections;
        s._collections_abc = _collections_abc;
        s.types = types;
        s.abc = abc;
        s.functools = functools;
        s.enum_file = enum_file;
        s.dataclasses_file = dataclasses_file;
        s.typing_extensions = typing_extensions;
        s.mypy_extensions = mypy_extensions;
        s.warnings = warnings;

        typing_changes(
            s.typing(),
            s.builtins(),
            s.collections(),
            s.types(),
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

        // Set class indexes and calculate the base types.
        // This needs to be done before it gets accessed, because we expect the MRO etc. to be
        // calculated when a class is accessed. Normally this happens on access, but here we access
        // classes randomly via db.python_state. Therefore do the calculation here.
        fn cache_index(
            db: &mut Database,
            module: impl Fn(&Database) -> &PythonFile,
            name: &str,
            update: impl FnOnce(&mut Database, Option<NodeIndex>),
            is_func: bool,
        ) {
            let name_index = module(db).symbol_table.lookup_symbol(name);
            let Some(name_index) = name_index else {
                update(db, None);
                return;
            };
            let class_index = name_index - NAME_TO_CLASS_DIFF;
            if NodeRef::new(module(db), class_index)
                .maybe_class()
                .is_some()
            {
                if is_func {
                    panic!(
                        "Expected a function for {}.{name}",
                        module(db).qualified_name(db)
                    )
                }
                update(db, Some(class_index));
                let class =
                    ClassInitializer::from_node_ref(ClassNodeRef::new(module(db), class_index));
                let name_def_ref =
                    NodeRef::new(class.node_ref.file, class.node().name_def().index());
                cache_class_name(
                    name_def_ref,
                    NodeRef::new(module(db), class_index).maybe_class().unwrap(),
                );
                name_def_ref.set_point(Point::new_redirect(
                    name_def_ref.file_index(),
                    class.node_ref.node_index,
                    Locality::Todo,
                ));
                class.ensure_calculated_class_infos(db);
            } else {
                let func_index = name_index - NAME_TO_FUNCTION_DIFF;
                let file = module(db);
                let node_ref = NodeRef::new(file, func_index);

                if node_ref.maybe_function().is_some() {
                    if !is_func {
                        panic!(
                            "Expected a class for {}.{name}",
                            module(db).qualified_name(db)
                        )
                    }
                    Function::new(node_ref, None)
                        .ensure_cached_func(&InferenceState::new(db, file));
                    update(db, Some(func_index))
                } else if NodeRef::new(file, name_index)
                    .maybe_import_of_name_in_symbol_table()
                    .is_some()
                {
                    // This is not a proper identifier, it's an import, for now assign None
                    update(db, None);
                } else {
                    panic!(
                        "It's not possible to cache the index for the alias {}.{name}",
                        module(db).qualified_name(db)
                    )
                }
            }
        }
        #[collapse_debuginfo(yes)]
        macro_rules! cache_index {
            ($attr_name:ident, $module_name:ident, $name:literal) => {
                cache_index!($attr_name, $module_name, $name, false)
            };
            ($attr_name:ident, $module_name:ident, $name:literal, $is_func:expr) => {
                cache_index(
                    db,
                    |db| db.python_state.$module_name(),
                    $name,
                    |db, new_index| {
                        db.python_state.$attr_name =
                            new_index.unwrap_or_else(|| panic!("Expected {}", $name));
                    },
                    $is_func,
                );
            };
        }
        macro_rules! cache_typing_link_with_typing_extensions_fallback {
            ($attr_name:ident, $name:literal, $is_func:expr) => {
                // NewType is special, because the fallback is a function in current
                // Typeshed, so use TypingExtensions for now...
                let use_new_type_from_typing_extensions = $name == "NewType" && legacy_new_type(db);
                cache_index(
                    db,
                    |db| {
                        if use_new_type_from_typing_extensions {
                            return db.python_state.typing_extensions();
                        }
                        db.python_state.typing()
                    },
                    $name,
                    |db, new_index| {
                        let Some(new_index) = new_index else {
                            cache_index(
                                db,
                                |db| db.python_state.typing_extensions(),
                                $name,
                                |db, new_index| {
                                    db.python_state.$attr_name = PointLink::new(
                                        db.python_state.typing_extensions().file_index,
                                        new_index.unwrap_or_else(|| panic!("Expected {}", $name)),
                                    );
                                },
                                $is_func,
                            );
                            return;
                        };
                        let file_index = if use_new_type_from_typing_extensions {
                            db.python_state.typing_extensions().file_index
                        } else {
                            db.python_state.typing().file_index
                        };
                        db.python_state.$attr_name = PointLink::new(file_index, new_index);
                    },
                    $is_func,
                );
            };
        }

        macro_rules! cache_optional_index {
            ($attr_name:ident, $module_name:ident, $name:literal) => {
                cache_optional_index!($attr_name, $module_name, $name, false)
            };
            ($attr_name:ident, $module_name:ident, $name:literal, $is_func:expr) => {
                cache_index(
                    db,
                    |db| db.python_state.$module_name(),
                    $name,
                    |db, class_index| {
                        db.python_state.$attr_name = class_index;
                    },
                    $is_func,
                );
            };
        }

        // This first block
        cache_index!(typing_final_index, typing, "final", true);
        cache_index!(typing_no_type_check_index, typing, "no_type_check", true);
        cache_index!(
            typing_runtime_checkable_index,
            typing,
            "runtime_checkable",
            true
        );
        cache_index!(
            typing_extensions_runtime_checkable_index,
            typing_extensions,
            "runtime_checkable",
            true
        );
        cache_index!(
            functools_total_ordering_index,
            functools,
            "total_ordering",
            true
        );
        cache_index!(builtins_object_index, builtins, "object");
        cache_index!(builtins_type_index, builtins, "type");
        cache_index!(abc_abc_meta_index, abc, "ABCMeta");
        cache_index!(types_module_type_index, types, "ModuleType");
        cache_index!(enum_enum_meta_index, enum_file, "EnumMeta");
        cache_index!(typing_overload_index, typing, "overload", true);
        cache_index!(typing_type_var_index, typing, "TypeVar");
        cache_index!(builtins_str_index, builtins, "str");
        cache_index!(enum_enum_index, enum_file, "Enum");
        cache_index!(enum_auto_index, enum_file, "auto");

        cache_index!(builtins_dict_index, builtins, "dict");
        cache_index!(builtins_list_index, builtins, "list");
        cache_index!(builtins_set_index, builtins, "set");
        cache_index!(builtins_frozenset_index, builtins, "frozenset");
        cache_index!(builtins_bool_index, builtins, "bool");
        cache_index!(builtins_int_index, builtins, "int");
        cache_index!(builtins_float_index, builtins, "float");
        cache_index!(builtins_complex_index, builtins, "complex");
        cache_index!(builtins_tuple_index, builtins, "tuple");
        cache_index!(builtins_function_index, builtins, "function");
        cache_index!(builtins_base_exception_index, builtins, "BaseException");
        cache_index!(builtins_exception_index, builtins, "Exception");
        cache_optional_index!(
            builtins_base_exception_group_index,
            builtins,
            "BaseExceptionGroup"
        );
        cache_optional_index!(builtins_exception_group_index, builtins, "ExceptionGroup");
        cache_index!(builtins_bytes_index, builtins, "bytes");
        cache_index!(builtins_bytearray_index, builtins, "bytearray");
        cache_index!(builtins_memoryview_index, builtins, "memoryview");
        cache_index!(builtins_slice_index, builtins, "slice");
        cache_index!(builtins_classmethod_index, builtins, "classmethod");
        cache_index!(builtins_staticmethod_index, builtins, "staticmethod");
        cache_index!(builtins_property_index, builtins, "property");
        cache_index!(
            builtins_notimplementederror,
            builtins,
            "NotImplementedError"
        );
        cache_index!(
            builtins_notimplemented_type,
            builtins,
            "_NotImplementedType"
        );
        cache_index!(
            typeshed_supports_keys_and_get_item_index,
            typeshed,
            "SupportsKeysAndGetItem"
        );
        cache_typing_link_with_typing_extensions_fallback!(
            type_var_tuple_link,
            "TypeVarTuple",
            false
        );
        cache_typing_link_with_typing_extensions_fallback!(param_spec_link, "ParamSpec", false);
        cache_typing_link_with_typing_extensions_fallback!(
            typinglike_namedtuple_link,
            "NamedTuple",
            false
        );
        cache_typing_link_with_typing_extensions_fallback!(new_type_link, "NewType", false);
        cache_typing_link_with_typing_extensions_fallback!(reveal_type_link, "reveal_type", true);
        cache_typing_link_with_typing_extensions_fallback!(
            type_alias_type_link,
            "TypeAliasType",
            false
        );
        cache_index!(typing_cast_index, typing, "cast", true);
        cache_index!(typing_coroutine_index, typing, "Coroutine");
        cache_index!(typing_iterator_index, typing, "Iterator");
        cache_index!(typing_iterable_index, typing, "Iterable");
        cache_index!(typing_sequence_index, typing, "Sequence");
        cache_index!(typing_generator_index, typing, "Generator");
        cache_index!(typing_async_generator_index, typing, "AsyncGenerator");
        cache_index!(typing_async_iterator_index, typing, "AsyncIterator");
        cache_index!(typing_async_iterable_index, typing, "AsyncIterable");
        cache_index!(typing_supports_index_index, typing, "SupportsIndex");
        cache_index!(typing_typed_dict_index, typing, "_TypedDict");
        cache_index!(typing_container_index, typing, "Container");
        cache_index!(typing_mapping_index, typing, "Mapping");
        cache_index!(typing_mutable_mapping_index, typing, "MutableMapping");
        cache_index!(typing_keys_view_index, typing, "KeysView");
        cache_index!(typing_special_form_index, typing, "_SpecialForm");
        cache_optional_index!(types_none_type_index, types, "NoneType");
        cache_optional_index!(types_ellipsis_type_index, types, "EllipsisType");
        cache_optional_index!(types_union_type_index, types, "UnionType");
        if let Some(ellipsis) = db.python_state.builtins().lookup_symbol("ellipsis")
            && matches!(
                ellipsis
                    .name_def_ref_of_name()
                    .expect_name_def()
                    .expect_type(),
                TypeLike::ClassDef(_)
            )
        {
            cache_optional_index!(builtins_ellipsis_fallback_index, builtins, "ellipsis");
        }
        cache_index!(abc_abstractproperty_index, abc, "abstractproperty");
        cache_index!(
            functools_cached_property_index,
            functools,
            "cached_property"
        );
        cache_index!(dataclasses_capital_field_index, dataclasses_file, "Field");

        cache_index!(builtins_isinstance_index, builtins, "isinstance", true);
        cache_index!(builtins_issubclass_index, builtins, "issubclass", true);
        cache_index!(builtins_super_index, builtins, "super");
        cache_index!(builtins_callable_index, builtins, "callable", true);
        cache_index!(builtins_hasattr_index, builtins, "hasattr", true);
        cache_index!(builtins_len_index, builtins, "len", true);

        cache_optional_index!(typing_override_index, typing, "override", true);

        cache_index!(dataclasses_replace_index, dataclasses_file, "replace", true);

        cache_optional_index!(warnings_deprecated_index, warnings, "deprecated");
        if db.python_state.warnings_deprecated_index.is_none() {
            cache_optional_index!(warnings_deprecated_index, typing_extensions, "deprecated");
        }

        cache_index!(abc_abstractmethod_index, abc, "abstractmethod", true);
        cache_index!(abc_abstractmethod_index, abc, "abstractmethod", true);

        cache_index!(
            collections_namedtuple_index,
            collections,
            "namedtuple",
            true
        );
        cache_index!(collections_defaultdict_index, collections, "defaultdict");
        cache_index!(
            _collections_abc_dict_keys_index,
            _collections_abc,
            "dict_keys"
        );
        // Some cases "Special" types need to be precalculated, because their names are overwritten.
        {
            let legacy_new_type = legacy_new_type(db);
            let mut cache_without_saving_in_typing = |name| {
                cache_index(db, |db| db.python_state.typing(), name, |_, _| (), true);
                cache_index(
                    db,
                    |db| db.python_state.typing_extensions(),
                    name,
                    |_, _| (),
                    true,
                );
            };
            cache_without_saving_in_typing("dataclass_transform");
            cache_without_saving_in_typing("assert_type");
            if legacy_new_type {
                cache_index(
                    db,
                    |db| db.python_state.typing(),
                    "NewType",
                    |_, _| (),
                    true,
                );
            }
            let mut cache_without_saving_mypy_extensions = |name| {
                cache_index(
                    db,
                    |db| db.python_state.mypy_extensions(),
                    name,
                    |_, _| (),
                    true,
                )
            };
            cache_without_saving_mypy_extensions("Arg");
            cache_without_saving_mypy_extensions("DefaultArg");
            cache_without_saving_mypy_extensions("NamedArg");
            cache_without_saving_mypy_extensions("DefaultNamedArg");
            cache_without_saving_mypy_extensions("VarArg");
            cache_without_saving_mypy_extensions("KwArg");
            cache_without_saving_mypy_extensions("TypedDict");
        }

        let typed_dict_mro = calculate_mro_for_class(db, db.python_state.typed_dict_class());
        let builtins_int_mro = calculate_mro_for_class(db, db.python_state.int());
        let builtins_bool_mro = calculate_mro_for_class(db, db.python_state.bool());
        let builtins_str_mro = calculate_mro_for_class(db, db.python_state.str());
        let builtins_bytes_mro = calculate_mro_for_class(db, db.python_state.bytes());

        let s = &mut db.python_state;
        let object_type = s.object_type();
        s.type_of_object = Type::Type(Arc::new(object_type));
        s.list_of_any = new_class!(s.list_node_ref().as_link(), Type::ERROR);
        s.dict_of_any = new_class!(s.dict_node_ref().as_link(), Type::ERROR, Type::ERROR);
        s.set_of_any = new_class!(s.set_node_ref().as_link(), Type::ERROR);
        s.list_of_never = new_class!(
            s.list_node_ref().as_link(),
            Type::Never(NeverCause::Inference)
        );
        s.dict_of_never = new_class!(
            s.dict_node_ref().as_link(),
            Type::Never(NeverCause::Inference),
            Type::Never(NeverCause::Inference),
        );
        s.tuple_of_obj = Type::Tuple(Tuple::new_arbitrary_length(s.object_type()));
        s.dict_of_str_and_obj =
            new_class!(s.dict_node_ref().as_link(), s.str_type(), s.object_type(),);
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
        s.valid_getattr_supertype = Type::Callable(Arc::new(CallableContent::new_simple(
            None,
            None,
            PointLink::new(FileIndex(0), 0),
            s.empty_type_var_likes.clone(),
            CallableParams::new_simple(Arc::new([
                CallableParam::new_anonymous(ParamType::PositionalOnly(Type::Any(
                    AnyCause::Internal,
                ))),
                CallableParam::new_anonymous(ParamType::PositionalOnly(s.str_type())),
            ])),
            Type::Any(AnyCause::Internal),
        )));
        s.iterable_of_str = new_class!(s.iterable_link(), s.str_type(),);

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

        // Set promotions
        let s = &db.python_state;
        s.int()
            .use_cached_class_infos(db)
            .set_promote_to(Some(s.float_node_ref().as_link()));
        s.bool()
            .use_cached_class_infos(db)
            .set_promote_to(Some(s.float_node_ref().as_link()));
        s.float()
            .use_cached_class_infos(db)
            .set_promote_to(Some(s.complex_node_ref().as_link()));
        if !db.project.flags.disable_memoryview_promotion {
            s.memoryview_class_with_generics_to_be_defined()
                .use_cached_class_infos(db)
                .set_promote_to(Some(s.bytes_node_ref().as_link()));
        }
        if !db.project.flags.disable_bytearray_promotion {
            s.bytearray()
                .use_cached_class_infos(db)
                .set_promote_to(Some(s.bytes_node_ref().as_link()));
        }
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
    pub fn _collections_abc(&self) -> &PythonFile {
        debug_assert!(!self._collections_abc.is_null());
        unsafe { &*self._collections_abc }
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
    pub fn warnings(&self) -> &PythonFile {
        debug_assert!(!self.warnings.is_null());
        unsafe { &*self.warnings }
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
    pub fn tuple_class_with_generics_to_be_defined(&self) -> Class<'_> {
        let class_ref = self.tuple_node_ref();
        Class::from_position(class_ref, Generics::NotDefinedYet { class_ref }, None)
    }

    pub fn memoryview_class_with_generics_to_be_defined(&self) -> Class<'_> {
        let class_ref = self.memoryview_node_ref();
        Class::from_position(class_ref, Generics::NotDefinedYet { class_ref }, None)
    }

    pub fn memoryview_type_with_any_generics(&self, db: &Database) -> Type {
        self.memoryview_class_with_generics_to_be_defined()
            .as_type(db)
    }

    pub fn bare_tuple_type_with_any(&self) -> Type {
        new_class!(
            self.tuple_node_ref().as_link(),
            Type::Any(AnyCause::Internal),
        )
    }

    class_node_ref!(builtins, pub object_node_ref, builtins_object_index);
    class_node_ref!(builtins, pub bare_type_node_ref, builtins_type_index);
    class_node_ref!(builtins, pub list_node_ref, builtins_list_index);
    class_node_ref!(builtins, pub tuple_node_ref, builtins_tuple_index);
    class_node_ref!(builtins, pub dict_node_ref, builtins_dict_index);
    class_node_ref!(builtins, pub set_node_ref, builtins_set_index);
    class_node_ref!(builtins, pub frozenset_node_ref, builtins_frozenset_index);
    class_node_ref!(builtins, pub bool_node_ref, builtins_bool_index);
    class_node_ref!(builtins, pub int_node_ref, builtins_int_index);
    class_node_ref!(builtins, float_node_ref, builtins_float_index);
    class_node_ref!(builtins, complex_node_ref, builtins_complex_index);
    class_node_ref!(builtins, pub str_node_ref, builtins_str_index);
    class_node_ref!(builtins, pub bytes_node_ref, builtins_bytes_index);
    class_node_ref!(builtins, pub bytearray_node_ref, builtins_bytearray_index);
    class_node_ref!(builtins, pub memoryview_node_ref, builtins_memoryview_index);
    attribute_node_ref!(builtins, pub classmethod_node_ref, builtins_classmethod_index);
    attribute_node_ref!(builtins, pub staticmethod_node_ref, builtins_staticmethod_index);
    attribute_node_ref!(builtins, pub property_node_ref, builtins_property_index);
    attribute_node_ref!(builtins, pub isinstance_node_ref, builtins_isinstance_index);
    attribute_node_ref!(builtins, pub issubclass_node_ref, builtins_issubclass_index);
    attribute_node_ref!(builtins, pub super_node_ref, builtins_super_index);
    attribute_node_ref!(builtins, pub callable_node_ref, builtins_callable_index);
    attribute_node_ref!(builtins, pub hasattr_node_ref, builtins_hasattr_index);
    attribute_node_ref!(builtins, pub len_node_ref, builtins_len_index);
    class_node_ref!(builtins, pub function_node_ref, builtins_function_index);
    attribute_node_ref!(builtins, pub notimplemented_type_node_ref, builtins_notimplemented_type);
    attribute_node_ref!(
        builtins,
        pub base_exception_node_ref,
        builtins_base_exception_index
    );
    attribute_node_ref!(builtins, pub exception_node_ref, builtins_exception_index);
    optional_class_node_ref!(
        builtins,
        pub base_exception_group_node_ref,
        builtins_base_exception_group_index
    );
    optional_class_node_ref!(
        builtins,
        pub exception_group_node_ref,
        builtins_exception_group_index
    );

    attribute_node_ref!(typing, pub type_var_node_ref, typing_type_var_index);
    //attribute_node_ref!(typing, cast_node_ref, typing_cast_index);
    attribute_node_ref!(typing, supports_index_node_ref, typing_supports_index_index);
    class_node_ref!(typing, typed_dict_node_ref, typing_typed_dict_index);
    attribute_node_ref!(typing, pub container_node_ref, typing_container_index);
    class_node_ref!(typing, pub mapping_node_ref, typing_mapping_index);
    class_node_ref!(typing, pub mutable_mapping_node_ref, typing_mutable_mapping_index);
    class_node_ref!(typing, pub keys_view_node_ref, typing_keys_view_index);
    optional_attribute_node_ref!(typing, pub typing_override, typing_override_index);
    optional_attribute_node_ref!(warnings, pub deprecated, warnings_deprecated_index);
    attribute_node_ref!(typing, pub typing_final, typing_final_index);
    class_node_ref!(typing, pub generator_node_ref, typing_generator_index);
    attribute_node_ref!(typing, pub iterable_node_ref, typing_iterable_index);
    class_node_ref!(typing, pub sequence_node_ref, typing_sequence_index);
    attribute_node_ref!(
        typing,
        pub typing_special_form_node_ref,
        typing_special_form_index
    );
    optional_class_node_ref!(types, none_type_node_ref, types_none_type_index);
    class_node_ref!(types, module_node_ref, types_module_type_index);
    class_node_ref!(
        typeshed,
        pub supports_keys_and_get_item_node_ref,
        typeshed_supports_keys_and_get_item_index
    );
    attribute_node_ref!(enum_file, pub enum_node_ref, enum_enum_index);
    attribute_node_ref!(
        collections,
        collections_named_tuple_node_ref,
        collections_namedtuple_index
    );
    class_node_ref!(_collections_abc, pub _collections_abc_dict_keys_node_ref, _collections_abc_dict_keys_index);
    attribute_node_ref!(functools, pub total_ordering_node_ref, functools_total_ordering_index);
    attribute_node_ref!(typing, pub runtime_checkable_node_ref, typing_runtime_checkable_index);
    attribute_node_ref!(typing_extensions, pub typing_extensions_runtime_checkable_node_ref, typing_extensions_runtime_checkable_index);

    attribute_link!(builtins, pub object_link, builtins_object_index);
    attribute_link!(builtins, pub int_link, builtins_int_index);
    attribute_link!(builtins, pub float_link, builtins_float_index);
    attribute_link!(builtins, pub str_link, builtins_str_index);
    attribute_link!(builtins, pub bytes_link, builtins_bytes_index);
    attribute_link!(builtins, pub bytearray_link, builtins_bytearray_index);
    attribute_link!(builtins, pub bool_link, builtins_bool_index);
    attribute_link!(builtins, pub list_link, builtins_list_index);
    attribute_link!(builtins, pub dict_link, builtins_dict_index);
    attribute_link!(builtins, pub set_link, builtins_set_index);
    attribute_link!(builtins, pub frozenset_link, builtins_frozenset_index);
    attribute_link!(builtins, pub notimplementederror_link, builtins_notimplementederror);
    attribute_link!(builtins, pub slice_link, builtins_slice_index);
    attribute_link!(abc, pub abc_meta_link, abc_abc_meta_index);
    attribute_link!(abc, pub abstractmethod_link, abc_abstractmethod_index);
    attribute_link!(abc, pub abstractproperty_link, abc_abstractproperty_index);
    attribute_link!(functools, pub cached_property_link, functools_cached_property_index);
    attribute_link!(enum_file, pub enum_meta_link, enum_enum_meta_index);
    attribute_link!(enum_file, pub enum_auto_link, enum_auto_index);
    attribute_link!(typing, pub overload_link, typing_overload_index);
    attribute_link!(typing, pub sequence_link, typing_sequence_index);
    attribute_link!(typing, pub coroutine_link, typing_coroutine_index);
    attribute_link!(typing, pub generator_link, typing_generator_index);
    attribute_link!(typing, pub iterator_link, typing_iterator_index);
    attribute_link!(typing, pub iterable_link, typing_iterable_index);
    attribute_link!(typing, pub async_generator_link, typing_async_generator_index);
    attribute_link!(typing, pub async_iterator_link, typing_async_iterator_index);
    attribute_link!(typing, pub async_iterable_link, typing_async_iterable_index);
    attribute_link!(typing, pub no_type_check_link, typing_no_type_check_index);
    attribute_link!(collections, pub defaultdict_link, collections_defaultdict_index);
    optional_attribute_link!(types, ellipsis_type_link, types_ellipsis_type_index);
    optional_attribute_link!(types, union_type_link, types_union_type_index);
    optional_attribute_link!(
        builtins,
        ellipsis_fallback_link,
        builtins_ellipsis_fallback_index
    );
    attribute_link!(
        dataclasses_file,
        dataclasses_capital_field_link,
        dataclasses_capital_field_index
    );
    optional_attribute_link!(warnings, pub deprecated_link, warnings_deprecated_index);

    node_ref_to_class!(pub object_class, object_node_ref);
    node_ref_to_class!(int, int_node_ref);
    node_ref_to_class!(pub str_class, str_node_ref);
    node_ref_to_class!(bool, bool_node_ref);
    node_ref_to_class!(str, str_node_ref);
    node_ref_to_class!(bytes, bytes_node_ref);
    node_ref_to_class!(float, float_node_ref);
    node_ref_to_class!(pub bytearray, bytearray_node_ref);
    node_ref_to_class!(pub function_class, function_node_ref);
    node_ref_to_class!(pub bare_type_class, bare_type_node_ref);
    node_ref_to_class!(pub typed_dict_class, typed_dict_node_ref);

    node_ref_to_type_class_without_generic!(pub object_type, object_node_ref);
    node_ref_to_type_class_without_generic!(pub str_type, str_node_ref);
    node_ref_to_type_class_without_generic!(pub bytes_type, bytes_node_ref);
    node_ref_to_type_class_without_generic!(pub bytearray_type, bytearray_node_ref);
    node_ref_to_type_class_without_generic!(pub super_type, super_node_ref);
    node_ref_to_type_class_without_generic!(pub int_type, int_node_ref);
    node_ref_to_type_class_without_generic!(pub bool_type, bool_node_ref);
    node_ref_to_type_class_without_generic!(pub float_type, float_node_ref);
    node_ref_to_type_class_without_generic!(pub complex_type, complex_node_ref);
    node_ref_to_type_class_without_generic!(pub module_type, module_node_ref);
    node_ref_to_type_class_without_generic!(pub property_type, property_node_ref);
    node_ref_to_type_class_without_generic!(pub function_type, function_node_ref);
    node_ref_to_type_class_without_generic!(pub bare_type_type, bare_type_node_ref);
    node_ref_to_type_class_without_generic!(pub type_var_type, type_var_node_ref);
    node_ref_to_type_class_without_generic!(pub typing_special_form_type, typing_special_form_node_ref);
    node_ref_to_type_class_without_generic!(pub supports_index_type, supports_index_node_ref);

    link_to_type_class_without_generic!(pub type_var_tuple_type, type_var_tuple_link);
    link_to_type_class_without_generic!(pub param_spec_type, param_spec_link);
    link_to_type_class_without_generic!(pub new_type_type, new_type_link);
    link_to_type_class_without_generic!(pub typing_named_tuple_type, typinglike_namedtuple_link);
    link_to_type_class_without_generic!(pub type_alias_type_type, type_alias_type_link);

    pub fn typing_named_tuple_class<'db>(&self, db: &'db Database) -> Class<'db> {
        Class::from_position(
            ClassNodeRef::from_link(db, self.typinglike_namedtuple_link),
            Generics::None,
            None,
        )
    }

    pub fn none_instance(&self) -> Instance<'_> {
        let Some(none_node_ref) = self.none_type_node_ref() else {
            // TODO this might not be correct, but does it really matter?
            return self.object_class().instance();
        };
        Instance::new(Class::from_non_generic_node_ref(none_node_ref), None)
    }

    pub fn ellipsis_link(&self) -> PointLink {
        self.ellipsis_type_link().unwrap_or_else(|| {
            self.ellipsis_fallback_link()
                .expect("None of typing.ellipsis or types.EllipsisType exists")
        })
    }

    pub fn ellipsis_type(&self) -> Type {
        Type::new_class(self.ellipsis_link(), ClassGenerics::None)
    }

    pub fn union_type(&self) -> Option<Type> {
        Some(Type::new_class(
            self.union_type_link()?,
            ClassGenerics::None,
        ))
    }

    pub fn supports_keys_and_get_item_class<'a>(&'a self, db: &'a Database) -> Class<'a> {
        Class::with_self_generics(db, self.supports_keys_and_get_item_node_ref())
    }

    pub(crate) fn collections_namedtuple_function(&self) -> Function<'_, '_> {
        Function::new(self.collections_named_tuple_node_ref(), None)
    }

    pub(crate) fn dataclasses_replace(&self) -> Function<'_, '_> {
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
        let func = Function::new(NodeRef::new(self.mypy_extensions(), node_index), None);
        func.ensure_cached_func(&InferenceState::new(db, func.file));
        Inferred::from_saved_node_ref(func.node_ref.into())
    }

    pub fn module_instance(&self) -> Instance<'_> {
        Instance::new(
            Class::from_non_generic_node_ref(self.module_node_ref()),
            None,
        )
    }

    pub fn isinstance_type(&self, db: &Database) -> Type {
        node_ref_to_global_func_type(db, self.isinstance_node_ref())
    }

    pub fn issubclass_type(&self, db: &Database) -> Type {
        node_ref_to_global_func_type(db, self.issubclass_node_ref())
    }

    pub fn reveal_type(&self, db: &Database) -> Type {
        node_ref_to_global_func_type(db, NodeRef::from_link(db, self.reveal_type_link))
    }
}

fn node_ref_to_global_func_type(db: &Database, n: NodeRef) -> Type {
    assert!(
        n.maybe_function().is_some(),
        "Expected a function for {:?}",
        n.file.tree.short_debug_of_index(n.node_index)
    );
    let func = Function::new(n, None);
    let i_s = InferenceState::new(db, func.file);
    func.as_type(&i_s, FirstParamProperties::None)
}

fn typing_changes(
    typing: &PythonFile,
    builtins: &PythonFile,
    collections: &PythonFile,
    types: &PythonFile,
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
    set_typing_inference(typing, "TypeAliasType", Specific::TypingTypeAliasType);
    set_typing_inference(typing, "Self", Specific::TypingSelf);
    set_typing_inference(typing, "Annotated", Specific::TypingAnnotated);
    set_typing_inference(typing, "Never", Specific::TypingNeverOrNoReturn);
    set_typing_inference(typing, "NoReturn", Specific::TypingNeverOrNoReturn);
    set_typing_inference(typing, "Required", Specific::TypingRequired);
    set_typing_inference(typing, "NotRequired", Specific::TypingNotRequired);
    set_typing_inference(typing, "ReadOnly", Specific::TypingReadOnly);
    set_typing_inference(typing, "TypeGuard", Specific::TypingTypeGuard);
    set_typing_inference(typing, "TypeIs", Specific::TypingTypeIs);
    set_typing_inference(typing, "reveal_type", Specific::RevealTypeFunction);
    set_typing_inference(typing, "assert_type", Specific::AssertTypeFunction);
    set_typing_inference(
        typing,
        "dataclass_transform",
        Specific::TypingDataclassTransform,
    );

    set_typing_inference(builtins, "tuple", Specific::TypingTuple);
    set_typing_inference(builtins, "type", Specific::BuiltinsType);
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
    if let Some(none_type_index) = types.symbol_table.lookup_symbol("NoneType") {
        // Making NoneType Type[None] just makes type checking way easier.
        NodeRef::new(types, none_type_index).insert_type(Type::Type(Arc::new(Type::None)));
    }

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
    set_typing_inference(t, "TypeGuard", Specific::TypingTypeGuard);
    set_typing_inference(t, "TypeIs", Specific::TypingTypeIs);
    set_typing_inference(t, "Self", Specific::TypingSelf);
    set_typing_inference(t, "TypeAliasType", Specific::TypingTypeAliasType);
    setup_type_alias(t, "final", typing, "final");
    set_typing_inference(t, "Concatenate", Specific::TypingConcatenateClass);
    set_typing_inference(t, "TypeAlias", Specific::TypingTypeAlias);
    set_typing_inference(t, "LiteralString", Specific::TypingLiteralString);
    set_typing_inference(t, "NamedTuple", Specific::TypingNamedTuple);
    set_typing_inference(t, "Unpack", Specific::TypingUnpack);
    set_typing_inference(t, "reveal_type", Specific::RevealTypeFunction);
    set_typing_inference(t, "assert_type", Specific::AssertTypeFunction);
    set_typing_inference(t, "NotRequired", Specific::TypingNotRequired);
    set_typing_inference(t, "Required", Specific::TypingRequired);
    set_typing_inference(t, "dataclass_transform", Specific::TypingDataclassTransform);

    for module in [typing, mypy_extensions, typing_extensions] {
        set_typing_inference(module, "TypedDict", Specific::TypingTypedDict);
    }
    set_typing_inference(mypy_extensions, "NoReturn", Specific::TypingNeverOrNoReturn);
    set_typing_inference(
        mypy_extensions,
        "FlexibleAlias",
        Specific::MypyExtensionsFlexibleAlias,
    );
}

fn set_typing_inference(file: &PythonFile, name: &str, specific: Specific) {
    if let Some(node_index) = file.symbol_table.lookup_symbol(name) {
        let name_def = Name::by_index(&file.tree, node_index).name_def().unwrap();
        if name_def.maybe_import().is_some() {
            // No need to set it, because it's an import and will point probably from
            // typing_extensions to typing.
            return;
        }
        let index = if name_def.maybe_name_of_func().is_some() {
            name_def.index()
        } else {
            node_index
        };
        file.points
            .set(index, Point::new_specific(specific, Locality::File));
    }
}

fn set_custom_behavior(file: &PythonFile, name: &str, custom: CustomBehavior) {
    let node_index = file.symbol_table.lookup_symbol(name).unwrap();
    NodeRef::new(file, node_index).insert_type(Type::CustomBehavior(custom));
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
    NodeRef::new(file, node_index).insert_type(Type::CustomBehavior(custom));
}
*/

fn setup_type_alias(typing: &PythonFile, name: &str, target_file: &PythonFile, target_name: &str) {
    let node_index = typing.symbol_table.lookup_symbol(name).unwrap();
    debug_assert_eq!(
        typing.points.get(node_index).specific(),
        Specific::FirstNameOfNameDef
    );
    debug_assert_eq!(typing.points.get(node_index).node_index(), node_index);
    let target_node_index = target_file.symbol_table.lookup_symbol(target_name).unwrap();
    typing.points.set(
        node_index, // Set it on name
        Point::new_redirect(target_file.file_index, target_node_index, Locality::File),
    );
}

fn set_mypy_extension_specific(file: &PythonFile, name: &str, specific: Specific) -> NodeIndex {
    let node_index = file.symbol_table.lookup_symbol(name).unwrap();
    let name_def_node_index = node_index - NAME_DEF_TO_NAME_DIFFERENCE;
    // Act on the name def index and not the name.
    file.points.set(
        name_def_node_index,
        Point::new_specific(specific, Locality::File),
    );
    let function_index = node_index - NAME_TO_FUNCTION_DIFF;
    debug_assert!(FunctionDef::maybe_by_index(&file.tree, function_index).is_some());
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

fn legacy_new_type(db: &Database) -> bool {
    db.project.settings.python_version_or_default() < PythonVersion::new(3, 10)
}
