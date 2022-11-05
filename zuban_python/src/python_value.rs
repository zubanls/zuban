/*
fn get_position(&self) -> Option<TreeNode> {
}

fn get_array_type() -> ArrayType {
}

fn py__getitem__(&self, index_value_set, contextualized_node) {
    from jedi.inference import analysis
    # TODO this value is probably not right.
    analysis.add(
        contextualized_node.context,
        'type-error-not-subscriptable',
        contextualized_node.node,
        message="TypeError: '%s' object is not subscriptable" % self
    )
    return NO_VALUES
}

fn py__simple_getitem__(&self, index) -> Option<Values> {
    //raise SimpleGetItemNotFound
    None
}

fn py__iter__(&self, contextualized_node=None) {
    if contextualized_node is not None:
        from jedi.inference import analysis
        analysis.add(
            contextualized_node.context,
            'type-error-not-iterable',
            contextualized_node.node,
            message="TypeError: '%s' object is not iterable" % self)
    return iter([])
}

fn py__next__(&self, contextualized_node=None) {
    return self.py__iter__(contextualized_node)
}

def get_signatures(&self):
    return []

def is_class(&self):
    return False

def is_class_mixin(&self):
    return False

def is_instance(&self):
    return False

def is_function(&self):
    return False

def is_module(&self):
    return False

def is_namespace(&self):
    return False

def is_compiled(&self):
    return False

def is_bound_method(&self):
    return False

def is_builtins_module(&self):
    return False

def py__bool__(&self):
    """
    Since Wrapper is a super class for classes, functions and modules,
    the return value will always be true.
    """
    return True

def py__doc__(&self):
    try:
        self.tree_node.get_doc_node
    except AttributeError:
        return ''
    else:
        return clean_scope_docstring(self.tree_node)

def get_safe_value(&self, default=sentinel):
    if default is sentinel:
        raise ValueError("There exists no safe value for value %s" % self)
    return default

def execute_operation(&self, other, operator):
    debug.warning("%s not possible between %s and %s", operator, self, other)
    return NO_VALUES

def py__call__(&self, arguments):
    debug.warning("no execution possible %s", self)
    return NO_VALUES

def py__stop_iteration_returns(&self):
    debug.warning("Not possible to return the stop iterations of %s", self)
    return NO_VALUES

def py__getattribute__alternatives(&self, name_or_str):
    """
    For now a way to add values in cases like __getattr__.
    """
    return NO_VALUES

def py__get__(&self, instance, class_value):
    debug.warning("No __get__ defined on %s", self)
    return ValueSet([self])

def py__get__on_class(&self, calling_instance, instance, class_value):
    return NotImplemented

def get_qualified_names(&self):
    # Returns Optional[Tuple[str, ...]]
    return None

def is_stub(&self):
    # The root value knows if it's a stub or not.
    return self.parent_context.is_stub()

def _as_context(&self):
    raise NotImplementedError('Not all values need to be converted to contexts: %s', self)

@property
def name(&self):
    raise NotImplementedError

fn type__hint(&self, add_class_info=True) {
    return None
}

fn infer_type_vars(&self, value_set) {
    """
    When the current instance represents a type annotation, this method
    tries to find information about undefined type vars and returns a dict
    from type var name to value set.

    This is for example important to understand what `iter([1])` returns.
    According to typeshed, `iter` returns an `Iterator[_T]`:

        def iter(iterable: Iterable[_T]) -> Iterator[_T]: ...

    This functions would generate `int` for `_T` in this case, because it
    unpacks the `Iterable`.

    Parameters
    ----------

    `self`: represents the annotation of the current parameter to infer the
        value for. In the above example, this would initially be the
        `Iterable[_T]` of the `iterable` parameter and then, when recursing,
        just the `_T` generic parameter.

    `value_set`: represents the actual argument passed to the parameter
        we're inferrined for, or (for recursive calls) their types. In the
        above example this would first be the representation of the list
        `[1]` and then, when recursing, just of `1`.
    """
    return {}
}
*/
