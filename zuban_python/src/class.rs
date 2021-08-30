// TODO work on this
enum OperatorType {
    // See also https://docs.python.org/3/reference/datamodel.html
    // Type conversions like __int__, __float__ are handled with protocols
    // and not here (see e.g. SupportsInt in typeshed).
    Add(),            // __add__
    Substract(),      // __sub__
    Multiply(),       // __mul__
    MatrixMultiply(), // __matmul__
    TrueDivision(),   // __truediv__
    FloorDivision(),  // __floordiv__
    Modulo(),         // __module__
    Divmod(),         // __divmod__
    Power(),          // __pow__
    LeftShift(),      // __lshift__
    RightShift(),     // __rshift__
    And(),            // __and__
    Xor(),            // __xor__
    Or(),             // __or__

    // TODO all of them with reverse like: __radd__
    // TODO all of them except __divmod__ with in place like +=: __iadd__
    Negate(ValueLink),     // __neg__
    SimplePlus(ValueLink), // __pos__
    Invert(ValueLink),     // __invert__
    Call(ValueLink),       // __call__

                           // TODO
                           // __package__; __file__;
                           // __doc__; __name__; __qualname__; __module__; __defaults__; __code__;
                           // __globals__; __closure__; __annotations__; __kwdefaults__;
                           // __init__; __new__; __dict__; __class__; __slots__; __weakref__; __self__; __bases__;
                           // __init_subclass__; __mro_entries__; __prepare__;
                           // __instancecheck__; __subclasscheck__; (on type)
                           // __del__
                           // __class_getitem__
                           // __get__; __set__; __delete__; __set_name__
                           // __getitem__; __setitem__; __delitem__; __missing__;
                           // __enter__; __exit__;
                           // __await__; __aiter__; __anext__; __aenter__; __aexit__;
                           // coroutine.send; coroutine.throw; coroutine.close
                           // Expected to match object implementation
                           // __repr__; __str__; __bytes__; __format__;
                           // __contains__; __reversed__; __len__; __length_hint__; __iter__
                           // __complex__; __int__; __float__; __index__;
                           // __round__; __trunc__; __floor__; __ceil__;
                           // __lt__; __le__; __eq__; __ne__; __gt__; __gt__; __hash__; __bool__;
                           // __getattr__; __getattribute__; __setattr__; __delattr__; __dir__;
}

struct Operator {
    locality: Locality,
    type_: OperatorType,
}

struct TreeClass {
    mro: Optional<ValueLink>,
    operators: Optional<Vec<Operator>>,
}

impl TreeClass {
    fn new(tree_link: ValueLink) -> Self {
        Self { tree_link }
    }

    fn lookup(&self) {}
}

struct ActualClass {
    class: Class,
    tree_link: ValueLink,
}
