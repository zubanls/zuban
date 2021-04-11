pub use std::mem;
pub use std::path::PathBuf;
pub use std::collections::HashMap;
pub use parsa_python::PythonTree;

type TreeIndex = u32;
type ModuleIndex = u32;
type ComplexIndex = u32;

// Most significant bits
// 27 bits = 134217728; 20 bits = 1048576
// 0xxxxx Reference
// 1xxxxx Value
// xYYYxx YYY = Locality
// -> x0xx Internal
// -> x1xx External
// -> 1xxxX unused
// -> 1xxx0 non nullable
// -> 1xxx1 nullable
// Rest 27 bits = ModuleIndex
// If Internal second field = Value
// If External second field = ModuleIndex

const IS_REFERENCE_MASK: u32 = 1 << 31;
const IS_DEFINITION_MASK: u32 = 1 << 30;
const LOCALITY_MASK: u32 = 0b111 << 27
const REST_MASK: u32 = LOCALITY_MASK | IS_REFERENCE_MASK | IS_DEFINITION_MASK;

struct InternalValueOrReference {
    flags: u32,
    tree_index: TreeIndex,
}

impl InternalValueOrReference {
    fn get_locality(self) -> Locality {
        mem::transmute(self.flags << 28 & 7)
    }

    fn is_uncalculated(self) -> bool {
         self.flags == 0
    }

    fn is_value(self) -> bool {
        self.flags & IS_REFERENCE_MASK != 0
    }

    fn get_x(self) -> ValueOrReference {
        if self.is_calculated() {
            ValueOrReference::Uncalculated
        }
        if self.is_value() {
            ValueOrReference::Value()
        } else {
            ValueOrReference::Reference()
        }
    }
}

enum ValueOrReference {
    Value(Value),
    Reference(Reference),
    Uncalculated,
    Calculating,
    RecursionError,
}

enum Reference {
    LocalLink(TreeIndex),
    Link(ModuleIndex, TreeIndex),
    MultiReference(TreeIndex),
    Missing,
}

enum Value {
    Class(TreeIndex),
    Function(TreeIndex),  // Result
    NoReturnFunction(TreeIndex),
    String,
    Bytes,
    Float,
    Integer,
    Complex,
    Bool,
    None,

    Unknown,
    Param,  // Can be optional if param has default `foo=None`
    SelfParam,
    ParamWithDefault(TreeIndex),
    Any,
    SimpleGeneric, // primary: primary '[' slices ']'
    TypeVar(TreeIndex),

    LocalLink(TreeIndex),
    Link(ModuleIndex, TreeIndex),
    ComplexIndex(ComplexIndex),

    //Optional<Value>,
    // list literal/vs func; instance; closure
}

#[repr(u32)]
enum Locality {
    // Intern: 0xx
    Module,
    MostOuterClassOrFunction,
    ClassOrFunction,
    Stmt,

    // Extern: 1xx
    IndirectExtern,
    CheckModuleExtern,
    NeedsRecheckModuleExtern,
    DirectExtern,
}

struct InternalValue(u32, u32);

struct ValueLink {
    module: ModuleIndex,
    tree_index: TreeIndex,
}

enum ComplexValue {
    Union(Box<[ValueLink]>),
    Instance(Execution),
    Closure(ValueLink, Execution),
    Generic(Execution),
}

struct Execution {
    function: ValueLink,
    args: Box<[Value]>,
}

type InvalidatedDependencies = Vec<ModuleIndex>;
enum ModuleState<T> {
    DoesNotExist,
    Unparsed,
    Parsed(T),
    LocalReferencesCreated(T),
    InvalidatedDependencies(T, InvalidatedDependencies),
    FulllyInferred(T),
}

struct Module {
    path: PathBuf,
    state: ModuleState<Tree>,
    definition_names: HashMap<&str, TreeIndex>,
    reference_bloom_filter: BloomFilter<&str>,
    dependencies: Vec<ModuleIndex>,
    values_or_references: Vec<InternalValueOrReference>,
    complex_values: Vec<ComplexValue>,
    issues: Vec<Issue>,
}

struct Issue {
    issue_id: u32,
    tree_node: TreeIndex,
    locality: Locality,
}

