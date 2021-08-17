mod class;
mod function;
mod instance;

pub use class::Class;
pub use function::Function;
pub use instance::Instance;
use crate::file::Inferred;
use crate::database::Database;

enum ArrayType {
    None,
    Tuple,
    List,
    Dict,
    Set,
}

#[derive(Eq, PartialEq)]
pub enum ValueKind {
    Unknown = 0,
    // Taken from LSP, unused kinds are commented
	//File = 1,
	Module = 2,
	Namespace = 3,
	//Package = 4,
	Class = 5,
	Method = 6,
	Property = 7,
	Field = 8,
	//Constructor = 9,
	//Enum = 10,
	//Interface = 11,
	Function = 12,
	//Variable = 13,
	Constant = 14,
	String = 15,
	Number = 16,
	Boolean = 17,
	Array = 18,
	Object = 19,  // From JavaScript objects -> Basically an instance
	//Key = 20,
	Null = 21,
	//EnumMember = 22,
	//Struct = 23,
	//Event = 24,
	//Operator = 25,
	TypeParameter = 26,
}


pub trait Value<'a>: std::fmt::Debug {
    fn get_kind(&self) -> ValueKind;

    //fn get_file(&self) -> &'a dyn File;

    fn get_name(&self) -> &'a str;

    fn lookup(&self, database: &'a Database, name: &str) -> Inferred<'a>;
    fn execute(&self, database: &'a Database) -> Inferred<'a>;
}
