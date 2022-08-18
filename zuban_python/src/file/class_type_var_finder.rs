use parsa_python_ast::*;

use super::type_computation::{SpecialType, TypeNameLookup};
use crate::database::{Locality, Point, TypeVarIndex, TypeVarManager, TypeVars};
use crate::file::{PythonFile, PythonInference};
use crate::file_state::File;
use crate::getitem::{SliceOrSimple, SliceType};
use crate::inferred::Inferred;
use crate::node_ref::NodeRef;

#[derive(Debug, Clone)]
enum BaseLookup<'db> {
    Module(&'db PythonFile),
    Class(Inferred<'db>),
    Protocol,
    Generic,
    Other,
}

pub struct ClassTypeVarFinder<'db, 'a, 'b, 'c> {
    inference: &'c mut PythonInference<'db, 'a, 'b>,
    type_var_manager: TypeVarManager,
    had_protocol_or_generic: bool,
}

impl<'db, 'a, 'b, 'c> ClassTypeVarFinder<'db, 'a, 'b, 'c> {
    pub fn new(inference: &'c mut PythonInference<'db, 'a, 'b>) -> Self {
        Self {
            inference,
            type_var_manager: TypeVarManager::default(),
            had_protocol_or_generic: false,
        }
    }

    pub fn find(mut self, node: ClassDef) -> TypeVars {
        if let Some(arguments) = node.arguments() {
            for argument in arguments.iter() {
                match argument {
                    Argument::Positional(n) => {
                        self.find_in_expr(n.expression());
                    }
                    Argument::Keyword(_, _) => (), // Ignore for now -> part of meta class
                    Argument::Starred(_) | Argument::DoubleStarred(_) => (), // Nobody probably cares about this
                }
            }
        }
        self.type_var_manager.into_type_vars()
    }

    fn find_in_expr(&mut self, expr: Expression) {
        let type_content = match expr.unpack() {
            ExpressionContent::ExpressionPart(n) => {
                self.find_in_expression_part(n);
            }
            ExpressionContent::Lambda(_) => todo!(),
            ExpressionContent::Ternary(t) => todo!(),
        };
    }

    fn find_in_expression_part(&mut self, node: ExpressionPart) -> BaseLookup<'db> {
        match node {
            ExpressionPart::Atom(atom) => self.find_in_atom(atom),
            ExpressionPart::Primary(primary) => self.find_in_primary(primary),
            ExpressionPart::BitwiseOr(bitwise_or) => {
                let (a, b) = bitwise_or.unpack();
                self.find_in_expression_part(a);
                self.find_in_expression_part(b);
                BaseLookup::Other
            }
            _ => BaseLookup::Other,
        }
    }

    fn find_in_primary(&mut self, primary: Primary) -> BaseLookup<'db> {
        let base = self.find_in_primary_or_atom(primary.first());
        match primary.second() {
            PrimaryContent::Attribute(name) => {
                match base {
                    BaseLookup::Module(f) => {
                        // TODO this is a bit weird. shouldn't this just do a goto?
                        if let Some(index) = f.symbol_table.lookup_symbol(name.as_str()) {
                            self.inference.file.points.set(
                                name.index(),
                                Point::new_redirect(f.file_index(), index, Locality::Todo),
                            );
                            self.find_in_name(name)
                        } else {
                            BaseLookup::Other
                        }
                    }
                    BaseLookup::Class(i) => {
                        let cls = i.maybe_class(self.inference.i_s).unwrap();
                        let node_ref = NodeRef::new(self.inference.file, primary.index());
                        if let Some(index) = cls
                            .class_storage
                            .class_symbol_table
                            .lookup_symbol(name.as_str())
                        {
                            todo!();
                            self.inference.file.points.set(
                                name.index(),
                                Point::new_redirect(
                                    cls.node_ref.file.file_index(),
                                    index,
                                    Locality::Todo,
                                ),
                            );
                            self.find_in_name(name)
                        } else {
                            BaseLookup::Other
                        }
                    }
                    _ => BaseLookup::Other,
                }
            }
            PrimaryContent::Execution(details) => BaseLookup::Other,
            PrimaryContent::GetItem(slice_type) => {
                let s = SliceType::new(self.inference.file, primary.index(), slice_type);
                match base {
                    /*
                    BaseLookup::Protocol | BaseLookup::Generic => {
                        todo!()
                    }*/
                    _ => {
                        for slice_or_simple in s.iter() {
                            if let SliceOrSimple::Simple(s) = slice_or_simple {
                                self.find_in_expr(s.named_expr.expression())
                            }
                        }
                        BaseLookup::Other
                    }
                }
            }
        }
    }

    fn find_in_atom(&mut self, atom: Atom) -> BaseLookup<'db> {
        match atom.unpack() {
            AtomContent::Name(n) => {
                self.inference.infer_name_reference(n);
                self.find_in_name(n)
            }
            AtomContent::Strings(s_o_b) => match s_o_b.as_python_string() {
                Some(PythonString::Ref(start, s)) => {
                    todo!()
                    //self.compute_forward_reference(start, s.to_owned())
                }
                Some(PythonString::String(start, s)) => todo!(),
                Some(PythonString::FString) => todo!(),
                None => todo!(),
            },
            _ => BaseLookup::Other,
        }
    }

    fn find_in_name(&mut self, name: Name) -> BaseLookup<'db> {
        match self.inference.lookup_type_name(name) {
            TypeNameLookup::Module(f) => BaseLookup::Module(f),
            TypeNameLookup::Class(i) => BaseLookup::Class(i),
            TypeNameLookup::TypeVar(type_var) => {
                self.type_var_manager.add(type_var.clone(), None);
                BaseLookup::Other
            }
            TypeNameLookup::SpecialType(SpecialType::Generic) => BaseLookup::Generic,
            TypeNameLookup::SpecialType(SpecialType::Protocol) => BaseLookup::Protocol,
            _ => BaseLookup::Other,
        }
    }

    fn find_in_primary_or_atom(&mut self, p: PrimaryOrAtom) -> BaseLookup<'db> {
        match p {
            PrimaryOrAtom::Primary(primary) => self.find_in_primary(primary),
            PrimaryOrAtom::Atom(atom) => self.find_in_atom(atom),
        }
    }
}
