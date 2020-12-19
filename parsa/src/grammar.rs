use std::collections::{HashMap};
use std::marker::PhantomData;

use crate::automaton::{Automatons, RuleAutomaton, InternalSquashedType, Plan, 
                       DFAState, Keywords, generate_automatons, Rule, RuleMap,
                       InternalStrToToken, InternalStrToNode,
                       InternalTokenType, InternalNodeType};
use std::fmt::Debug;

pub type ExtraData = u32;
pub type NodeIndex = u32;
pub type CodeIndex = u32;
pub type CodeLength = u32;

pub trait Token {
    fn get_start_index(&self) -> u32;
    fn get_length(&self) -> u32;
    fn get_type(&self) -> InternalTokenType;
    fn can_contain_syntax(&self) -> bool;
}

pub trait Tokenizer<'a, T: Token>: Iterator {
    fn new(code: &'a str) -> Self;
}

#[derive(Debug)]
pub struct InternalTree {
    pub code: Vec<u8>,
    pub nodes: Vec<InternalNode>,
    pub lines: Option<Vec<u32>>,
}

#[derive(Copy, Clone, Debug)]
pub struct InternalNode {
    pub next_node_offset: NodeIndex,
    // Positive values are token types, negative values are nodes
    pub type_: InternalSquashedType,

    pub start_index: CodeIndex,
    pub length: CodeLength,
    pub extra_data: ExtraData,
}

// This node is currently not used and just here for future optimization purposes.
struct CompressedNode {
    next_node_offset: u8,
    // Positive values are token types, negative values are nodes
    type_: i8,

    start_index: u16,
    length: u16,
    extra_data1: u16,
    extra_data2: u16,
}

#[cfg(test)]
mod tests {
    use std::mem::{size_of, align_of};
    use super::*;

    #[test]
    fn sizes() {
        assert_eq!(size_of::<InternalNode>(), 20);
        assert_eq!(size_of::<CompressedNode>(), 10);
        assert_eq!(align_of::<InternalNode>(), 4);
        assert_eq!(align_of::<CompressedNode>(), 2);
    }
}

#[derive(Debug)]
pub struct Grammar<T> {
    terminal_map: &'static InternalStrToToken,
    nonterminal_map: &'static InternalStrToNode,
    phantom: PhantomData<T>,
    automatons: Automatons,
    keywords: Keywords,
}

#[derive(Debug)]
struct StackNode<'a> {
    node_id: InternalNodeType,
    tree_node_index: usize,
    latest_child_node_index: usize,
    dfa_state: &'a DFAState,
    backtrack_length_counts: Vec<u32>,
}

#[derive(Debug, Default)]
struct Stack<'a, T: Token> {
    stack_nodes: Vec<StackNode<'a>>,
    tree_nodes: Vec<InternalNode>,
    phantom: PhantomData<T>,
}

impl<'a, T: Token+Debug> Grammar<T> {
    pub fn new(rules: &RuleMap,
               nonterminal_map: &'static InternalStrToNode, 
               terminal_map: &'static InternalStrToToken) -> Self {
        let (automatons, keywords) = generate_automatons(nonterminal_map, terminal_map, rules);
        let mut grammar = Self {
            terminal_map: terminal_map,
            nonterminal_map: nonterminal_map,
            phantom: PhantomData,
            automatons: automatons,
            keywords: keywords,
        };

        // Since we now know every nonterminal has a first terminal, we know that there is no
        // left recursion.
        grammar
    }

    pub fn parse(&self, code: &str, tokens: impl Iterator<Item=T>, start: InternalNodeType) -> Vec<InternalNode> {
        let mut stack = Stack::new(
            start,
            &self.automatons[&start].dfa_states[0]
        );

        for token in tokens {
            let transition;
            if token.can_contain_syntax() {
                let start = token.get_start_index() as usize;
                let token_str = &code[start..start + token.get_length() as usize];
                transition = self.keywords.get_squashed(token_str).unwrap_or(
                    token.get_type().to_squashed(),
                );
            } else {
                transition = token.get_type().to_squashed();
            }

            //dbg!(&token);
            loop {
                let tos = stack.get_tos();
                match tos.dfa_state.transition_to_plan.get(&transition) {
                    None => {
                        //dbg!(stack.get_tos().dfa_state.from_rule);
                        //dbg!(stack.get_tos().dfa_state.transition_to_plan.values()
                        //     .map(|x| x.debug_text).collect::<Vec<_>>());
                        if tos.dfa_state.is_final {
                            stack.pop()
                        } else {
                            panic!("Error recovery");
                        }
                    },
                    Some(plan) => {
                        let cloned_plan = plan.clone();
                        stack.apply_plan(&self.automatons, &cloned_plan, &token);
                        break
                    },
                }
            }
        }

        while stack.len() > 0 {
            let tos = stack.get_tos();
            if tos.dfa_state.is_final {
                stack.pop()
                // We never broke out -- EOF is too soon -- Unfinished statement.
                // However, the error recovery might have added the token again, if
                // the stack is empty, we're fine.
            } else {
                panic!("incomplete input {:?}", tos.dfa_state)
            }
        }
        stack.tree_nodes
    }
}

impl<'a, T: Token+Debug> Stack<'a, T> {
    fn new(node_id: InternalNodeType, dfa_state: &'a DFAState) -> Self {
        let mut stack = Stack {
            stack_nodes: Default::default(),
            tree_nodes: Default::default(),
            phantom: PhantomData,
        };
        stack.push(node_id, dfa_state, 0);
        stack
    }

    #[inline]
    fn get_tos(&self) -> &StackNode{
        self.stack_nodes.last().unwrap()
    }

    #[inline]
    fn len(&self) -> usize {
        self.stack_nodes.len()
    }

    #[inline]
    fn pop(&mut self) {
        let stack_node = self.stack_nodes.pop().unwrap();
        let last_tree_node = *self.tree_nodes.last().unwrap();
        // We can simply get the last token and check its end position to
        // calculate how long a token is.
        let mut n = self.tree_nodes.get_mut(stack_node.tree_node_index).unwrap();
        n.length = last_tree_node.start_index - n.start_index + last_tree_node.length;
    }

    #[inline]
    fn apply_plan(&mut self, automatons: &'a Automatons, plan: &Plan, token: &T) {
        self.calculate_previous_next_node();
        let start_index = token.get_start_index();
        let tos = self.get_tos();


        let next = &automatons[&tos.node_id].dfa_states[plan.next_dfa_state.0];
        self.stack_nodes.last_mut().unwrap().dfa_state = next;
        for (node_type, push) in &plan.pushes {
            self.push(
                *node_type,
                &automatons[&node_type].dfa_states[push.0],
                start_index,
            );
            self.stack_nodes.last_mut().unwrap().latest_child_node_index = self.tree_nodes.len();
        }
        // Once all the nodes are dealt with, add the token
        self.tree_nodes.push(InternalNode {
            next_node_offset: 0,
            // Positive values are token types, negative values are nodes
            type_: plan.type_,
            start_index: start_index,
            length: token.get_length(),
            extra_data: 0,
        });
    }

    #[inline]
    fn push(&mut self, node_id: InternalNodeType, dfa_state: &'a DFAState, start: CodeIndex) {
        self.stack_nodes.push(StackNode {
            node_id: node_id,
            tree_node_index: self.tree_nodes.len(),
            latest_child_node_index: 0,
            dfa_state: dfa_state,
            backtrack_length_counts: Vec::new()
        });
        self.tree_nodes.push(InternalNode {
            next_node_offset: 0,
            type_: node_id.to_squashed(),
            start_index: start,
            length: 0,
            extra_data: 0,
        });
    }

    #[inline]
    fn calculate_previous_next_node(&mut self) {
        // Care for next_node_offset here.
        let index = self.get_tos().latest_child_node_index;
        let next = self.tree_nodes.len();

        // The first node does not need to be updated.
        if index != 0 {
            self.tree_nodes[index].next_node_offset = (next - index) as u32;
        }
        self.stack_nodes.last_mut().unwrap().latest_child_node_index = next;
    }
}

impl StackNode<'_> {
    fn get_terminal_name(&self, nonterminal_map: &InternalStrToNode) -> &str {
        for (label, &id) in nonterminal_map {
            if id == self.node_id {
                return label
            }
        }
        unreachable!();
    }
}
