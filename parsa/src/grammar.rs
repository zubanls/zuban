use std::collections::{HashMap};
use std::marker::PhantomData;

use crate::{InternalTokenType, InternalNodeType, Rule, InternalStrToToken,
            InternalStrToNode, InternalNode, Token, CodeIndex};
use crate::automaton::{Automatons, RuleAutomaton, InternalSquashedType, Plan, 
                       DFAState, Keywords, node_type_to_squashed,
                       token_type_to_squashed, generate_automatons}; 
use std::fmt::Debug;
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
    pub fn new(rules: &HashMap<InternalNodeType, Rule>,
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
                    token_type_to_squashed(token.get_type()),
                );
            } else {
                transition = token_type_to_squashed(token.get_type());
            }

            loop {
                let tos = stack.get_tos();
                match tos.dfa_state.transition_to_plan.get(&transition) {
                    None => {
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

        loop {
            let tos = stack.get_tos();
            if !tos.dfa_state.is_final {
                // We never broke out -- EOF is too soon -- Unfinished statement.
                // However, the error recovery might have added the token again, if
                // the stack is empty, we're fine.
                panic!("incomplete input {:?}", tos.dfa_state)
            }

            if stack.len() > 1 {
                stack.pop()
            } else {
                panic!();
            }
        }
    }
}

impl<'a, T: Token> Stack<'a, T> {
    fn new(node_id: InternalNodeType, dfa_state: &'a DFAState) -> Self {
        let mut stack = Stack {
            stack_nodes: Default::default(),
            tree_nodes: Default::default(),
            phantom: PhantomData,
        };
        stack.push(node_id, dfa_state, 0);
        stack
    }

    fn get_tos(&self) -> &StackNode{
        &self.stack_nodes.last().unwrap()
    }

    fn len(&self) -> usize {
        self.stack_nodes.len()
    }

    fn pop(&mut self) {
        self.stack_nodes.pop();
    }

    fn apply_plan(&mut self, automatons: &'a Automatons, plan: &Plan, token: &T) {
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
            dfa_state: dfa_state,
            backtrack_length_counts: Vec::new()
        });
        self.tree_nodes.push(InternalNode {
            next_node_offset: 0,
            // Positive values are token types, negative values are nodes
            type_: node_type_to_squashed(node_id),
            start_index: start,
            length: 0,
            extra_data: 0,
        });
    }
}
