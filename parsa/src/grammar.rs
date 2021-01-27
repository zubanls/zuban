use std::collections::{HashMap};
use std::marker::PhantomData;

use crate::automaton::{Automatons, RuleAutomaton, InternalSquashedType, Plan,
                       DFAState, Keywords, generate_automatons, Rule, RuleMap,
                       InternalStrToToken, InternalStrToNode, StackMode,
                       InternalTokenType, InternalNodeType};
use std::fmt::Debug;

pub type ExtraData = u32;
pub type NodeIndex = u32;
pub type CodeIndex = u32;
pub type CodeLength = u32;

pub trait Token: Copy+Debug {
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

#[derive(Debug, Clone, Copy)]
enum ModeData<'a> {
    Alternative(BacktrackingPoint<'a>),
    NegativeLookahead(usize),
    PositiveLookahead(usize),
    Normal,
}

#[derive(Debug, Clone, Copy)]
struct BacktrackingPoint<'a> {
    tree_node_count: usize,
    token_index: usize,
    fallback: &'a DFAState,
}

#[derive(Debug)]
struct StackNode<'a> {
    node_id: InternalNodeType,
    tree_node_index: usize,
    latest_child_node_index: usize,
    dfa_state: &'a DFAState,
    children_count: usize,

    mode: ModeData<'a>,
    enabled_token_recording: bool,
    add_tree_nodes: bool,
}

struct Stack<'a, T: Token, I> {
    stack_nodes: Vec<StackNode<'a>>,
    tree_nodes: Vec<InternalNode>,
    phantom: PhantomData<T>,
    phantom2: PhantomData<I>,
}

#[derive(Debug)]
struct BacktrackingTokenizer<T: Token, I: Iterator<Item=T>> {
    tokenizer: I,
    tokens: Vec<T>,
    next_index: usize,
}

impl<'a, T: Token> Grammar<T> {
    pub fn new(rules: &RuleMap,
               nonterminal_map: &'static InternalStrToNode,
               terminal_map: &'static InternalStrToToken) -> Self {
        let (automatons, keywords) = generate_automatons(nonterminal_map, terminal_map, rules);
        // Since we now know every nonterminal has a first terminal, we know that there is no
        // left recursion.
        let mut grammar = Self {
            terminal_map: terminal_map,
            nonterminal_map: nonterminal_map,
            phantom: PhantomData,
            automatons: automatons,
            keywords: keywords,
        };

        grammar
    }

    pub fn parse(&self, code: &str, tokens: impl Iterator<Item=T>, start: InternalNodeType) -> Vec<InternalNode> {
        let mut stack = Stack::new(
            start,
            &self.automatons[&start].dfa_states[0]
        );
        let mut backtracking_tokenizer = BacktrackingTokenizer::new(tokens);

        while let Some(token) = backtracking_tokenizer.next() {
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
            stack.apply_transition(&self.automatons, &mut backtracking_tokenizer, transition, &token);
        }

        while stack.len() > 0 {
            let tos = stack.get_tos();
            let is_final = tos.dfa_state.is_final;
            let mode = tos.mode;
            stack.end_of_node(&mut backtracking_tokenizer, is_final, mode);
        }
        stack.tree_nodes
    }
}

impl<'a, T: Token+Debug, I: Iterator<Item=T>> Stack<'a, T, I> {
    fn new(node_id: InternalNodeType, dfa_state: &'a DFAState) -> Self {
        let mut stack = Stack {
            stack_nodes: vec!(),
            tree_nodes: vec!(),
            phantom: PhantomData,
            phantom2: PhantomData,
        };
        stack.push(node_id, dfa_state, 0, ModeData::Normal, false, true);
        stack
    }

    #[inline]
    fn get_tos(&self) -> &StackNode<'a> {
        self.stack_nodes.last().unwrap()
    }

    #[inline]
    fn len(&self) -> usize {
        self.stack_nodes.len()
    }

    #[inline]
    fn apply_transition(
            &mut self, automatons: &'a Automatons,
            backtracking_tokenizer: &mut BacktrackingTokenizer<T, I>,
            transition: InternalSquashedType, token: &T) {
        loop {
            let tos = self.get_tos();
                    let is_final = tos.dfa_state.is_final;
                    let mode = tos.mode;
            match tos.dfa_state.transition_to_plan.get(&transition) {
                None => {
                    //dbg!(stack.get_tos().dfa_state.from_rule);
                    //dbg!(stack.get_tos().dfa_state.transition_to_plan.values()
                    //     .map(|x| x.debug_text).collect::<Vec<_>>());
                    self.end_of_node(backtracking_tokenizer, is_final, mode);
                },
                Some(plan) => {
                    let cloned_plan = plan.clone();
                    self.apply_plan(automatons, &cloned_plan,
                                    &token, backtracking_tokenizer);
                    break
                },
            }
        }
    }

    #[inline]
    fn end_of_node(&mut self, backtracking_tokenizer: &mut BacktrackingTokenizer<T, I>,
                   is_final: bool, mode: ModeData<'a>) {
        if is_final {
            match mode {
                ModeData::Normal => {
                    self.pop_normal();
                },
                ModeData::PositiveLookahead(token_index) => {
                    self.stack_nodes.pop();
                    backtracking_tokenizer.reset(token_index);
                },
                ModeData::NegativeLookahead(token_index) => {
                    backtracking_tokenizer.reset(token_index);
                    unimplemented!();
                },
                ModeData::Alternative(backtracking_point) => {
                    let old_tos = self.stack_nodes.pop().unwrap();
                    let tos = self.stack_nodes.last_mut().unwrap();
                    tos.children_count = old_tos.children_count;
                    tos.latest_child_node_index = old_tos.latest_child_node_index;
                }
            }
        } else {
            for (i, node) in self.stack_nodes.iter().enumerate().rev() {
                match node.mode {
                    ModeData::NegativeLookahead(token_index) => {
                        self.stack_nodes.truncate(i);
                        backtracking_tokenizer.reset(token_index);
                        return
                    },
                    ModeData::Alternative(backtracking_point) => {
                        self.stack_nodes.truncate(i);

                        self.tree_nodes.truncate(backtracking_point.tree_node_count);
                        let tos = self.stack_nodes.last_mut().unwrap();
                        tos.dfa_state = backtracking_point.fallback;
                        backtracking_tokenizer.reset(backtracking_point.token_index);
                        panic!("YAY");
                        return
                    },
                    _ => {}
                }
            }
            //let rest = &code[token.get_start_index() as usize..];
            //dbg!(token, rest);
            dbg!(self.stack_nodes.iter().map(
                 |n| n.dfa_state.from_rule).collect::<Vec<_>>());
            panic!("Error recovery");
        }
    }

    #[inline]
    fn pop_normal(&mut self) {
        let stack_node = self.stack_nodes.pop().unwrap();
        let last_tree_node = *self.tree_nodes.last().unwrap();

        if stack_node.dfa_state.node_may_be_omitted && stack_node.children_count == 1 {
            self.tree_nodes.remove(stack_node.tree_node_index);
        } else {
            // We can simply get the last token and check its end position to
            // calculate how long a node is.
            debug_assert!(stack_node.children_count >= 1);
            let mut n = self.tree_nodes.get_mut(stack_node.tree_node_index).unwrap();
            n.length = last_tree_node.start_index - n.start_index + last_tree_node.length;
        }
    }

    #[inline]
    fn apply_plan(&mut self, automatons: &'a Automatons, plan: &Plan, token: &T,
                  backtracking_tokenizer: &mut BacktrackingTokenizer<T, I>) {
        let tos_mut = self.stack_nodes.last_mut().unwrap();
        tos_mut.dfa_state = &automatons[&tos_mut.node_id].dfa_states[plan.next_dfa_state.0];
        let mut enabled_token_recording = tos_mut.enabled_token_recording;
        let mut add_tree_nodes = tos_mut.add_tree_nodes;

        if add_tree_nodes {
            self.calculate_previous_next_node();
        }

        let start_index = token.get_start_index();
        for push in &plan.pushes {
            // Lookaheads need to be accounted for.
            let tos = self.stack_nodes.last_mut().unwrap();
            tos.children_count += 1;
            //dbg!(&automatons[&push.node_type].dfa_states[push.to_state.0]);
            enabled_token_recording |= push.stack_mode != StackMode::Normal;
            add_tree_nodes &= match push.stack_mode {
                StackMode::Normal | StackMode::Alternative(_) => true,
                _ => false,
            };
            self.push(
                push.node_type,
                &automatons[&push.node_type].dfa_states[push.to_state.0],
                start_index,
                match push.stack_mode {
                    StackMode::Normal => ModeData::Normal,
                    StackMode::PositiveLookahead => ModeData::PositiveLookahead(
                        backtracking_tokenizer.start(token)
                    ),
                    StackMode::NegativeLookahead => ModeData::NegativeLookahead(
                        backtracking_tokenizer.start(token)
                    ),
                    StackMode::Alternative(dfa_state_id) => ModeData::Alternative(
                        BacktrackingPoint {
                            tree_node_count: self.tree_nodes.len(),
                            token_index: backtracking_tokenizer.start(token),
                            fallback: &automatons[&push.node_type].dfa_states[dfa_state_id.0],
                        }
                    ),
                },
                enabled_token_recording,
                add_tree_nodes,
            );
            if add_tree_nodes {
                let tos_mut = self.stack_nodes.last_mut().unwrap();
                tos_mut.latest_child_node_index = self.tree_nodes.len();
            }
        }
        if add_tree_nodes {
            // Once all the nodes are dealt with, add the token
            self.stack_nodes.last_mut().unwrap().children_count += 1;
            self.tree_nodes.push(InternalNode {
                next_node_offset: 0,
                // Positive values are token types, negative values are nodes
                type_: plan.type_,
                start_index: start_index,
                length: token.get_length(),
                extra_data: 0,
            });
        }
    }

    #[inline]
    fn push(&mut self, node_id: InternalNodeType, dfa_state: &'a DFAState, start: CodeIndex,
            mode: ModeData<'a>, enabled_token_recording: bool, add_tree_nodes: bool) {
        self.stack_nodes.push(StackNode {
            node_id: node_id,
            tree_node_index: self.tree_nodes.len(),
            latest_child_node_index: 0,
            dfa_state: dfa_state,
            children_count: 0,
            mode: mode,
            enabled_token_recording: enabled_token_recording,
            add_tree_nodes: add_tree_nodes,
        });
        if add_tree_nodes {
            self.tree_nodes.push(InternalNode {
                next_node_offset: 0,
                type_: node_id.to_squashed(),
                start_index: start,
                length: 0,
                extra_data: 0,
            });
        }
    }

    #[inline]
    fn calculate_previous_next_node(&mut self) {
        let tos = self.stack_nodes.last_mut().unwrap();
        // Care for next_node_offset here.
        let index = tos.latest_child_node_index;
        let next = self.tree_nodes.len();

        // The first node does not need to be updated.
        if index != 0 {
            self.tree_nodes[index].next_node_offset = (next - index) as u32;
        }
        tos.latest_child_node_index = next;
    }
}

impl<T: Token, I: Iterator<Item=T>> BacktrackingTokenizer<T, I> {
    fn new(tokenizer: I) -> Self {
        Self {
            tokenizer: tokenizer,
            tokens: vec!(),
            next_index: 0,
        }
    }

    #[inline]
    fn start(&mut self, token: &T) -> usize {
        if self.tokens.len() == 0 {
            self.tokens.push(*token);
            1
        } else {
            self.next_index
        }
    }

    #[inline]
    fn reset(&mut self, token_index: usize) {
        self.next_index = token_index;
    }

    #[inline]
    fn stop(&mut self) {
        self.tokens.clear();
        self.next_index = 0;
    }
}

impl<T: Token, I: Iterator<Item=T>> Iterator for BacktrackingTokenizer<T, I> {
    type Item = T;
    fn next(&mut self) -> Option<Self::Item> {
        if self.tokens.len() > 0 {
            match self.tokens.get(self.next_index) {
                None => {
                    self.next_index += 1;
                    if let Some(next) = self.tokenizer.next() {
                        self.tokens.push(next);
                        Some(next)
                    } else {
                        None
                    }
                },
                Some(next) => {
                    self.next_index += 1;
                    Some(*next)
                }
            }
        } else {
            self.tokenizer.next()
        }
    }
}
