use std::{cell::UnsafeCell, fmt, marker::PhantomData};

use crate::{
    automaton::{
        generate_automatons, Automatons, DFAState, FastHashMap, InternalNonterminalType,
        InternalSquashedType, InternalStrToNode, InternalStrToToken, InternalTerminalType,
        Keywords, Plan, PlanMode, Rule, RuleAutomaton, RuleMap, SoftKeywords, Squashable,
        StackMode,
    },
    backtracking::BacktrackingTokenizer,
};

pub type NodeIndex = u32;
pub type CodeIndex = u32;
pub type CodeLength = u32;

pub trait Token: Copy + fmt::Debug {
    fn start_index(&self) -> u32;
    fn length(&self) -> u32;
    fn type_(&self) -> InternalTerminalType;
    fn can_contain_syntax(&self) -> bool;
}

pub trait Tokenizer<'a, T: Token>: Iterator {
    fn new(code: &'a str) -> Self;
}

#[derive(Debug, Clone)]
pub struct InternalTree {
    pub code: Box<str>,
    pub nodes: Vec<InternalNode>,
}

#[derive(Copy, Clone, Debug)]
pub struct InternalNode {
    pub next_node_offset: NodeIndex,
    pub type_: InternalSquashedType,

    pub start_index: CodeIndex,
    pub length: CodeLength,
}

impl InternalNode {
    fn end_index(&self) -> u32 {
        self.start_index + self.length
    }
}

// This node is currently not used and just here for future optimization purposes.
struct CompressedNode {
    next_node_offset: u8,
    type_: i8,

    start_index: u16,
    length: u16,
}

#[cfg(test)]
mod tests {
    use std::mem::{align_of, size_of};

    use super::*;

    #[test]
    fn sizes() {
        assert_eq!(size_of::<InternalNode>(), 16);
        assert_eq!(size_of::<CompressedNode>(), 6);
        assert_eq!(align_of::<InternalNode>(), 4);
        assert_eq!(align_of::<CompressedNode>(), 2);
    }
}

impl InternalTree {
    pub fn new(code: Box<str>, nodes: Vec<InternalNode>) -> Self {
        Self { code, nodes }
    }
}

#[derive(Debug)]
pub struct Grammar<T> {
    terminal_map: &'static InternalStrToToken,
    nonterminal_map: &'static InternalStrToNode,
    phantom: PhantomData<T>,
    automatons: Automatons,
    keywords: Keywords,
    soft_keywords: SoftKeywords,
}

#[derive(Debug, Clone, Copy)]
enum ModeData<'a> {
    Alternative(BacktrackingPoint<'a>),
    LL,
}

#[derive(Debug, Clone, Copy)]
struct BacktrackingPoint<'a> {
    tree_node_count: usize,
    token_index: usize,
    fallback_plan: &'a Plan,
    children_count: usize,
}

struct StackNode<'a> {
    node_id: InternalNonterminalType,
    tree_node_index: usize,
    latest_child_node_index: usize,
    dfa_state: &'a DFAState,
    children_count: usize,

    mode: ModeData<'a>,
    enabled_token_recording: bool,
}

impl<'a> fmt::Debug for StackNode<'a> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        f.debug_struct("StackNode")
            .field("tree_node_index", &self.tree_node_index)
            .field("latest_child_node_index", &self.latest_child_node_index)
            .field(
                "dfa_state",
                &format!(
                    "{{name: {}, is_final: {}, node_may_be_omitted: {}}}",
                    self.dfa_state.from_rule,
                    self.dfa_state.is_final,
                    self.dfa_state.node_may_be_omitted,
                ),
            )
            .field("children_count", &self.children_count)
            .field("mode", &self.mode)
            .field("enabled_token_recording", &self.enabled_token_recording)
            .finish()
    }
}

struct Stack<'a> {
    stack_nodes: Vec<StackNode<'a>>,
    tree_nodes: Vec<InternalNode>,
}

impl<'a, T: Token> Grammar<T> {
    pub fn new(
        rules: &RuleMap,
        nonterminal_map: &'static InternalStrToNode,
        terminal_map: &'static InternalStrToToken,
        soft_keywords: SoftKeywords,
    ) -> Self {
        let (automatons, keywords) =
            generate_automatons(nonterminal_map, terminal_map, rules, &soft_keywords);
        // Since we now know every nonterminal has a first terminal, we know that there is no
        // left recursion.
        Self {
            terminal_map,
            nonterminal_map,
            phantom: PhantomData,
            automatons,
            keywords,
            soft_keywords,
        }
    }

    pub fn parse<I: Iterator<Item = T>>(
        &self,
        code: &str,
        tokens: I,
        start: InternalNonterminalType,
    ) -> Vec<InternalNode> {
        let mut stack = Stack::new(start, &self.automatons[&start].dfa_states[0], code.len());
        let mut backtracking_tokenizer = BacktrackingTokenizer::new(tokens);

        while stack.len() > 0 {
            while let Some(token) = backtracking_tokenizer.next() {
                let transition = if token.can_contain_syntax() {
                    let start = token.start_index() as usize;
                    let token_str = &code[start..start + token.length() as usize];
                    self.keywords
                        .squashed(token_str)
                        .unwrap_or_else(|| token.type_().to_squashed())
                } else {
                    token.type_().to_squashed()
                };
                self.apply_transition(&mut stack, &mut backtracking_tokenizer, transition, &token);
            }

            let tos = stack.tos();
            let mode = tos.mode;
            if tos.dfa_state.is_final {
                self.end_of_node(&mut stack, &mut backtracking_tokenizer, mode)
            } else {
                self.error_recovery(&mut stack, &mut backtracking_tokenizer, None, None);
            }
        }
        stack.tree_nodes
    }

    #[inline]
    fn apply_transition<I: Iterator<Item = T>>(
        &self,
        stack: &mut Stack,
        backtracking_tokenizer: &mut BacktrackingTokenizer<T, I>,
        transition: InternalSquashedType,
        token: &T,
    ) {
        loop {
            let tos = stack.tos();
            let is_final = tos.dfa_state.is_final;
            let mode = tos.mode;
            match tos.dfa_state.transition_to_plan.get(&transition) {
                None => {
                    //dbg!(stack.tos().dfa_state.from_rule);
                    //dbg!(stack.tos().dfa_state.transition_to_plan.values()
                    //     .map(|x| x.debug_text).collect::<Vec<_>>());
                    if is_final {
                        self.end_of_node(stack, backtracking_tokenizer, mode)
                    } else {
                        self.error_recovery(
                            stack,
                            backtracking_tokenizer,
                            Some(transition),
                            Some(token),
                        );
                        return;
                    }
                }
                Some(plan) => {
                    if plan.mode == PlanMode::PositivePeek {
                        let tos_mut = stack.tos_mut();
                        tos_mut.dfa_state = plan.next_dfa();
                    } else {
                        self.apply_plan(stack, plan, token, backtracking_tokenizer);
                        break;
                    }
                }
            }
        }
    }

    #[inline]
    fn end_of_node<I: Iterator<Item = T>>(
        &self,
        stack: &mut Stack,
        backtracking_tokenizer: &mut BacktrackingTokenizer<T, I>,
        mode: ModeData<'a>,
    ) {
        match mode {
            ModeData::LL => {
                stack.pop_normal();
            }
            ModeData::Alternative(backtracking_point) => {
                let old_tos = stack.stack_nodes.pop().unwrap();
                let tos = stack.tos_mut();
                tos.children_count = old_tos.children_count;
                tos.latest_child_node_index = old_tos.latest_child_node_index;
                if !tos.enabled_token_recording {
                    backtracking_tokenizer.stop();
                }
                debug_assert!(tos.dfa_state.is_final);
            }
        }
    }

    fn error_recovery<I: Iterator<Item = T>>(
        &self,
        stack: &mut Stack,
        backtracking_tokenizer: &mut BacktrackingTokenizer<T, I>,
        transition: Option<InternalSquashedType>,
        token: Option<&T>,
    ) {
        // In case we have a token that is not allowed at this position, try alternatives.
        for (i, node) in stack.stack_nodes.iter().enumerate().rev() {
            if let ModeData::Alternative(backtracking_point) = node.mode {
                stack.stack_nodes.truncate(i);

                stack
                    .tree_nodes
                    .truncate(backtracking_point.tree_node_count);
                let tos = stack.tos_mut();
                tos.children_count = backtracking_point.children_count;
                backtracking_tokenizer.reset(backtracking_point.token_index);
                let t = backtracking_tokenizer.next().unwrap();
                self.apply_plan(
                    stack,
                    backtracking_point.fallback_plan,
                    &t,
                    backtracking_tokenizer,
                );
                if !stack.tos().enabled_token_recording {
                    backtracking_tokenizer.stop();
                }
                // The token was not used, but the tokenizer backtracked.
                return; // Error Recovery done.
            }
        }

        // First step of error recovery is to mark tree nodes as failed and pop the
        // stack nodes that are failed.
        for (i, node) in stack.stack_nodes.iter().enumerate().rev() {
            if self.automatons[&node.node_id].does_error_recovery {
                while stack.stack_nodes.len() > i {
                    let stack_node = stack.stack_nodes.pop().unwrap();
                    update_tree_node_position(&mut stack.tree_nodes, &stack_node);
                    let mut n = stack
                        .tree_nodes
                        .get_mut(stack_node.tree_node_index)
                        .unwrap();
                    n.type_ = n.type_.set_error_recovery_bit();
                }
                if let Some(transition) = transition {
                    self.apply_transition(
                        stack,
                        backtracking_tokenizer,
                        transition,
                        token.unwrap(),
                    );
                }
                return; // Error recovery is done.
            }
        }
        if let Some(transition) = transition {
            // If the first step did not work, we try to add the token as an error terminal to
            // the tree.
            for nonterminal_id in stack.tos().dfa_state.nonterminal_transition_ids() {
                let automaton = &self.automatons[&nonterminal_id];
                if automaton.does_error_recovery {
                    stack.calculate_previous_next_node();
                    let token = token.unwrap();
                    // First add the nonterminal
                    stack.tree_nodes.push(InternalNode {
                        next_node_offset: 0,
                        type_: nonterminal_id.to_squashed().set_error_recovery_bit(),
                        start_index: token.start_index(),
                        length: token.length(),
                    });
                    // And then add the terminal
                    stack.tree_nodes.push(InternalNode {
                        next_node_offset: 0,
                        type_: transition.set_error_recovery_bit(),
                        start_index: token.start_index(),
                        length: token.length(),
                    });
                    return; // Error recovery is done.
                }
            }
        }
        //let rest = &code[token.start_index() as usize..];
        //dbg!(token, rest);
        dbg!(stack
            .stack_nodes
            .iter()
            .map(|n| n.dfa_state.from_rule)
            .collect::<Vec<_>>());
        //dbg!(self.tos());
        panic!("No error recovery function found");
    }

    #[inline]
    fn apply_plan<I: Iterator<Item = T>>(
        &self,
        stack: &mut Stack<'a>,
        plan: &'a Plan,
        token: &T,
        backtracking_tokenizer: &mut BacktrackingTokenizer<T, I>,
    ) {
        let tos_mut = stack.stack_nodes.last_mut().unwrap();
        tos_mut.dfa_state = plan.next_dfa();

        let start_index = token.start_index();
        // If we have left recursion we have to do something a bit weird: We push the same tree
        // node in between, because we only handle direct recursion. This is kind of similar
        // how LR would work. So it's an interesting mixture of LL and LR.
        // There's one exception: If the node can be omitted we don't even have to do it.
        if plan.mode == PlanMode::LeftRecursive && !tos_mut.can_omit_children() {
            tos_mut.children_count = 1;
            tos_mut.latest_child_node_index = tos_mut.tree_node_index + 1;

            update_tree_node_position(&mut stack.tree_nodes, tos_mut);

            let old_node = stack.tree_nodes[tos_mut.tree_node_index];
            stack.tree_nodes.insert(
                tos_mut.tree_node_index,
                InternalNode {
                    next_node_offset: 0,
                    type_: old_node.type_,
                    start_index: old_node.start_index,
                    length: 0,
                },
            );
        }

        let mut enabled_token_recording = tos_mut.enabled_token_recording;
        stack.calculate_previous_next_node();

        for push in &plan.pushes {
            // Lookaheads need to be accounted for.
            let tos = stack.tos_mut();
            let children_count = tos.children_count;
            tos.children_count += 1;
            //dbg!(&automatons[&push.node_type].dfa_states[push.to_state.0]);
            if matches!(push.stack_mode, StackMode::Alternative(_)) {
                enabled_token_recording = true;
            }
            match push.stack_mode {
                StackMode::LL => {
                    stack.push(
                        push.node_type,
                        stack.tree_nodes.len(),
                        push.next_dfa(),
                        start_index,
                        ModeData::LL,
                        0,
                        enabled_token_recording,
                    );
                }
                StackMode::Alternative(alternative_plan) => {
                    stack.push(
                        push.node_type,
                        stack.tos().tree_node_index,
                        push.next_dfa(),
                        start_index,
                        ModeData::Alternative(BacktrackingPoint {
                            tree_node_count: stack.tree_nodes.len(),
                            token_index: backtracking_tokenizer.start(token),
                            fallback_plan: unsafe { &*alternative_plan },
                            children_count,
                        }),
                        children_count,
                        enabled_token_recording,
                    );
                }
                StackMode::PositivePeek => {
                    panic!("Pushing peeks is currently not supported")
                }
            };
            stack.tos_mut().latest_child_node_index = stack.tree_nodes.len();
        }
        // Once all the nodes are dealt with, add the token
        stack.tos_mut().children_count += 1;
        stack.tree_nodes.push(InternalNode {
            next_node_offset: 0,
            type_: plan.type_,
            start_index,
            length: token.length(),
        });
    }
}

impl<'a> Stack<'a> {
    fn new(node_id: InternalNonterminalType, dfa_state: &'a DFAState, string_len: usize) -> Self {
        let mut stack = Stack {
            stack_nodes: vec![],
            tree_nodes: vec![],
        };
        // Just reserve enough so the vec contents don't need to be copied.
        stack.stack_nodes.reserve(128);
        // TODO need some research in how much we should reserve.
        stack.tree_nodes.reserve(string_len / 4);
        stack.push(node_id, 0, dfa_state, 0, ModeData::LL, 0, false);
        stack
    }

    #[inline]
    fn tos(&self) -> &StackNode<'a> {
        self.stack_nodes.last().unwrap()
    }

    #[inline]
    fn tos_mut(&mut self) -> &mut StackNode<'a> {
        self.stack_nodes.last_mut().unwrap()
    }

    #[inline]
    fn len(&self) -> usize {
        self.stack_nodes.len()
    }

    #[inline]
    fn pop_normal(&mut self) {
        let stack_node = self.stack_nodes.pop().unwrap();
        if stack_node.can_omit_children() {
            self.tree_nodes.remove(stack_node.tree_node_index);
        } else {
            // We can simply get the last token and check its end position to
            // calculate how long a node is.
            debug_assert!(stack_node.children_count >= 1);
            update_tree_node_position(&mut self.tree_nodes, &stack_node);
        }
    }

    #[inline]
    #[allow(clippy::too_many_arguments)]
    fn push(
        &mut self,
        node_id: InternalNonterminalType,
        tree_node_index: usize,
        dfa_state: &'a DFAState,
        start: CodeIndex,
        mode: ModeData<'a>,
        children_count: usize,
        enabled_token_recording: bool,
    ) {
        self.stack_nodes.push(StackNode {
            node_id,
            tree_node_index,
            latest_child_node_index: 0,
            dfa_state,
            children_count,
            mode,
            enabled_token_recording,
        });
        // ModeData::Alternative(_) needs to be excluded here, because the tree node is already
        // part of the parent stack node.
        if matches!(mode, ModeData::LL) {
            self.tree_nodes.push(InternalNode {
                next_node_offset: 0,
                type_: node_id.to_squashed(),
                start_index: start,
                length: 0,
            });
        }
    }

    #[inline]
    fn calculate_previous_next_node(&mut self) {
        let tos = self.stack_nodes.last_mut().unwrap();
        // Care for next_node_offset here.
        let index = tos.latest_child_node_index;
        let next = self.tree_nodes.len();

        // The first node (root node) does not need to be updated.
        if index != 0 {
            if let Some(n) = self.tree_nodes.get_mut(index) {
                n.next_node_offset = (next - index) as u32;
            }
        }
        tos.latest_child_node_index = next;
    }

    fn debug_tree(
        &self,
        nonterminal_map: &'static InternalStrToNode,
        terminal_map: &'static InternalStrToToken,
    ) -> String {
        fn recurse(
            nonterminal_map: &'static InternalStrToNode,
            terminal_map: &'static InternalStrToToken,
            tree_nodes: &[InternalNode],
            code: &mut String,
            index: usize,
            depth: usize,
        ) {
            fn find_key_for_value<K, V: Squashable + std::cmp::Eq>(
                map: &FastHashMap<K, V>,
                value: InternalSquashedType,
            ) -> Option<&K> {
                map.iter().find_map(|(key, val)| {
                    if val.to_squashed() == value {
                        Some(key)
                    } else {
                        None
                    }
                })
            }

            *code += &" ".repeat(depth);
            let node = tree_nodes[index];
            let t = node.type_.remove_error_recovery_bit();
            *code += &format!(
                "{}{}: {}-{}\n",
                if node.type_.is_error_recovery() {
                    "ERROR"
                } else {
                    ""
                },
                find_key_for_value(nonterminal_map, t)
                    .or_else(|| find_key_for_value(terminal_map, t))
                    .unwrap_or(&"Keyword"),
                node.start_index,
                node.start_index + node.length,
            );
            if !node.type_.is_leaf() {
                recurse(
                    nonterminal_map,
                    terminal_map,
                    tree_nodes,
                    code,
                    index + 1,
                    depth + 1,
                );
            }
            if node.next_node_offset != 0 {
                recurse(
                    nonterminal_map,
                    terminal_map,
                    tree_nodes,
                    code,
                    index + node.next_node_offset as usize,
                    depth,
                );
            }
        }

        let mut code = String::new();
        recurse(
            nonterminal_map,
            terminal_map,
            &self.tree_nodes,
            &mut code,
            0,
            0,
        );
        code
    }
}

impl<'a> StackNode<'a> {
    #[inline]
    fn can_omit_children(&self) -> bool {
        self.dfa_state.node_may_be_omitted && self.children_count == 1
    }
}

#[inline]
fn update_tree_node_position(tree_nodes: &mut [InternalNode], stack_node: &StackNode) {
    let last_tree_node = *tree_nodes.last().unwrap();
    let mut n = tree_nodes.get_mut(stack_node.tree_node_index).unwrap();
    n.length = last_tree_node.end_index() - n.start_index;
}
