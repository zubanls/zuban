use std::collections::{HashMap, HashSet};
use std::marker::PhantomData;

use crate::{InternalTokenType, InternalNodeType, Rule, InternalStrToToken,
            InternalStrToNode, InternalNode, Token, CodeIndex};

type SquashedTransitions = HashMap<InternalSquashedType, Plan>;
type Automatons = HashMap<InternalNodeType, RuleAutomaton>;
#[derive(Copy, Clone, Debug, PartialEq, Eq, Hash, Default)]
pub struct InternalSquashedType(i16);

#[derive(Debug, Clone, Copy, Hash, PartialEq, Eq)]
struct NFAStateId(usize);
#[derive(Debug, Clone, Copy)]
struct DFAStateId(usize);

// NFA = nondeterministic finite automaton
#[derive(Default, Debug)]
struct NFAState {
    transitions: Vec<NFATransition>,
}

// DFA = deterministic finite automaton
#[derive(Debug)]
struct DFAState {
    transitions: Vec<DFATransition>,
    nfa_set: HashSet<NFAStateId>,
    is_final: bool,
    is_calculated: bool,

    // This is the important part that will be used by the parser. The rest is
    // just there to generate this information.
    transition_to_plan: SquashedTransitions,
}

#[derive(Debug, Clone, Copy, Hash, Eq, PartialEq)]
enum NFATransitionType {
    Terminal(InternalTokenType),
    Nonterminal(InternalNodeType),
    Keyword(&'static str),
}

#[derive(Debug)]
struct NFATransition {
    type_: Option<NFATransitionType>,
    to: NFAStateId,
}

#[derive(Debug, Clone, Copy)]
struct DFATransition {
    type_: NFATransitionType,
    to: DFAStateId,
}

#[derive(Debug, Default)]
struct Keywords {
    counter: usize,
    keywords: HashMap<&'static str, usize>,
}

#[derive(Debug, Clone)]
struct Plan {
    pushes: Vec<(InternalNodeType, DFAStateId)>,
    next_dfa_state: DFAStateId,
    type_: InternalSquashedType,
}

enum FirstPlan {
    Calculated(SquashedTransitions),
    Calculating,
}

#[derive(Debug)]
pub struct Grammar<T> {
    reserved_strings: HashMap<&'static str, InternalSquashedType>,
    terminal_map: &'static InternalStrToToken,
    nonterminal_map: &'static InternalStrToNode,
    phantom: PhantomData<T>,
    plans: Vec<Plan>,
    automatons: Automatons,
    keywords: Keywords,
}

#[derive(Default, Debug)]
struct RuleAutomaton {
    type_: InternalNodeType,
    nfa_states: Vec<NFAState>,
    dfa_states: Vec<DFAState>,
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

impl<'a, T: Token> Grammar<T> {
    pub fn new(rules: &HashMap<InternalNodeType, Rule>,
               nonterminal_map: &'static InternalStrToNode, 
               terminal_map: &'static InternalStrToToken) -> Self {
        let mut grammar = Self {
            reserved_strings: Default::default(),
            terminal_map: terminal_map,
            nonterminal_map: nonterminal_map,
            phantom: PhantomData,
            plans: Default::default(),
            automatons: Default::default(),
            keywords: Default::default(),
        };
        let mut keywords = Default::default();
        let mut automatons = HashMap::new();
        let dfa_counter = 0;
        for (internal_type, rule) in rules {
            let mut automaton = RuleAutomaton {
                type_: *internal_type,
                nfa_states: Default::default(),
                dfa_states: Default::default(),
            };
            let (start, end) = grammar.build_automaton(&mut automaton, &mut keywords, rule);
            let dfa_states = automaton.construct_powerset(start, end);
            automaton.dfa_states = dfa_states;
            automatons.insert(*internal_type, automaton);
        }
        grammar.keywords = keywords;

        // Calculate first plans
        let mut first_plans = HashMap::new();
        for rule_label in automatons.keys().cloned().collect::<Vec<InternalNodeType>>() {
            grammar.create_first_plans(&mut first_plans, &mut automatons, rule_label);
        }
        // Optimize and calculate all plans
        for rule_label in [InternalNodeType(1)].iter() {
            // Now optimize the whole thing
            // TODO proper transitions for operators/names
            for (i, dfa_state) in automatons.get_mut(&rule_label).unwrap().dfa_states.iter_mut().enumerate() {
                dfa_state.transition_to_plan = grammar.create_all_plans(&dfa_state, &first_plans);
            }
        }

        // Since we now know every nonterminal has a first terminal, we know that there is no
        // left recursion.
        grammar
    }

    fn build_automaton(&self, automaton: &mut RuleAutomaton, keywords: &mut Keywords,
                       rule: &Rule) -> (NFAStateId, NFAStateId) {
        use Rule::*;
        match *rule {
            Identifier(string) => {
                let (start, end) = automaton.new_nfa_states();
                if let Some(&t) = self.terminal_map.get(string) {
                    automaton.add_transition(start, end, Some(NFATransitionType::Terminal(t)));
                } else if let Some(&t) = self.nonterminal_map.get(string) {
                    automaton.add_transition(start, end, Some(NFATransitionType::Nonterminal(t)));
                } else {
                    panic!("No terminal / nonterminal found for {}", string);
                }
                (start, end)
            },
            Keyword(string) => {
                let (start, end) = automaton.new_nfa_states();
                automaton.add_transition(start, end, Some(NFATransitionType::Keyword(string)));
                keywords.add(string);
                (start, end)
            },
            Or(rule1, rule2) => {
                let (start, end) = automaton.new_nfa_states();
                for r in [rule1, rule2].iter() {
                    let (x, y) = self.build_automaton(automaton, keywords, r);
                    automaton.add_empty_transition(start, x);
                    automaton.add_empty_transition(y, end);
                }
                (start, end)
            },
            Maybe(rule1) => {
                let (start, end) = self.build_automaton(automaton, keywords, rule1);
                automaton.add_empty_transition(start, end);
                (start, end)
            },
            Multiple(rule1) => {
                let (start, end) = self.build_automaton(automaton, keywords, rule1);
                automaton.add_empty_transition(end, start);
                (start, end)
            }
            NegativeLookahead(rule1) => {
                // TODO for now this is basically ignored
                self.build_automaton(automaton, keywords, rule1)
            },
            PositiveLookahead(rule1) => {
                // TODO for now this is basically ignored
                self.build_automaton(automaton, keywords, rule1)
            }
            // TODO Cut is ignored for now.
            Cut(rule1, rule2) | Next(rule1, rule2) => {
                let (start1, end1) = self.build_automaton(automaton, keywords, rule1);
                let (start2, end2) = self.build_automaton(automaton, keywords, rule2);
                automaton.add_empty_transition(end1, start2);
                (start1, end2)
            }
        }
    }

    fn create_first_plans(&self,
                          first_plans: &mut HashMap<InternalNodeType, FirstPlan>,
                          automatons: &Automatons,
                          automaton_key: InternalNodeType) {
        let automaton = &automatons[&automaton_key];
        match first_plans.get(&automaton_key) {
            None => {
                first_plans.insert(automaton_key, FirstPlan::Calculating);
            }
            Some(first_plan) => {
                match first_plan {
                    FirstPlan::Calculated(_) => {return},
                    FirstPlan::Calculating => {
                        panic!("The grammar contains left recursion for rule {:?}",
                               self.nonterminal_to_str(automaton_key))
                    },
                }
            }
        }
        let mut plans = HashMap::new();
        for transition in &automaton.dfa_states[0].transitions {
            match transition.type_ {
                NFATransitionType::Terminal(type_) => {
                    let t = token_type_to_squashed(type_);
                    plans.insert(t, Plan {
                        pushes: Vec::new(),
                        next_dfa_state: transition.to,
                        type_: t,
                    });
                },
                NFATransitionType::Nonterminal(type_) => {
                    self.create_first_plans(first_plans, &automatons, type_);
                    match &first_plans[&type_] {
                        FirstPlan::Calculating => {unreachable!()},
                        FirstPlan::Calculated(transitions) => {
                            for (t, nested_plan) in transitions {
                                let mut pushes = nested_plan.pushes.clone();
                                pushes.insert(0, (type_, nested_plan.next_dfa_state));
                                plans.insert(*t, Plan {
                                    pushes: pushes,
                                    next_dfa_state: transition.to,
                                    type_: *t,
                                });
                            }
                        },
                    }
                },
                NFATransitionType::Keyword(keyword) => {
                    let t = self.keyword_to_squashed(keyword);
                    plans.insert(t, Plan {
                        pushes: Vec::new(),
                        next_dfa_state: transition.to,
                        type_: t,
                    });
                },
            }
        }
        first_plans.insert(automaton_key, FirstPlan::Calculated(plans));
    }

    fn create_all_plans(&self, dfa_state: &DFAState,
                        first_plans: &HashMap<InternalNodeType, FirstPlan>) -> SquashedTransitions {
        let mut plans = HashMap::new();
        for transition in &dfa_state.transitions {
            match transition.type_ {
                NFATransitionType::Terminal(type_) => {
                    let t = token_type_to_squashed(type_);
                    plans.insert(t, Plan {
                        pushes: Vec::new(),
                        next_dfa_state: transition.to,
                        type_: t,
                    });
                },
                NFATransitionType::Nonterminal(type_) => {
                    let first_plan = &first_plans[&type_];
                    if let FirstPlan::Calculated(p) = first_plan {
                        plans.extend(p.iter().map(|(k, v)| (*k, v.clone())));
                    } else {
                        panic!("Shouldn't happen");
                    }
                },
                NFATransitionType::Keyword(keyword) => {
                    let t = self.keyword_to_squashed(keyword);
                    plans.insert(t, Plan {
                        pushes: Vec::new(),
                        next_dfa_state: transition.to,
                        type_: t,
                    });
                },
            }
        }
        plans
    }

    pub fn parse(&self, tokens: impl Iterator<Item=T>, start: InternalNodeType) -> Vec<InternalNode> {
        let mut stack = Stack::new(
            start,
            &self.automatons[&start].dfa_states[0]
        );

        for token in tokens {
            let transition;
            if token.can_contain_syntax() {
                transition = match self.reserved_strings.get("") {
                    None => token_type_to_squashed(token.get_type()),
                    Some(type_) => *type_
                }
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

    fn nonterminal_to_str(&self, nonterminal: InternalNodeType) -> &str {
        for (k, v) in self.nonterminal_map {
            if nonterminal == *v {
                return *k
            }
        }
        panic!("Something is very wrong, integer not found");
    }

    fn keyword_to_squashed(&self, keyword: &str) -> InternalSquashedType {
        InternalSquashedType(self.keywords.get(keyword) as i16)
    }
}

#[inline]
fn token_type_to_squashed(token_type: InternalTokenType) -> InternalSquashedType {
    InternalSquashedType(token_type.0)
}

#[inline]
fn node_type_to_squashed(token_type: InternalNodeType) -> InternalSquashedType {
    // TODO hmmmmmm
    InternalSquashedType(token_type.0)
}

impl RuleAutomaton {
    fn get_nfa_state_mut(&mut self, id: NFAStateId) -> &mut NFAState {
        &mut self.nfa_states[id.0]
    }

    fn get_nfa_state(&self, id: NFAStateId) -> &NFAState {
        &self.nfa_states[id.0]
    }

    fn new_nfa_states(&mut self) -> (NFAStateId, NFAStateId) {
        let mut new = || {
            self.nfa_states.push(Default::default());
            NFAStateId(self.nfa_states.len() - 1)
        };
        (new(), new())
    }

    fn add_transition(&mut self, start: NFAStateId, to: NFAStateId,
                      type_: Option<NFATransitionType>) {
        self.get_nfa_state_mut(start).transitions.push(
            NFATransition {type_: type_, to: to}
        );
    }

    fn add_empty_transition(&mut self, start: NFAStateId, to: NFAStateId) {
        self.add_transition(start, to, None);
    }

    fn group_nfas(&self, nfa_state_ids: Vec<NFAStateId>) -> HashSet<NFAStateId> {
        // Group all NFAs that are ε-moves (which are essentially transitions with None)
        let mut set: HashSet<_> = nfa_state_ids.iter().cloned().collect();
        for nfa_state_id in nfa_state_ids {
            for transition in &self.get_nfa_state(nfa_state_id).transitions {
                if let None = transition.type_ {
                    set.insert(transition.to);
                }
            }
        }
        set
    }

    fn nfa_to_dfa(&self, dfa_states: &mut Vec<DFAState>, starts: Vec<NFAStateId>,
                  end: NFAStateId) -> DFAStateId {
        let grouped_nfas = self.group_nfas(starts);
        for (i, dfa_state) in dfa_states.iter().enumerate() {
            if dfa_state.nfa_set == grouped_nfas {
                return DFAStateId(i);
            }
        }
        let is_final = grouped_nfas.contains(&end);
        dfa_states.push(DFAState {
            transitions: Default::default(),
            nfa_set: grouped_nfas,
            is_final: is_final,
            is_calculated: false,
            transition_to_plan: Default::default(),
        });
        DFAStateId(dfa_states.len() - 1)
    }

    fn construct_powerset(&mut self, start: NFAStateId, end: NFAStateId) -> Vec<DFAState> {
        let mut dfa_states = Vec::new();
        let dfa_id = self.nfa_to_dfa(&mut dfa_states, vec!(start), end);
        self.construct_powerset_for_dfa(&mut dfa_states, dfa_id, end);
        dfa_states
    }

    fn construct_powerset_for_dfa(&mut self, dfa_states: &mut Vec<DFAState>,
                                  dfa_id: DFAStateId, end: NFAStateId) {
        let state = &dfa_states[dfa_id.0];
        if state.is_calculated {
            return
        }

        let mut grouped_transitions = HashMap::new();
        for nfa_state_id in state.nfa_set.clone()  {
            let n = &self.get_nfa_state(nfa_state_id);
            for transition in &n.transitions {
                if let Some(t) = &transition.type_ {
                    grouped_transitions.insert(t, vec!(transition.to));
                }
            }
        }

        let mut transitions = Vec::new();
        for (type_, grouped_starts) in grouped_transitions {
                let new_dfa_id = self.nfa_to_dfa(dfa_states, grouped_starts, end);
                transitions.push(DFATransition {type_: *type_, to: new_dfa_id});
            }

        dfa_states[dfa_id.0].transitions = transitions;
        dfa_states[dfa_id.0].is_calculated = true;
        for transition in dfa_states[dfa_id.0].transitions.clone() {
            self.construct_powerset_for_dfa(dfa_states, transition.to, end)
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


impl Keywords {
    fn add(&mut self, keyword: &'static str) {
        if !self.keywords.contains_key(keyword) {
            self.keywords.insert(keyword, self.counter);
            self.counter += 1;
        }
    }
    fn get(&self, keyword: &str) -> usize {
        self.keywords[keyword]
    }
}
