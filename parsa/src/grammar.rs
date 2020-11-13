use std::collections::{HashMap, HashSet};
use std::marker::PhantomData;
use std::rc::Rc;

use crate::{InternalTokenType, InternalNodeType, Rule, InternalStrToToken,
            InternalStrToNode, InternalNode, Token};

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
struct DFAState {
    transitions: Vec<DFATransition>,
    nfa_set: HashSet<NFAStateId>,
    is_final: bool,
    is_calculated: bool,
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

#[derive(Debug)]
struct Plan {
    pushes: Vec<&'static OptimizedDFAState>,
    next_dfa_state: &'static OptimizedDFAState,
    type_: InternalSquashedType,
}

enum FirstPlan {
    Plan(HashMap<InternalSquashedType, Plan>),
    Calculating,
}

#[derive(Debug)]
pub struct Grammar<T> {
    reserved_strings: HashMap<&'static str, InternalSquashedType>,
    terminal_map: &'static InternalStrToToken,
    nonterminal_map: &'static InternalStrToNode,
    phantom: PhantomData<T>,
    plans: Vec<Plan>,
    optimized_dfa_states: Vec<OptimizedDFAState>,
    node_to_optimized_dfa_states: HashMap<InternalNodeType, usize>,
}

#[derive(Default)]
struct RuleAutomaton {
    type_: InternalNodeType,
    nfa_states: Vec<NFAState>,
    dfa_states: Vec<DFAState>,
}

#[derive(Debug)]
struct StackNode<'a> {
    dfa_state: &'a OptimizedDFAState,
    backtrack_length_counts: Vec<u32>,
}

#[derive(Debug)]
struct Stack<'a> {
    nodes: Vec<StackNode<'a>>,
}

#[derive(Debug)]
struct OptimizedDFAState {
    transitions: HashMap<InternalSquashedType, &'static Plan>,
    is_final: bool,
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
            optimized_dfa_states: Default::default(),
            node_to_optimized_dfa_states: Default::default(),
        };
        let mut automatons = HashMap::new();
        let mut optimized_dfa_states = Vec::new();
        let mut node_to_optimized_dfa_states = HashMap::new();
        for (internal_type, rule) in rules {
            let mut automaton = RuleAutomaton {
                type_: *internal_type,
                nfa_states: Default::default(),
                dfa_states: Default::default(),
            };
            let (start, end) = grammar.build_automaton(&mut automaton, rule);
            dbg!(rule);
            let dfa_states = automaton.construct_powerset(start, end);
            automaton.dfa_states = dfa_states;
            automatons.insert(*internal_type, automaton);

            // Now optimize the whole thing
            // TODO proper transitions for operators/names
            for (i, dfa_state) in automatons[internal_type].dfa_states.iter().enumerate() {
                let opt = OptimizedDFAState {
                    transitions: Default::default(),
                    is_final: dfa_state.is_final,
                };
                optimized_dfa_states.push(opt);
                if i == 1 {
                    node_to_optimized_dfa_states.insert(
                        internal_type,
                        optimized_dfa_states.len() - 1
                    );
                }
            }
        }

        // Calculate first plans
        let mut first_plans = HashMap::new();
        for id in automatons.keys().cloned().collect::<Vec<InternalNodeType>>() {
            grammar.create_first_plans(&mut first_plans, &mut automatons, id);
        }
        grammar.optimized_dfa_states = optimized_dfa_states;

        // Since we now know every nonterminal has a first terminal, we know that there is no
        // left recursion.
        grammar
    }

    fn build_automaton(&self, automaton: &mut RuleAutomaton,
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
                (start, end)
            },
            Or(rule1, rule2) => {
                let (start, end) = automaton.new_nfa_states();
                for r in [rule1, rule2].iter() {
                    let (x, y) = self.build_automaton(automaton, r);
                    automaton.add_empty_transition(start, x);
                    automaton.add_empty_transition(y, end);
                }
                (start, end)
            },
            Maybe(rule1) => {
                let (start, end) = self.build_automaton(automaton, rule1);
                automaton.add_empty_transition(start, end);
                (start, end)
            },
            Multiple(rule1) => {
                let (start, end) = self.build_automaton(automaton, rule1);
                automaton.add_empty_transition(end, start);
                (start, end)
            }
            NegativeLookahead(rule1) => {
                // TODO for now this is basically ignored
                self.build_automaton(automaton, rule1)
            },
            PositiveLookahead(rule1) => {
                // TODO for now this is basically ignored
                self.build_automaton(automaton, rule1)
            }
            // TODO Cut is ignored for now.
            Cut(rule1, rule2) | Next(rule1, rule2) => {
                let (start1, end1) = self.build_automaton(automaton, rule1);
                let (start2, end2) = self.build_automaton(automaton, rule2);
                automaton.add_empty_transition(end1, start2);
                (start1, end2)
            }
        }
    }

    fn create_first_plans(&self,
                          first_plans: &mut HashMap<InternalNodeType, FirstPlan>,
                          automatons: &mut HashMap<InternalNodeType, RuleAutomaton>,
                          automaton_key: InternalNodeType) {
        let automaton = &automatons[&automaton_key];
        for transition in &automaton.dfa_states[0].transitions {
            match transition.type_ {
                NFATransitionType::Terminal(type_) => {
                },
                NFATransitionType::Nonterminal(type_) => {
                },
                NFATransitionType::Keyword(string) => {
                },
            }
        }
        /*
        first_plans[&id] = FirstPlan::Plan(Plan {
            pushes: Vec::new(),
            next_dfa_state: &optimized_dfa_states[node_to_optimized_dfa_states[id]],
            type_: InternalType,
        });
        */
    }

    fn create_all_plans(&self) {
    }

    pub fn parse(&self, tokens: impl Iterator<Item=T>, start_token: InternalNodeType) -> Vec<InternalNode> {
        let mut stack = Stack::new(&self.optimized_dfa_states[self.node_to_optimized_dfa_states[&start_token]]);
        let mut nodes = Vec::new();

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

            let start_index = token.get_start_index();
            loop {
                let tos = stack.get_tos();
                match tos.dfa_state.transitions.get(&transition) {
                    None => {
                        if tos.dfa_state.is_final {
                            stack.pop()
                        } else {
                            panic!("Error recovery");
                        }
                    },
                    Some(plan) => {
                        let p: &Plan = *plan;
                        stack.set_dfa_state(p.next_dfa_state);
                        for push in &p.pushes {
                            stack.push(push);
                            nodes.push(InternalNode {
                                next_node_offset: 0,
                                // Positive values are token types, negative values are nodes
                                type_: p.type_,
                                start_index: start_index,
                                length: token.get_start_index(),
                                extra_data: 0,
                            });
                        }
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
                return nodes
            }
        }
    }
}

#[inline]
fn token_type_to_squashed(token_type: InternalTokenType) -> InternalSquashedType {
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

        dbg!(dfa_id.0, &transitions);
        dfa_states[dfa_id.0].transitions = transitions;
        dfa_states[dfa_id.0].is_calculated = true;
        for transition in dfa_states[dfa_id.0].transitions.clone() {
            self.construct_powerset_for_dfa(dfa_states, transition.to, end)
        }
    }
}

impl<'a> Stack<'a> {
    fn new(dfa_state: &'a OptimizedDFAState) -> Self {
        let mut stack = Self {nodes: Default::default()};
        stack.nodes.push(StackNode {dfa_state: dfa_state, backtrack_length_counts: Vec::new()});
        stack
    }

    fn get_tos(&self) -> &StackNode{
        &self.nodes[self.nodes.len() - 1]
    }

    fn len(&self) -> usize {
        self.nodes.len()
    }

    fn pop(&mut self) {
        self.nodes.pop();
    }

    fn push(&mut self, dfa_state: &'a OptimizedDFAState) {
        self.nodes.push(StackNode {dfa_state: dfa_state, backtrack_length_counts: Vec::new()});
    }

    fn set_dfa_state(&mut self, dfa_state: &'a OptimizedDFAState) {
        let index = self.nodes.len() - 1;
        self.nodes[index].dfa_state = dfa_state
    }
}
