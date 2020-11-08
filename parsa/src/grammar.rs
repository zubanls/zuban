use std::collections::{HashMap, HashSet};
use crate::{InternalType, Rule};

#[derive(Debug, Clone, Copy, Hash, PartialEq, Eq)]
struct NFAStateId(usize);
#[derive(Debug, Clone, Copy)]
struct DFAStateId(usize);

#[derive(Default)]
struct RuleAutomaton {
    nfa_states: Vec<NFAState>,
    dfa_states: Vec<DFAState>,
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


// NFA = nondeterministic finite automaton
#[derive(Default, Debug)]
struct NFAState {
    transitions: Vec<NFATransition>,
}

struct DFAState {
    transitions: Vec<DFATransition>,
    nfa_set: HashSet<NFAStateId>,
    is_final: bool,
    is_calculated: bool,
}

#[derive(Debug, Clone, Copy, Hash, Eq, PartialEq)]
enum NFATransitionType {
    Terminal(InternalType),
    Nonterminal(InternalType),
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

pub trait Grammar {
    fn terminal_name_to_int(&self, identifier: &str) -> Option<InternalType>;
    fn nonterminal_name_to_int(&self, identifier: &str) -> Option<InternalType>;
    fn generate(&mut self, rules: &HashMap<InternalType, Rule>) where Self: Sized {
        for (internal_type, rule) in rules {
            let mut automaton = Default::default();
            let (start, end) = build_automaton(self, &mut automaton, rule);
            dbg!(rule);
            let dfa_states = automaton.construct_powerset(start, end);
            // TODO proper transitions for operators/names
            // calculate first plans

            // Since we now know every nonterminal has a first terminal, we know that there is no
            // left recursion.
        }
    }

    fn foo(&self) {
    }
}

fn build_automaton(grammar: &dyn Grammar, automaton: &mut RuleAutomaton,
                   rule: &Rule) -> (NFAStateId, NFAStateId) {
    use Rule::*;
    match *rule {
        Identifier(string) => {
            let (start, end) = automaton.new_nfa_states();
            if let Some(t) = grammar.terminal_name_to_int(string) {
                automaton.add_transition(start, end, Some(NFATransitionType::Terminal(t)));
            } else if let Some(t) = grammar.nonterminal_name_to_int(string) {
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
                let (x, y) = build_automaton(grammar, automaton, r);
                automaton.add_empty_transition(start, x);
                automaton.add_empty_transition(y, end);
            }
            (start, end)
        },
        Maybe(rule1) => {
            let (start, end) = build_automaton(grammar, automaton, rule1);
            automaton.add_empty_transition(start, end);
            (start, end)
        },
        Multiple(rule1) => {
            let (start, end) = build_automaton(grammar, automaton, rule1);
            automaton.add_empty_transition(end, start);
            (start, end)
        }
        NegativeLookahead(rule1) => {
            // TODO for now this is basically ignored
            build_automaton(grammar, automaton, rule1)
        },
        PositiveLookahead(rule1) => {
            // TODO for now this is basically ignored
            build_automaton(grammar, automaton, rule1)
        }
        // TODO Cut is ignored for now.
        Cut(rule1, rule2) | Next(rule1, rule2) => {
            let (start1, end1) = build_automaton(grammar, automaton, rule1);
            let (start2, end2) = build_automaton(grammar, automaton, rule2);
            automaton.add_empty_transition(end1, start2);
            (start1, end2)
        }
    }
}
