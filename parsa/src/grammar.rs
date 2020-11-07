use std::collections::{HashMap, HashSet};
use crate::{InternalType, Rule};

type NFAStateId = usize;

#[derive(Default)]
struct RuleAutomaton {
    nfa_states: Vec<NFAState>,
}

impl RuleAutomaton {
    fn get_nfa_state(&mut self, id: NFAStateId) -> &mut NFAState {
        &mut self.nfa_states[id]
    }

    fn new_nfa_states(&mut self) -> (NFAStateId, NFAStateId) {
        let mut new = || {
            self.nfa_states.push(Default::default());
            self.nfa_states.len() - 1
        };
        (new(), new())
    }

    fn add_transition(&mut self, start: NFAStateId, to: NFAStateId, transition: NFATransitionType) {
        self.get_nfa_state(start).transitions.push(
            NFATransition {transition: transition, to: to}
        );
    }

    fn add_empty_transition(&mut self, start: NFAStateId, to: NFAStateId) {
        self.add_transition(start, to, NFATransitionType::None);
    }

    fn group_nfas(nfa_state: NFAStateId) -> HashSet<NFAStateId> {
        // Group all NFAs that are ε-moves
        let mut set = HashSet::new();
        set.insert(nfa_state);
        set
    }
}


// NFA = nondeterministic finite automaton
#[derive(Default)]
struct NFAState {
    transitions: Vec<NFATransition>,
}

enum NFATransitionType {
    Terminal(InternalType),
    Nonterminal(InternalType),
    Keyword(&'static str),
    None,
}

struct NFATransition {
    transition: NFATransitionType,
    to: NFAStateId,
}

pub trait Grammar {
    fn terminal_name_to_int(&self, identifier: &str) -> Option<InternalType>;
    fn nonterminal_name_to_int(&self, identifier: &str) -> Option<InternalType>;
    fn generate(&mut self, rules: &HashMap<InternalType, Rule>) where Self: Sized {
        for (internal_type, rule) in rules {
            let mut automaton = Default::default();
            let (start, end) = build_automaton(self, &mut automaton, rule);
            nfa_to_dfa(start, end);
            dbg!(rule);
        }
    }

    fn foo(&self) {
    }
}

fn build_automaton(grammar: &dyn Grammar, automaton: &mut RuleAutomaton, rule: &Rule) -> (NFAStateId, NFAStateId) {
    use Rule::*;
    match *rule {
        Identifier(string) => {
            let (start, end) = automaton.new_nfa_states();
            if let Some(t) = grammar.terminal_name_to_int(string) {
                automaton.add_transition(start, end, NFATransitionType::Terminal(t));
            } else if let Some(t) = grammar.nonterminal_name_to_int(string) {
                automaton.add_transition(start, end, NFATransitionType::Nonterminal(t));
            } else {
                panic!("No terminal / nonterminal found for {}", string);
            }
            (start, end)
        },
        Keyword(string) => {
            let (start, end) = automaton.new_nfa_states();
            automaton.add_transition(start, end, NFATransitionType::Keyword(string));
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
            automaton.add_empty_transition(end1, start1);
            (start1, end2)
        }
    }
}

struct DFAState {
    transitions: Vec<u8>,
    is_final: bool,
}

fn nfa_to_dfa(start: NFAStateId, end: NFAStateId) -> u8 {
    //let dfa_states = vec!();
    1
}
