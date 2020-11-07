use std::cell::RefCell;
use std::rc::{Rc, Weak};
use std::collections::HashMap;
use crate::{InternalType, Rule};

type NFAStateRc = Rc<RefCell<NFAState>>;

struct RuleAutomaton {
    states: Vec<NFAStateRc>,
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
    to: Weak<RefCell<NFAState>>,
}

pub trait Grammar {
    fn terminal_name_to_int(&self, identifier: &str) -> Option<InternalType>;
    fn nonterminal_name_to_int(&self, identifier: &str) -> Option<InternalType>;
    fn generate(&mut self, rules: &HashMap<InternalType, Rule>) where Self: Sized {
        fn new_states(automaton: &mut RuleAutomaton) -> (NFAStateRc, NFAStateRc) {
            automaton.states.push(Default::default());
            automaton.states.push(Default::default());
            (Rc::clone(&automaton.states[0]), Rc::clone(&automaton.states[0]))
        }

        fn add_transition(start: &NFAStateRc, to: &NFAStateRc, transition: NFATransitionType) {
            start.borrow_mut().transitions.push(
                NFATransition {transition: transition, to: Rc::downgrade(to)}
            );
        }

        fn add_empty_transition(start: &NFAStateRc, to: &NFAStateRc) {
            add_transition(start, to, NFATransitionType::None);
        }

        fn build_automaton(grammar: &dyn Grammar, automaton: &mut RuleAutomaton, rule: &Rule) -> (NFAStateRc, NFAStateRc) {
            use Rule::*;
            match *rule {
                Identifier(string) => {
                    let (start, end) = new_states(automaton);
                    if let Some(t) = grammar.terminal_name_to_int(string) {
                        add_transition(&start, &end, NFATransitionType::Terminal(t));
                    } else if let Some(t) = grammar.nonterminal_name_to_int(string) {
                        add_transition(&start, &end, NFATransitionType::Nonterminal(t));
                    } else {
                        panic!("No terminal / nonterminal found for {}", string);
                    }
                    (start, end)
                },
                Keyword(string) => {
                    let (start, end) = new_states(automaton);
                    add_transition(&start, &end, NFATransitionType::Keyword(string));
                    (start, end)
                },
                Or(rule1, rule2) => {
                    let (start, end) = new_states(automaton);
                    for r in [rule1, rule2].iter() {
                        let (x, y) = build_automaton(grammar, automaton, r);
                        add_empty_transition(&start, &x);
                        add_empty_transition(&y, &end);
                    }
                    (start, end)
                },
                Maybe(rule1) => {
                    let (start, end) = build_automaton(grammar, automaton, rule1);
                    add_empty_transition(&start, &end);
                    (start, end)
                },
                Multiple(rule1) => {
                    let (start, end) = build_automaton(grammar, automaton, rule1);
                    add_empty_transition(&end, &start);
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
                    add_empty_transition(&end1, &start1);
                    (start1, end2)
                }
            }
        }

        for (internal_type, rule) in rules {
            let mut automaton = RuleAutomaton {states: vec!(Default::default())};
            build_automaton(self, &mut automaton, rule);
            dbg!(rule);
        }
    }

    fn foo(&self) {
    }
}
