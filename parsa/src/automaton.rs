use std::collections::{HashMap, HashSet};

use crate::grammar::{InternalNode, Token, CodeIndex};

pub const NODE_START: u16 = 1<<15;

type SquashedTransitions = HashMap<InternalSquashedType, Plan>;
pub type Automatons = HashMap<InternalNodeType, RuleAutomaton>;
pub type InternalStrToToken = HashMap<&'static str, InternalTokenType>;
pub type InternalStrToNode = HashMap<&'static str, InternalNodeType>;


#[derive(Debug)]
pub enum Rule {
    Identifier(&'static str),
    Keyword(&'static str),
    Or(&'static Rule, &'static Rule),
    Cut(&'static Rule, &'static Rule),
    Maybe(&'static Rule),
    Multiple(&'static Rule),
    NegativeLookahead(&'static Rule),
    PositiveLookahead(&'static Rule),
    Next(&'static Rule, &'static Rule),
}

#[derive(Copy, Clone, Debug, PartialEq, Eq, Hash, Default)]
pub struct InternalSquashedType(pub u16);

impl InternalSquashedType {
    pub fn is_leaf(&self) -> bool {
        return self.0 < NODE_START
    }
}

#[derive(Copy, Clone, Debug, PartialEq, Eq, Hash, Default)]
pub struct InternalNodeType(pub u16);
impl InternalNodeType {
    #[inline]
    pub fn to_squashed(&self) -> InternalSquashedType {
        InternalSquashedType(self.0)
    }
}

#[derive(Copy, Clone, Debug, PartialEq, Eq, Hash, Default)]
pub struct InternalTokenType(pub u16);
impl InternalTokenType {
    #[inline]
    pub fn to_squashed(&self) -> InternalSquashedType {
        InternalSquashedType(self.0)
    }
}

#[derive(Debug, Clone, Copy, Hash, PartialEq, Eq)]
struct NFAStateId(usize);

#[derive(Debug, Clone, Copy)]
pub struct DFAStateId(pub usize);

// NFA = nondeterministic finite automaton
#[derive(Default, Debug)]
struct NFAState {
    transitions: Vec<NFATransition>,
}

// DFA = deterministic finite automaton
#[derive(Debug)]
pub struct DFAState {
    transitions: Vec<DFATransition>,
    nfa_set: HashSet<NFAStateId>,
    pub is_final: bool,
    is_calculated: bool,

    // This is the important part that will be used by the parser. The rest is
    // just there to generate this information.
    pub transition_to_plan: SquashedTransitions,
}

#[derive(Debug, Clone, Copy, Hash, Eq, PartialEq)]
enum NFATransitionType {
    Terminal(InternalTokenType, &'static str),
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

#[derive(Debug, Clone)]
pub struct Plan {
    pub pushes: Vec<(InternalNodeType, DFAStateId)>,
    pub next_dfa_state: DFAStateId,
    pub type_: InternalSquashedType,
    pub debug_text: &'static str,
}

enum FirstPlan {
    Calculated(SquashedTransitions),
    Calculating,
}

#[derive(Debug, Default)]
pub struct Keywords {
    counter: usize,
    keywords: HashMap<&'static str, InternalSquashedType>,
}

impl Keywords {
    fn add(&mut self, keyword: &'static str) {
        if !self.keywords.contains_key(keyword) {
            self.keywords.insert(keyword, Self::keyword_to_squashed(self.counter));
            self.counter += 1;
        }
    }

    pub fn keyword_to_squashed(number: usize) -> InternalSquashedType {
        InternalSquashedType(number as u16)
    }


    pub fn get_squashed(&self, keyword: &str) -> Option<InternalSquashedType> {
        self.keywords.get(keyword).copied()
    }
}

#[derive(Default, Debug)]
pub struct RuleAutomaton {
    type_: InternalNodeType,
    nfa_states: Vec<NFAState>,
    pub dfa_states: Vec<DFAState>,
}

impl RuleAutomaton {
    fn build(&mut self, nonterminal_map: &InternalStrToNode, terminal_map: &InternalStrToToken,
             keywords: &mut Keywords, rule: &Rule) -> (NFAStateId, NFAStateId) {
        let mut build = |automaton: &mut Self, rule| automaton.build(
            nonterminal_map, terminal_map, keywords, rule);
        use Rule::*;
        match *rule {
            Identifier(string) => {
                let (start, end) = self.new_nfa_states();
                if let Some(&t) = terminal_map.get(string) {
                    self.add_transition(start, end, Some(NFATransitionType::Terminal(t, string)));
                } else if let Some(&t) = nonterminal_map.get(string) {
                    self.add_transition(start, end, Some(NFATransitionType::Nonterminal(t)));
                } else {
                    panic!("No terminal / nonterminal found for {:?}; token_map = {:?}; node_map ={:?}",
                           string, terminal_map, nonterminal_map);
                }
                (start, end)
            },
            Keyword(string) => {
                let (start, end) = self.new_nfa_states();
                self.add_transition(start, end, Some(NFATransitionType::Keyword(string)));
                keywords.add(string);
                (start, end)
            },
            Or(rule1, rule2) => {
                let (start, end) = self.new_nfa_states();
                for r in [rule1, rule2].iter() {
                    let (x, y) = build(self, r);
                    self.add_empty_transition(start, x);
                    self.add_empty_transition(y, end);
                }
                (start, end)
            },
            Maybe(rule1) => {
                let (start, end) = build(self, rule1);
                self.add_empty_transition(start, end);
                (start, end)
            },
            Multiple(rule1) => {
                let (start, end) = build(self, rule1);
                self.add_empty_transition(end, start);
                (start, end)
            }
            NegativeLookahead(rule1) => {
                // TODO for now this is basically ignored
                build(self, rule1)
            },
            PositiveLookahead(rule1) => {
                // TODO for now this is basically ignored
                build(self, rule1)
            }
            // TODO Cut is ignored for now.
            Cut(rule1, rule2) | Next(rule1, rule2) => {
                let (start1, end1) = build(self, rule1);
                let (start2, end2) = build(self, rule2);
                self.add_empty_transition(end1, start2);
                (start1, end2)
            }
        }
    }

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
        for nfa_state_id in &nfa_state_ids {
            for transition in &self.get_nfa_state(*nfa_state_id).transitions {
                if let None = transition.type_ {
                    set.insert(transition.to);
                    if !nfa_state_ids.contains(&transition.to) {
                        set.extend(self.group_nfas(set.iter().cloned().collect()));
                    }
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

pub fn generate_automatons(nonterminal_map: &InternalStrToNode, terminal_map: &InternalStrToToken,
                           rules: &HashMap<InternalNodeType, Rule>) -> (Automatons, Keywords) {
    let mut keywords = Keywords {
        // We need to start the numbers of keywords after tokens. Keyword ID's therefore never
        // clash with Token IDs (both are of type SquashedInternalType).
        counter: terminal_map.len(),
        .. Default::default()
    };
    let mut automatons = HashMap::new();
    let dfa_counter = 0;
    for (internal_type, rule) in rules {
        let mut automaton = RuleAutomaton {
            type_: *internal_type,
            nfa_states: Default::default(),
            dfa_states: Default::default(),
        };
        let (start, end) = automaton.build(nonterminal_map, terminal_map, &mut keywords, rule);
        let dfa_states = automaton.construct_powerset(start, end);
        automaton.dfa_states = dfa_states;
        automatons.insert(*internal_type, automaton);
    }

    // Calculate first plans
    let mut first_plans = HashMap::new();
    let rule_labels = automatons.keys().cloned().collect::<Vec<InternalNodeType>>();
    for rule_label in &rule_labels {
        create_first_plans(nonterminal_map, &keywords, &mut first_plans, &mut automatons, *rule_label);
    }
    // Optimize and calculate all plans
    for rule_label in &rule_labels {
        // Now optimize the whole thing
        // TODO proper transitions for operators/names
        for (i, dfa_state) in automatons.get_mut(rule_label).unwrap().dfa_states.iter_mut().enumerate() {
            dfa_state.transition_to_plan = create_all_plans(&keywords, &dfa_state, &first_plans);
        }
    }
    (automatons, keywords)
}

fn create_first_plans(nonterminal_map: &InternalStrToNode,
                      keywords: &Keywords,
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
                           nonterminal_to_str(nonterminal_map, automaton_key))
                },
            }
        }
    }
    let mut plans = HashMap::new();
    for transition in &automaton.dfa_states[0].transitions {
        match transition.type_ {
            NFATransitionType::Terminal(type_, debug_text) => {
                let t = type_.to_squashed();
                plans.insert(t, Plan {
                    pushes: Vec::new(),
                    next_dfa_state: transition.to,
                    type_: t,
                    debug_text: debug_text
                });
            },
            NFATransitionType::Nonterminal(node_id) => {
                create_first_plans(nonterminal_map, keywords, first_plans, &automatons, node_id);
                match &first_plans[&node_id] {
                    FirstPlan::Calculating => {unreachable!()},
                    FirstPlan::Calculated(transitions) => {
                        for (t, nested_plan) in transitions {
                            plans.insert(*t, nest_plan(nested_plan, node_id, transition.to));
                        }
                    },
                }
            },
            NFATransitionType::Keyword(keyword) => {
                let t = keywords.get_squashed(keyword).unwrap();
                plans.insert(t, Plan {
                    pushes: Vec::new(),
                    next_dfa_state: transition.to,
                    type_: t,
                    debug_text: keyword,
                });
            },
        }
    }
    first_plans.insert(automaton_key, FirstPlan::Calculated(plans));
}

fn create_all_plans(keywords: &Keywords, dfa_state: &DFAState,
                    first_plans: &HashMap<InternalNodeType, FirstPlan>) -> SquashedTransitions {
    let mut plans = HashMap::new();
    for transition in &dfa_state.transitions {
        match transition.type_ {
            NFATransitionType::Terminal(type_, debug_text) => {
                let t = type_.to_squashed();
                plans.insert(t, Plan {
                    pushes: Vec::new(),
                    next_dfa_state: transition.to,
                    type_: t,
                    debug_text: debug_text,
                });
            },
            NFATransitionType::Nonterminal(node_id) => {
                let first_plan = &first_plans[&node_id];
                if let FirstPlan::Calculated(p) = first_plan {
                    plans.extend(p.iter().map(|(k, v)| (
                        *k, nest_plan(v, node_id, transition.to))));
                } else {
                    unreachable!();
                }
            },
            NFATransitionType::Keyword(keyword) => {
                let t = keywords.get_squashed(keyword).unwrap();
                plans.insert(t, Plan {
                    pushes: Vec::new(),
                    next_dfa_state: transition.to,
                    type_: t,
                    debug_text: keyword,
                });
            },
        }
    }
    plans
}

fn nest_plan(plan: &Plan, new_node_id: InternalNodeType, next_dfa_state: DFAStateId) -> Plan {
    let mut pushes = plan.pushes.clone();
    pushes.insert(0, (new_node_id, plan.next_dfa_state));
    Plan {
        pushes: pushes,
        next_dfa_state: next_dfa_state,
        // TODO isn't this redundant  with the hashmap insertion?
        type_: plan.type_,
        debug_text: plan.debug_text
    }
}

fn nonterminal_to_str(nonterminal_map: &InternalStrToNode, nonterminal: InternalNodeType) -> &str {
    for (k, v) in nonterminal_map {
        if nonterminal == *v {
            return *k
        }
    }
    panic!("Something is very wrong, integer not found");
}
