use std::collections::{HashMap, HashSet};
use std::iter::repeat;
use std::fmt;

use crate::grammar::{InternalNode, Token, CodeIndex};

pub const NODE_START: u16 = 1<<15;

type SquashedTransitions = HashMap<InternalSquashedType, Plan>;
pub type Automatons = HashMap<InternalNodeType, RuleAutomaton>;
pub type InternalStrToToken = HashMap<&'static str, InternalTokenType>;
pub type InternalStrToNode = HashMap<&'static str, InternalNodeType>;
pub type RuleMap = HashMap<InternalNodeType, (&'static str, Rule)>;


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
    NodeMayBeOmitted(&'static Rule),
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

#[derive(Debug, Clone, Copy, Hash, PartialEq, Eq)]
pub struct DFAStateId(pub usize);

// NFA = nondeterministic finite automaton
#[derive(Debug)]
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
    pub node_may_be_omitted: bool,

    // This is the important part that will be used by the parser. The rest is
    // just there to generate this information.
    pub transition_to_plan: SquashedTransitions,
    pub from_rule: &'static str,
}

#[derive(Debug, Clone, Copy, Hash, Eq, PartialEq)]
enum TransitionType {
    Terminal(InternalTokenType, &'static str),
    Nonterminal(InternalNodeType),
    Keyword(&'static str),
    PositiveLookaheadStart,
    NegativeLookaheadStart,
    LookaheadEnd,
}

#[derive(Debug)]
struct NFATransition {
    type_: Option<TransitionType>,
    to: NFAStateId,
}

#[derive(Debug, Clone)]
struct DFATransition {
    type_: TransitionType,
    to: DFAStateId,
}

#[derive(Debug, Clone, Copy, PartialEq)]
pub enum StackMode<> {
    NegativeLookahead,
    PositiveLookahead,
    Alternative(DFAStateId),
    Normal,
}

#[derive(Debug, Clone)]
pub struct Push {
    pub node_type: InternalNodeType,
    pub to_state: DFAStateId,
    pub stack_mode: StackMode,
}

#[derive(Debug, Clone)]
pub struct Plan {
    pub pushes: Vec<Push>,
    pub next_dfa_state: DFAStateId,
    pub type_: InternalSquashedType,
    pub debug_text: &'static str,
}

enum FirstPlan {
    Calculated(SquashedTransitions, bool),
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
    name: &'static str,
    node_may_be_omitted: bool,
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
                    self.add_transition(
                        start, end,
                        Some(TransitionType::Terminal(t, string)),
                    );
                } else if let Some(&t) = nonterminal_map.get(string) {
                    self.add_transition(
                        start, end,
                        Some(TransitionType::Nonterminal(t)),
                    );
                } else {
                    panic!("No terminal / nonterminal found for {:?}; token_map = {:?}; node_map ={:?}",
                           string, terminal_map, nonterminal_map);
                }
                (start, end)
            },
            Keyword(string) => {
                let (start, end) = self.new_nfa_states();
                self.add_transition(
                    start, end, Some(TransitionType::Keyword(string)));
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
                let (start, end) = build(self, rule1);
                let (new_start, new_end) = self.new_nfa_states();
                self.add_transition(new_start, start, Some(TransitionType::NegativeLookaheadStart));
                self.add_transition(end, new_end, Some(TransitionType::LookaheadEnd));
                (new_start, new_end)
            },
            PositiveLookahead(rule1) => {
                let (start, end) = build(self, rule1);
                let (new_start, new_end) = self.new_nfa_states();
                self.add_transition(new_start, start, Some(TransitionType::PositiveLookaheadStart));
                self.add_transition(end, new_end, Some(TransitionType::LookaheadEnd));
                (new_start, new_end)
            }
            // TODO Cut is ignored for now.
            Cut(rule1, rule2) | Next(rule1, rule2) => {
                let (start1, end1) = build(self, rule1);
                let (start2, end2) = build(self, rule2);
                self.add_empty_transition(end1, start2);
                (start1, end2)
            }
            NodeMayBeOmitted(rule1) => {
                self.node_may_be_omitted = true;
                build(self, rule1)
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
            self.nfa_states.push(NFAState {
                transitions: Default::default(),
            });
            NFAStateId(self.nfa_states.len() - 1)
        };
        (new(), new())
    }

    fn add_transition(&mut self, start: NFAStateId, to: NFAStateId,
                      type_: Option<TransitionType>) {
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
                // Mode changes need to have separate DFA states as well.
                if transition.type_ == None {
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
        // Since we have the intial `starts` grouped by the mode change, we can
        // now just check for all ε-transitions that have no mode change.
        let grouped_nfas = self.group_nfas(starts);
        for (i, dfa_state) in dfa_states.iter().enumerate() {
            if dfa_state.nfa_set == grouped_nfas {
                return DFAStateId(i);
            }
        }
        let is_final = grouped_nfas.contains(&end)
            || grouped_nfas.iter().any(|nfa_id| self.get_nfa_state(*nfa_id).is_lookahead_end());
        dfa_states.push(DFAState {
            nfa_set: grouped_nfas,
            is_final: is_final,
            is_calculated: false,
            node_may_be_omitted: self.node_may_be_omitted,
            from_rule: self.name,
            transition_to_plan: Default::default(),
            transitions: Default::default(),
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

        let mut grouped_transitions = HashMap::<_, Vec<NFAStateId>>::new();
        let mut nfa_list: Vec<NFAStateId> = state.nfa_set.iter().cloned().collect();
        // Need to sort the list by ID to make sure that the lower IDs have higher priority. The
        // rules always generate NFAStates in order of priority.
        nfa_list.sort_by_key(|x| x.0);
        for nfa_state_id in nfa_list  {
            let n = &self.get_nfa_state(nfa_state_id);
            for transition in &n.transitions {
                // The nodes that have no proper type are only interesting if there's a mode
                // change.
                if let Some(t) = transition.type_ {
                    let t = transition.type_.unwrap();
                    match grouped_transitions.get_mut(&(t)).and_then(
                        |x| if transition.is_terminal_nonterminal_or_keyword() {
                                Some(x)
                            } else {
                                None
                            }
                    ) {

                        Some(v) => v.push(transition.to),
                        None => {grouped_transitions.insert(t, vec!(transition.to));},
                    }
                }
            }
        }

        let mut transitions = Vec::new();
        for (type_, grouped_starts) in grouped_transitions {
            let new_dfa_id = self.nfa_to_dfa(dfa_states, grouped_starts, end);
            transitions.push(DFATransition {
                type_: type_,
                to: new_dfa_id,
            });
        }

        dfa_states[dfa_id.0].transitions = transitions;
        dfa_states[dfa_id.0].is_calculated = true;
        for transition in dfa_states[dfa_id.0].transitions.clone() {
            self.construct_powerset_for_dfa(dfa_states, transition.to, end)
        }
    }

    pub fn illustrate_dfas(&self, nonterminal_map: &InternalStrToNode) -> String {
        // Sorry for this code, it's really ugly, but since it's really only for debugging
        // purposes, I don't care too much. ~dave
        let format_index = |id: usize, dfa: &DFAState|
            (id + 1).to_string() + (if dfa.is_final {" (final)"} else {""});
        let mut out_strings = vec!();
        let mut transition_list = vec!();
        let mut first_line = vec!(format_index(0, &self.dfa_states[0]), "#".to_owned());
        first_line.extend(repeat("o".to_owned()).take(self.dfa_states[0].transitions.len())
                          .collect::<Vec<_>>());
        out_strings.push(first_line);
        for (i, dfa) in self.dfa_states.iter().enumerate() {
            if i + 1 == self.dfa_states.len() {
                // Was already displayed.
                break
            }

            while transition_list.last() == Some(&None) {
                transition_list.pop();
            }
            for t in &dfa.transitions {
                transition_list.push(Some((
                    t.to,
                    match t.type_ {
                        TransitionType::Terminal(_, s) => {s.to_owned()},
                        TransitionType::Nonterminal(t) => {
                            nonterminal_to_str(nonterminal_map, t).to_owned()},
                        TransitionType::Keyword(s) => {format!("{:#?}", s)},
                        TransitionType::PositiveLookaheadStart => {"POS_LOOK".to_owned()},
                        TransitionType::LookaheadEnd => {"LOOK_END".to_owned()},
                        TransitionType::NegativeLookaheadStart => {"NEG_LOOK".to_owned()},
                    }
                )));
            }

            let mut v1 = vec!("".to_owned(), "#".to_owned());
            let mut v2 = vec!("".to_owned(), "#".to_owned());
            let mut v3 = vec!("".to_owned(), "#".to_owned());
            let mut v4 = vec!(format_index(i + 1, &self.dfa_states[i + 1]), "#".to_owned());
            let len = transition_list.len();
            for t in transition_list.iter_mut() {
                if let Some((to, s)) = t.clone() {
                    v1.push("|".to_owned());
                    v2.push(if s.is_empty() {"|".to_owned()} else {s});
                    t.replace((to, "".to_owned()));
                    v3.push(if to.0 <= i + 1 {
                                t.take();
                                if to.0 == i + 1 {
                                    "|".to_owned()
                                } else {
                                    format!("-> {}", to.0 + 1)
                                }
                            } else {
                                "|".to_owned()
                            }
                    );
                    v4.push((
                        if to.0 == i + 1 {
                            "o"
                        } else if to.0 <= i {
                            ""
                        } else {
                            "|"
                        }).to_owned());
                } else {
                    v1.push("".to_owned());
                    v2.push("".to_owned());
                    v3.push("".to_owned());
                    v4.push("".to_owned());
                }
            }
            out_strings.push(v1);
            out_strings.push(v2);
            out_strings.push(v3);
            out_strings.push(v4);
        }
        let mut column_widths = vec!();
        for line in &out_strings {
            for (i, field) in line.iter().enumerate() {
                match column_widths.get(i) {
                    None => column_widths.push(field.len()),
                    Some(f) => if column_widths[i] < field.len() {column_widths[i] = field.len()},
                };
            }
        }
        let mut s = String::new();
        for line in &out_strings {
            for (field, max_width) in line.iter().zip(&column_widths) {
                s += &format!("{:^width$}", field, width=max_width + 2);
            }
            s += "\n";
        }
        return s
    }
}

impl NFAState {
    fn is_lookahead_end(&self) -> bool {
        self.transitions.iter().any(|t| t.type_ == Some(TransitionType::LookaheadEnd))
    }
}

impl NFATransition {
    fn is_terminal_nonterminal_or_keyword(&self) -> bool {
        self.type_.map_or(false, |t| match t {
            TransitionType::Nonterminal(_)
            | TransitionType::Terminal(_, _)
            | TransitionType::Keyword(_) => true,
            _ => false,
        })
    }
}

pub fn generate_automatons(nonterminal_map: &InternalStrToNode, terminal_map: &InternalStrToToken,
                           rules: &RuleMap) -> (Automatons, Keywords) {
    let mut keywords = Keywords {
        // We need to start the numbers of keywords after tokens. Keyword ID's therefore never
        // clash with Token IDs (both are of type SquashedInternalType).
        counter: terminal_map.len(),
        .. Default::default()
    };
    let mut automatons = HashMap::new();
    let dfa_counter = 0;
    for (internal_type, (rule_name, rule)) in rules {
        let mut automaton = RuleAutomaton {
            type_: *internal_type,
            name: rule_name,
            .. Default::default()
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

        // There should never be a case where a first plan is an empty production.
        // There should always be child nodes, otherwise the data structures won't work.
        let automaton = &automatons[&rule_label];
        if automaton.dfa_states[0].is_final {
            panic!("The rule \"{}\" is allowed to have no child nodes", automaton.name);
        }
    }
    // Optimize and calculate all plans
    for rule_label in &rule_labels {
        // Now optimize the whole thing
        // TODO proper transitions for operators/names
        let automaton: *const RuleAutomaton = automatons.get(rule_label).unwrap();
        for (i, dfa_state) in automatons.get_mut(rule_label).unwrap().dfa_states.iter_mut().enumerate() {
            // The dfa_states need to refer to themselves, having it unsafe
            // here is the easiest way.
            dfa_state.transition_to_plan = create_all_plans(
                &keywords, unsafe {&*automaton}, &dfa_state, &first_plans);

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
    if let None = first_plans.get(&automaton_key) {
        first_plans.insert(automaton_key, FirstPlan::Calculating);
        let (plans, is_left_recursive) = first_plans_for_dfa(
            nonterminal_map, keywords, automatons, first_plans, automaton, &automaton.dfa_states[0]);

        if is_left_recursive {
            if plans.len() == 0 {
                panic!("The grammar contains left recursion without an \
                        alternative for rule {:?}",
                       nonterminal_to_str(nonterminal_map, automaton.type_));
            }
        }
        first_plans.insert(automaton_key, FirstPlan::Calculated(plans, is_left_recursive));
    }
}

fn first_plans_for_dfa(nonterminal_map: &InternalStrToNode,
                       keywords: &Keywords,
                       automatons: &Automatons,
                       first_plans: &mut HashMap<InternalNodeType, FirstPlan>,
                       automaton: &RuleAutomaton,
                       dfa_state: &DFAState) -> (SquashedTransitions, bool) {
    let mut plans = HashMap::new();
    let mut is_left_recursive = false;
    for transition in &dfa_state.transitions {
        match transition.type_ {
            TransitionType::Terminal(type_, debug_text) => {
                let t = type_.to_squashed();
                if plans.contains_key(&t) {
                    panic!("ambigous! {}", dfa_state.from_rule);
                }
                plans.insert(t, Plan {
                    pushes: Vec::new(),
                    next_dfa_state: transition.to,
                    type_: t,
                    debug_text: debug_text,
                });
            },
            TransitionType::Nonterminal(node_id) => {
                if let Some(FirstPlan::Calculating) = first_plans.get(&node_id) {
                    if node_id != automaton.type_ {
                        panic!("Indirect left recursion not supported (in rule {:?})",
                               nonterminal_to_str(nonterminal_map, automaton.type_));
                    }
                    is_left_recursive = true;
                    continue
                }
                create_first_plans(nonterminal_map, keywords, first_plans, &automatons, node_id);
                match &first_plans[&node_id] {
                    FirstPlan::Calculated(transitions, is_left_recursive) => {
                        for (t, nested_plan) in transitions {
                            if plans.contains_key(&t) {
                                panic!("ambigous2! {} in {}", nested_plan.debug_text, dfa_state.from_rule);
                            }
                            plans.insert(*t, nest_plan(nested_plan, node_id, 
                                                       transition.to, StackMode::Normal));
                        }
                    },
                    FirstPlan::Calculating => {unreachable!()},
                }
            },
            TransitionType::Keyword(keyword) => {
                let t = keywords.get_squashed(keyword).unwrap();
                if plans.contains_key(&t) {
                    panic!("ambigous3! {}", dfa_state.from_rule);
                }
                plans.insert(t, Plan {
                    pushes: Vec::new(),
                    next_dfa_state: transition.to,
                    type_: t,
                    debug_text: keyword,
                });
            },
            TransitionType::PositiveLookaheadStart | TransitionType::NegativeLookaheadStart => {
                let (inner_plans, inner_is_left_recursive) = first_plans_for_dfa(
                    nonterminal_map, keywords, automatons, first_plans,
                    automaton, &automaton.dfa_states[transition.to.0]);
                if inner_is_left_recursive {
                    panic!("Left recursion with lookaheads is not supported (in rule {:?})",
                           nonterminal_to_str(nonterminal_map, automaton.type_));
                }
                plans.extend(create_lookahead_plans(automaton, transition, &inner_plans));
            },
            TransitionType::LookaheadEnd => {
                unreachable!();
            },
        }
    }
    (plans, is_left_recursive)
}

fn create_lookahead_plans(automaton: &RuleAutomaton, transition: &DFATransition,
                          inner_plans: &SquashedTransitions) -> SquashedTransitions {
    let mode = match transition.type_ {
        TransitionType::PositiveLookaheadStart => StackMode::PositiveLookahead,
        TransitionType::NegativeLookaheadStart => StackMode::NegativeLookahead,
        _ => unreachable!()
    };
    inner_plans.iter().map(
        |(k, plan)| (*k, nest_plan(
                plan, automaton.type_, search_lookahead_end(
                    automaton, plan.next_dfa_state
                ), mode
        ))
    ).collect()
}

fn create_all_plans(keywords: &Keywords, automaton: &RuleAutomaton, dfa_state: &DFAState,
                    first_plans: &HashMap<InternalNodeType, FirstPlan>) -> SquashedTransitions {
    let mut plans = HashMap::new();
    for transition in &dfa_state.transitions {
        match transition.type_ {
            TransitionType::Terminal(type_, debug_text) => {
                let t = type_.to_squashed();
                plans.insert(t, Plan {
                    pushes: Vec::new(),
                    next_dfa_state: transition.to,
                    type_: t,
                    debug_text: debug_text,
                });
            },
            TransitionType::Nonterminal(node_id) => {
                let first_plan = &first_plans[&node_id];
                if let FirstPlan::Calculated(p, _) = first_plan {
                    plans.extend(p.iter().map(|(k, v)| (
                        *k, nest_plan(v, node_id, transition.to, StackMode::Normal))));
                } else {
                    unreachable!();
                }
            },
            TransitionType::Keyword(keyword) => {
                let t = keywords.get_squashed(keyword).unwrap();
                plans.insert(t, Plan {
                    pushes: Vec::new(),
                    next_dfa_state: transition.to,
                    type_: t,
                    debug_text: keyword,
                });
            },
            TransitionType::PositiveLookaheadStart | TransitionType::NegativeLookaheadStart => {
                let inner_plans = create_all_plans(
                    &keywords, automaton, &automaton.dfa_states[transition.to.0],
                    &first_plans);
                plans.extend(create_lookahead_plans(automaton, transition, &inner_plans));
            },
            TransitionType::LookaheadEnd => {
                // No plans needed.
            },
        }
    }
    plans
}

fn nest_plan(plan: &Plan, new_node_id: InternalNodeType, next_dfa_state: DFAStateId,
             mode: StackMode) -> Plan {
    let mut pushes = plan.pushes.clone();
    pushes.insert(0, Push {
        node_type: new_node_id,
        to_state: plan.next_dfa_state,
        stack_mode: mode,
    });
    Plan {
        pushes: pushes,
        next_dfa_state: next_dfa_state,
        // TODO isn't this redundant  with the hashmap insertion?
        type_: plan.type_,
        debug_text: plan.debug_text,
    }
}

fn search_lookahead_end(automaton: &RuleAutomaton, dfa_state_id: DFAStateId) -> DFAStateId {
    let mut already_checked = HashSet::new();
    already_checked.insert(dfa_state_id);

    fn search(already_checked: &mut HashSet<DFAStateId>, automaton: &RuleAutomaton, dfa_state_id: DFAStateId) -> DFAStateId {
        for transition in &automaton.dfa_states[dfa_state_id.0].transitions {
            match transition.type_ {
                TransitionType::LookaheadEnd => return transition.to,
                TransitionType::PositiveLookaheadStart | TransitionType::NegativeLookaheadStart
                    => unimplemented!(),
                _ => {
                    if !already_checked.contains(&transition.to) {
                        already_checked.insert(transition.to);
                        // It is a bit weird that this return works. It probably works, but maybe
                        // wouldn't in some weird cases. We can still fix it then if necessary. 
                        return search(already_checked, automaton, transition.to);
                    }
                }
            }
        }
        unreachable!()
    }
    return search(&mut already_checked, automaton, dfa_state_id)
}

fn nonterminal_to_str(nonterminal_map: &InternalStrToNode, nonterminal: InternalNodeType) -> &str {
    for (k, v) in nonterminal_map {
        if nonterminal == *v {
            return *k
        }
    }
    panic!("Something is very wrong, integer not found");
}
