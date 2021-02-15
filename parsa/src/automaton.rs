use std::collections::{HashMap, HashSet};
use std::iter::repeat;
use std::fmt;
use std::pin::Pin;

use crate::grammar::{InternalNode, Token, CodeIndex};

pub const NODE_START: u16 = 1<<15;

type SquashedTransitions = HashMap<InternalSquashedType, Plan>;
pub type Automatons = HashMap<InternalNodeType, RuleAutomaton>;
pub type InternalStrToToken = HashMap<&'static str, InternalTokenType>;
pub type InternalStrToNode = HashMap<&'static str, InternalNodeType>;
pub type RuleMap = HashMap<InternalNodeType, (&'static str, Rule)>;
type FirstPlans = HashMap<InternalNodeType, FirstPlan>;
type DFAStates = Vec<Pin<Box<DFAState>>>;


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

#[derive(Debug, Clone, Copy, Hash, PartialEq, Eq, Default)]
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
    list_index: DFAStateId,  // The index in the dfa_states vec in the automaton.

    // This is the important part that will be used by the parser. The rest is
    // just there to generate this information.
    pub transition_to_plan: SquashedTransitions,
    pub from_rule: &'static str,
}

// Safe, because dfas are behind a pinned box that never gets changed
unsafe impl Sync for DFAState {}
unsafe impl Send for DFAState {}

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

#[derive(Debug, Clone, Copy)]
struct DFATransition {
    type_: TransitionType,
    to: *mut DFAState,
}

#[derive(Debug, Clone, Copy, PartialEq)]
pub enum StackMode {
    NegativeLookahead,
    PositiveLookahead,
    Alternative(*const Plan),
    Normal,
}

#[derive(Debug, Clone)]
pub struct Push {
    pub node_type: InternalNodeType,
    pub next_dfa: *const DFAState,
    pub stack_mode: StackMode,
}

#[derive(Debug, Clone)]
pub struct Plan {
    pub pushes: Vec<Push>,
    pub next_dfa: *const DFAState,
    pub type_: InternalSquashedType,
    pub is_left_recursive: bool,
    pub debug_text: &'static str,
}

// Safe, because plan pointers are behind a pinned box that never gets changed
unsafe impl Sync for Plan {}
unsafe impl Send for Plan {}

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
    pub type_: InternalNodeType,
    nfa_states: Vec<NFAState>,
    pub dfa_states: DFAStates,
    name: &'static str,
    node_may_be_omitted: bool,
    nfa_end_id: NFAStateId,
    fallback_plans: Vec<Pin<Box<Plan>>>,
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

    fn nfa_to_dfa(&self, dfa_states: &mut DFAStates, starts: Vec<NFAStateId>,
                  end: NFAStateId) -> *mut DFAState {
        // Since we have the intial `starts` grouped by the mode change, we can
        // now just check for all ε-transitions that have no mode change.
        let grouped_nfas = self.group_nfas(starts);
        for (i, dfa_state) in dfa_states.iter_mut().enumerate() {
            if dfa_state.nfa_set == grouped_nfas {
                return dfa_state as &mut DFAState;
            }
        }
        let is_final = grouped_nfas.contains(&end)
            || grouped_nfas.iter().any(|nfa_id| self.get_nfa_state(*nfa_id).is_lookahead_end());
        dfa_states.push(Pin::new(Box::new(DFAState {
            nfa_set: grouped_nfas,
            is_final: is_final,
            is_calculated: false,
            list_index: DFAStateId(dfa_states.len()),
            node_may_be_omitted: self.node_may_be_omitted,
            from_rule: self.name,
            transition_to_plan: Default::default(),
            transitions: Default::default(),
        })));
        dfa_states.last_mut().unwrap() as &mut DFAState
    }

    fn construct_powerset(&mut self, start: NFAStateId, end: NFAStateId) -> DFAStates {
        let mut dfa_states = Vec::new();
        let dfa = self.nfa_to_dfa(&mut dfa_states, vec!(start), end);
        self.construct_powerset_for_dfa(&mut dfa_states, dfa, end);
        dfa_states
    }

    fn construct_powerset_for_dfa(&mut self, dfa_states: &mut DFAStates,
                                  dfa: *mut DFAState, end: NFAStateId) {
        let state = unsafe {&mut *dfa};
        if state.is_calculated {
            return
        }

        use std::mem;
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

        state.transitions = transitions;
        state.is_calculated = true;
        let transitions = state.transitions.clone();
        for transition in transitions {
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
                    t.get_next_dfa().list_index,
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

impl DFAState {
    fn is_lookahead_end(&self) -> bool {
        self.transitions.iter().any(|t| t.type_ == TransitionType::LookaheadEnd)
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

impl DFATransition {
    pub fn get_next_dfa(&self) -> &DFAState{
        unsafe {&*self.to}
    }
}

impl Plan {
    pub fn get_next_dfa(&self) -> &DFAState{
        unsafe {&*self.next_dfa}
    }
}

impl Push {
    pub fn get_next_dfa(&self) -> &DFAState{
        unsafe {&*self.next_dfa}
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
        automaton.nfa_end_id = end;
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
        let automaton = unsafe {&mut *(automatons.get_mut(rule_label).unwrap() as *mut RuleAutomaton)};
        for (i, mut dfa_state) in automatons.get_mut(rule_label).unwrap().dfa_states.iter_mut().enumerate() {
            // The dfa_states need to refer to themselves, having it unsafe
            // here is the easiest way.
            dfa_state.transition_to_plan = create_all_plans(
                &keywords, *rule_label, &dfa_state, &first_plans);
        }

        for (i, mut dfa_state) in automatons.get_mut(rule_label).unwrap().dfa_states.iter_mut().enumerate() {
            let recursion_plans = create_left_recursion_plans(
                automaton, &mut dfa_state, &first_plans);
            dfa_state.transition_to_plan.extend(recursion_plans);
        }
    }
    (automatons, keywords)
}

fn create_first_plans(nonterminal_map: &InternalStrToNode,
                      keywords: &Keywords,
                      first_plans: &mut FirstPlans,
                      automatons: &mut Automatons,
                      automaton_key: InternalNodeType) {
    if let None = first_plans.get(&automaton_key) {
        first_plans.insert(automaton_key, FirstPlan::Calculating);
        let (plans, is_left_recursive) = first_plans_for_dfa(
            nonterminal_map, keywords, automatons, first_plans, automaton_key, DFAStateId(0));

        if is_left_recursive {
            if plans.len() == 0 {
                panic!("The grammar contains left recursion without an \
                        alternative for rule {:?}",
                       nonterminal_to_str(nonterminal_map, automaton_key));
            }
        }
        first_plans.insert(automaton_key, FirstPlan::Calculated(plans, is_left_recursive));
    }
}

fn first_plans_for_dfa(nonterminal_map: &InternalStrToNode,
                       keywords: &Keywords,
                       automatons: &mut Automatons,
                       first_plans: &mut FirstPlans,
                       automaton_key: InternalNodeType,
                       dfa_id: DFAStateId) -> (SquashedTransitions, bool) {
    let mut conflict_tokens = HashSet::new();
    let mut conflict_transitions = HashSet::new();
    let mut plans = HashMap::new();
    let mut is_left_recursive = false;
    // It is safe to get the dfa_state here, because they are pinned in a list that is insert only.
    let dfa_state = unsafe {&*(&automatons[&automaton_key].dfa_states[dfa_id.0] as &DFAState as *const DFAState)};
    for transition in &dfa_state.transitions {
        match transition.type_ {
            TransitionType::Terminal(type_, debug_text) => {
                let t = type_.to_squashed();
                if plans.contains_key(&t) {
                    panic!("ambigous! {}", dfa_state.from_rule);
                }
                plans.insert(t, (transition, Plan {
                    pushes: Vec::new(),
                    next_dfa: transition.to,
                    type_: t,
                    debug_text: debug_text,
                    is_left_recursive: false,
                }));
            },
            TransitionType::Nonterminal(node_id) => {
                if let Some(FirstPlan::Calculating) = first_plans.get(&node_id) {
                    if node_id != automaton_key {
                        panic!("Indirect left recursion not supported (in rule {:?})",
                               nonterminal_to_str(nonterminal_map, automaton_key));
                    }
                    is_left_recursive = true;
                    continue
                }
                create_first_plans(nonterminal_map, keywords, first_plans, automatons, node_id);
                match &first_plans[&node_id] {
                    FirstPlan::Calculated(transitions, is_left_recursive) => {
                        for (t, nested_plan) in transitions {
                            if conflict_tokens.contains(t) {
                                conflict_transitions.insert(transition.type_);
                            } else {
                                if let Some((&t_x, _)) = plans.get(t) {
                                    if t_x.type_ != transition.type_ {
                                        plans.remove(t);
                                        conflict_tokens.insert(*t);
                                        conflict_transitions.insert(transition.type_);
                                        conflict_transitions.insert(t_x.type_);
                                        debug_assert!(conflict_transitions.len() == 2);
                                        continue;
                                    }
                                }
                                plans.insert(*t, (
                                    transition, nest_plan(nested_plan, node_id,
                                                          transition.to, StackMode::Normal)));
                            }
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
                plans.insert(t, (transition, Plan {
                    pushes: Vec::new(),
                    next_dfa: transition.to,
                    type_: t,
                    debug_text: keyword,
                    is_left_recursive: false,
                }));
            },
            TransitionType::PositiveLookaheadStart => {
                let (inner_plans, inner_is_left_recursive) = first_plans_for_dfa(
                    nonterminal_map, keywords, automatons, first_plans,
                    automaton_key, transition.get_next_dfa().list_index);
                if inner_is_left_recursive {
                    panic!("Left recursion with lookaheads is not supported (in rule {:?})",
                           nonterminal_to_str(nonterminal_map, automaton_key));
                }
                if inner_plans.iter().any(|(key, _)| plans.contains_key(&key)) {
                    panic!("ambigous4");
                }
                plans.extend::<Vec<_>>(
                    create_lookahead_plans(automaton_key, transition, &inner_plans).iter().map(
                        |(&t, plan)| (t, (transition, plan.clone()))
                    ).collect()
                );
            },
            TransitionType::NegativeLookaheadStart => {
                unimplemented!("It is currently not supported to have negative \
                                lookaheads as a first token in a rule")
            },
            TransitionType::LookaheadEnd => {
                unreachable!();
            },
        }
    }

    for c in &conflict_tokens {
        debug_assert!(!plans.contains_key(c));
    }

    let mut result: SquashedTransitions
        = plans.iter().map(|(&t, (_, plan))| (t, plan.clone())).collect();
    if conflict_tokens.len() > 0 {
        let automaton = automatons.get_mut(&automaton_key).unwrap();
        let (start, end) = split_tokens(automaton, &dfa_state, conflict_transitions);
        let t = automaton.type_;
        for dfa_id in (start..automaton.dfa_states.len()).rev() {
            let (new_plans, left_recursive) = first_plans_for_dfa(
                nonterminal_map, keywords, automatons, first_plans, automaton_key, DFAStateId(dfa_id)
            );
            debug_assert!(!left_recursive);
            for (transition, mut new_plan) in new_plans {
                if conflict_tokens.contains(&transition) {
                    if let Some(fallback_plan) = result.remove(&transition) {
                        let automaton = automatons.get_mut(&automaton_key).unwrap();
                        // This sets a const pointer on the fallback plan. This is only save,
                        // because the plans are not touched after they have been generated.
                        automaton.fallback_plans.push(Pin::new(Box::new(fallback_plan)));
                        new_plan = nest_plan(
                            &new_plan, t, end,
                            StackMode::Alternative(automaton.fallback_plans.last().unwrap() as &Plan));
                    }
                    //dbg!(&transition, &new_plan);
                    result.insert(transition, new_plan);
                }
            }
        }
    }
    (result, is_left_recursive)
}

fn create_lookahead_plans(automaton_key: InternalNodeType, transition: &DFATransition,
                          inner_plans: &SquashedTransitions) -> SquashedTransitions {
    let mode = match transition.type_ {
        TransitionType::PositiveLookaheadStart => StackMode::PositiveLookahead,
        TransitionType::NegativeLookaheadStart => StackMode::NegativeLookahead,
        _ => unreachable!()
    };
    inner_plans.iter().map(
        |(k, plan)| (*k, nest_plan(
            plan, automaton_key, search_lookahead_end(plan.get_next_dfa()), mode
        ))
    ).collect()
}

fn create_all_plans(keywords: &Keywords, automaton_key: InternalNodeType, dfa_state: &DFAState,
                    first_plans: &FirstPlans) -> SquashedTransitions {
    let mut plans = HashMap::new();
    for transition in &dfa_state.transitions {
        match transition.type_ {
            TransitionType::Terminal(type_, debug_text) => {
                let t = type_.to_squashed();
                plans.insert(t, Plan {
                    pushes: Vec::new(),
                    next_dfa: transition.to,
                    type_: t,
                    debug_text: debug_text,
                    is_left_recursive: false,
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
                    next_dfa: transition.to,
                    type_: t,
                    debug_text: keyword,
                    is_left_recursive: false,
                });
            },
            TransitionType::PositiveLookaheadStart | TransitionType::NegativeLookaheadStart => {
                let inner_plans = create_all_plans(
                    &keywords, automaton_key, transition.get_next_dfa(),
                    &first_plans);
                plans.extend(create_lookahead_plans(automaton_key, transition, &inner_plans));
            },
            TransitionType::LookaheadEnd => {
                // No plans needed.
            },
        }
    }
    plans
}

fn create_left_recursion_plans(automaton: &RuleAutomaton, dfa_state: &mut DFAState,
                               first_plans: &FirstPlans) -> SquashedTransitions {
    let mut plans = HashMap::new();
    if dfa_state.is_final && !dfa_state.is_lookahead_end(){
        // DFAStates that are the end of a lookahead are ignored here, because left recursion is
        // not allowed for lookaheads and they get a separate stack node anyway.
        match first_plans[&automaton.type_] {
            FirstPlan::Calculated(_, is_left_recursive) => {
                if is_left_recursive {
                    for transition in &automaton.dfa_states[0].transitions {
                        match transition.type_ {
                            TransitionType::Nonterminal(node_id) => {
                                if node_id == automaton.type_ {
                                    for (&t, p) in &transition.get_next_dfa().transition_to_plan {
                                        plans.insert(t, Plan {
                                            pushes: p.pushes.clone(),
                                            next_dfa: p.next_dfa,
                                            type_: t,
                                            debug_text: p.debug_text,
                                            is_left_recursive: true,
                                        });
                                    }
                                }
                            },
                            _ => {},
                        }
                    }
                }
            },
            _ => unreachable!(),
        }
    }
    plans
}

fn nest_plan(plan: &Plan, new_node_id: InternalNodeType, next_dfa: *const DFAState,
             mode: StackMode) -> Plan {
    let mut pushes = plan.pushes.clone();
    pushes.insert(0, Push {
        node_type: new_node_id,
        next_dfa: plan.next_dfa,
        stack_mode: mode,
    });
    Plan {
        pushes: pushes,
        next_dfa: next_dfa,
        // TODO isn't this redundant with the hashmap insertion?
        type_: plan.type_,
        debug_text: plan.debug_text,
        is_left_recursive: false,
    }
}

fn search_lookahead_end(dfa_state: &DFAState) -> *const DFAState {
    let mut already_checked = HashSet::new();
    already_checked.insert(dfa_state.list_index);

    fn search(already_checked: &mut HashSet<DFAStateId>, dfa_state: &DFAState) -> *const DFAState {
        for transition in &dfa_state.transitions {
            match transition.type_ {
                TransitionType::LookaheadEnd => return transition.to,
                TransitionType::PositiveLookaheadStart | TransitionType::NegativeLookaheadStart
                    => unimplemented!(),
                _ => {
                    let to_dfa = transition.get_next_dfa();
                    if !already_checked.contains(&to_dfa.list_index) {
                        already_checked.insert(to_dfa.list_index);
                        // It is a bit weird that this return works. It probably works, but maybe
                        // wouldn't in some weird cases. We can still fix it then if necessary. 
                        return search(already_checked, to_dfa);
                    }
                }
            }
        }
        unreachable!()
    }
    return search(&mut already_checked, dfa_state)
}

fn split_tokens(automaton: &mut RuleAutomaton, dfa: &DFAState,
                conflict_transitions: HashSet<TransitionType>) -> (usize, *const DFAState) {
    let mut transition_to_nfas = HashMap::<_, Vec<_>>::new();
    let mut nfas: Vec<_> = dfa.nfa_set.iter().collect();
    nfas.sort_by_key(|id| id.0);
    for &nfa_id in &nfas {
        let nfa = &automaton.nfa_states[nfa_id.0];
        for transition in &nfa.transitions {
            if let Some(t) = transition.type_ {
                if conflict_transitions.contains(&t) {
                    if let Some(list) = transition_to_nfas.get_mut(&t) {
                        list.push(nfa_id);
                    } else {
                        transition_to_nfas.insert(t, vec!(nfa_id));
                    }
                }
            }
        }
    }

    // TODO Fix rule automaton shit
    let x = unsafe {&mut *(automaton as *mut RuleAutomaton)};
    let end_dfa = automaton.nfa_to_dfa(&mut x.dfa_states, vec!(x.nfa_end_id), x.nfa_end_id);
    let first_new_index = automaton.dfa_states.len();

    let mut as_list: Vec<_> = transition_to_nfas.iter().map(|(_, nfa_ids)| nfa_ids.clone()).collect();
    while as_list.len() > 0 {
        as_list.sort_by_key(|nfa_ids| nfa_ids[0].0);
        let mut new_dfa_nfa_ids = vec!();
        if as_list.len() > 1 {
            let must_be_smaller = *as_list[1][0];
            debug_assert!(as_list[0].len() > 0);
            while let Some(&&nfa_id) = as_list[0].get(0) {
                // It should basically never happen that two transitions are possible from an
                // NFA. ε-moves are of course always possible.
                debug_assert!(nfa_id != must_be_smaller);
                if nfa_id.0 > must_be_smaller.0 {
                    break
                }
                new_dfa_nfa_ids.push(*as_list[0].remove(0));
            }
            if as_list[0].len() == 0 {
                as_list.remove(0);
            }
        } else {
            new_dfa_nfa_ids.extend(as_list.pop().unwrap().iter().cloned());
        }
        debug_assert!(new_dfa_nfa_ids.len() > 0);

        let dfa = automaton.nfa_to_dfa(&mut x.dfa_states, new_dfa_nfa_ids, x.nfa_end_id);
        automaton.construct_powerset_for_dfa(&mut x.dfa_states, dfa, x.nfa_end_id);
        //dbg!(x.dfa_states.len(), x.dfa_states.last().unwrap());
    }
    (first_new_index, end_dfa)
}

fn nonterminal_to_str(nonterminal_map: &InternalStrToNode, nonterminal: InternalNodeType) -> &str {
    for (k, v) in nonterminal_map {
        if nonterminal == *v {
            return *k
        }
    }
    panic!("Something is very wrong, integer not found");
}
