use std::collections::{HashMap, HashSet};

use crate::{
    middleware::{Predicate, StatementTmplArg, Value, ValueRef, Wildcard},
    solver::{
        engine::semi_naive::{Bindings, Fact, FactStore, SemiNaiveEngine},
        error::SolverError,
        ir::{Atom, PredicateIdentifier, Rule},
        metrics::{self, NoOpMetrics},
        semantics::materializer::Materializer,
    },
};

/// One blocking literal together with the bindings that were known
/// when we tried to join it.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct MissingLiteral {
    pub predicate: Predicate,
    pub args: Vec<StatementTmplArg>, // may still contain wildcards
}

pub struct MissingFactFinder<'a> {
    all_facts: &'a FactStore,
    materializer: &'a Materializer,
}

impl<'a> MissingFactFinder<'a> {
    pub fn new(all_facts: &'a FactStore, materializer: &'a Materializer) -> Self {
        Self {
            all_facts,
            materializer,
        }
    }

    /// Returns every literal that caused a join failure in every
    /// guarded rule reachable from the request.
    pub fn collect(&self, rules: &[Rule]) -> Vec<MissingLiteral> {
        let mut seen: HashSet<MissingLiteral> = HashSet::new();
        let mut ordered = Vec::new();

        let mut interim = Vec::new();
        for rule in rules {
            self.replay_rule(rule, &mut HashMap::new(), &mut interim);
        }

        for lit in interim.into_iter() {
            if seen.insert(lit.clone()) {
                ordered.push(lit);
            }
        }

        ordered
    }

    // ----------------------------------------------------------------
    // replay_rule ≈ stripped-down version of `perform_join`
    // ----------------------------------------------------------------
    fn replay_rule(&self, rule: &Rule, seed: &Bindings, out: &mut Vec<MissingLiteral>) {
        // Determine external (public) wildcards from rule head
        let externals: HashSet<Wildcard> = rule
            .head
            .terms
            .iter()
            .filter_map(|t| match t {
                StatementTmplArg::Wildcard(wc) => Some(wc.clone()),
                StatementTmplArg::AnchoredKey(pod_wc, _) => Some(pod_wc.clone()),
                _ => None,
            })
            .collect();

        self.replay_rule_inner(rule, seed, &externals, out);
    }

    fn replay_rule_inner(
        &self,
        rule: &Rule,
        seed: &Bindings,
        externals: &HashSet<Wildcard>,
        out: &mut Vec<MissingLiteral>,
    ) {
        let mut current: Vec<Bindings> = vec![seed.clone()];
        let mut invalid: HashSet<Wildcard> = HashSet::new();

        for atom in &rule.body {
            // If atom uses an invalidated wildcard, treat as failed immediately
            if self.atom_mentions_invalid(atom, &invalid) {
                out.push(self.partial_instantiate(atom, &current[0], externals));
                invalid.extend(self.wildcards_in_atom(atom));
                continue;
            }

            // Otherwise attempt join
            let mut next = Vec::new();
            for b in &current {
                let rel = self.fetch_relation(atom, b);
                for fact in &rel {
                    if let Some(nb) = self.unify(b, atom, &fact.args).ok().flatten() {
                        next.push(nb);
                    }
                }
            }

            if next.is_empty() {
                // Atom truly fails under current bindings
                out.push(self.partial_instantiate(atom, &current[0], externals));
                invalid.extend(self.wildcards_in_atom(atom));
                // We continue scanning tail so that later atoms that depend on these
                // wildcards are captured as failed.
                continue;
            }

            current = next;
        }
    }

    fn atom_mentions_invalid(&self, atom: &Atom, invalid: &HashSet<Wildcard>) -> bool {
        atom.terms.iter().any(|t| match t {
            StatementTmplArg::Wildcard(wc) => invalid.contains(wc),
            StatementTmplArg::AnchoredKey(wc, _) => invalid.contains(wc),
            _ => false,
        })
    }

    fn wildcards_in_atom(&self, atom: &Atom) -> HashSet<Wildcard> {
        let mut set = HashSet::new();
        for t in &atom.terms {
            match t {
                StatementTmplArg::Wildcard(wc) => {
                    set.insert(wc.clone());
                }
                StatementTmplArg::AnchoredKey(wc, _) => {
                    set.insert(wc.clone());
                }
                _ => {}
            }
        }
        set
    }

    // ------------------------------------------------------------
    // helpers (all borrowed from existing engine code)
    // ------------------------------------------------------------
    fn fetch_relation(&self, atom: &Atom, b: &Bindings) -> Vec<Fact> {
        match &atom.predicate {
            crate::solver::ir::PredicateIdentifier::Normal(pred) => {
                // EDB + IDB via materializer
                self.materializer
                    .materialize_statements(pred.clone(), atom.terms.clone(), b)
                    .unwrap_or_default()
                    .into_iter()
                    .collect()
            }
            crate::solver::ir::PredicateIdentifier::Magic { .. } => {
                // Magic predicates are IDB-only – look them up directly in the fact store.
                self.all_facts
                    .get(&atom.predicate)
                    .cloned()
                    .unwrap_or_default()
                    .into_iter()
                    .collect()
            }
            _ => Vec::new(),
        }
    }

    fn unify(
        &self,
        b: &Bindings,
        atom: &Atom,
        fact: &[ValueRef],
    ) -> Result<Option<Bindings>, SolverError> {
        SemiNaiveEngine::<NoOpMetrics>::default().unify(b, atom, fact)
    }

    fn partial_instantiate(
        &self,
        atom: &Atom,
        b: &Bindings,
        externals: &HashSet<Wildcard>,
    ) -> MissingLiteral {
        let args = atom
            .terms
            .iter()
            .map(|t| match t {
                StatementTmplArg::Wildcard(wc) if externals.contains(wc) => b
                    .get(wc)
                    .map(|v| StatementTmplArg::Literal(v.clone()))
                    .unwrap_or(t.clone()),
                StatementTmplArg::AnchoredKey(pod_wc, key) if externals.contains(pod_wc) => {
                    // Keep anchored key but ensure pod wildcard remains same placeholder
                    StatementTmplArg::AnchoredKey(pod_wc.clone(), key.clone())
                }
                _ => t.clone(),
            })
            .collect();
        MissingLiteral {
            predicate: match &atom.predicate {
                crate::solver::ir::PredicateIdentifier::Normal(p) => p.clone(),
                _ => unreachable!(),
            },
            args,
        }
    }
}
