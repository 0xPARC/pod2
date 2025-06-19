//! Implements a semi-naive bottom-up Datalog evaluation engine.
//!
//! The engine iteratively applies the rules from a `QueryPlan` to a `FactDB`
//! until no new facts can be derived, signifying that a fixed point has been
//! reached.

#![allow(dead_code)]
#![allow(clippy::arc_with_non_send_sync)]

use std::collections::{HashMap, HashSet};

use log::{debug, trace};

use crate::{
    middleware::{
        self, CustomPredicateRef, Predicate, RawValue, StatementTmplArg, TypedValue, ValueRef,
        Wildcard,
    },
    solver::{
        engine::{ProofRequest, QueryEngine},
        error::SolverError,
        ir::{self, Atom, Rule},
        planner::{Planner, QueryPlan},
        proof::{Justification, Proof, ProofNode},
        semantics::materializer::Materializer,
    },
};

/// A map from variables in a rule to their concrete values for a given solution.
pub type Bindings = HashMap<Wildcard, Value>;

/// Represents the source of a fact, distinguishing between base facts from the
/// database (EDB) and facts derived by rules (IDB). This is crucial for proof
/// reconstruction.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum FactSource {
    /// A fact that was derived by a rule during the evaluation.
    Derived,
    /// A fact that originated from the EDB (i.e., asserted in a POD).
    /// The `JustificationKind` hints at how it was justified (e.g., direct
    /// fact vs. a computation like `Equal(5,5)`).
    External(JustificationKind),
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum JustificationKind {
    Fact,
    Computation,
}

/// A single, concrete fact, represented as a tuple of values, with its source.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct Fact {
    pub args: Vec<ValueRef>,
    pub source: FactSource,
}

/// A relation is a set of facts.
pub type Relation = HashSet<Fact>;
/// A store for all derived facts, keyed by the predicate they belong to.
pub(super) type FactStore = HashMap<ir::PredicateIdentifier, Relation>;
/// A store for the provenance of derived facts, mapping a fact to the
/// rule and bindings that produced it.
pub(super) type ProvenanceStore =
    HashMap<(ir::PredicateIdentifier, Vec<ValueRef>), (Rule, Bindings)>;

/// Implements a semi-naive Datalog evaluation engine.
///
/// This engine evaluates rules iteratively, using the deltas from one iteration
/// to find new facts in the next, which is more efficient than naive evaluation.
/// It processes a `QueryPlan` which contains rules that have been optimized
/// with the Magic Set transformation, ensuring goal-directed evaluation.
pub struct SemiNaiveEngine;

impl SemiNaiveEngine {
    pub fn new() -> Self {
        Self {}
    }

    /// Executes a query plan to find a proof for a request.
    ///
    /// This is the main entry point for the semi-naive engine. It orchestrates
    /// the evaluation process, which involves:
    /// 1. Unifying magic and guarded rules from the `QueryPlan`.
    /// 2. Sorting rules to optimize evaluation order (e.g., rules with fewer
    ///    dependencies on derived predicates are run first).
    /// 3. Running the core semi-naive evaluation loop (`evaluate_rules`) to derive
    ///    all possible facts relevant to the query.
    /// 4. Analyzing the final fact set to find a concrete solution that
    ///    satisfies the original query and constructing a proof tree.
    ///
    /// Note: This implementation finds the *first* solution for any of the
    /// requested predicates and constructs its proof. It does not yet handle
    /// requests that require proving multiple top-level statements simultaneously.
    pub fn execute(
        &self,
        plan: &QueryPlan,
        materializer: &Materializer,
    ) -> Result<Option<Proof>, SolverError> {
        use crate::middleware::Statement;

        // 1.  Evaluate all rules (magic + guarded) together so that recursive
        //     dependencies are handled correctly.
        let mut combined_rules = plan.magic_rules.clone();
        combined_rules.extend(plan.guarded_rules.clone());

        let (all_facts, _prov) =
            self.evaluate_rules(&combined_rules, materializer, FactStore::new())?;

        // 2.  Find the first *non-synthetic* custom fact derived.  We treat
        //     it as the answer to the query and wrap it in a minimal proof.
        // Build an ordered list of target predicate identifiers based on the
        // order of guarded rule heads (excluding the synthetic goal).  This
        // ensures we pick the predicate the user actually asked for (e.g.
        // `path`) rather than some auxiliary predicate like `edge` that just
        // happens to appear first in the facts map.
        let mut preferred_pids = Vec::new();
        for gr in &plan.guarded_rules {
            if let ir::PredicateIdentifier::Normal(Predicate::Custom(cpr)) = &gr.head.predicate {
                if cpr.predicate().name != "_request_goal" {
                    preferred_pids.push(gr.head.predicate.clone());
                }
            }
        }

        for pid in preferred_pids {
            if let Some(rel) = all_facts.get(&pid) {
                if let Some(fact) = rel.iter().next() {
                    let cpr = match &pid {
                        ir::PredicateIdentifier::Normal(Predicate::Custom(c)) => c.clone(),
                        _ => unreachable!(),
                    };
                    // Convert ValueRefs → Values (literals only; keys are ignored).
                    let mut vals = Vec::new();
                    for vr in &fact.args {
                        match vr {
                            ValueRef::Literal(v) => vals.push(v.clone()),
                            ValueRef::Key(_) => {
                                if let Some(v) = materializer.value_ref_to_value(vr) {
                                    vals.push(v);
                                } else {
                                    // Cannot dereference – skip this fact.
                                    continue;
                                }
                            }
                        }
                    }

                    let stmt = Statement::Custom(cpr, vals);
                    let node = ProofNode {
                        conclusion: stmt,
                        justification: Justification::Fact,
                    };

                    return Ok(Some(Proof {
                        root_nodes: vec![std::sync::Arc::new(node)],
                    }));
                }
            }
        }

        Ok(None)
    }

    /// The core semi-naive evaluation loop.
    ///
    /// This function iteratively applies a set of Datalog `rules` to derive new facts
    /// until a fixed point is reached (i.e., no new facts can be generated).
    /// It starts with an optional set of `initial_facts`.
    ///
    /// The "semi-naive" aspect comes from using a `delta_facts` set. In each
    /// iteration, we only consider joins where at least one of the participating
    /// relations is in the `delta_facts` from the *previous* iteration. This
    /// avoids re-computing the same derivations repeatedly.
    ///
    /// The process is as follows:
    /// 1. Initialize `all_facts` with any initial or seed facts (from body-less rules).
    /// 2. In each iteration, compute a `new_delta` by joining rules against the
    ///    `delta_facts` from the last iteration and the cumulative `all_facts`.
    /// 3. Add `new_delta` to `all_facts`.
    /// 4. Replace `delta_facts` with `new_delta`.
    /// 5. Repeat until `new_delta` is empty.
    fn evaluate_rules(
        &self,
        rules: &[Rule],
        materializer: &Materializer,
        initial_facts: FactStore,
    ) -> Result<(FactStore, ProvenanceStore), SolverError> {
        let mut all_facts = initial_facts.clone();
        let mut delta_facts = initial_facts;
        let mut provenance_store = ProvenanceStore::new();

        debug!(
            "Starting evaluation with {} initial facts across {} relations.",
            delta_facts.values().map(|r| r.len()).sum::<usize>(),
            delta_facts.len()
        );
        for (pred, rel) in &delta_facts {
            trace!("  Initial facts for {:?}: {:?}", pred, rel);
        }

        // Seed with facts from body-less rules. This becomes the first delta if non-empty.
        let initial_delta = self.seed_initial_facts(rules, &mut all_facts)?;
        if !initial_delta.is_empty() {
            delta_facts = initial_delta;
        }

        let mut iteration = 0;
        loop {
            debug!("Starting semi-naive iteration {}", iteration);

            let new_delta = self.perform_iteration(
                rules,
                &mut all_facts,
                &mut delta_facts,
                materializer,
                &mut provenance_store,
            )?;

            if log::log_enabled!(log::Level::Trace) {
                for (p, rel) in &new_delta {
                    trace!("Iteration {} – Δ {:?} size = {}", iteration, p, rel.len());
                }
            }

            if new_delta.values().all(|rel| rel.is_empty()) {
                debug!("Fixpoint reached after {} iterations.", iteration);
                break; // Fixpoint reached.
            }

            trace!("Delta for next iteration: {:?}", new_delta);
            delta_facts = new_delta;
            iteration += 1;
        }

        Ok((all_facts, provenance_store))
    }

    /// Seeds the fact stores with initial facts derived from body-less rules.
    ///
    /// This function finds all rules in the program that have no body literals
    /// (i.e., `P(a, b).`) and treats them as axiomatic facts. It adds these
    /// facts to `all_facts` and returns a `FactStore` containing only these
    /// newly seeded facts, which can serve as the initial "delta" for the
    /// semi-naive evaluation.
    ///
    /// # Arguments
    /// * `rules` - The full set of Datalog rules for the program.
    /// * `all_facts` - A mutable reference to the main fact store, which will
    ///   be updated with the new seed facts.
    ///
    /// # Returns
    /// A `Result` containing a `FactStore` (the delta) of just the newly added
    /// seed facts, or an error if a fact rule contains variables.
    fn seed_initial_facts(
        &self,
        rules: &[Rule],
        all_facts: &mut FactStore,
    ) -> Result<FactStore, SolverError> {
        let mut initial_delta = FactStore::new();
        for rule in rules.iter().filter(|r| r.body.is_empty()) {
            // This is a fact. The terms should all be constants.
            let fact_tuple: Vec<ValueRef> = rule
                .head
                .terms
                .iter()
                .map(|term| match term {
                    StatementTmplArg::Literal(val) => Ok(ValueRef::Literal(val.clone())),
                    // Fact rules cannot contain dynamic parts.
                    StatementTmplArg::Wildcard(_) => Err(SolverError::Internal(
                        "Fact rule cannot contain wildcards".to_string(),
                    )),
                    StatementTmplArg::AnchoredKey(_, _) => Err(SolverError::Internal(
                        "Fact rule cannot contain anchored keys".to_string(),
                    )),
                    StatementTmplArg::None => Err(SolverError::Internal(
                        "Fact rule cannot contain None".to_string(),
                    )),
                })
                .collect::<Result<_, _>>()?;

            debug!(
                "Seeding with fact for {:?}: {:?}",
                rule.head.predicate, fact_tuple
            );

            let fact_struct = Fact {
                source: FactSource::External(JustificationKind::Fact),
                args: fact_tuple,
            };

            // Insert into all_facts and only add to delta if it's a new fact.
            if all_facts
                .entry(rule.head.predicate.clone())
                .or_default()
                .insert(fact_struct.clone())
            {
                initial_delta
                    .entry(rule.head.predicate.clone())
                    .or_default()
                    .insert(fact_struct);
            }
        }
        Ok(initial_delta)
    }

    /// Performs a single iteration of the semi-naive evaluation algorithm.
    ///
    /// This function iterates through all rules and joins their body literals
    /// against the current `all_facts` and `delta_facts` to derive new facts.
    /// Any newly derived facts are added to `all_facts` and `provenance_store`,
    /// and are also returned in a `new_delta` fact store.
    ///
    /// # Arguments
    /// * `rules` - The rules to evaluate.
    /// * `all_facts` - A mutable reference to the cumulative set of all facts.
    /// * `delta_facts` - The set of facts that were newly derived in the *previous*
    ///   iteration.
    /// * `semantics` - The semantics provider for EDB lookups.
    /// * `provenance_store` - A mutable reference to the store for rule provenance.
    ///
    /// # Returns
    /// A `Result` containing the set of new facts (`new_delta`) derived in this
    /// iteration.
    fn perform_iteration(
        &self,
        rules: &[Rule],
        all_facts: &mut FactStore,
        delta_facts: &mut FactStore,
        materializer: &Materializer,
        provenance_store: &mut ProvenanceStore,
    ) -> Result<FactStore, SolverError> {
        let mut new_delta = FactStore::new();

        for rule in rules {
            if rule.body.is_empty() {
                continue; // Seed facts are not re-evaluated.
            }

            trace!("Evaluating rule: {:?}", rule);

            for new_bindings in self.join_rule_body(rule, all_facts, delta_facts, materializer)? {
                let head_fact_tuple = self.project_head_fact(&rule.head, &new_bindings)?;
                let pred_id = rule.head.predicate.clone();

                trace!("Δ {:?} {:?}", pred_id, head_fact_tuple);

                // A fact is "new" if its tuple has not been seen before for this predicate.
                if !all_facts
                    .get(&pred_id)
                    .is_some_and(|r| r.iter().any(|f| f.args == head_fact_tuple))
                {
                    trace!("New fact derived for {:?}: {:?}", pred_id, head_fact_tuple);
                    let new_fact = Fact {
                        source: FactSource::Derived,
                        args: head_fact_tuple.clone(),
                    };

                    // Add to all_facts immediately so it's available for subsequent
                    // rules in this same iteration.
                    all_facts
                        .entry(pred_id.clone())
                        .or_default()
                        .insert(new_fact.clone());

                    // Add to this iteration's delta.
                    new_delta
                        .entry(pred_id.clone())
                        .or_default()
                        .insert(new_fact.clone());

                    // Record the provenance for this newly derived fact.
                    provenance_store.insert((pred_id, new_fact.args), (rule.clone(), new_bindings));
                }
            }
        }
        Ok(new_delta)
    }

    /// Creates a concrete fact for a rule's head from a set of variable bindings.
    fn project_head_fact(
        &self,
        head: &ir::Atom,
        bindings: &Bindings,
    ) -> Result<Vec<ValueRef>, SolverError> {
        head.terms
            .iter()
            .map(|term| match term {
                StatementTmplArg::Literal(c) => Ok(ValueRef::Literal(c.clone())),
                StatementTmplArg::Wildcard(w) => {
                    let binding = bindings.get(w);
                    if let Some(v) = binding {
                        Ok(ValueRef::Literal(v.clone()))
                    } else {
                        Err(SolverError::Internal(format!(
                            "Unbound wildcard in head: ?{}",
                            w.name
                        )))
                    }
                }
                StatementTmplArg::AnchoredKey(pod_wc, key) => {
                    let pod_id_val = bindings.get(pod_wc).cloned().ok_or_else(|| {
                        SolverError::Internal(format!(
                            "Unbound pod wildcard in head: ?{}",
                            pod_wc.name
                        ))
                    })?;
                    let pod_id = PodId::try_from(pod_id_val.typed())
                        .map_err(|e| SolverError::Internal(format!("{}", e)))?;
                    let ak = middleware::AnchoredKey::new(pod_id, key.clone());
                    Ok(ValueRef::Key(ak))
                }
                StatementTmplArg::None => Err(SolverError::Internal(
                    "None argument not allowed in rule head".to_string(),
                )),
            })
            .collect()
    }

    /// Handles the semi-naive evaluation for a single rule's body.
    ///
    /// A key optimization in semi-naive evaluation is that to derive a *new* fact,
    /// at least one of the literals in the rule's body must be joined with a fact that
    /// was *newly derived* in the previous iteration (a "delta" fact).
    ///
    /// This function implements that logic by:
    /// 1. Identifying which body literals correspond to predicates that have new
    ///    facts in `delta_facts`.
    /// 2. For each such "delta literal", it performs a full join of the rule's body,
    ///    where that one literal is joined against `delta_facts` and all others are
    ///    joined against `all_facts`.
    /// 3. It accumulates the new variable bindings produced from each of these joins.
    fn join_rule_body<'a>(
        &'a self,
        rule: &'a Rule,
        all_facts: &'a mut FactStore,
        delta_facts: &'a mut FactStore,
        materializer: &'a Materializer,
    ) -> Result<Vec<Bindings>, SolverError> {
        let mut all_new_bindings = Vec::new();
        trace!("Joining body for rule: {:?}", rule.head);

        // Helper to map a literal to the predicate identifier actually used
        // for fact storage (i.e. after resolving BatchSelf references).
        let resolve_pred_id = |lit: &Atom| {
            match &lit.predicate {
                ir::PredicateIdentifier::Normal(Predicate::BatchSelf(idx)) => {
                    // Resolve BatchSelf to a concrete Custom predicate using the head's batch.
                    if let ir::PredicateIdentifier::Normal(Predicate::Custom(head_cpr)) =
                        &rule.head.predicate
                    {
                        Some(ir::PredicateIdentifier::Normal(Predicate::Custom(
                            CustomPredicateRef::new(head_cpr.batch.clone(), *idx),
                        )))
                    } else {
                        None
                    }
                }
                other => Some(other.clone()),
            }
        };

        // Identify body positions whose (resolved) predicate appears in the current Δ.
        let delta_positions: Vec<usize> = rule
            .body
            .iter()
            .enumerate()
            .filter(|(_, lit)| {
                if let Some(pred_id) = resolve_pred_id(lit) {
                    delta_facts.get(&pred_id).is_some_and(|rel| !rel.is_empty())
                } else {
                    false
                }
            })
            .map(|(idx, _)| idx)
            .collect();

        trace!(
            "  Processing rule for {:?}. Delta-eligible literal indices: {:?}",
            rule.head.predicate,
            delta_positions
        );

        // Fallback: if no literal's predicate changed, the rule cannot produce
        // new facts based on the previous iteration's delta, so we can skip it.
        if delta_positions.is_empty() {
            trace!(
                "  No delta-eligible predicates for rule {:?}, skipping delta joins for this rule.",
                rule.head.predicate
            );
            return Ok(Vec::new());
        }

        for &i in &delta_positions {
            trace!("  Delta join on literal index {}", i);
            let new_bindings =
                self.perform_join(rule, &rule.body, i, all_facts, delta_facts, materializer)?;
            trace!(
                "    Found {} new bindings with delta on literal {}",
                new_bindings.len(),
                i
            );
            all_new_bindings.extend(new_bindings);
        }

        Ok(all_new_bindings)
    }

    /// Performs a join of all body literals for a rule, with one specific
    /// atom (`delta_idx`) being joined against the `delta` set of facts,
    /// while all others are joined against the `full` set.
    fn perform_join<'a>(
        &'a self,
        rule: &'a Rule,
        body: &'a [Atom],
        delta_idx: usize,
        all_facts: &'a mut FactStore,
        delta_facts: &'a mut FactStore,
        materializer: &'a Materializer,
    ) -> Result<Vec<Bindings>, SolverError> {
        // Start with an empty binding set (one empty solution).
        let mut current_bindings: Vec<Bindings> = vec![HashMap::new()];

        for (idx, atom) in body.iter().enumerate() {
            let is_delta = idx == delta_idx;
            trace!("    Joining with atom {:?} (is_delta: {})", atom, is_delta);

            let mut next_bindings = Vec::new();

            for binding in current_bindings.into_iter() {
                let relation = self.get_relation(
                    atom,
                    is_delta,
                    all_facts,
                    delta_facts,
                    materializer,
                    &binding,
                    rule,
                )?;

                for fact in relation.iter() {
                    if let Some(unified) = self.unify(&binding, atom, &fact.args)? {
                        next_bindings.push(unified);
                    }
                }
            }

            trace!(
                "      Accumulated bindings count after join: {}",
                next_bindings.len()
            );

            // If this literal produced no compatible bindings, the rule fails early.
            if next_bindings.is_empty() {
                return Ok(Vec::new());
            }

            current_bindings = next_bindings;
        }

        Ok(current_bindings)
    }

    /// Unifies a set of existing bindings with a new fact for a given atom,
    /// producing a new, extended set of bindings if they are compatible.
    fn unify(
        &self,
        bindings: &Bindings,
        atom: &Atom,
        fact: &[ValueRef],
    ) -> Result<Option<Bindings>, SolverError> {
        let mut new_bindings = bindings.clone();
        // Fact is our new fact. Atom is equivalent to StatementTmpl, with a predicate
        // and a list of arguments.
        // We follow the structure of the Atom, and use it to understand how the values
        // in the fact relate to bindings.
        // These values must either match the existing bindings, or be a new value for
        // a binding which does not currently exist.
        for (term_idx, term) in atom.terms.iter().enumerate() {
            let value_ref = &fact[term_idx];
            match term {
                StatementTmplArg::Literal(c) => {
                    if let ValueRef::Literal(value) = value_ref {
                        // Treat values as equal if their raw hashes are identical, even if the
                        // typed wrappers differ (e.g. Raw vs PodId).
                        if c.raw() != value.raw() {
                            return Ok(None); // Conflict with a constant
                        }
                    } else {
                        return Err(SolverError::Internal(format!(
                            "Literal value_ref should be a Literal: {:?}",
                            value_ref
                        )));
                    }
                }
                StatementTmplArg::Wildcard(w) => {
                    match value_ref {
                        // Wildcard bound to a concrete literal value.
                        ValueRef::Literal(value) => {
                            if let Some(existing_val) = new_bindings.get(w) {
                                if existing_val.raw() != value.raw() {
                                    return Ok(None); // Conflict with existing binding
                                }
                            } else {
                                new_bindings.insert(w.clone(), value.clone());
                            }
                        }
                        // Wildcard bound through an AnchoredKey – bind to the pod id's raw hash.
                        ValueRef::Key(ak) => {
                            let pod_value =
                                Value::new(TypedValue::Raw(RawValue::from((ak.pod_id).0)));

                            if let Some(existing_val) = new_bindings.get(w) {
                                if existing_val.raw() != pod_value.raw() {
                                    return Ok(None); // Conflict with existing binding
                                }
                            } else {
                                new_bindings.insert(w.clone(), pod_value);
                            }
                        }
                    }
                }
                StatementTmplArg::AnchoredKey(pod_wc, key) => {
                    if let ValueRef::Key(ak) = value_ref {
                        // 1. The literal key name in the rule must match the key found in the fact.
                        if &ak.key != key {
                            return Ok(None); // Different key – this fact doesn't match the literal.
                        }

                        // 2. The wildcard should be bound to the raw hash of the pod id so that
                        //    downstream facts use the canonical Raw representation expected by
                        //    tests and by other parts of the engine.
                        let pod_value = Value::new(TypedValue::Raw(RawValue::from((ak.pod_id).0)));

                        match new_bindings.get(pod_wc) {
                            // Wildcard already bound – ensure consistency.
                            Some(existing_val) if existing_val.raw() != pod_value.raw() => {
                                return Ok(None); // Mismatch with existing binding.
                            }
                            Some(_) => { /* already bound consistently, nothing to do */ }
                            None => {
                                new_bindings.insert(pod_wc.clone(), pod_value);
                            }
                        }
                    } else {
                        return Ok(None); // Term is AnchoredKey, but fact is a Literal – mismatch.
                    }
                }
                StatementTmplArg::None => {
                    return Err(SolverError::Internal(
                        "None argument not allowed in rule body".to_string(),
                    ))
                }
            }
        }
        Ok(Some(new_bindings))
    }

    /// Fetches derived facts (IDB) for a given literal from the relevant fact store.
    /// This handles magic predicates, custom predicates, and `BatchSelf` resolution.
    fn get_idb_relation<'a>(
        &self,
        fact_source: &'a FactStore,
        literal: &Atom,
        rule: &'a Rule,
    ) -> Result<std::borrow::Cow<'a, Relation>, SolverError> {
        let empty_relation = std::borrow::Cow::Owned(HashSet::new());

        let pred_id_to_lookup = match &literal.predicate {
            ir::PredicateIdentifier::Normal(Predicate::BatchSelf(idx)) => {
                let head_cpr = match &rule.head.predicate {
                    ir::PredicateIdentifier::Normal(Predicate::Custom(cpr)) => cpr,
                    _ => {
                        return Err(SolverError::Internal(format!(
                            "Rule with BatchSelf in body must have a Custom predicate head. Found: {:?}",
                            rule.head
                        )))
                    }
                };
                let body_pred_cpr =
                    middleware::CustomPredicateRef::new(head_cpr.batch.clone(), *idx);
                Some(ir::PredicateIdentifier::Normal(Predicate::Custom(
                    body_pred_cpr,
                )))
            }
            ir::PredicateIdentifier::Normal(Predicate::Custom(cpr)) => Some(
                ir::PredicateIdentifier::Normal(Predicate::Custom(cpr.clone())),
            ),
            id @ ir::PredicateIdentifier::Magic { .. } => Some(id.clone()),
            // Native and GetValue predicates are not in the IDB.
            _ => None,
        };

        if let Some(pred_id) = pred_id_to_lookup {
            if let Some(relation) = fact_source.get(&pred_id) {
                Ok(std::borrow::Cow::Borrowed(relation))
            } else {
                Ok(empty_relation)
            }
        } else {
            Ok(empty_relation)
        }
    }

    /// Fetches base facts (EDB) for a given literal from the `PodSemantics` provider.
    /// This handles native predicates and custom statements (but not evaluation of
    /// custom predicates).
    fn get_edb_relation<'a>(
        &self,
        materializer: &'a Materializer,
        atom: &'a Atom,
        bindings: &'a Bindings,
        all_facts: &'a mut FactStore,
    ) -> Result<Relation, SolverError> {
        let relation = match &atom.predicate {
            ir::PredicateIdentifier::Normal(pred) => {
                let relation =
                    materializer.facts_for_predicate(pred.clone(), atom.terms.clone(), bindings)?;

                // Cache into IDB so future queries see it without re-materialising.
                let pred_id = ir::PredicateIdentifier::Normal(pred.clone());
                let entry = all_facts.entry(pred_id).or_default();
                for fact in &relation {
                    entry.insert(fact.clone());
                }
                relation
            }
            // Magic predicates are purely IDB; no EDB facts.
            ir::PredicateIdentifier::Magic { .. } => Relation::new(),
        };
        Ok(relation)
    }

    /// Retrieves the relation (set of facts) for a given literal, considering the
    /// current bindings and whether to use the delta or full set of facts.
    ///
    /// This is a crucial function that bridges the abstract Datalog IR with the
    /// concrete data in the `FactDB` (EDB) and derived facts in the `FactStore` (IDB).
    ///
    /// It first queries for derived (IDB) facts from the current `fact_source`
    /// (`delta_facts` or `all_facts`). If the query is not a delta-join (i.e., it
    /// uses `all_facts`), it will also query for base (EDB) facts from the
    /// `PodSemantics` provider and merge the results.
    #[allow(clippy::too_many_arguments)]
    fn get_relation<'a>(
        &self,
        literal: &Atom,
        is_delta: bool,
        all_facts: &'a mut FactStore,
        delta_facts: &'a mut FactStore,
        materializer: &'a Materializer,
        bindings: &Bindings,
        rule: &'a Rule,
    ) -> Result<std::borrow::Cow<'a, Relation>, SolverError> {
        trace!(
            "Getting relation for literal: {:?}, is_delta: {}, bindings: {:?}",
            literal,
            is_delta,
            bindings
        );

        // 1. Get facts from the Intensional Database (derived facts) and own them
        let idb_owned = {
            let store_ref: &FactStore = if is_delta { delta_facts } else { &*all_facts };
            self.get_idb_relation(store_ref, literal, rule)?
                .into_owned()
        };

        // 2. If this is a delta-join, we ONLY care about IDB facts.
        if is_delta {
            return Ok(std::borrow::Cow::Owned(idb_owned));
        }

        // 3. If not a delta join, we also need facts from the Extensional Database.
        let edb_rel = self.get_edb_relation(materializer, literal, bindings, all_facts)?;

        // 4. Merge EDB and IDB facts as needed.
        match (idb_owned.is_empty(), edb_rel.is_empty()) {
            (true, true) => Ok(std::borrow::Cow::Owned(HashSet::new())),
            (false, true) => Ok(std::borrow::Cow::Owned(idb_owned)),
            (true, false) => Ok(std::borrow::Cow::Owned(edb_rel)),
            (false, false) => {
                // Both have facts, so we must merge them into a new owned relation.
                let mut merged_rel = edb_rel;
                merged_rel.extend(idb_owned);
                Ok(std::borrow::Cow::Owned(merged_rel))
            }
        }
    }
}

impl QueryEngine for SemiNaiveEngine {
    fn solve(
        &self,
        request: &ProofRequest,
        materializer: &Materializer,
    ) -> Result<Option<Proof>, SolverError> {
        let planner = Planner::new();
        let plan = planner.create_plan(request)?;
        self.execute(&plan, materializer)
    }
}

impl Default for SemiNaiveEngine {
    fn default() -> Self {
        Self::new()
    }
}

use crate::middleware::{PodId, Value};

#[cfg(test)]
mod tests {
    use std::sync::Arc;

    use hex::ToHex;

    use super::*;
    use crate::{
        backends::plonky2::mock::signedpod::MockSigner,
        examples::{attest_eth_friend, custom::eth_dos_batch},
        lang::parse,
        middleware::{
            hash_str, AnchoredKey, Params, Pod, PodId, Predicate, RawValue, Statement, TypedValue,
            Value, ValueRef,
        },
        solver::{db::FactDB, planner::Planner},
    };

    // A mock Pod for testing purposes.
    #[derive(Debug, Clone)]
    struct TestPod {
        id: PodId,
        statements: Vec<Statement>,
    }

    impl Pod for TestPod {
        fn params(&self) -> &Params {
            unimplemented!()
        }

        fn verify(&self) -> Result<(), Box<dyn std::error::Error + Send + Sync>> {
            Ok(())
        }

        fn id(&self) -> PodId {
            self.id
        }

        fn pod_type(&self) -> (usize, &'static str) {
            (99, "MockPod")
        }

        fn pub_self_statements(&self) -> Vec<Statement> {
            self.statements.clone()
        }

        fn serialize_data(&self) -> serde_json::Value {
            serde_json::Value::Null
        }
    }

    fn pod_id_from_name(name: &str) -> PodId {
        PodId(hash_str(name))
    }

    #[test]
    fn test_simple_rule_evaluation() {
        let _ = env_logger::builder().is_test(true).try_init();
        // 1. Setup Pods and Facts
        let pod_id1 = pod_id_from_name("pod1");
        let pod1 = TestPod {
            id: pod_id1,
            statements: vec![Statement::equal(
                AnchoredKey::from((pod_id1, "foo")),
                Value::from(5),
            )],
        };

        let pod_id2 = pod_id_from_name("pod2");
        let pod2 = TestPod {
            id: pod_id2,
            statements: vec![Statement::equal(
                AnchoredKey::from((pod_id2, "foo")),
                Value::from(20),
            )],
        };

        // 2. Build DB and Semantics
        let pods: Vec<Box<dyn Pod>> = vec![Box::new(pod1), Box::new(pod2)];
        let db = Arc::new(FactDB::build(pods).unwrap());
        let params = Params::default();
        let materializer = Materializer::new(db, &params);

        // 3. Define podlog and create plan
        let podlog = r#"
            is_large(P) = AND(
                Lt(10, ?P["foo"])
            )
            REQUEST(
                is_large(?SomePod)
            )
        "#;
        let params = Params::default();
        let processed = parse(podlog, &params, &[]).unwrap();
        let request = processed.request_templates;

        let planner = Planner::new();
        let plan = planner.create_plan(&request).unwrap();

        // 4. Execute plan
        let engine = SemiNaiveEngine::new();
        let mut combined_rules = plan.magic_rules.clone();
        combined_rules.extend(plan.guarded_rules.clone());

        let (all_facts, _provenance_store) = engine
            .evaluate_rules(&combined_rules, &materializer, FactStore::new())
            .unwrap();

        // 5. Assert results
        let is_large_rule = plan
            .guarded_rules
            .iter()
            .find(|r| {
                if let ir::PredicateIdentifier::Normal(Predicate::Custom(cpr)) = &r.head.predicate {
                    cpr.predicate().name == "is_large"
                } else {
                    false
                }
            })
            .unwrap();
        let p_id = is_large_rule.head.predicate.clone();
        println!("all_facts: {:#?}", all_facts);
        let results = all_facts.get(&p_id).unwrap();

        assert_eq!(results.len(), 1);
        let result_fact = results.iter().next().unwrap();

        // The result should be the pod id of pod2.
        // The IR variable `P` is bound to a pod ID, which is a hash, represented as a Raw Value.
        let pod2_id_val = Value::new(TypedValue::Raw(RawValue((pod_id2.0).0)));

        assert_eq!(result_fact.args, vec![ValueRef::Literal(pod2_id_val)]);
    }

    #[test]
    fn test_join_evaluation() {
        let _ = env_logger::builder().is_test(true).try_init();
        // 1. Setup:
        // Pod1 has id=1
        // Pod2 has friend_id=1
        // The rule `are_friends` should find that Pod1 and Pod2 are friends.
        let pod1_id = pod_id_from_name("pod1");
        let pod1 = TestPod {
            id: pod1_id,
            statements: vec![Statement::equal(
                AnchoredKey::from((pod1_id, "id")),
                Value::from(1),
            )],
        };

        let pod2_id = pod_id_from_name("pod2");
        let pod2 = TestPod {
            id: pod2_id,
            statements: vec![Statement::equal(
                AnchoredKey::from((pod2_id, "friend_id")),
                Value::from(1),
            )],
        };

        let pods: Vec<Box<dyn Pod>> = vec![Box::new(pod1), Box::new(pod2)];
        let db = Arc::new(FactDB::build(pods).unwrap());
        let params = Params::default();
        let materializer = Materializer::new(db, &params);

        // 2. Define podlog and create plan
        let podlog = r#"
            are_friends(A, B) = AND(
                Equal(?A["id"], ?B["friend_id"])
            )
            REQUEST(
                are_friends(?P1, ?P2)
            )
        "#;
        let params = Params::default();
        let processed = parse(podlog, &params, &[]).unwrap();
        let request = processed.request_templates;

        let planner = Planner::new();
        let plan = planner.create_plan(&request).unwrap();

        // 3. Execute plan
        let engine = SemiNaiveEngine::new();
        let mut combined_rules = plan.magic_rules.clone();
        combined_rules.extend(plan.guarded_rules.clone());

        let (all_facts, _provenance_store) = engine
            .evaluate_rules(&combined_rules, &materializer, FactStore::new())
            .unwrap();

        // 4. Assert results
        let rule = plan
            .guarded_rules
            .iter()
            .find(|r| {
                if let ir::PredicateIdentifier::Normal(Predicate::Custom(cpr)) = &r.head.predicate {
                    cpr.predicate().name == "are_friends"
                } else {
                    false
                }
            })
            .unwrap();
        let p_id = rule.head.predicate.clone();
        let results = all_facts.get(&p_id).unwrap();

        assert_eq!(results.len(), 1);
        let result_fact = results.iter().next().unwrap();

        // Expected result: are_friends(pod1, pod2)
        let p1_id_val = Value::new(TypedValue::Raw(RawValue((pod1_id.0).0)));
        let p2_id_val = Value::new(TypedValue::Raw(RawValue((pod2_id.0).0)));
        assert_eq!(
            result_fact.args,
            vec![ValueRef::Literal(p1_id_val), ValueRef::Literal(p2_id_val)]
        );
    }

    #[test]
    fn test_recursive_evaluation() {
        let _ = env_logger::builder().is_test(true).try_init();
        // 1. Setup: A -> B -> C
        // We define an 'edge' predicate that connects pods if one pod's "next" key
        // holds the ID of another pod.
        let pod_a_id = pod_id_from_name("podA");
        let pod_b_id = pod_id_from_name("podB");
        let pod_c_id = pod_id_from_name("podC");

        let pod_a = TestPod {
            id: pod_a_id,
            statements: vec![Statement::equal(
                AnchoredKey::from((pod_a_id, "next")),
                // The value is the raw ID of pod B
                Value::new(TypedValue::Raw(RawValue(pod_b_id.0 .0))),
            )],
        };
        let pod_b = TestPod {
            id: pod_b_id,
            statements: vec![
                Statement::equal(
                    AnchoredKey::from((pod_b_id, "id")),
                    Value::new(TypedValue::Raw(RawValue(pod_b_id.0 .0))),
                ),
                Statement::equal(
                    AnchoredKey::from((pod_b_id, "next")),
                    Value::new(TypedValue::Raw(RawValue(pod_c_id.0 .0))),
                ),
            ],
        };
        let pod_c = TestPod {
            id: pod_c_id,
            statements: vec![Statement::equal(
                AnchoredKey::from((pod_c_id, "id")),
                Value::new(TypedValue::Raw(RawValue(pod_c_id.0 .0))),
            )],
        };

        let pods: Vec<Box<dyn Pod>> = vec![Box::new(pod_a), Box::new(pod_b), Box::new(pod_c)];
        let db = Arc::new(FactDB::build(pods).unwrap());
        let params = Params::default();
        let materializer = Materializer::new(db, &params);

        // 2. Define podlog and create plan
        let pod_a_id_hex = pod_a_id.0.encode_hex::<String>();
        let podlog = format!(
            r#"
            edge(A, B) = AND(
                Equal(?A["next"], ?B["id"])
            )

            path(X, Y) = OR(
                edge(?X, ?Y)
                path_rec(?X, ?Y)
            )

            path_rec(X, Y, private: Z) = AND(
                path(?X, ?Z)
                edge(?Z, ?Y)
            )

            REQUEST(
                path(0x{}, ?End)
            )
        "#,
            pod_a_id_hex
        );

        let params = Params::default();
        let processed = parse(&podlog, &params, &[]).unwrap();
        let request = processed.request_templates;

        let planner = Planner::new();
        let plan = planner.create_plan(&request).unwrap();

        // 3. Execute plan – run magic and guarded rules together so that
        // recursive dependencies between data and magic predicates are
        // handled correctly in a single semi-naive fix-point.
        let engine = SemiNaiveEngine::new();
        let mut combined_rules = plan.magic_rules.clone();
        combined_rules.extend(plan.guarded_rules.clone());

        let (all_facts, _provenance_store) = engine
            .evaluate_rules(&combined_rules, &materializer, FactStore::new())
            .unwrap();

        // 4. Assert results
        let path_pred_ids: Vec<_> = plan
            .guarded_rules
            .iter()
            .filter_map(|r| match &r.head.predicate {
                ir::PredicateIdentifier::Normal(Predicate::Custom(cpr))
                    if cpr.predicate().name == "path" =>
                {
                    Some(r.head.predicate.clone())
                }
                _ => None,
            })
            .collect();

        assert!(
            !path_pred_ids.is_empty(),
            "Expected at least one guarded rule with head predicate 'path'"
        );

        let mut results: HashSet<Vec<ValueRef>> = HashSet::new();
        for pid in &path_pred_ids {
            if let Some(rel) = all_facts.get(pid) {
                results.extend(rel.iter().map(|f| f.args.clone()));
            }
        }

        println!("Results: {:?}", results);
        //  println!("Plan: {:#?}", plan);

        assert_eq!(results.len(), 2, "Should find paths to B and C");

        let pod_a_id_val = Value::new(TypedValue::Raw(RawValue(pod_a_id.0 .0)));
        let pod_b_id_val = Value::new(TypedValue::Raw(RawValue(pod_b_id.0 .0)));
        let pod_c_id_val = Value::new(TypedValue::Raw(RawValue(pod_c_id.0 .0)));

        let expected_results: HashSet<Vec<ValueRef>> = [
            vec![
                ValueRef::Literal(pod_a_id_val.clone()),
                ValueRef::Literal(pod_b_id_val),
            ],
            vec![
                ValueRef::Literal(pod_a_id_val),
                ValueRef::Literal(pod_c_id_val),
            ],
        ]
        .iter()
        .cloned()
        .collect();

        assert_eq!(results, expected_results);
    }

    #[test]
    fn test_execute_with_proof_reconstruction() {
        let _ = env_logger::builder().is_test(true).try_init();
        // 1. Setup Pods and Facts
        let pod_id1 = pod_id_from_name("pod1");
        let pod1 = TestPod {
            id: pod_id1,
            statements: vec![Statement::equal(
                AnchoredKey::from((pod_id1, "foo")),
                Value::from(5),
            )],
        };

        let pod_id2 = pod_id_from_name("pod2");
        let pod2 = TestPod {
            id: pod_id2,
            statements: vec![Statement::equal(
                AnchoredKey::from((pod_id2, "foo")),
                Value::from(20),
            )],
        };

        // 2. Build DB and Semantics
        let pods: Vec<Box<dyn Pod>> = vec![Box::new(pod1), Box::new(pod2)];
        let db = Arc::new(FactDB::build(pods).unwrap());
        let params = Params::default();
        let materializer = Materializer::new(db, &params);

        // 3. Define podlog and create plan for a NATIVE predicate request
        let podlog = r#"
            REQUEST(
                Lt(10, ?P["foo"])
            )
        "#;
        let params = Params::default();
        let processed = parse(podlog, &params, &[]).unwrap();
        let request = processed.request_templates;

        let planner = Planner::new();
        let plan = planner.create_plan(&request).unwrap();

        // 4. Execute plan
        let engine = SemiNaiveEngine::new();
        let result = engine.execute(&plan, &materializer);

        // 5. Assert results
        assert!(result.is_ok(), "Execution should succeed");
        let _proof_opt = result.unwrap();
        //assert!(proof_opt.is_some(), "Should find a proof");

        //let proof = proof_opt.unwrap();
        //assert_eq!(
        //    proof.root_nodes.len(),
        //    1,
        //    "Should have one root node in the proof"
        //);

        //println!("Proof: {:#?}", proof);

        //let root_node = &proof.root_nodes[0];

        // Check the conclusion of the proof
        // We expect the proof to be for the original native predicate, not the synthetic one.
        // ?P["foo"] should be bound to the value from pod2 (20).
        //let pod2_ak = AnchoredKey::new(pod_id2, Key::new("foo".to_string()));
        //let expected_conclusion =
        //    Statement::Lt(ValueRef::Literal(10.into()), ValueRef::Key(pod2_ak));
        //assert_eq!(root_node.conclusion, expected_conclusion);

        // The justification for the Lt premise should be ValueComparison, as it's a native check.
        //assert!(
        //    matches!(root_node.justification, Justification::ValueComparison),
        //    "Lt premise should be justified by ValueComparison, but was {:?}",
        //    root_node.justification
        //);
    }

    #[test]
    fn test_execute_with_proof_reconstruction_custom_predicate() {
        let _ = env_logger::builder().is_test(true).try_init();
        let params = Params {
            max_input_pods_public_statements: 8,
            max_statements: 24,
            max_public_statements: 8,
            ..Default::default()
        };

        let mut alice = MockSigner { pk: "Alice".into() };
        let mut bob = MockSigner { pk: "Bob".into() };
        let charlie = MockSigner {
            pk: "Charlie".into(),
        };
        let _david = MockSigner { pk: "David".into() };

        let alice_attestation = attest_eth_friend(&params, &mut alice, bob.public_key());
        let bob_attestation = attest_eth_friend(&params, &mut bob, charlie.public_key());
        let batch = eth_dos_batch(&params, true).unwrap();

        let req1 = format!(
            r#"
        use _, _, _, eth_dos from 0x{}
        REQUEST(
            eth_dos(0x{}, 0x{}, ?Distance)
        )
        "#,
            batch.id().encode_hex::<String>(),
            hash_str(&alice.pk).encode_hex::<String>(),
            hash_str(&charlie.pk).encode_hex::<String>()
        );

        let db = Arc::new(FactDB::build(vec![alice_attestation.pod, bob_attestation.pod]).unwrap());
        let params = Params::default();
        let materializer = Materializer::new(db, &params);

        let processed = parse(&req1, &params, &[batch.clone()]).unwrap();
        let request = processed.request_templates;

        let planner = Planner::new();
        let plan = planner.create_plan(&request).unwrap();

        // 4. Execute plan
        let engine = SemiNaiveEngine::new();
        let result = engine.execute(&plan, &materializer);

        println!("Proof tree: {}", result.unwrap().unwrap());
    }

    #[test]
    fn test_magic_set_pruning_with_logging() {
        // This test is designed to be run with `RUST_LOG=trace`.
        // Its primary purpose is to generate logs that demonstrate the pruning
        // effect of the Magic Set transformation. A naive engine would explore
        // both "islands" of data, while the magic set engine should only
        // explore the island relevant to the query (A->B).
        let _ = env_logger::builder().is_test(true).try_init();

        // --- Setup: Two disconnected "islands" of data ---
        // Island 1: A -> B
        let pod_a_id = pod_id_from_name("podA");
        let pod_b_id = pod_id_from_name("podB");
        let pod_a = TestPod {
            id: pod_a_id,
            statements: vec![
                Statement::equal(
                    AnchoredKey::from((pod_a_id, "id")),
                    Value::new(TypedValue::Raw(RawValue(pod_a_id.0 .0))),
                ),
                Statement::equal(
                    AnchoredKey::from((pod_a_id, "next")),
                    Value::new(TypedValue::Raw(RawValue(pod_b_id.0 .0))),
                ),
            ],
        };
        let pod_b = TestPod {
            id: pod_b_id,
            statements: vec![Statement::equal(
                AnchoredKey::from((pod_b_id, "id")),
                Value::new(TypedValue::Raw(RawValue(pod_b_id.0 .0))),
            )],
        };

        // Island 2: X -> Y
        let pod_x_id = pod_id_from_name("podX");
        let pod_y_id = pod_id_from_name("podY");
        let pod_x = TestPod {
            id: pod_x_id,
            statements: vec![
                Statement::equal(
                    AnchoredKey::from((pod_x_id, "id")),
                    Value::new(TypedValue::Raw(RawValue(pod_x_id.0 .0))),
                ),
                Statement::equal(
                    AnchoredKey::from((pod_x_id, "next")),
                    Value::new(TypedValue::Raw(RawValue(pod_y_id.0 .0))),
                ),
            ],
        };
        let pod_y = TestPod {
            id: pod_y_id,
            statements: vec![Statement::equal(
                AnchoredKey::from((pod_y_id, "id")),
                Value::new(TypedValue::Raw(RawValue(pod_y_id.0 .0))),
            )],
        };

        let pods: Vec<Box<dyn Pod>> = vec![
            Box::new(pod_a.clone()),
            Box::new(pod_b.clone()),
            Box::new(pod_x.clone()),
            Box::new(pod_y.clone()),
        ];
        let db = Arc::new(FactDB::build(pods).unwrap());
        let params = Params::default();
        let materializer = Materializer::new(db, &params);

        // --- Podlog with a recursive path predicate ---
        let pod_a_id_hex = pod_a_id.0.encode_hex::<String>();
        let podlog = format!(
            r#"
        edge(A, B) = AND(
            Equal(?A["next"], ?B["id"])
        )

        path_rec(X, Y, private: Z) =  AND(
            path(?X, ?Z)
            edge(?Z, ?Y)
        )

        path(X, Y) = OR(
            edge(?X, ?Y)
            path_rec(?X, ?Y)
        )

        REQUEST(
            path(0x{}, ?End)
        )
    "#,
            pod_a_id_hex
        );

        let params = Params::default();
        let processed = parse(&podlog, &params, &[]).unwrap();
        let request = processed.request_templates;

        let planner = Planner::new();
        let plan = planner.create_plan(&request).unwrap();

        // --- Execute plan ---
        let engine = SemiNaiveEngine::new();
        let result = engine.execute(&plan, &materializer).unwrap();
        println!("result: {:?}", result);
        // --- Assertions ---
        // The main goal is to check the logs, but we can also assert that
        // the final proof only contains the expected result from Island 1.
        assert!(result.is_some(), "A proof should have been found");
        let proof = result.unwrap();

        // The proof returned by `execute` should now directly contain the proof for `path`.
        assert_eq!(
            proof.root_nodes.len(),
            1,
            "Expected one proven statement in the root"
        );
        let path_node = &proof.root_nodes[0];

        let pod_a_id_val = Value::new(TypedValue::Raw(RawValue(pod_a_id.0 .0)));
        let pod_b_id_val = Value::new(TypedValue::Raw(RawValue(pod_b_id.0 .0)));

        // Check the conclusion of the path proof node
        if let Statement::Custom(cpr, values) = &path_node.conclusion {
            assert_eq!(cpr.predicate().name, "path");
            assert_eq!(values, &vec![pod_a_id_val, pod_b_id_val]);
        } else {
            panic!(
                "Expected a Custom statement, but found {:?}",
                path_node.conclusion
            );
        }
    }
}
