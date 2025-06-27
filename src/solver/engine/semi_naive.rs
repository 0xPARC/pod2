//! Implements a semi-naive bottom-up Datalog evaluation engine.
//!
//! The engine iteratively applies the rules from a `QueryPlan` to a `FactDB`
//! until no new facts can be derived, signifying that a fixed point has been
//! reached.

#![allow(clippy::arc_with_non_send_sync)]

use std::{
    collections::{HashMap, HashSet},
    sync::Arc,
};

use log::{debug, trace};

use crate::{
    middleware::{
        self, CustomPredicateRef, NativeOperation, Predicate, StatementTmplArg, ValueRef, Wildcard,
    },
    solver::{
        engine::proof_reconstruction::ProofReconstructor,
        error::SolverError,
        ir::{self, Atom, Rule},
        metrics::MetricsSink,
        planner::QueryPlan,
        proof::Proof,
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
    Custom,
    /// A fact that originated from the EDB (i.e., asserted in a POD).
    /// The `OperationKind` hints at how it was justified (e.g., direct
    /// fact vs. a computation like `Equal(5,5)`).
    Native(NativeOperation),
    Copy,
    Special,
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
pub type FactStore = HashMap<ir::PredicateIdentifier, Relation>;
/// A store for the provenance of derived facts, mapping a fact to the
/// rule and bindings that produced it.
pub type ProvenanceStore = HashMap<(ir::PredicateIdentifier, Vec<ValueRef>), (Rule, Bindings)>;

/// Implements a semi-naive Datalog evaluation engine.
///
/// This engine evaluates rules iteratively, using the deltas from one iteration
/// to find new facts in the next, which is more efficient than naive evaluation.
/// It processes a `QueryPlan` which contains rules that have been optimized
/// with the Magic Set transformation, ensuring goal-directed evaluation.
pub struct SemiNaiveEngine<M: MetricsSink> {
    metrics: M,
}

impl<M: MetricsSink> SemiNaiveEngine<M> {
    /// Creates a new engine with a given metrics sink.
    pub fn new(metrics: M) -> Self {
        Self { metrics }
    }

    /// Consumes the engine to retrieve the collected metrics.
    pub fn into_metrics(self) -> M {
        self.metrics
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
        &mut self,
        plan: &QueryPlan,
        materializer: &Materializer,
    ) -> Result<(FactStore, ProvenanceStore), SolverError> {
        // 1.  Evaluate all rules (magic + guarded) together so that recursive
        //     dependencies are handled correctly.
        let mut combined_rules = plan.magic_rules.clone();
        combined_rules.extend(plan.guarded_rules.clone());

        let (all_facts, prov) =
            self.evaluate_rules(&combined_rules, materializer, FactStore::new())?;

        Ok((all_facts, prov))
    }

    pub fn reconstruct_proof(
        &self,
        all_facts: &FactStore,
        provenance: &ProvenanceStore,
        materializer: &Materializer,
    ) -> Result<Proof, SolverError> {
        // The planner always emits a synthetic predicate `_request_goal`.  The
        // query is proven if (and only if) at least one fact for that
        // predicate is derived.

        let request_pid = all_facts.keys().find(|pid| {
            matches!(pid,
                ir::PredicateIdentifier::Normal(Predicate::Custom(cpr)) if cpr.predicate().name == "_request_goal")
        }).cloned();
        if let Some(pid) = request_pid {
            if let Some(rel) = all_facts.get(&pid) {
                if let Some(fact) = rel.iter().next() {
                    let recon = ProofReconstructor::new(all_facts, provenance, materializer);
                    let root = recon.build(&pid, fact)?;
                    return Ok(Proof {
                        root_nodes: vec![root],
                        db: Arc::clone(&materializer.db),
                    });
                }
            }
        }

        Err(SolverError::Internal(
            "No proof found for request goal".to_string(),
        ))
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
        &mut self,
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

        loop {
            self.metrics.increment_iterations();

            let new_delta = self.perform_iteration(
                rules,
                &mut all_facts,
                &mut delta_facts,
                materializer,
                &mut provenance_store,
            )?;

            self.metrics.record_delta(new_delta.clone());

            let num_new_facts = new_delta.values().map(|rel| rel.len()).sum();
            self.metrics.record_delta_size(num_new_facts);
            trace!(
                "Iteration complete. New facts this iteration: {}",
                num_new_facts
            );

            if new_delta.values().all(|rel| rel.is_empty()) {
                debug!("Fixpoint reached.");
                break; // Fixpoint reached.
            }

            trace!("Delta for next iteration: {:?}", new_delta);
            delta_facts = new_delta;
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
                source: FactSource::Copy,
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
        materializer.begin_iteration();

        for rule in rules {
            if rule.body.is_empty() {
                continue; // Seed facts are not re-evaluated.
            }

            trace!("Evaluating rule: {:?}", rule);

            for new_bindings in self.join_rule_body(rule, all_facts, delta_facts, materializer)? {
                let head_fact_tuple = self.project_head_fact(&rule.head, &new_bindings)?;
                let pred_id = rule.head.predicate.clone();

                trace!("Delta {:?} {:?}", pred_id, head_fact_tuple);

                // A fact is "new" if its tuple has not been seen before for this predicate.
                if !all_facts
                    .get(&pred_id)
                    .is_some_and(|r| r.iter().any(|f| f.args == head_fact_tuple))
                {
                    trace!("New fact derived for {:?}: {:?}", pred_id, head_fact_tuple);
                    let new_fact = Fact {
                        source: FactSource::Custom,
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

        // Identify body positions whose (resolved) predicate appears in the current delta.
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

        // Fallback: if no literal's predicate appears in delta *but* the rule's body
        // depends **only on EDB (native) predicates**, we still have to evaluate
        // it once to seed the IDB with facts that stem purely from the extensional
        // database.  (Think `base(X,Y) :- Equal(X,Y), Equal(D,0).`)
        if delta_positions.is_empty() {
            let all_edb = rule.body.iter().all(|lit| {
                matches!(
                    &lit.predicate,
                    ir::PredicateIdentifier::Normal(Predicate::Native(_))
                )
            });

            if !all_edb {
                trace!(
                    "  No delta-eligible predicates for rule {:?}, skipping delta joins for this rule.",
                    rule.head.predicate
                );
                return Ok(Vec::new());
            } else {
                trace!(
                    "  Rule {:?} contains only EDB predicates - performing one full join despite empty Δ.",
                    rule.head.predicate
                );
                let fake_delta_idx = rule.body.len(); // ensures `is_delta` is false for every atom
                let new_bindings = self.perform_join(
                    rule,
                    &rule.body,
                    fake_delta_idx,
                    all_facts,
                    delta_facts,
                    materializer,
                )?;
                all_new_bindings.extend(new_bindings);
                return Ok(all_new_bindings);
            }
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
                trace!(
                    "Rule {:?} – join failed at literal index {} ({:?}). No compatible bindings left after this literal.",
                    rule.head.predicate,
                    idx,
                    atom.predicate
                );
                return Ok(Vec::new());
            }

            current_bindings = next_bindings;
        }

        Ok(current_bindings)
    }

    /// Unifies a set of existing bindings with a new fact for a given atom,
    /// producing a new, extended set of bindings if they are compatible.
    pub fn unify(
        &self,
        bindings: &Bindings,
        atom: &Atom,
        fact: &[ValueRef],
    ) -> Result<Option<Bindings>, SolverError> {
        let mut new_bindings = bindings.clone();
        // An "Atom" here is a single statement, and its "terms" are in fact the
        // statement template arguments. The "fact" is the concrete set of statement
        // arguments we are trying to unify with the bindings.
        // In other words, given a statement template and a concrete set of statement
        // arguments, we work out what this means for the wildcards in the statement
        // template.
        for (term_idx, term) in atom.terms.iter().enumerate() {
            // Given the index of the statement template argument, we can get the
            // corresponding ValueRef from the concrete statement.
            let value_ref = &fact[term_idx];
            match term {
                StatementTmplArg::Literal(c) => {
                    if let ValueRef::Literal(value) = value_ref {
                        // If the value in the fact does not match the value in the
                        // statement template, then the unification fails.
                        if c != value {
                            return Ok(None);
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
                            // If the wildcard is already bound to a value, and it does not
                            // match the value in the fact, then the unification fails.
                            if let Some(existing_val) = new_bindings.get(w) {
                                if existing_val != value {
                                    return Ok(None);
                                }
                            } else {
                                // No existing binding for this wildcard, so we can bind it to
                                // the literal value.
                                new_bindings.insert(w.clone(), value.clone());
                            }
                        }
                        // The statement template argument is a wildcard, but the equivalent
                        // ValueRef is not a Literal. This is a mismatch (can't bind an anchored
                        // key to a plain wildcard).
                        _ => {
                            return Err(SolverError::Internal(format!(
                                "Wildcard value_ref should be a ValueRef::Literal: {:?}",
                                value_ref
                            )));
                        }
                    }
                }
                StatementTmplArg::AnchoredKey(pod_wc, key) => {
                    if let ValueRef::Key(ak) = value_ref {
                        // The statement template argument is an AnchoredKey, and the fact is
                        // also an AnchoredKey. We need to check that the key names match.
                        if &ak.key != key {
                            return Ok(None);
                        }

                        let pod_id_value = Value::from(ak.pod_id.0);

                        match new_bindings.get(pod_wc) {
                            // If the wildcard is already bound to a value, and it does not
                            // match the value in the fact, then the unification fails.
                            Some(existing_val) if *existing_val != pod_id_value => {
                                println!(
                                    "Unification failed: {:?} != {:?}",
                                    existing_val, pod_id_value
                                );
                                return Ok(None);
                            }
                            Some(_) => { /* already bound consistently, nothing to do */ }
                            None => {
                                // No existing binding for this wildcard, so we can bind it to
                                // the pod id value.
                                new_bindings.insert(pod_wc.clone(), pod_id_value);
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
                let relation = materializer.materialize_statements(
                    pred.clone(),
                    atom.terms.clone(),
                    bindings,
                )?;

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

impl<M: MetricsSink> Default for SemiNaiveEngine<M> {
    fn default() -> Self {
        Self::new(M::default())
    }
}

use crate::middleware::{PodId, Value};

#[cfg(test)]
mod tests {
    use std::sync::Arc;

    use hex::ToHex;

    use super::*;
    use crate::{
        backends::plonky2::mock::{mainpod::MockProver, signedpod::MockSigner},
        examples::{attest_eth_friend, custom::eth_dos_batch, MOCK_VD_SET},
        frontend::MainPodBuilder,
        lang::parse,
        middleware::{
            hash_str, AnchoredKey, OperationType, Params, PodId, Predicate, RawValue, Statement,
            TypedValue, Value, ValueRef,
        },
        solver::{
            db::{FactDB, IndexablePod, TestPod},
            explainer::MissingFactFinder,
            metrics::{DebugMetrics, NoOpMetrics},
            planner::Planner,
            proof::Justification,
            vis,
        },
    };

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
        let pods: Vec<IndexablePod> = vec![
            IndexablePod::TestPod(Arc::new(pod1)),
            IndexablePod::TestPod(Arc::new(pod2)),
        ];
        let db = Arc::new(FactDB::build(&pods).unwrap());
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
        let mut combined_rules = plan.magic_rules.clone();
        combined_rules.extend(plan.guarded_rules.clone());

        // 4. Execute plan
        let mut engine = SemiNaiveEngine::new(NoOpMetrics);
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

        let pods: Vec<IndexablePod> = vec![
            IndexablePod::TestPod(Arc::new(pod1)),
            IndexablePod::TestPod(Arc::new(pod2)),
        ];
        let db = Arc::new(FactDB::build(&pods).unwrap());
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
        let mut combined_rules = plan.magic_rules.clone();
        combined_rules.extend(plan.guarded_rules.clone());

        // 3. Execute plan
        let mut engine = SemiNaiveEngine::new(NoOpMetrics);
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

        let pods: Vec<IndexablePod> = vec![
            IndexablePod::TestPod(Arc::new(pod_a)),
            IndexablePod::TestPod(Arc::new(pod_b)),
            IndexablePod::TestPod(Arc::new(pod_c)),
        ];
        let db = Arc::new(FactDB::build(&pods).unwrap());
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
        let mut engine = SemiNaiveEngine::new(DebugMetrics::default());
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
    fn test_transitive_equality() {
        let _ = env_logger::builder().is_test(true).try_init();

        let pod_a_id = pod_id_from_name("podA");
        let pod_b_id = pod_id_from_name("podB");
        let pod_c_id = pod_id_from_name("podC");
        let pod_d_id = pod_id_from_name("podD");

        let pod_a = TestPod {
            id: pod_a_id,
            statements: vec![
                Statement::equal(
                    AnchoredKey::from((pod_a_id, "k1")),
                    AnchoredKey::from((pod_b_id, "k2")),
                ),
                Statement::equal(
                    AnchoredKey::from((pod_b_id, "k2")),
                    AnchoredKey::from((pod_c_id, "k3")),
                ),
                Statement::equal(
                    AnchoredKey::from((pod_c_id, "k3")),
                    AnchoredKey::from((pod_d_id, "k4")),
                ),
            ],
        };

        let pods: Vec<IndexablePod> = vec![IndexablePod::TestPod(Arc::new(pod_a))];
        let db = Arc::new(FactDB::build(&pods).unwrap());
        let params = Params::default();
        let materializer = Materializer::new(db, &params);

        let program = r#"
        REQUEST(
            Equal(?A["k1"], ?P["k4"])
        )
        "#;

        let processed = parse(program, &params, &[]).unwrap();
        let request = processed.request_templates;

        let planner = Planner::new();
        let plan = planner.create_plan(&request).unwrap();

        let mut engine = SemiNaiveEngine::new(NoOpMetrics);
        let result = engine.execute(&plan, &materializer);

        let (all_facts, provenance) = result.unwrap();
        let proof = engine.reconstruct_proof(&all_facts, &provenance, &materializer);

        assert!(proof.is_ok(), "Execution should succeed");
        let proof = proof.unwrap();
        println!("Proof: {:?}", proof);
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
        let pods: Vec<IndexablePod> = vec![
            IndexablePod::TestPod(Arc::new(pod1)),
            IndexablePod::TestPod(Arc::new(pod2)),
        ];
        let db = Arc::new(FactDB::build(&pods).unwrap());
        let params = Params::default();
        let materializer = Materializer::new(db.clone(), &params);

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
        let mut engine = SemiNaiveEngine::new(NoOpMetrics);
        let result = engine.execute(&plan, &materializer);

        // 5. Assert results
        assert!(result.is_ok(), "Execution should succeed");
        let (all_facts, provenance) = result.unwrap();
        let proof = engine.reconstruct_proof(&all_facts, &provenance, &materializer);
        assert!(proof.is_ok(), "Should find a proof");
        let proof = proof.unwrap();
        println!("Proof: {:?}", proof);

        assert_eq!(
            proof.root_nodes.len(),
            1,
            "Should have one root node in the proof"
        );
    }

    #[test]
    fn test_execute_with_proof_reconstruction_custom_predicate() {
        let _ = env_logger::builder().is_test(true).try_init();
        let params = Params {
            max_input_pods_public_statements: 8,
            max_statements: 32,
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

        println!("batch: {}", batch.id().encode_hex::<String>());

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

        let db = Arc::new(
            FactDB::build(&[
               // IndexablePod::signed_pod(&alice_attestation),
               // IndexablePod::signed_pod(&bob_attestation),
            ])
            .unwrap(),
        );
        let materializer = Materializer::new(db.clone(), &params);

        let processed = parse(&req1, &params, &[batch.clone()]).unwrap();
        let request = processed.request_templates;

        let planner = Planner::new();
        let plan = planner.create_plan(&request).unwrap();

        // 4. Execute plan
        let mut engine = SemiNaiveEngine::new(NoOpMetrics);
        let result = engine.execute(&plan, &materializer);

        let (all_facts, provenance) = result.unwrap();
        let proof = engine.reconstruct_proof(&all_facts, &provenance, &materializer);

        let finder = MissingFactFinder::new(&all_facts, &materializer);
        let missing = finder.collect(&plan.guarded_rules);
        for tmpl in missing {
            println!(
                "{}({})",
                match tmpl.pred {
                    Predicate::Custom(cpr) => cpr.predicate().name.clone().replace("\"", ""),
                    Predicate::Native(op) => format!("{:?}", op).replace("\"", ""),
                    _ => unreachable!(),
                },
                tmpl.args
                    .iter()
                    .map(|a| match a {
                        StatementTmplArg::Literal(l) => l.to_string(),
                        StatementTmplArg::Wildcard(w) => format!("{}", w),
                        StatementTmplArg::AnchoredKey(w, k) => {
                            format!("{}[\"{}\"]", w, k.name())
                        }
                        StatementTmplArg::None => "".to_string(),
                    })
                    .collect::<Vec<_>>()
                    .join(", ")
            );
        }

        assert!(proof.is_ok(), "Should find a proof");
        let proof = proof.unwrap();
        println!("Proof: {}", proof);
        //println!("Operations: {:#?}", proof.to_operations(&db.clone()));
        for (operation, public) in proof.to_operations() {
            println!(
                "{:?}  public:{}",
                match operation.0 {
                    OperationType::Native(op) => format!("{:?}", op),
                    OperationType::Custom(cpr) => cpr.predicate().name.clone(),
                },
                public
            );
            for arg in &operation.1 {
                println!("  {}", arg);
            }
            println!();
        }
        let vd_set = &*MOCK_VD_SET;
        let mut builder = MainPodBuilder::new(&params, vd_set);
        let prover = MockProver {};

        let inputs = proof.to_inputs();
        let (_, ops) = inputs;
        for (operation, public) in ops {
            if public {
                builder.pub_op(operation).unwrap();
            } else {
                builder.priv_op(operation).unwrap();
            }
        }

        builder.add_signed_pod(&alice_attestation);
        builder.add_signed_pod(&bob_attestation);

        let result = builder.prove(&prover, &params);
        assert!(result.is_ok(), "Should prove");
        let main_pod = result.unwrap();
        println!("Main pod: {}", main_pod);
        println!("{}", vis::mermaid_markdown(&proof));

        let req2 = format!(
            r#"
        use _, _, _, eth_dos from 0x{}
        REQUEST(
            eth_dos(0x{}, 0x{}, ?Distance)
        )
        "#,
            batch.id().encode_hex::<String>(),
            hash_str(&alice.pk).encode_hex::<String>(),
            hash_str(&bob.pk).encode_hex::<String>()
        );

        let processed = parse(&req2, &params, &[batch.clone()]).unwrap();
        let request = processed.request_templates;

        let planner = Planner::new();
        let plan = planner.create_plan(&request).unwrap();

        let db = Arc::new(
            FactDB::build(&[
                IndexablePod::main_pod(&main_pod),
                IndexablePod::signed_pod(&alice_attestation),
                // IndexablePod::signed_pod(&bob_attestation),
            ])
            .unwrap(),
        );
        let materializer = Materializer::new(db.clone(), &params);

        let mut engine = SemiNaiveEngine::new(NoOpMetrics);
        let result = engine.execute(&plan, &materializer);

        let (all_facts, provenance) = result.unwrap();
        let proof = engine.reconstruct_proof(&all_facts, &provenance, &materializer);

        assert!(proof.is_ok(), "Should find a proof");
        let proof = proof.unwrap();
        println!("Proof: {}", proof);
        println!("{}", vis::mermaid_markdown(&proof));
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

        let pods: Vec<IndexablePod> = vec![
            IndexablePod::TestPod(Arc::new(pod_a)),
            IndexablePod::TestPod(Arc::new(pod_b)),
            IndexablePod::TestPod(Arc::new(pod_x)),
            IndexablePod::TestPod(Arc::new(pod_y)),
        ];
        let db = Arc::new(FactDB::build(&pods).unwrap());
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
        let mut engine = SemiNaiveEngine::new(DebugMetrics::default());
        let result = engine.execute(&plan, &materializer);
        // --- Assertions ---
        // The main goal is to check the logs, but we can also assert that
        // the final proof only contains the expected result from Island 1.
        let (all_facts, provenance) = result.unwrap();
        let proof = engine.reconstruct_proof(&all_facts, &provenance, &materializer);
        assert!(proof.is_ok(), "A proof should have been found");
        let proof = proof.unwrap();

        // The proof is for the synthetic `_request_goal` predicate, which has the
        // actual user-request predicate proof as its premise.
        assert_eq!(
            proof.root_nodes.len(),
            1,
            "Expected one root node for the synthetic goal"
        );
        let root_node = &proof.root_nodes[0];

        // Check that the root is indeed for `_request_goal`.
        if let Statement::Custom(root_cpr, _) = &root_node.statement {
            assert_eq!(root_cpr.predicate().name, "_request_goal");
        } else {
            panic!(
                "Expected root conclusion to be a Custom statement for _request_goal, but got {:?}",
                root_node.statement
            );
        }

        // Extract the `path` proof node from the premises of the root node.
        let path_node = match &root_node.justification {
            Justification::Custom(_, premises) => {
                assert_eq!(
                    premises.len(),
                    1,
                    "Expected one premise for the synthetic goal"
                );
                premises[0].clone()
            }
            _ => panic!(
                "Expected root justification to be Custom, but got {:?}",
                root_node.justification
            ),
        };

        let pod_a_id_val = Value::new(TypedValue::Raw(RawValue(pod_a_id.0 .0)));
        let pod_b_id_val = Value::new(TypedValue::Raw(RawValue(pod_b_id.0 .0)));

        // Check the conclusion of the path proof node
        if let Statement::Custom(cpr, values) = &path_node.statement {
            assert_eq!(cpr.predicate().name, "path");
            assert_eq!(values, &vec![pod_a_id_val, pod_b_id_val]);
        } else {
            panic!(
                "Expected a Custom statement, but found {:?}",
                path_node.statement
            );
        }
    }

    //     #[test]
    //     fn test_array_sum() {
    //         let _ = env_logger::builder().is_test(true).try_init();

    //         let pods: Vec<Box<dyn Pod>> = vec![];
    //         let db = Arc::new(FactDB::build(pods).unwrap());
    //         let params = Params::default();
    //         let materializer = Materializer::new(db, &params);

    //         let program = r#"
    //  sum_from_base(A, I, S) = AND(
    //     NotContains(?A, ?I)        // I is past the end
    //     SumOf(?S, 0, 0)            // therefore S = 0
    // )

    // sum_from_step(A, I, S, private: J, Rest, V) = AND(
    //     Contains(?A, ?I, ?V)       // element V exists at index I
    //     SumOf(?J, ?I, 1)           // J = I + 1
    //     sum_from(?A, ?J, ?Rest)    // recursive call
    //     SumOf(?S, ?V, ?Rest)       // S = V + Rest
    // )

    // // ------------ single public definition --------------------------
    // sum_from(A, I, S) = OR(
    //     sum_from_base(?A, ?I, ?S)
    //     sum_from_step(?A, ?I, ?S)
    // )

    // array_sum(A, S) = AND(
    //     sum_from(?A, 0, ?S)
    // )
    // // --- What a client would request ---------------------------------
    // REQUEST(
    //     array_sum([1, 2, 3], ?Total)
    // )
    //         "#;

    //         let processed = parse(program, &params, &[]).unwrap();
    //         let request = processed.request_templates;

    //         let planner = Planner::new();
    //         let plan = planner.create_plan(&request).unwrap();

    //         let mut engine = SemiNaiveEngine::new(NoOpMetrics);
    //         let result = engine.execute(&plan, &materializer);

    //         let (all_facts, provenance) = result.unwrap();
    //         let proof = engine.reconstruct_proof(&all_facts, &provenance, &materializer);
    //         println!("Metrics: {:#?}", engine.into_metrics());
    //         print_all_facts(&all_facts);
    //         println!("Proof: {:#?}", proof);
    //         assert!(proof.is_ok(), "Execution should succeed");
    //         let proof = proof.unwrap();
    //         println!("Proof: {:?}", proof);
    //     }
}
