//! Handles the backward-chaining proof reconstruction phase of the solver.
//!
//! After the semi-naive engine has derived all facts, this module takes a
//! specific solution and walks the `ProvenanceStore` to build a verifiable
//! `Proof` tree.

use std::{collections::HashMap, sync::Arc};

use super::semi_naive::{Bindings, Fact, FactSource, FactStore, ProvenanceStore};
use crate::{
    middleware::{
        self, AnchoredKey, Hash, Key, PodId, Predicate, Statement, TypedValue, Value, ValueRef,
        Wildcard,
    },
    solver::{
        error::SolverError,
        ir::{self},
        proof::{Justification, ProofNode},
    },
};

/// A map from a fresh variable to the AnchoredKey template it represents.
/// The template is stored as the Pod wildcard and the literal Key.
pub(super) type FreshVarMap = HashMap<Wildcard, (Wildcard, Key)>;

/// Contextual information needed for reconstructing a proof tree.
pub(super) struct ProofReconstructionContext<'a> {
    pub(super) bindings: &'a Bindings,
    pub(super) fresh_var_to_ak_template: FreshVarMap,
    pub(super) memo: &'a mut HashMap<(ir::PredicateIdentifier, Vec<Value>), Arc<ProofNode>>,
}

pub(super) struct ProofReconstructor<'a> {
    all_facts: &'a FactStore,
    provenance_store: &'a ProvenanceStore,
    semantics: &'a PodSemantics,
}

impl<'a> ProofReconstructor<'a> {
    pub(super) fn new(
        all_facts: &'a FactStore,
        provenance_store: &'a ProvenanceStore,
        semantics: &'a PodSemantics,
    ) -> Self {
        Self {
            all_facts,
            provenance_store,
            semantics,
        }
    }

    /// The main entry point for proof reconstruction. It sets up the initial
    /// context and starts the recursive process.
    pub(super) fn reconstruct_proof(
        &self,
        target_fact: &Fact,
        literal: &ir::Literal,
    ) -> Result<Arc<ProofNode>, SolverError> {
        // For the top-level call, the context is built based on whether the
        // target fact was derived or not.
        let bindings_storage;
        let mut ctx;
        let empty_bindings;
        let empty_fresh_var_map;
        let mut memo = HashMap::new();
        let mut rule_for_context = None;

        if let FactSource::Derived = target_fact.source {
            let key = (literal.predicate.clone(), target_fact.tuple.clone());
            let (rule, bindings) = self.provenance_store.get(&key).ok_or_else(|| {
                SolverError::Internal(format!(
                    "Could not find provenance for derived fact: {:?}, literal: {:?}",
                    target_fact, literal
                ))
            })?;
            rule_for_context = Some(rule);
            bindings_storage = bindings.clone();

            let mut fresh_var_map = FreshVarMap::new();
            for body_lit in &rule.body {
                if body_lit.predicate == ir::PredicateIdentifier::GetValue {
                    if let [ir::Term::Variable(pod_wc), ir::Term::Constant(key_val), ir::Term::Variable(val_wc)] =
                        &body_lit.terms[..]
                    {
                        if let TypedValue::String(key_str) = key_val.typed() {
                            fresh_var_map.insert(
                                val_wc.clone(),
                                (pod_wc.clone(), Key::new(key_str.clone())),
                            );
                        }
                    }
                }
            }
            ctx = ProofReconstructionContext {
                bindings: &bindings_storage,
                fresh_var_to_ak_template: fresh_var_map,
                memo: &mut memo,
            };
        } else {
            empty_bindings = HashMap::new();
            empty_fresh_var_map = HashMap::new();
            ctx = ProofReconstructionContext {
                bindings: &empty_bindings,
                fresh_var_to_ak_template: empty_fresh_var_map,
                memo: &mut memo,
            };
        }

        self.reconstruct_proof_recursive(target_fact, literal, &mut ctx, rule_for_context)
    }

    /// The core recursive function for building the proof tree node by node.
    fn reconstruct_proof_recursive(
        &self,
        target_fact: &Fact,
        literal: &ir::Literal,
        ctx: &mut ProofReconstructionContext,
        parent_rule: Option<&'a ir::Rule>,
    ) -> Result<Arc<ProofNode>, SolverError> {
        // Memoization check
        let memo_key = (literal.predicate.clone(), target_fact.tuple.clone());
        if let Some(memoized_node) = ctx.memo.get(&memo_key) {
            return Ok(memoized_node.clone());
        }

        let result = match &target_fact.source {
            FactSource::External(kind) => {
                // This path is taken for EDB facts. We have the original literal
                // (with variables) and the bindings from the parent rule's context.
                let conclusion = self.native_literal_to_statement(literal, ctx)?;
                let justification = match kind {
                    JustificationKind::Fact => Justification::Fact,
                    JustificationKind::Computation => Justification::ValueComparison,
                };
                Ok(Arc::new(ProofNode {
                    conclusion,
                    justification,
                }))
            }
            FactSource::Derived => {
                let resolved_head_id = self.resolve_predicate_id(literal, parent_rule)?;
                let key = (resolved_head_id, target_fact.tuple.clone());
                let (rule, bindings) = self.provenance_store.get(&key).ok_or_else(|| {
                    SolverError::Internal(format!(
                        "Could not find provenance for derived fact: {:?}, literal: {:?}",
                        target_fact, literal
                    ))
                })?;

                // Build the context for reconstructing premises of *this* rule.
                let mut fresh_var_map = FreshVarMap::new();
                for literal in &rule.body {
                    if literal.predicate == ir::PredicateIdentifier::GetValue {
                        if let [ir::Term::Variable(pod_wc), ir::Term::Constant(key_val), ir::Term::Variable(val_wc)] =
                            &literal.terms[..]
                        {
                            if let TypedValue::String(key_str) = key_val.typed() {
                                fresh_var_map.insert(
                                    val_wc.clone(),
                                    (pod_wc.clone(), Key::new(key_str.clone())),
                                );
                            }
                        }
                    }
                }

                let mut premise_ctx = ProofReconstructionContext {
                    bindings,
                    fresh_var_to_ak_template: fresh_var_map,
                    memo: ctx.memo,
                };

                // Recursively build proofs for the premises of the rule.
                // Filter out GetValue and Magic literals, as they are implementation details.
                let premises: Vec<Arc<ProofNode>> = rule
                    .body
                    .iter()
                    .filter(|lit| {
                        !matches!(
                            lit.predicate,
                            ir::PredicateIdentifier::GetValue
                                | ir::PredicateIdentifier::Magic { .. }
                        )
                    })
                    .map(|premise_lit| {
                        let premise_tuple = self.instantiate_tuple(premise_lit, bindings)?;

                        // Resolve BatchSelf before looking up the fact.
                        let resolved_pred_id =
                            self.resolve_predicate_id(premise_lit, Some(rule))?;

                        // Check if the premise is a derived fact (IDB) or needs to be
                        // verified against the base facts (EDB).
                        let premise_fact_owned: Fact; // Use an owned Fact
                        if let Some(found_fact) =
                            self.find_fact_by_tuple(&resolved_pred_id, &premise_tuple)?
                        {
                            premise_fact_owned = found_fact.clone();
                        } else {
                            // The premise was not a derived fact, so we must check if it's a
                            // computable EDB fact (e.g. Lt(10,20)). We delegate this check
                            // to the semantics provider by first instantiating the literal.
                            let ground_premise_lit = ir::Literal {
                                predicate: premise_lit.predicate.clone(),
                                terms: premise_tuple
                                    .iter()
                                    .map(|v| ir::Term::Constant(v.clone()))
                                    .collect(),
                            };
                            let is_valid_edb = self.semantics.is_edb_fact(&ground_premise_lit)?;

                            if is_valid_edb {
                                premise_fact_owned = Fact {
                                    source: FactSource::External(JustificationKind::Computation),
                                    tuple: premise_tuple.clone(),
                                };
                            } else {
                                return Err(SolverError::Internal(format!(
                                    "Could not prove premise (failed EDB check): {:?}, tuple: {:?}",
                                    premise_lit, premise_tuple
                                )));
                            }
                        }

                        // Create a new literal with the resolved predicate ID to ensure
                        // the recursive call doesn't see the temporary `BatchSelf`.
                        let resolved_premise_lit = ir::Literal {
                            predicate: resolved_pred_id,
                            terms: premise_lit.terms.clone(),
                        };

                        self.reconstruct_proof_recursive(
                            &premise_fact_owned,
                            &resolved_premise_lit,
                            &mut premise_ctx,
                            Some(rule),
                        )
                    })
                    .collect::<Result<Vec<_>, _>>()?;

                let conclusion = self.ir_literal_to_statement(&rule.head, &premise_ctx)?;
                let cpr = match &rule.head.predicate {
                    ir::PredicateIdentifier::Normal(middleware::Predicate::Custom(cpr)) => {
                        cpr.clone()
                    }
                    _ => {
                        return Err(SolverError::Internal(
                            "Cannot create custom justification for a non-custom predicate"
                                .to_string(),
                        ));
                    }
                };

                let justification = Justification::Custom(cpr, premises);

                Ok(Arc::new(ProofNode {
                    conclusion,
                    justification,
                }))
            }
        };

        // Finally, memoize the result before returning.
        if let Ok(node) = &result {
            ctx.memo.insert(memo_key, node.clone());
        }
        result
    }

    /// Resolves a predicate identifier, converting `BatchSelf` to `Custom` if
    /// the necessary rule context is available.
    fn resolve_predicate_id(
        &self,
        literal: &ir::Literal,
        rule_context: Option<&ir::Rule>,
    ) -> Result<ir::PredicateIdentifier, SolverError> {
        match &literal.predicate {
            ir::PredicateIdentifier::Normal(Predicate::BatchSelf(idx)) => {
                let rule = rule_context.ok_or_else(|| {
                    SolverError::Internal(
                        "Cannot resolve BatchSelf without a rule context.".to_string(),
                    )
                })?;
                let head_cpr = match &rule.head.predicate {
                    ir::PredicateIdentifier::Normal(Predicate::Custom(cpr)) => cpr,
                    _ => return Err(SolverError::Internal(
                        "Cannot resolve BatchSelf in proof reconstruction without custom predicate head.".to_string()
                    ))
                };
                let resolved_cpr =
                    middleware::CustomPredicateRef::new(head_cpr.batch.clone(), *idx);
                Ok(ir::PredicateIdentifier::Normal(Predicate::Custom(
                    resolved_cpr,
                )))
            }
            other => Ok(other.clone()),
        }
    }

    /// Finds a fact in the fact store by its predicate and tuple.
    fn find_fact_by_tuple<'b>(
        &self,
        pred_id: &ir::PredicateIdentifier,
        tuple: &[Value],
    ) -> Result<Option<&'b Fact>, SolverError>
    where
        'a: 'b,
    {
        if let Some(relation) = self.all_facts.get(pred_id) {
            Ok(relation.iter().find(|f| f.tuple == tuple))
        } else {
            Ok(None)
        }
    }

    /// Instantiates an IR literal's terms into a concrete tuple of values using bindings.
    fn instantiate_tuple(
        &self,
        literal: &ir::Literal,
        bindings: &Bindings,
    ) -> Result<Vec<Value>, SolverError> {
        literal
            .terms
            .iter()
            .map(|term| match term {
                ir::Term::Constant(c) => Ok(c.clone()),
                ir::Term::Variable(w) => bindings.get(w).cloned().ok_or_else(|| {
                    SolverError::Internal(format!("Unbound variable in head: ?{}", w.name))
                }),
            })
            .collect()
    }

    /// Converts an instantiated IR literal into a middleware `Statement`.
    /// This is complex because it must reconstruct `AnchoredKey`s from `GetValue` relations.
    fn ir_literal_to_statement(
        &self,
        literal: &ir::Literal,
        ctx: &ProofReconstructionContext,
    ) -> Result<Statement, SolverError> {
        let pred = match &literal.predicate {
            ir::PredicateIdentifier::Normal(p) => p,
            _ => {
                return Err(SolverError::Internal(format!(
                    "Cannot create statement from non-normal predicate: {:?}",
                    literal.predicate
                )))
            }
        };
        let bindings = ctx.bindings;

        // This is a simplified conversion that works for rule heads. A full
        // implementation would need to look at the rule context to reconstruct
        // AnchoredKeys from GetValue literals in the body.
        match pred {
            Predicate::Custom(cpr) => {
                let wcvs = literal
                    .terms
                    .iter()
                    .map(|term| -> Result<Value, SolverError> {
                        match term {
                            ir::Term::Constant(v) => Ok(v.clone()),
                            ir::Term::Variable(w) => {
                                // For custom predicate arguments, we don't reconstruct AnchoredKeys,
                                // we just pass the bound value through.
                                Ok(bindings.get(w).cloned().ok_or_else(|| {
                                    SolverError::Internal(format!(
                                        "Unbound variable ?{} in literal",
                                        w.name
                                    ))
                                })?)
                            }
                        }
                    })
                    .collect::<Result<Vec<_>, _>>()?;
                Ok(Statement::Custom(cpr.clone(), wcvs))
            }
            Predicate::Native(_) => {
                // For native predicates, we can just use the native_literal_to_statement helper
                self.native_literal_to_statement(literal, ctx)
            }
            Predicate::BatchSelf(_) => Err(SolverError::Internal(
                "Cannot convert BatchSelf predicate to a statement directly.".to_string(),
            )),
        }
    }

    /// Converts an IR-level native predicate fact into a middleware `Statement`.
    fn native_literal_to_statement(
        &self,
        literal: &ir::Literal,
        ctx: &ProofReconstructionContext,
    ) -> Result<Statement, SolverError> {
        let native_pred = match &literal.predicate {
            ir::PredicateIdentifier::Normal(Predicate::Native(np)) => np,
            _ => {
                return Err(SolverError::Internal(format!(
                    "Cannot create a native statement from a non-native predicate: {:?}",
                    literal.predicate
                )))
            }
        };

        // The primary logic for converting terms to ValueRefs, using the context.
        let vrs: Vec<ValueRef> = literal
            .terms
            .iter()
            .map(|term| -> Result<ValueRef, SolverError> {
                if let ir::Term::Variable(w) = term {
                    if let Some((pod_wc, key)) = ctx.fresh_var_to_ak_template.get(w) {
                        // This variable came from a GetValue. Reconstruct the AnchoredKey.
                        let pod_id_val = ctx.bindings.get(pod_wc).ok_or_else(|| {
                            SolverError::Internal(format!(
                                "Could not find binding for pod wildcard: ?{}",
                                pod_wc.name
                            ))
                        })?;
                        if let TypedValue::Raw(raw) = pod_id_val.typed() {
                            let pod_id = PodId(Hash(raw.0));
                            return Ok(ValueRef::Key(AnchoredKey::new(pod_id, key.clone())));
                        } else {
                            return Err(SolverError::Internal(
                                "Pod wildcard was not bound to a Raw PodID value".to_string(),
                            ));
                        }
                    }
                }
                // Default case: The term is a constant or a variable not from GetValue.
                // Resolve it to a literal value.
                let value = match term {
                    ir::Term::Constant(c) => c.clone(),
                    ir::Term::Variable(w) => ctx.bindings.get(w).cloned().ok_or_else(|| {
                        SolverError::Internal(format!("Unbound variable ?{}", w.name))
                    })?,
                };
                Ok(ValueRef::Literal(value))
            })
            .collect::<Result<_, _>>()?;

        let statement_args: Vec<middleware::StatementArg> =
            vrs.iter().map(|v| v.clone().into()).collect();
        let statement = Statement::from_args(Predicate::Native(*native_pred), statement_args)
            .map_err(|e| SolverError::Internal(e.to_string()))?;
        Ok(statement)
    }
}
