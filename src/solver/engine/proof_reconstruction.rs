use std::{
    collections::{HashMap, HashSet},
    sync::Arc,
};

use crate::{
    middleware::{
        AnchoredKey as MWAnchoredKey, CustomPredicateRef, PodId, Predicate, Statement,
        StatementTmplArg, Value, ValueRef, Wildcard,
    },
    solver::{
        engine::semi_naive::{Fact, FactSource, FactStore, JustificationKind, ProvenanceStore},
        error::SolverError,
        ir,
        proof::{Justification, ProofNode},
        semantics::materializer::Materializer,
    },
};

/// Responsible for turning a derived fact back into a `ProofNode` tree by
/// following the `(rule, bindings)` information stored in the
/// `ProvenanceStore`.
pub struct ProofReconstructor<'a> {
    all_facts: &'a FactStore,
    provenance: &'a ProvenanceStore,
    materializer: &'a Materializer,
    /// Guard against cycles in recursive rules.
    visited: HashSet<(ir::PredicateIdentifier, Vec<ValueRef>)>,
}

impl<'a> ProofReconstructor<'a> {
    pub fn new(
        all_facts: &'a FactStore,
        provenance: &'a ProvenanceStore,
        materializer: &'a Materializer,
    ) -> Self {
        Self {
            all_facts,
            provenance,
            materializer,
            visited: HashSet::new(),
        }
    }

    /// Entry-point. Builds a proof tree for the given fact.
    pub fn build(
        mut self,
        pid: &ir::PredicateIdentifier,
        fact: &Fact,
    ) -> Result<Arc<ProofNode>, SolverError> {
        self.build_inner(pid, fact)
    }

    fn build_inner(
        &mut self,
        pid: &ir::PredicateIdentifier,
        fact: &Fact,
    ) -> Result<Arc<ProofNode>, SolverError> {
        if !self.visited.insert((pid.clone(), fact.args.clone())) {
            // Already constructing this node – break cycle.
            return Ok(Arc::new(ProofNode {
                conclusion: Statement::None,
                justification: Justification::Fact,
            }));
        }

        let conclusion = self.statement_from_fact(pid, fact)?;

        let node = match &fact.source {
            FactSource::External(kind) => {
                let just = match kind {
                    JustificationKind::Existing => Justification::Fact,
                    JustificationKind::ByValue(_) => Justification::ValueComparison,
                    JustificationKind::Special => Justification::ValueComparison,
                };
                Arc::new(ProofNode {
                    conclusion,
                    justification: just,
                })
            }
            FactSource::Derived => {
                let key = (pid.clone(), fact.args.clone());
                let (rule, bindings) = self.provenance.get(&key).ok_or_else(|| {
                    SolverError::Internal("Missing provenance for derived fact".into())
                })?;

                // Build premises recursively (skip magic predicates).
                let mut premises = Vec::new();
                for body_atom in &rule.body {
                    if matches!(body_atom.predicate, ir::PredicateIdentifier::Magic { .. }) {
                        continue;
                    }

                    let resolved_pid = self.resolve_predicate_id(body_atom, rule)?;
                    let instantiated_args = self.instantiate_atom(body_atom, bindings)?;

                    // Find the matching fact.
                    let body_fact = self
                        .all_facts
                        .get(&resolved_pid)
                        .and_then(|rel| rel.iter().find(|f| f.args == instantiated_args).cloned())
                        .ok_or_else(|| {
                            SolverError::Internal(format!(
                                "Could not locate fact for {:?} {:?}",
                                resolved_pid, instantiated_args
                            ))
                        })?;

                    let child = self.build_inner(&resolved_pid, &body_fact)?;
                    premises.push(child);
                }

                let justification = match pid {
                    ir::PredicateIdentifier::Normal(Predicate::Custom(cpr)) => {
                        Justification::Custom(cpr.clone(), premises)
                    }
                    _ => Justification::ValueComparison, // fallback for native or others
                };

                Arc::new(ProofNode {
                    conclusion,
                    justification,
                })
            }
        };

        Ok(node)
    }

    // ------------ helpers ----------------

    fn statement_from_fact(
        &self,
        pid: &ir::PredicateIdentifier,
        fact: &Fact,
    ) -> Result<Statement, SolverError> {
        match pid {
            ir::PredicateIdentifier::Normal(pred) => match pred {
                Predicate::Custom(cpr) => {
                    // Convert args to Values (Literal only).
                    let mut vals = Vec::new();
                    for vr in &fact.args {
                        match vr {
                            ValueRef::Literal(v) => vals.push(v.clone()),
                            ValueRef::Key(_) => {
                                if let Some(v) = self.materializer.value_ref_to_value(vr) {
                                    vals.push(v);
                                } else {
                                    return Err(SolverError::Internal(
                                        "Cannot dereference key to value".into(),
                                    ));
                                }
                            }
                        }
                    }
                    Ok(Statement::Custom(cpr.clone(), vals))
                }
                Predicate::Native(np) => {
                    use Statement::*;

                    use crate::middleware::NativePredicate as NP;
                    let s = match (np, fact.args.as_slice()) {
                        (NP::Equal, [a, b]) => Equal(a.clone(), b.clone()),
                        (NP::NotEqual, [a, b]) => NotEqual(a.clone(), b.clone()),
                        (NP::LtEq, [a, b]) => LtEq(a.clone(), b.clone()),
                        (NP::Lt, [a, b]) => Lt(a.clone(), b.clone()),
                        (NP::Contains, [r, k, v]) => Contains(r.clone(), k.clone(), v.clone()),
                        (NP::NotContains, [r, k]) => NotContains(r.clone(), k.clone()),
                        (NP::SumOf, [a, b, c]) => SumOf(a.clone(), b.clone(), c.clone()),
                        (NP::ProductOf, [a, b, c]) => ProductOf(a.clone(), b.clone(), c.clone()),
                        (NP::MaxOf, [a, b, c]) => MaxOf(a.clone(), b.clone(), c.clone()),
                        (NP::HashOf, [a, b, c]) => HashOf(a.clone(), b.clone(), c.clone()),
                        _ => {
                            return Err(SolverError::Internal(
                                "Unsupported native predicate".into(),
                            ))
                        }
                    };
                    Ok(s)
                }
                Predicate::BatchSelf(_) => {
                    Err(SolverError::Internal("BatchSelf unexpected".into()))
                }
            },
            _ => Err(SolverError::Internal(
                "Magic predicate has no statement".into(),
            )),
        }
    }

    fn instantiate_atom(
        &self,
        atom: &ir::Atom,
        bindings: &HashMap<Wildcard, Value>,
    ) -> Result<Vec<ValueRef>, SolverError> {
        use StatementTmplArg::*;
        atom.terms
            .iter()
            .map(|term| match term {
                Literal(v) => Ok(ValueRef::Literal(v.clone())),
                Wildcard(w) => bindings
                    .get(w)
                    .cloned()
                    .map(ValueRef::Literal)
                    .ok_or_else(|| SolverError::Internal("Unbound wildcard in body".into())),
                AnchoredKey(pod_wc, key) => {
                    let pod_val = bindings.get(pod_wc).cloned().ok_or_else(|| {
                        SolverError::Internal("Unbound pod wildcard in AnchoredKey".into())
                    })?;
                    let pid = PodId::try_from(pod_val.typed())
                        .map_err(|e| SolverError::Internal(format!("{e}")))?;
                    Ok(ValueRef::Key(MWAnchoredKey::new(pid, key.clone())))
                }
                None => Err(SolverError::Internal("None arg not allowed".into())),
            })
            .collect()
    }

    fn resolve_predicate_id(
        &self,
        lit: &ir::Atom,
        rule: &ir::Rule,
    ) -> Result<ir::PredicateIdentifier, SolverError> {
        use crate::middleware::Predicate as P;
        match &lit.predicate {
            ir::PredicateIdentifier::Normal(P::BatchSelf(idx)) => match &rule.head.predicate {
                ir::PredicateIdentifier::Normal(P::Custom(head_cpr)) => {
                    Ok(ir::PredicateIdentifier::Normal(P::Custom(
                        CustomPredicateRef::new(head_cpr.batch.clone(), *idx),
                    )))
                }
                _ => Err(SolverError::Internal(
                    "BatchSelf literal in rule whose head is not custom".into(),
                )),
            },
            other => Ok(other.clone()),
        }
    }
}
