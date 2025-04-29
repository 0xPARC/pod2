use std::collections::{HashMap, HashSet};

use super::{
    types::{Constraint, Domain, ExpectedType},
    SolverState,
};
use crate::{
    middleware::{KeyOrWildcard, StatementTmpl, StatementTmplArg, Wildcard},
    prover::{error::ProverError, indexing::ProverIndexes, types::ConcreteValue},
}; // Need SolverState definition from mod.rs

// Helper to check for conflicting type assignments for a wildcard
fn update_wildcard_type(
    wildcard_types: &mut HashMap<Wildcard, ExpectedType>,
    wildcard: &Wildcard,
    new_type: ExpectedType,
) -> Result<(), ProverError> {
    let current_type = wildcard_types
        .entry(wildcard.clone())
        .or_insert(ExpectedType::Unknown);

    match (*current_type, new_type) {
        (ExpectedType::Unknown, _) => {
            *current_type = new_type;
            Ok(())
        }
        (t1, t2) if t1 == t2 => Ok(()),
        (t1, t2) => Err(ProverError::Other(format!(
            "Wildcard '{}' used with conflicting types: {:?} and {:?}",
            wildcard.name, t1, t2
        ))),
    }
}

pub(super) fn initialize_solver_state(
    request_templates: &[StatementTmpl],
    indexes: &ProverIndexes,
) -> Result<SolverState, ProverError> {
    let mut wildcard_types: HashMap<Wildcard, ExpectedType> = HashMap::new();
    let mut constraints = Vec::new();

    // 1. Identify wildcards, infer types, and extract structural constraints
    for tmpl in request_templates {
        // First pass: Identify all wildcards and their basic types
        for arg in &tmpl.args {
            match arg {
                StatementTmplArg::Key(wc_pod, key_or_wc) => {
                    update_wildcard_type(&mut wildcard_types, wc_pod, ExpectedType::Pod)?;
                    constraints.push(Constraint::Type {
                        wildcard: wc_pod.clone(),
                        expected_type: ExpectedType::Pod,
                    });
                    match key_or_wc {
                        KeyOrWildcard::Wildcard(wc_key) => {
                            update_wildcard_type(&mut wildcard_types, wc_key, ExpectedType::Key)?;
                            constraints.push(Constraint::Type {
                                wildcard: wc_key.clone(),
                                expected_type: ExpectedType::Key,
                            });
                        }
                        KeyOrWildcard::Key(_) => {}
                    }
                }
                StatementTmplArg::WildcardLiteral(wc_val) => {
                    update_wildcard_type(&mut wildcard_types, wc_val, ExpectedType::Val)?;
                    constraints.push(Constraint::Type {
                        wildcard: wc_val.clone(),
                        expected_type: ExpectedType::Val,
                    });
                }
                StatementTmplArg::Literal(_) | StatementTmplArg::None => {}
            }
        }

        // Second pass: Extract structural constraints based on argument pairings and predicate
        // TODO: Refine this logic based on actual predicate semantics
        match tmpl.pred {
            // Example: If predicate is ValueOf, the first arg (Key) gives LiteralKey/LiteralOrigin constraints
            crate::middleware::Predicate::Native(crate::middleware::NativePredicate::ValueOf) => {
                if let Some(StatementTmplArg::Key(wc_pod, key_or_wc)) = tmpl.args.get(0) {
                    match key_or_wc {
                        KeyOrWildcard::Key(literal_key) => {
                            constraints.push(Constraint::LiteralKey {
                                pod_wildcard: wc_pod.clone(),
                                literal_key: literal_key.name().to_string(),
                            });
                        }
                        KeyOrWildcard::Wildcard(_wc_key) => {
                            // This case implies a relation PodX[?Y] or ?A[?Y]
                            // If the PodId part wc_pod comes from a LiteralOrigin PodId, we might add LiteralOrigin constraint here.
                            // This needs more context about how template arguments are constructed.
                            // For now, we handle LiteralOrigin based on KeyOrWildcard structure below.
                        }
                    }
                }
                // ValueOf doesn't create LiteralValue constraints directly between args
            }
            // Example: If predicate implies equality (like a hypothetical ValueEq)
            // Predicate::ValueEq => { // Hypothetical
            //     if let (Some(StatementTmplArg::WildcardLiteral(w)), Some(StatementTmplArg::Literal(v))) =
            //         (tmpl.args.get(0), tmpl.args.get(1))
            //     {
            //         constraints.push(Constraint::LiteralValue { wildcard: w.clone(), literal_value: v.clone() });
            //     } else if let (Some(StatementTmplArg::Literal(v)), Some(StatementTmplArg::WildcardLiteral(w))) =
            //         (tmpl.args.get(0), tmpl.args.get(1))
            //     {
            //         constraints.push(Constraint::LiteralValue { wildcard: w.clone(), literal_value: v.clone() });
            //     }
            // }
            _ => {
                // Default handling for other predicates, focusing on Key/Literal structure
                for arg in &tmpl.args {
                    match arg {
                        StatementTmplArg::Key(wc_pod, key_or_wc) => {
                            match key_or_wc {
                                KeyOrWildcard::Key(literal_key) => {
                                    constraints.push(Constraint::LiteralKey {
                                        pod_wildcard: wc_pod.clone(),
                                        literal_key: literal_key.name().to_string(),
                                    });
                                }
                                KeyOrWildcard::Wildcard(_wc_key) => {
                                    // Handled by type constraints mostly
                                    // Potential LiteralOrigin needs PodId context
                                }
                            }
                            // Check if wc_pod itself comes from a literal PodId source? Needs more info.
                            // TODO: How to detect LiteralOrigin constraints robustly?
                            // Maybe analyze the template structure that *created* this wc_pod binding?
                            // This seems complex for the initialization phase.
                        }
                        _ => {} // Other arg types handled in first pass or ValueEq example
                    }
                }
            }
        }
    }

    // 2. Establish initial broad domains
    let mut domains = HashMap::new();
    for (wildcard, expected_type) in wildcard_types {
        let initial_domain: Domain = match expected_type {
            ExpectedType::Pod => indexes
                .pod_id_to_anchored_keys()
                .keys()
                .map(|pod_id| ConcreteValue::Pod(*pod_id))
                .collect(),
            ExpectedType::Key => indexes
                .key_to_anchored_keys()
                .keys()
                .map(|k| k.to_string()) // Key struct to String
                .map(ConcreteValue::Key)
                .collect(),
            ExpectedType::Val => indexes
                .value_map()
                .values()
                .map(|value| ConcreteValue::Val(value.clone()))
                .collect(),
            ExpectedType::Unknown => {
                return Err(ProverError::Other(format!(
                    "Could not determine type for wildcard: {}",
                    wildcard.name
                )));
            }
        };
        domains.insert(wildcard, (initial_domain, expected_type));
    }

    Ok(SolverState {
        domains,
        constraints,
        proof_chains: HashMap::new(),
        scope: HashSet::new(),
    })
}
