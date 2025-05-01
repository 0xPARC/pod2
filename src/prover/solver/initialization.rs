use std::collections::{HashMap, HashSet};

use super::{
    types::{Constraint, Domain, ExpectedType},
    SolverState,
};
use crate::{
    middleware::{KeyOrWildcard, Predicate, StatementTmpl, StatementTmplArg, ToFields, Wildcard},
    prover::{
        error::ProverError,
        indexing::ProverIndexes,
        types::{ConcreteValue, CustomDefinitions},
    },
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

/// Helper function to get all wildcards defined within a CustomPredicate's statements.
fn get_wildcards_from_definition_stmts(statements: &[StatementTmpl]) -> HashSet<Wildcard> {
    let mut wildcards = HashSet::new();
    for stmt_tmpl in statements {
        for arg in &stmt_tmpl.args {
            match arg {
                StatementTmplArg::Key(wc_pod, key_or_wc) => {
                    wildcards.insert(wc_pod.clone());
                    if let KeyOrWildcard::Wildcard(wc_key) = key_or_wc {
                        wildcards.insert(wc_key.clone());
                    }
                }
                StatementTmplArg::WildcardLiteral(wc_val) => {
                    wildcards.insert(wc_val.clone());
                }
                _ => {}
            }
        }
        // Consider wildcards within nested custom predicate calls if needed
        if let Predicate::Custom(custom_ref) = &stmt_tmpl.pred {
            // We currently parse recursively, so nested wildcards are handled there.
        }
    }
    wildcards
}

/// Helper function to get all wildcards used in a specific StatementTmplArg.
fn get_wildcards_from_tmpl_arg(arg: &StatementTmplArg) -> Vec<Wildcard> {
    match arg {
        StatementTmplArg::Key(wc_pod, KeyOrWildcard::Wildcard(wc_key)) => {
            vec![wc_pod.clone(), wc_key.clone()]
        }
        StatementTmplArg::Key(wc_pod, KeyOrWildcard::Key(_)) => vec![wc_pod.clone()],
        StatementTmplArg::WildcardLiteral(wc_val) => vec![wc_val.clone()],
        _ => vec![],
    }
}

/// Helper function to recursively parse templates and generate constraints.
fn parse_template_and_generate_constraints(
    tmpl: &StatementTmpl,
    // Wildcards defined in the *calling* context (could be top-level or from an outer predicate)
    // caller_args_tmpl: &[StatementTmplArg], // May not be needed if alias map is correct
    wildcard_types: &mut HashMap<Wildcard, ExpectedType>,
    constraints: &mut Vec<Constraint>,
    custom_definitions: &CustomDefinitions,
    indexes: &ProverIndexes,
    // Map from INNER wildcards (of the predicate being processed) to OUTER wildcards (from caller)
    // TODO: Implement alias map logic carefully
    alias_map: &HashMap<Wildcard, Wildcard>,
) -> Result<(), ProverError> {
    // --- Pass 1: Basic Type Inference & Constraints from Arguments ---
    // Apply constraints based on the structure of the *current* template (`tmpl`)
    // using the *caller's* wildcards (accessed via alias_map if needed).
    for arg in &tmpl.args {
        match arg {
            StatementTmplArg::Key(inner_wc_pod, key_or_wc) => {
                let outer_wc_pod = alias_map.get(inner_wc_pod).unwrap_or(inner_wc_pod); // Use outer alias if exists
                update_wildcard_type(wildcard_types, outer_wc_pod, ExpectedType::Pod)?;
                constraints.push(Constraint::Type {
                    wildcard: outer_wc_pod.clone(),
                    expected_type: ExpectedType::Pod,
                });

                match key_or_wc {
                    KeyOrWildcard::Wildcard(inner_wc_key) => {
                        let outer_wc_key = alias_map.get(inner_wc_key).unwrap_or(inner_wc_key);
                        update_wildcard_type(wildcard_types, outer_wc_key, ExpectedType::Key)?;
                        constraints.push(Constraint::Type {
                            wildcard: outer_wc_key.clone(),
                            expected_type: ExpectedType::Key,
                        });
                        // Add WildcardOrigin constraint instead of trying to access domain here
                        constraints.push(Constraint::WildcardOrigin {
                            key_wildcard: outer_wc_key.clone(),
                            pod_wildcard: outer_wc_pod.clone(), // Use the potentially aliased outer pod wildcard
                        });
                    }
                    KeyOrWildcard::Key(literal_key) => {
                        constraints.push(Constraint::LiteralKey {
                            pod_wildcard: outer_wc_pod.clone(), // Constraint on the outer Pod wildcard
                            literal_key: literal_key.name().to_string(),
                        });
                    }
                }
            }
            StatementTmplArg::WildcardLiteral(inner_wc_val) => {
                let outer_wc_val = alias_map.get(inner_wc_val).unwrap_or(inner_wc_val);
                update_wildcard_type(wildcard_types, outer_wc_val, ExpectedType::Val)?;
                constraints.push(Constraint::Type {
                    wildcard: outer_wc_val.clone(),
                    expected_type: ExpectedType::Val,
                });
            }
            StatementTmplArg::Literal(lit_val) => {
                // If this literal is used as an argument to a custom predicate,
                // we need to propagate this constraint down.
                // Find the wildcard this literal corresponds to in the alias map.
                // This requires iterating through the alias map to find the key whose value is this literal's position?
                // This is getting complex. Let's assume for now that literal constraints
                // are primarily handled during pruning based on the `Constraint::LiteralValue`.

                // If this template uses a literal value, potentially create a constraint for any wildcard used in the corresponding position
                // e.g. ValueOf(?A[?X], Literal(10)). If ?A[?X] corresponds to ?V, add constraint LiteralValue{?V, 10}
                // This requires knowing the mapping from tmpl.args to wildcards.

                // Alternative: Look for wildcards in this position via alias map.
                // Find `inner_wc` such that `alias_map.get(inner_wc) == Some(outer_wc_representing_this_position)`.
                // Then add `Constraint::LiteralValue { wildcard: outer_wc, literal_value: lit_val.clone() }`.
            }
            StatementTmplArg::None => {}
        }
    }

    // --- Pass 2: Predicate-Specific Constraints & Recursion ---
    match &tmpl.pred {
        Predicate::Native(native_pred) => {
            // TODO: Generate predicate-specific constraints based on native predicate rules
            // E.g., Gt/Lt -> args must resolve to Int (Type constraints handled above)
            // SumOf/ProductOf -> args must resolve to Int (Type constraints handled above)
            // Contains -> arg0 must be container (Val), arg1 key/index (Val), arg2 value (Val)
            // Need to ensure the *concrete types* within Val match (e.g., Int for SumOf) later during pruning/proof.
        }
        Predicate::Custom(custom_ref) => {
            let predicate_key = Predicate::Custom(custom_ref.clone()).to_fields(&indexes.params);
            if let Some((custom_pred_def, _batch_arc)) = custom_definitions.get(&predicate_key) {
                if custom_pred_def.conjunction {
                    // --- AND Predicate Handling ---

                    // 1. Identify Inner Wildcards (Public vs. Private)
                    let inner_wildcards =
                        get_wildcards_from_definition_stmts(&custom_pred_def.statements);
                    let public_args_count = custom_pred_def.args_len;

                    // 2. TODO: Create the *next level* alias map (`next_alias_map`)
                    // This is complex: map inner public wildcards (index < args_len)
                    // to the corresponding outer wildcards provided in `tmpl.args`.
                    // Requires careful handling of how Key(wc_pod, wc_key) etc. map positionally.
                    // For now, we pass an empty map recursively.
                    let next_alias_map: HashMap<Wildcard, Wildcard> = HashMap::new();
                    println!("Warning: Alias map creation for custom predicates not yet fully implemented in initialization.");

                    // 3. Identify and Register Private Wildcards
                    for inner_wc in &inner_wildcards {
                        if inner_wc.index >= public_args_count {
                            // Ensure the private wildcard is tracked, defaulting to Unknown type if new
                            wildcard_types
                                .entry(inner_wc.clone())
                                .or_insert(ExpectedType::Unknown);
                            println!("Identified private wildcard: {:?}", inner_wc);
                        }
                    }

                    // 4. Recursively Parse Internal Templates
                    for internal_tmpl in &custom_pred_def.statements {
                        parse_template_and_generate_constraints(
                            internal_tmpl,
                            // tmpl.args(), // Pass caller args down? Or rely on alias map?
                            wildcard_types,
                            constraints,
                            custom_definitions,
                            indexes,
                            &next_alias_map, // Pass the (currently empty) next alias map
                        )?;
                    }
                } else {
                    // --- OR Predicate Handling ---
                    // Do nothing during initialization, constraints are handled during proof search.
                    println!(
                        "Skipping OR predicate constraint generation during init: {}",
                        custom_pred_def.name
                    );
                }
            } else {
                return Err(ProverError::Other(format!(
                    "Custom predicate definition not found for ref: {:?}",
                    custom_ref
                )));
            }
        }
        Predicate::BatchSelf(index) => {
            // TODO: Resolve BatchSelf index based on context.
            return Err(ProverError::NotImplemented(
                "BatchSelf predicate parsing during initialization".to_string(),
            ));
        }
    }

    Ok(())
}

pub(super) fn initialize_solver_state(
    request_templates: &[StatementTmpl],
    indexes: &ProverIndexes,
    custom_definitions: &CustomDefinitions,
) -> Result<SolverState, ProverError> {
    let mut wildcard_types: HashMap<Wildcard, ExpectedType> = HashMap::new();
    let mut constraints = Vec::new();

    // Top-level calls don't have an alias map initially
    let initial_alias_map = HashMap::new();

    for tmpl in request_templates {
        parse_template_and_generate_constraints(
            tmpl,
            // tmpl.args(), // Pass top-level template args?
            &mut wildcard_types,
            &mut constraints,
            custom_definitions,
            indexes,
            &initial_alias_map,
        )?;
    }

    // Establish initial broad domains for ALL identified wildcards (including private ones)
    let mut domains = HashMap::new();
    for (wildcard, expected_type) in &wildcard_types {
        let initial_domain: Domain = match expected_type {
            ExpectedType::Pod => indexes
                .pod_id_to_anchored_keys()
                .keys()
                .map(|pod_id| ConcreteValue::Pod(*pod_id))
                .collect(),
            ExpectedType::Key => indexes
                .key_to_anchored_keys()
                .keys()
                .map(|k| k.to_string())
                .map(ConcreteValue::Key)
                .collect(),
            ExpectedType::Val => indexes
                .value_map()
                .values()
                .map(|value| ConcreteValue::Val(value.clone()))
                .collect(),
            ExpectedType::Unknown => {
                // Type should be inferred during the recursive parsing. If still Unknown, something went wrong or it's truly unconstrained.
                // For now, assign a broad domain and let pruning handle it.
                println!(
                    "Warning: Wildcard {} still has Unknown type after parsing. Assigning broad domain.",
                    wildcard.name
                );
                let all_pods: HashSet<_> = indexes
                    .pod_id_to_anchored_keys()
                    .keys()
                    .map(|id| ConcreteValue::Pod(*id))
                    .collect();
                let all_keys: HashSet<_> = indexes
                    .key_to_anchored_keys()
                    .keys()
                    .map(|k| ConcreteValue::Key(k.to_string()))
                    .collect();
                let all_vals: HashSet<_> = indexes
                    .value_map()
                    .values()
                    .map(|v| ConcreteValue::Val(v.clone()))
                    .collect();
                all_pods
                    .union(&all_keys)
                    .cloned()
                    .collect::<HashSet<_>>()
                    .union(&all_vals)
                    .cloned()
                    .collect()
            }
        };
        // Check if domain is empty only if the corresponding index is non-empty
        let domain_is_meaningfully_empty = match expected_type {
            ExpectedType::Pod => {
                !indexes.pod_id_to_anchored_keys().is_empty() && initial_domain.is_empty()
            }
            ExpectedType::Key => {
                !indexes.key_to_anchored_keys().is_empty() && initial_domain.is_empty()
            }
            ExpectedType::Val => !indexes.value_map().is_empty() && initial_domain.is_empty(),
            ExpectedType::Unknown => initial_domain.is_empty(), // Empty if everything is empty
        };

        if domain_is_meaningfully_empty {
            // This indicates an issue, perhaps the wildcard type is constrained in a way
            // that no known values match. However, this might be okay if the wildcard
            // is expected to bind to a value generated *during* the solve.
            println!(
                "Warning: Initial domain for {} ({:?}) is empty based on known indexes.",
                wildcard.name, expected_type
            );
        }
        domains.insert(wildcard.clone(), (initial_domain, *expected_type));
    }

    // Remove duplicates constraints if any
    let constraints_set: HashSet<_> = constraints.drain(..).collect();
    constraints.extend(constraints_set);

    Ok(SolverState {
        params: indexes.params.clone(),
        domains,
        constraints,
        proof_chains: HashMap::new(),
        scope: HashSet::new(),
    })
}
