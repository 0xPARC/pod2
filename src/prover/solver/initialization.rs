use std::{
    collections::{HashMap, HashSet},
    sync::Arc,
};

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

/// Infers the expected type of a public argument (by index) for a custom predicate
/// by recursively analyzing its usage within the predicate's internal statement templates,
/// including nested custom predicate calls.
fn infer_argument_type(
    pred_def: &crate::middleware::CustomPredicate,
    arg_index: usize,
    custom_definitions: &CustomDefinitions,
    params: &crate::middleware::Params,
    current_batch: Option<&Arc<crate::middleware::CustomPredicateBatch>>,
    visited: &mut HashSet<(String, usize)>,
) -> ExpectedType {
    // Prevent infinite recursion in case of cyclic predicate definitions (shouldn't happen ideally)
    let visited_key = (pred_def.name.clone(), arg_index);
    if !visited.insert(visited_key.clone()) {
        println!(
            "Warning: Cycle detected or redundant check during type inference for {} arg {}",
            pred_def.name, arg_index
        );
        return ExpectedType::Unknown; // Avoid infinite loop, return Unknown
    }

    let mut final_type = ExpectedType::Unknown;

    for stmt_tmpl in &pred_def.statements {
        let mut type_from_native = ExpectedType::Unknown;
        let mut type_from_recursive = ExpectedType::Unknown;

        // Check native usage first
        for arg in &stmt_tmpl.args {
            if let Predicate::Native(_) = &stmt_tmpl.pred {
                match arg {
                    StatementTmplArg::Key(wc_pod, key_or_wc) => {
                        if wc_pod.index == arg_index {
                            type_from_native = ExpectedType::Pod;
                            break; // Found direct usage
                        }
                        if let KeyOrWildcard::Wildcard(wc_key) = key_or_wc {
                            if wc_key.index == arg_index {
                                type_from_native = ExpectedType::Key;
                                break; // Found direct usage
                            }
                        }
                    }
                    StatementTmplArg::WildcardLiteral(wc_val) => {
                        if wc_val.index == arg_index {
                            // Don't immediately assume Val, but note it.
                            if type_from_native == ExpectedType::Unknown {
                                type_from_native = ExpectedType::Val;
                            } else if type_from_native != ExpectedType::Val {
                                // Conflict within the same native statement template usage
                                visited.remove(&visited_key);
                                return ExpectedType::Unknown;
                            }
                            // If it matches, no need to break, could be used elsewhere.
                        }
                    }
                    _ => {}
                }
            }
        }

        // If native usage gave a definite type, check for conflicts and update final_type
        if type_from_native != ExpectedType::Unknown {
            if final_type == ExpectedType::Unknown {
                final_type = type_from_native;
            } else if final_type != type_from_native {
                // Conflict found across different templates
                visited.remove(&visited_key);
                return ExpectedType::Unknown;
            }
            continue; // Move to the next statement template
        }

        // If no native usage found in this template, check for recursive usage
        match &stmt_tmpl.pred {
            Predicate::Custom(custom_ref) => {
                // Find which arg position corresponds to our arg_index
                for (nested_arg_pos, arg_tmpl) in stmt_tmpl.args.iter().enumerate() {
                    if let StatementTmplArg::WildcardLiteral(wc) = arg_tmpl {
                        if wc.index == arg_index {
                            // Found the mapping, now recurse
                            let predicate_key =
                                Predicate::Custom(custom_ref.clone()).to_fields(params);
                            if let Some((nested_pred_def, _)) =
                                custom_definitions.get(&predicate_key)
                            {
                                // Pass the nested predicate's batch
                                type_from_recursive = infer_argument_type(
                                    nested_pred_def,
                                    nested_arg_pos,
                                    custom_definitions,
                                    params,
                                    Some(&custom_ref.batch), // Pass Arc ref
                                    visited,
                                );
                                break; // Found the relevant argument, stop inner loop
                            } else {
                                // Definition not found - error? Or just Unknown?
                                println!(
                                    "Warning: Custom def not found for {:?} during type inference",
                                    custom_ref
                                );
                                type_from_recursive = ExpectedType::Unknown;
                                break;
                            }
                        }
                    }
                }
            }
            Predicate::BatchSelf(index) => {
                if let Some(batch_arc) = current_batch {
                    if let Some(nested_pred_def) = batch_arc.predicates.get(*index) {
                        // Find which arg position corresponds to our arg_index
                        for (nested_arg_pos, arg_tmpl) in stmt_tmpl.args.iter().enumerate() {
                            if let StatementTmplArg::WildcardLiteral(wc) = arg_tmpl {
                                if wc.index == arg_index {
                                    // Found the mapping, now recurse
                                    type_from_recursive = infer_argument_type(
                                        nested_pred_def,
                                        nested_arg_pos,
                                        custom_definitions,
                                        params,
                                        Some(batch_arc), // Pass the same batch Arc ref
                                        visited,
                                    );
                                    break; // Found the relevant argument, stop inner loop
                                }
                            }
                        }
                    } else {
                        // Index out of bounds - error? Or just Unknown?
                        println!(
                            "Warning: BatchSelf index {} out of bounds for batch '{}' during type inference",
                            index, batch_arc.name
                        );
                        type_from_recursive = ExpectedType::Unknown;
                    }
                } else {
                    // BatchSelf without context - error? Or just Unknown?
                    println!("Warning: BatchSelf used without current_batch context during type inference");
                    type_from_recursive = ExpectedType::Unknown;
                }
            }
            _ => {} // Native predicate already handled or not relevant here
        }

        // Update final_type based on recursive result, checking for conflicts
        if type_from_recursive != ExpectedType::Unknown {
            if final_type == ExpectedType::Unknown {
                final_type = type_from_recursive;
            } else if final_type != type_from_recursive {
                // Conflict found between native/recursive usage or across different recursive paths
                visited.remove(&visited_key);
                return ExpectedType::Unknown;
            }
            // If a definite type was found via recursion, no need to check further templates *for this arg_index*?
            // Let's allow checking all templates to ensure consistency.
        }
    }

    // Remove the key before returning
    visited.remove(&visited_key);
    final_type
}

/// Helper function to recursively parse templates and generate constraints.
fn parse_template_and_generate_constraints(
    tmpl: &StatementTmpl,
    current_batch: Option<Arc<crate::middleware::CustomPredicateBatch>>,
    wildcard_types: &mut HashMap<Wildcard, ExpectedType>,
    constraints: &mut Vec<Constraint>,
    custom_definitions: &CustomDefinitions,
    indexes: &ProverIndexes,
    alias_map: &HashMap<usize, Wildcard>,
) -> Result<(), ProverError> {
    // --- Pass 1: Basic Type Inference & Constraints from Arguments ---
    // Apply constraints based on the structure of the *current* template (`tmpl`)
    // using the *caller's* wildcards (accessed via alias_map if needed).
    for arg in &tmpl.args {
        match arg {
            StatementTmplArg::Key(inner_wc_pod, key_or_wc) => {
                // Resolve inner pod wc using alias map
                let outer_wc_pod = match alias_map.get(&inner_wc_pod.index) {
                    Some(outer_wc) => outer_wc,
                    None => inner_wc_pod, // Should only happen for private wildcards
                };
                update_wildcard_type(wildcard_types, outer_wc_pod, ExpectedType::Pod)?;
                // Constraint always applies to the outer/aliased wildcard
                constraints.push(Constraint::Type {
                    wildcard: outer_wc_pod.clone(),
                    expected_type: ExpectedType::Pod,
                });

                match key_or_wc {
                    KeyOrWildcard::Wildcard(inner_wc_key) => {
                        // Resolve inner key wc using alias map
                        let outer_wc_key = match alias_map.get(&inner_wc_key.index) {
                            Some(outer_wc) => outer_wc,
                            None => inner_wc_key,
                        };
                        update_wildcard_type(wildcard_types, outer_wc_key, ExpectedType::Key)?;
                        constraints.push(Constraint::Type {
                            wildcard: outer_wc_key.clone(),
                            expected_type: ExpectedType::Key,
                        });
                        // WildcardOrigin constraint relates the outer/aliased key and pod wildcards
                        constraints.push(Constraint::WildcardOrigin {
                            key_wildcard: outer_wc_key.clone(),
                            pod_wildcard: outer_wc_pod.clone(),
                        });
                    }
                    KeyOrWildcard::Key(literal_key) => {
                        // LiteralKey constraint applies to the outer/aliased pod wildcard
                        constraints.push(Constraint::LiteralKey {
                            pod_wildcard: outer_wc_pod.clone(),
                            literal_key: literal_key.name().to_string(),
                        });
                    }
                }
            }
            StatementTmplArg::WildcardLiteral(inner_wc_val) => {
                // Resolve inner val wc using alias map
                let outer_wc_val = match alias_map.get(&inner_wc_val.index) {
                    Some(outer_wc) => outer_wc,
                    None => inner_wc_val,
                };
                // The type for outer_wc_val will be correctly inferred when it's used
                // as an argument to a Custom/BatchSelf predicate call later in Pass 2.
            }
            StatementTmplArg::Literal(_lit_val) => {
                // TODO: Handle propagation of literal constraints down through aliases?
                // For now, assume Constraint::LiteralValue generated elsewhere handles this.
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

                    // 2. Create the next level alias map (`next_alias_map`)
                    let mut next_alias_map: HashMap<usize, Wildcard> =
                        HashMap::with_capacity(public_args_count);
                    for i in 0..public_args_count {
                        match tmpl.args.get(i) {
                            Some(StatementTmplArg::WildcardLiteral(outer_wc_from_tmpl)) => {
                                // Infer the type the target predicate expects for this argument index
                                let mut visited = HashSet::new(); // Create visited set for this inference path
                                let expected_arg_type = infer_argument_type(
                                    custom_pred_def,
                                    i,
                                    custom_definitions,
                                    &indexes.params,
                                    Some(&custom_ref.batch), // Pass batch from the Custom ref
                                    &mut visited,
                                );

                                // Resolve the wildcard passed by the caller using the *current* alias map
                                let actual_outer_wc = match alias_map.get(&outer_wc_from_tmpl.index)
                                {
                                    Some(outer_wc) => outer_wc,
                                    None => outer_wc_from_tmpl, // Use the template WC if no alias found (should mean it's top-level)
                                };

                                // Update the type for the *actual* outer wildcard
                                update_wildcard_type(
                                    wildcard_types,
                                    actual_outer_wc,
                                    expected_arg_type,
                                )?;

                                // Add type constraint for the *actual* outer wildcard
                                constraints.push(Constraint::Type {
                                    wildcard: actual_outer_wc.clone(),
                                    expected_type: expected_arg_type,
                                });

                                // Map: Inner Predicate Arg Index -> Actual Outer Wildcard
                                next_alias_map.insert(i, actual_outer_wc.clone());
                            }
                            Some(arg) => {
                                // Invalid Argument Type: Expected StatementTmplArg::WildcardLiteral when
                                // processing arguments for a custom predicate call, but found a different
                                // variant. This likely indicates an invalid template structure.
                                return Err(ProverError::Internal(format!(
                                    "Expected WildcardLiteral arg at index {} when calling Custom predicate '{}', found {:?}",
                                    i, custom_pred_def.name, arg
                                )));
                            }
                            None => {
                                return Err(ProverError::Internal(format!(
                                    "Argument count mismatch: Custom predicate '{}' expects {} args, but caller template provided fewer.",
                                    custom_pred_def.name, public_args_count
                                )));
                            }
                        }
                    }
                    // println!("Warning: Alias map creation for custom predicates not yet fully implemented in initialization.");

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
                            Some(custom_ref.batch.clone()),
                            wildcard_types,
                            constraints,
                            custom_definitions,
                            indexes,
                            &next_alias_map,
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
            if let Some(current_batch_arc) = current_batch.as_ref() {
                // Resolve the target predicate definition using the current batch context
                let target_pred_def =
                    current_batch_arc.predicates.get(*index).ok_or_else(|| {
                        ProverError::Internal(format!(
                            "BatchSelf index {} out of bounds for batch '{}' during initialization",
                            index, current_batch_arc.name
                        ))
                    })?;

                // Now we have the target_pred_def. Proceed with AND/OR logic and recursion.
                if target_pred_def.conjunction {
                    // --- AND Predicate Handling (Similar to Custom) ---
                    let inner_wildcards =
                        get_wildcards_from_definition_stmts(&target_pred_def.statements);
                    let public_args_count = target_pred_def.args_len;

                    // Create the next alias map (Step 3)
                    let mut next_alias_map: HashMap<usize, Wildcard> =
                        HashMap::with_capacity(public_args_count);
                    for i in 0..public_args_count {
                        match tmpl.args.get(i) {
                            Some(StatementTmplArg::WildcardLiteral(outer_wc_from_tmpl)) => {
                                // Infer the type the target predicate expects for this argument index
                                let mut visited = HashSet::new(); // Create visited set for this inference path
                                let expected_arg_type = infer_argument_type(
                                    target_pred_def,
                                    i,
                                    custom_definitions,
                                    &indexes.params,
                                    Some(current_batch_arc), // Pass the current batch
                                    &mut visited,
                                );

                                // Resolve the wildcard passed by the caller using the *current* alias map
                                let actual_outer_wc = match alias_map.get(&outer_wc_from_tmpl.index)
                                {
                                    Some(outer_wc) => outer_wc,
                                    None => outer_wc_from_tmpl, // Use the template WC if no alias found
                                };

                                // Update the type for the *actual* outer wildcard
                                update_wildcard_type(
                                    wildcard_types,
                                    actual_outer_wc,
                                    expected_arg_type,
                                )?;

                                // Add type constraint for the *actual* outer wildcard
                                constraints.push(Constraint::Type {
                                    wildcard: actual_outer_wc.clone(),
                                    expected_type: expected_arg_type,
                                });

                                // Map: Inner Predicate Arg Index -> Actual Outer Wildcard
                                next_alias_map.insert(i, actual_outer_wc.clone());
                            }
                            Some(arg) => {
                                // Invalid Argument Type: Expected StatementTmplArg::WildcardLiteral when
                                // processing arguments for a BatchSelf predicate call, but found a different
                                // variant. This likely indicates an invalid template structure.
                                return Err(ProverError::Internal(format!(
                                    "Expected WildcardLiteral arg at index {} when calling BatchSelf predicate '{}', found {:?}",
                                    i, target_pred_def.name, arg
                                )));
                            }
                            None => {
                                return Err(ProverError::Internal(format!(
                                    "Argument count mismatch: BatchSelf predicate '{}' expects {} args, but caller template provided fewer.",
                                    target_pred_def.name, public_args_count
                                )));
                            }
                        }
                    }
                    // println!("Warning: Alias map creation for BatchSelf not yet implemented.");

                    // Identify and Register Private Wildcards (Step 6 - verification needed)
                    for inner_wc in &inner_wildcards {
                        if inner_wc.index >= public_args_count {
                            wildcard_types
                                .entry(inner_wc.clone())
                                .or_insert(ExpectedType::Unknown);
                        }
                    }

                    // Recursively Parse Internal Templates (Step 4)
                    for internal_tmpl in &target_pred_def.statements {
                        parse_template_and_generate_constraints(
                            internal_tmpl,
                            Some(current_batch_arc.clone()),
                            wildcard_types,
                            constraints,
                            custom_definitions,
                            indexes,
                            &next_alias_map,
                        )?;
                    }
                } else {
                    // --- OR Predicate Handling ---
                    println!(
                        "Skipping OR predicate (BatchSelf) constraint generation during init: {}",
                        target_pred_def.name
                    );
                }
            } else {
                // BatchSelf encountered without a current_batch context
                return Err(ProverError::Internal(
                    "BatchSelf predicate encountered outside of a batch context during initialization"
                        .to_string(),
                ));
            }
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
    let initial_alias_map: HashMap<usize, Wildcard> = HashMap::new();

    for tmpl in request_templates {
        parse_template_and_generate_constraints(
            tmpl,
            None, // Top-level calls have no current_batch
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
