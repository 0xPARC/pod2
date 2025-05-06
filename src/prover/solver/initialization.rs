use std::{
    collections::{HashMap, HashSet},
    sync::Arc,
};

use super::{
    types::{Constraint, Domain, ExpectedType},
    SolverState,
};
use crate::{
    middleware::{
        AnchoredKey, CustomPredicate, CustomPredicateBatch, Key, KeyOrWildcard, NativePredicate,
        Params, PodId, Predicate, Statement, StatementTmpl, StatementTmplArg, ToFields, Value,
        Wildcard, SELF,
    },
    prover::{
        error::ProverError,
        indexing::ProverIndexes,
        types::{ConcreteValue, CustomDefinitions},
    },
};

// Key for the visited set in parse_template_and_generate_constraints
type VisitedPredicateParseKey = (*const CustomPredicateBatch, usize);

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
    }
    wildcards
}

/// Infers the expected type of a public argument (by index) for a custom predicate
/// by recursively analyzing its usage within the predicate's internal statement templates,
/// including nested custom predicate calls.
fn infer_argument_type(
    pred_def: &CustomPredicate,
    arg_index: usize,
    custom_definitions: &CustomDefinitions,
    params: &Params,
    current_batch: Option<&Arc<CustomPredicateBatch>>,
    visited: &mut HashSet<(String, usize)>,
) -> ExpectedType {
    // Prevent infinite recursion in case of cyclic predicate definitions (shouldn't happen ideally)
    let visited_key = (pred_def.name.clone(), arg_index);
    if !visited.insert(visited_key.clone()) {
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
                                type_from_recursive = infer_argument_type(
                                    nested_pred_def,
                                    nested_arg_pos,
                                    custom_definitions,
                                    params,
                                    Some(&custom_ref.batch),
                                    visited,
                                );
                                break; // Found the relevant argument, stop inner loop
                            } else {
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
                                        Some(batch_arc),
                                        visited,
                                    );
                                    break; // Found the relevant argument, stop inner loop
                                }
                            }
                        }
                    } else {
                        type_from_recursive = ExpectedType::Unknown;
                    }
                } else {
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
        }
    }

    visited.remove(&visited_key);
    final_type
}

type PotentialConstantInfo = (Wildcard, Key, Value);

/// Helper function to recursively parse templates and generate constraints.
/// Also collects literal values encountered.
fn parse_template_and_generate_constraints(
    tmpl: &StatementTmpl,
    current_batch: Option<Arc<CustomPredicateBatch>>,
    wildcard_types: &mut HashMap<Wildcard, ExpectedType>,
    constraints: &mut Vec<Constraint>,
    context: &SolverContext,
    alias_map: &HashMap<usize, Wildcard>,
    constant_template_info: &mut Vec<PotentialConstantInfo>,
    visited_parse: &mut HashSet<VisitedPredicateParseKey>,
) -> Result<(), ProverError> {
    let custom_definitions = context.custom_definitions;
    let params = context.params;

    // --- Pass 1: Basic Type Inference & Constraints from Arguments ---
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
            StatementTmplArg::WildcardLiteral(_) => {}
            StatementTmplArg::Literal(_) => {}
            StatementTmplArg::None => {}
        }
    }

    // --- Pass 2: Predicate-Specific Constraints & Recursion ---
    match &tmpl.pred {
        Predicate::Native(NativePredicate::ValueOf) => {
            if tmpl.args.len() == 2 {
                if let (
                    StatementTmplArg::Key(wc_pod_holder, KeyOrWildcard::Key(const_key)),
                    StatementTmplArg::Literal(literal_value),
                ) = (&tmpl.args[0], &tmpl.args[1])
                {
                    // Matched the pattern!
                    constant_template_info.push((
                        wc_pod_holder.clone(),
                        const_key.clone(),
                        literal_value.clone(), // Store the actual value
                    ));
                    // Apply type constraints
                    update_wildcard_type(wildcard_types, wc_pod_holder, ExpectedType::Pod)?;
                    // We know the value is literal, so no type constraint needed for it here.
                    constraints.push(Constraint::Type {
                        wildcard: wc_pod_holder.clone(),
                        expected_type: ExpectedType::Pod,
                    });
                    // Add constraint relating holder and key
                    constraints.push(Constraint::LiteralKey {
                        pod_wildcard: wc_pod_holder.clone(),
                        literal_key: const_key.name().to_string(),
                    });
                } else {
                    // This is the branch for when the pattern doesn't match
                    // Apply standard type inference/constraints if not the constant pattern
                    // (This part might need refinement depending on other ValueOf uses)
                    for arg in &tmpl.args {
                        match arg {
                            StatementTmplArg::Key(wc_pod, key_or_wc) => {
                                let outer_wc_pod = alias_map.get(&wc_pod.index).unwrap_or(wc_pod);
                                update_wildcard_type(
                                    wildcard_types,
                                    outer_wc_pod,
                                    ExpectedType::Pod,
                                )?;
                                constraints.push(Constraint::Type {
                                    wildcard: outer_wc_pod.clone(),
                                    expected_type: ExpectedType::Pod,
                                });
                                match key_or_wc {
                                    KeyOrWildcard::Wildcard(wc_key) => {
                                        let outer_wc_key =
                                            alias_map.get(&wc_key.index).unwrap_or(wc_key);
                                        update_wildcard_type(
                                            wildcard_types,
                                            outer_wc_key,
                                            ExpectedType::Key,
                                        )?;
                                        constraints.push(Constraint::Type {
                                            wildcard: outer_wc_key.clone(),
                                            expected_type: ExpectedType::Key,
                                        });
                                        constraints.push(Constraint::WildcardOrigin {
                                            key_wildcard: outer_wc_key.clone(),
                                            pod_wildcard: outer_wc_pod.clone(),
                                        });
                                    }
                                    KeyOrWildcard::Key(lit_key) => {
                                        constraints.push(Constraint::LiteralKey {
                                            pod_wildcard: outer_wc_pod.clone(),
                                            literal_key: lit_key.name().to_string(),
                                        });
                                    }
                                }
                            }
                            StatementTmplArg::WildcardLiteral(wc_val) => {
                                let outer_wc_val = alias_map.get(&wc_val.index).unwrap_or(wc_val);
                                update_wildcard_type(
                                    wildcard_types,
                                    outer_wc_val,
                                    ExpectedType::Val,
                                )?;
                                constraints.push(Constraint::Type {
                                    wildcard: outer_wc_val.clone(),
                                    expected_type: ExpectedType::Val,
                                });
                            }
                            StatementTmplArg::Literal(_) | StatementTmplArg::None => {}
                        }
                    }
                }
            }
        }
        Predicate::Native(_native_pred) => {
            // TODO: Generate predicate-specific constraints based on native predicate rules
            // E.g., Gt/Lt -> args must resolve to Int (Type constraints handled above)
            // SumOf/ProductOf -> args must resolve to Int (Type constraints handled above)
            // Contains -> arg0 must be container (Val), arg1 key/index (Val), arg2 value (Val)
            // Need to ensure the *concrete types* within Val match (e.g., Int for SumOf) later during pruning/proof.
        }
        Predicate::Custom(custom_ref) => {
            let predicate_key = Predicate::Custom(custom_ref.clone()).to_fields(context.params);

            // --- Cycle Detection for Custom Predicate --- START ---
            let visited_key: VisitedPredicateParseKey =
                (Arc::as_ptr(&custom_ref.batch), custom_ref.index);
            if !visited_parse.insert(visited_key) {
                return Ok(()); // Cycle detected, already processing this predicate in this path
            }
            // --- Cycle Detection for Custom Predicate --- END ---

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
                                    params,
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

                    // 3. Identify and Register Private Wildcards
                    for inner_wc in &inner_wildcards {
                        if inner_wc.index >= public_args_count {
                            // Ensure the private wildcard is tracked, defaulting to Unknown type if new
                            wildcard_types
                                .entry(inner_wc.clone())
                                .or_insert(ExpectedType::Unknown);
                        }
                    }

                    // 4. Recursively Parse Internal Templates
                    for internal_tmpl in &custom_pred_def.statements {
                        parse_template_and_generate_constraints(
                            internal_tmpl,
                            Some(custom_ref.batch.clone()),
                            wildcard_types,
                            constraints,
                            context,
                            &next_alias_map,
                            constant_template_info,
                            visited_parse,
                        )?;
                    }
                } else {
                    // --- OR Predicate Handling ---
                    // Collect constraints and types from each branch.
                    let mut branch_constraints_sets: Vec<HashSet<Constraint>> = Vec::new();
                    let mut branch_types_maps: Vec<HashMap<Wildcard, ExpectedType>> = Vec::new();
                    let public_args_count = custom_pred_def.args_len; // Needed for alias map

                    // 1. Build the alias map for this level (same as AND)
                    let mut next_alias_map: HashMap<usize, Wildcard> =
                        HashMap::with_capacity(public_args_count);
                    // Similar logic as AND to build next_alias_map...
                    for i in 0..public_args_count {
                        match tmpl.args.get(i) {
                            Some(StatementTmplArg::WildcardLiteral(outer_wc_from_tmpl)) => {
                                // Resolve the outer wildcard using the current alias map
                                let actual_outer_wc = match alias_map.get(&outer_wc_from_tmpl.index)
                                {
                                    Some(outer_wc) => outer_wc,
                                    None => outer_wc_from_tmpl,
                                };
                                // Map: Inner Predicate Arg Index -> Actual Outer Wildcard
                                next_alias_map.insert(i, actual_outer_wc.clone());
                                // NOTE: We don't infer/add type constraints here for OR,
                                // as the type might depend on the branch taken.
                                // We'll infer types within each branch's analysis below.
                            }
                            Some(arg) => {
                                // Error handling similar to AND
                                return Err(ProverError::Internal(format!(
                                    "OR: Expected WildcardLiteral arg at index {} when calling Custom predicate '{}', found {:?}",
                                    i, custom_pred_def.name, arg
                                )));
                            }
                            None => {
                                // Error handling similar to AND
                                return Err(ProverError::Internal(format!(
                                    "OR: Argument count mismatch: Custom predicate '{}' expects {} args, but caller template provided fewer.",
                                    custom_pred_def.name, public_args_count
                                )));
                            }
                        }
                    }

                    // 2. Analyze each branch recursively
                    for internal_tmpl in &custom_pred_def.statements {
                        let mut current_branch_constraints_vec: Vec<Constraint> = Vec::new();
                        let mut current_branch_types_map: HashMap<Wildcard, ExpectedType> =
                            HashMap::new();
                        // IMPORTANT: Also pass down potential constant info accumulation buffer,
                        // although constants found inside an OR branch might not be guaranteed.
                        // For simplicity, we'll collect constants but won't use them for SELF facts from OR branches for now.
                        let mut current_branch_constant_info: Vec<PotentialConstantInfo> =
                            Vec::new();

                        // Recursively parse, collecting constraints and types into temporary buffers
                        // Pass the correct batch context (custom_ref.batch)
                        match parse_template_and_generate_constraints(
                            internal_tmpl,
                            Some(custom_ref.batch.clone()),
                            &mut current_branch_types_map,
                            &mut current_branch_constraints_vec,
                            context,
                            &next_alias_map,
                            &mut current_branch_constant_info,
                            visited_parse,
                        ) {
                            Ok(_) => {
                                // Successfully parsed branch, store results
                                let constraints_set: HashSet<Constraint> =
                                    current_branch_constraints_vec.into_iter().collect();
                                branch_constraints_sets.push(constraints_set);
                                branch_types_maps.push(current_branch_types_map);
                            }
                            Err(e) => {
                                // If a branch is inherently unsatisfiable, we might ignore it for common constraint analysis?
                                // Or propagate the error if *all* branches fail?
                                // For now, let's just log and skip this branch's results.
                                // Consider if a single failing branch should invalidate the OR constraint analysis.
                                eprintln!(
                                    // Use eprintln for warnings/errors
                                    "Warning: Failed to parse OR branch template {:?}: {:?}",
                                    internal_tmpl, e
                                );
                                // If one branch fails, we cannot determine common constraints reliably.
                                // Reset collected results and break? Or just continue and potentially find no commonalities?
                                // Let's clear and break, assuming a broken branch prevents finding guaranteed common constraints.
                                branch_constraints_sets.clear();
                                branch_types_maps.clear();
                                break;
                            }
                        }
                    }

                    // 3. Find and add common constraints
                    if let Some(first_set) = branch_constraints_sets.first() {
                        let mut common_constraints = first_set.clone();
                        for other_set in branch_constraints_sets.iter().skip(1) {
                            common_constraints.retain(|constraint| other_set.contains(constraint));
                        }
                        // Add common constraints to the main constraints vector
                        constraints.extend(common_constraints);
                    }

                    // 4. Find and add common wildcard types
                    if !branch_types_maps.is_empty() {
                        // Collect all wildcards mentioned across all branch type maps
                        let mut all_wcs_in_or: HashSet<Wildcard> = HashSet::new();
                        for map in &branch_types_maps {
                            all_wcs_in_or.extend(map.keys().cloned());
                        }

                        for wc in all_wcs_in_or {
                            let mut common_type = ExpectedType::Unknown;
                            let mut first_type_found = false;
                            let mut conflict = false;

                            for map in &branch_types_maps {
                                match map.get(&wc) {
                                    Some(&branch_type) if branch_type != ExpectedType::Unknown => {
                                        if !first_type_found {
                                            common_type = branch_type;
                                            first_type_found = true;
                                        } else if common_type != branch_type {
                                            conflict = true;
                                            break; // Conflict found
                                        }
                                    }
                                    _ => {
                                        // Wildcard not mentioned or Unknown in this branch, doesn't affect commonality yet
                                    }
                                }
                            }

                            // If a common type was found across all branches (where mentioned) and no conflict occurred
                            if first_type_found && !conflict {
                                // Update the main wildcard_types map
                                update_wildcard_type(wildcard_types, &wc, common_type)?;
                                // Also add the Type constraint explicitly if not already added by intersection
                                let type_constraint = Constraint::Type {
                                    wildcard: wc.clone(),
                                    expected_type: common_type,
                                };
                                // Avoid adding duplicate constraints
                                if !constraints.contains(&type_constraint) {
                                    constraints.push(type_constraint);
                                }
                            }
                            // If conflict or only Unknown found, leave the type in the main map as is (likely Unknown)
                        }
                    }
                    // End of OR logic
                }
            } else {
                return Err(ProverError::Other(format!(
                    "Custom predicate definition not found for ref: {:?}",
                    custom_ref
                )));
            }
            visited_parse.remove(&visited_key); // Remove after processing this predicate's internals
        }
        Predicate::BatchSelf(target_idx) => {
            if let Some(current_batch_arc) = current_batch.as_ref() {
                // Resolve the target predicate definition using the current batch context
                let target_pred_def =
                    current_batch_arc
                        .predicates
                        .get(*target_idx)
                        .ok_or_else(|| {
                            ProverError::Internal(format!(
                            "BatchSelf index {} out of bounds for batch '{}' during initialization",
                            target_idx, current_batch_arc.name
                        ))
                        })?;

                // --- Cycle Detection for BatchSelf --- START ---
                let visited_key: VisitedPredicateParseKey =
                    (Arc::as_ptr(current_batch_arc), *target_idx);
                if !visited_parse.insert(visited_key) {
                    return Ok(()); // Cycle detected
                }
                // --- Cycle Detection for BatchSelf --- END ---

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
                                let mut visited = HashSet::new();
                                let expected_arg_type = infer_argument_type(
                                    target_pred_def,
                                    i,
                                    custom_definitions,
                                    params,
                                    Some(current_batch_arc),
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
                            context,
                            &next_alias_map,
                            constant_template_info,
                            visited_parse, // Pass visited set
                        )?;
                    }
                } else {
                    // --- OR Predicate Handling ---
                    // Collect constraints and types from each branch.
                    let mut branch_constraints_sets: Vec<HashSet<Constraint>> = Vec::new();
                    let mut branch_types_maps: Vec<HashMap<Wildcard, ExpectedType>> = Vec::new();
                    let public_args_count = target_pred_def.args_len; // Needed for alias map

                    // 1. Build the alias map for this level (same as AND)
                    let mut next_alias_map: HashMap<usize, Wildcard> =
                        HashMap::with_capacity(public_args_count);
                    // Similar logic as AND to build next_alias_map...
                    for i in 0..public_args_count {
                        match tmpl.args.get(i) {
                            Some(StatementTmplArg::WildcardLiteral(outer_wc_from_tmpl)) => {
                                // Resolve the outer wildcard using the current alias map
                                let actual_outer_wc = match alias_map.get(&outer_wc_from_tmpl.index)
                                {
                                    Some(outer_wc) => outer_wc,
                                    None => outer_wc_from_tmpl,
                                };
                                // Map: Inner Predicate Arg Index -> Actual Outer Wildcard
                                next_alias_map.insert(i, actual_outer_wc.clone());
                                // NOTE: Type constraints handled within branch analysis below.
                            }
                            Some(arg) => {
                                // Error handling similar to AND
                                return Err(ProverError::Internal(format!(
                                     "OR/BatchSelf: Expected WildcardLiteral arg at index {} when calling BatchSelf predicate '{}', found {:?}",
                                     i, target_pred_def.name, arg
                                 )));
                            }
                            None => {
                                // Error handling similar to AND
                                return Err(ProverError::Internal(format!(
                                     "OR/BatchSelf: Argument count mismatch: BatchSelf predicate '{}' expects {} args, but caller template provided fewer.",
                                     target_pred_def.name, public_args_count
                                 )));
                            }
                        }
                    }

                    // 2. Analyze each branch recursively
                    for internal_tmpl in &target_pred_def.statements {
                        let mut current_branch_constraints_vec: Vec<Constraint> = Vec::new();
                        let mut current_branch_types_map: HashMap<Wildcard, ExpectedType> =
                            HashMap::new();
                        let mut current_branch_constant_info: Vec<PotentialConstantInfo> =
                            Vec::new();

                        // Recursively parse, collecting constraints and types into temporary buffers
                        // Pass the current batch Arc ref
                        match parse_template_and_generate_constraints(
                            internal_tmpl,
                            Some(current_batch_arc.clone()),
                            &mut current_branch_types_map,
                            &mut current_branch_constraints_vec,
                            context,
                            &next_alias_map,
                            &mut current_branch_constant_info,
                            visited_parse,
                        ) {
                            Ok(_) => {
                                let constraints_set: HashSet<Constraint> =
                                    current_branch_constraints_vec.into_iter().collect();
                                branch_constraints_sets.push(constraints_set);
                                branch_types_maps.push(current_branch_types_map);
                            }
                            Err(e) => {
                                eprintln!( // Use eprintln for warnings/errors
                                     "Warning: Failed to parse OR/BatchSelf branch template {:?}: {:?}",
                                     internal_tmpl, e
                                 );
                                // Clear and break if one branch fails.
                                branch_constraints_sets.clear();
                                branch_types_maps.clear();
                                break;
                            }
                        }
                    }

                    // 3. Find and add common constraints (same logic as Custom OR)
                    if let Some(first_set) = branch_constraints_sets.first() {
                        let mut common_constraints = first_set.clone();
                        for other_set in branch_constraints_sets.iter().skip(1) {
                            common_constraints.retain(|constraint| other_set.contains(constraint));
                        }
                        constraints.extend(common_constraints);
                    }

                    // 4. Find and add common wildcard types (same logic as Custom OR)
                    if !branch_types_maps.is_empty() {
                        let mut all_wcs_in_or: HashSet<Wildcard> = HashSet::new();
                        for map in &branch_types_maps {
                            all_wcs_in_or.extend(map.keys().cloned());
                        }

                        for wc in all_wcs_in_or {
                            let mut common_type = ExpectedType::Unknown;
                            let mut first_type_found = false;
                            let mut conflict = false;

                            for map in &branch_types_maps {
                                match map.get(&wc) {
                                    Some(&branch_type) if branch_type != ExpectedType::Unknown => {
                                        if !first_type_found {
                                            common_type = branch_type;
                                            first_type_found = true;
                                        } else if common_type != branch_type {
                                            conflict = true;
                                            break;
                                        }
                                    }
                                    _ => {}
                                }
                            }

                            if first_type_found && !conflict {
                                update_wildcard_type(wildcard_types, &wc, common_type)?;
                                let type_constraint = Constraint::Type {
                                    wildcard: wc.clone(),
                                    expected_type: common_type,
                                };
                                if !constraints.contains(&type_constraint) {
                                    constraints.push(type_constraint);
                                }
                            }
                        }
                    }
                    // End of OR logic
                }
                visited_parse.remove(&visited_key); // Remove after processing this predicate's internals
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

type InitializationResult = (
    SolverState,
    Vec<PotentialConstantInfo>,
    Vec<(PodId, Statement)>,
);

pub(super) struct SolverContext<'a> {
    pub initial_facts: &'a [(PodId, Statement)],
    pub params: &'a Params,
    pub custom_definitions: &'a CustomDefinitions,
}

/// Initializes the `SolverState` based on request templates, indexes, and custom definitions.
pub(super) fn initialize_solver_state(
    request_templates: &[StatementTmpl],
    context: &SolverContext,
) -> Result<InitializationResult, ProverError> {
    let mut wildcard_types: HashMap<Wildcard, ExpectedType> = HashMap::new();
    let mut constraints = Vec::new();
    let mut constant_template_info: Vec<PotentialConstantInfo> = Vec::new();
    let mut visited_parse: HashSet<VisitedPredicateParseKey> = HashSet::new();

    let initial_alias_map: HashMap<usize, Wildcard> = HashMap::new();

    // Parse ALL templates to collect wildcards, constraints, etc.
    for tmpl in request_templates {
        parse_template_and_generate_constraints(
            tmpl,
            None, // Top-level calls have no current_batch
            &mut wildcard_types,
            &mut constraints,
            context,
            &initial_alias_map,
            &mut constant_template_info,
            &mut visited_parse,
        )?;
    }

    // --- Generate SELF facts from identified constants --- START ---
    let mut self_facts: Vec<(PodId, Statement)> = Vec::new();
    for (_holder_wc, key, literal_value) in &constant_template_info {
        let self_ak = AnchoredKey::new(SELF, key.clone());
        let value_of_stmt = Statement::ValueOf(self_ak, literal_value.clone());
        self_facts.push((SELF, value_of_stmt));
    }
    // --- Generate SELF facts from identified constants --- END ---

    // --- Combine original facts with newly generated SELF facts ---
    let mut combined_initial_facts = context.initial_facts.to_vec();
    combined_initial_facts.extend(self_facts.clone()); // Clone self_facts here

    // --- Build Indexes using the combined facts ---
    let solver_indexes = ProverIndexes::build(context.params.clone(), &combined_initial_facts);

    // --- Initialize Domains (Simplified - Now has Index Access) ---
    let mut wildcard_domains: HashMap<Wildcard, (Domain, ExpectedType)> = HashMap::new();

    for (wildcard, expected_type) in &wildcard_types {
        // Initialize with broad, potentially empty domains based only on type
        // Pruning will refine these later using the actual index built in solve()
        let initial_domain: Domain = match expected_type {
            ExpectedType::Pod => {
                let pod_map = solver_indexes.pod_id_to_anchored_keys();
                let mut pods: HashSet<_> = pod_map
                    .keys()
                    .map(|pod_id| ConcreteValue::Pod(*pod_id))
                    .collect();
                // Ensure SELF is included if relevant indexes exist for it
                let self_present_in_index = pod_map.contains_key(&SELF);
                if self_present_in_index {
                    pods.insert(ConcreteValue::Pod(SELF));
                }
                pods
            }
            ExpectedType::Key => solver_indexes
                .key_to_anchored_keys()
                .keys()
                .map(|k| k.to_string())
                .map(ConcreteValue::Key)
                .collect(),
            ExpectedType::Val => solver_indexes
                .value_map()
                .values()
                .map(|value| ConcreteValue::Val(value.clone()))
                .collect(),
            ExpectedType::Unknown => {
                let mut all = HashSet::new();
                // Collect all known concrete values
                for pod_id in solver_indexes.pod_id_to_anchored_keys().keys() {
                    all.insert(ConcreteValue::Pod(*pod_id));
                }
                if solver_indexes.pod_id_to_anchored_keys().contains_key(&SELF) {
                    all.insert(ConcreteValue::Pod(SELF));
                }
                for key in solver_indexes.key_to_anchored_keys().keys() {
                    all.insert(ConcreteValue::Key(key.to_string()));
                }
                for value in solver_indexes.value_map().values() {
                    all.insert(ConcreteValue::Val(value.clone()));
                }
                all
            }
        };

        wildcard_domains.insert(wildcard.clone(), (initial_domain, *expected_type));
    }

    // Remove duplicates constraints if any
    let constraints_set: HashSet<_> = constraints.drain(..).collect();
    constraints.extend(constraints_set);

    let solver_state = SolverState {
        params: context.params.clone(),
        domains: wildcard_domains,
        constraints,
        proof_chains: HashMap::new(),
        scope: HashSet::new(),
    };

    Ok((solver_state, constant_template_info, self_facts))
}
