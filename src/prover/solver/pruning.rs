use std::collections::{HashMap, HashSet};

use super::{
    types::{Constraint, Domain, ExpectedType},
    SolverState,
};
use crate::{
    middleware::{
        KeyOrWildcard, NativePredicate, PodId, Predicate, Statement, StatementTmpl,
        StatementTmplArg, TypedValue, Value, Wildcard,
    },
    prover::{error::ProverError, indexing::ProverIndexes, types::ConcreteValue},
};

/// Applies type constraints, removing incompatible ConcreteValue variants from domains.
/// Returns Ok(true) if any domain changed, Ok(false) otherwise.
pub fn prune_by_type(state: &mut SolverState) -> Result<bool, ProverError> {
    let mut changed = false;
    for (wildcard, (domain, expected_type_ref)) in state.domains.iter_mut() {
        // Dereference the mutable reference to get a copy, since ExpectedType derives Copy
        let expected_type = *expected_type_ref;
        let initial_size = domain.len();

        domain.retain(|value| match (expected_type, value) {
            // Closure now captures the copy
            (ExpectedType::Pod, ConcreteValue::Pod(_)) => true,
            (ExpectedType::Key, ConcreteValue::Key(_)) => true,
            (ExpectedType::Val, ConcreteValue::Val(_)) => true,
            (ExpectedType::Unknown, _) => true, // Don't prune if type is unknown
            _ => false,                         // Prune if types mismatch
        });

        if domain.is_empty() {
            return Err(ProverError::Unsatisfiable(format!(
                "Type pruning made domain for wildcard '{}' empty (expected {:?})",
                wildcard.name,
                expected_type // Use the copied value here too
            )));
        }

        if domain.len() < initial_size {
            changed = true;
        }
    }
    Ok(changed)
}

/// Applies literal key constraints (e.g., from `?A["foo"]`), removing PodIds from
/// the domain of `?A` if they are not known to have the key "foo".
/// Returns Ok(true) if any domain changed, Ok(false) otherwise.
pub fn prune_by_literal_key(
    state: &mut SolverState,
    indexes: &ProverIndexes,
    constraints: &[Constraint], // Pass constraints explicitly
) -> Result<bool, ProverError> {
    let mut changed = false;

    for constraint in constraints {
        if let Constraint::LiteralKey {
            pod_wildcard,
            literal_key,
        } = constraint
        {
            // Find the domain for the wildcard constrained by the literal key
            if let Some((domain, expected_type)) = state.domains.get_mut(pod_wildcard) {
                // This should only apply to Pod domains
                if *expected_type != ExpectedType::Pod {
                    continue; // Should have been caught by prune_by_type, but check defensively
                }

                let initial_size = domain.len();

                // Find the set of PodIds known to have this literal_key
                let middleware_key = crate::middleware::Key::new(literal_key.clone());
                let allowed_pod_ids: HashSet<PodId> = indexes
                    .get_anchored_keys_for_key(&middleware_key)
                    .map(|anchored_keys| anchored_keys.iter().map(|ak| ak.pod_id).collect())
                    .unwrap_or_default(); // If key not found in index, no PodIds are allowed

                // Retain only PodIds present in the allowed set
                domain.retain(|value| match value {
                    ConcreteValue::Pod(pod_id) => allowed_pod_ids.contains(pod_id),
                    _ => false, // Remove non-Pod values (should be gone after prune_by_type)
                });

                if domain.is_empty() {
                    return Err(ProverError::Unsatisfiable(format!(
                        "LiteralKey constraint ('{}[{}]') made domain empty",
                        pod_wildcard.name, literal_key
                    )));
                }

                if domain.len() < initial_size {
                    changed = true;
                    // We don't remove the constraint from the list as it might be needed
                    // again if domains change due to other propagations.
                }
            } else {
                // Wildcard mentioned in constraint but not in domains? Should not happen.
                return Err(ProverError::Internal(format!(
                    "Wildcard '{}' from LiteralKey constraint not found in domains",
                    pod_wildcard.name
                )));
            }
        }
    }

    Ok(changed)
}

/// Applies literal origin constraints (e.g., from `PodX[?Y]`), removing Keys from
/// the domain of `?Y` if they are not known to exist within the literal `PodX`.
/// Returns Ok(true) if any domain changed, Ok(false) otherwise.
pub fn prune_by_literal_origin(
    state: &mut SolverState,
    indexes: &ProverIndexes,
    constraints: &[Constraint],
) -> Result<bool, ProverError> {
    let mut changed = false;

    for constraint in constraints {
        if let Constraint::LiteralOrigin {
            key_wildcard,
            literal_pod_id,
        } = constraint
        {
            // Find the domain for the wildcard constrained by the literal origin
            if let Some((domain, expected_type)) = state.domains.get_mut(key_wildcard) {
                // This should only apply to Key domains
                if *expected_type != ExpectedType::Key {
                    continue; // Should have been caught by prune_by_type
                }

                let initial_size = domain.len();

                // Find the set of Keys (as Strings) known to exist for this literal_pod_id
                let allowed_keys: HashSet<String> = indexes
                    .get_anchored_keys_for_pod_id(literal_pod_id)
                    .map(|anchored_keys| {
                        anchored_keys
                            .iter()
                            .map(|ak| ak.key.name().to_string()) // Extract key name as String
                            .collect()
                    })
                    .unwrap_or_default(); // If pod_id not found in index, no keys are allowed

                // Retain only Key strings present in the allowed set
                domain.retain(|value| match value {
                    ConcreteValue::Key(key_string) => allowed_keys.contains(key_string),
                    _ => false, // Remove non-Key values
                });

                if domain.is_empty() {
                    return Err(ProverError::Unsatisfiable(format!(
                        "LiteralOrigin constraint ('{}[?{}]') made domain empty",
                        literal_pod_id, // Display PodId
                        key_wildcard.name
                    )));
                }

                if domain.len() < initial_size {
                    changed = true;
                }
            } else {
                return Err(ProverError::Internal(format!(
                    "Wildcard '{}' from LiteralOrigin constraint not found in domains",
                    key_wildcard.name
                )));
            }
        }
    }

    Ok(changed)
}

/// Applies literal value constraints, removing Values from the domain of a wildcard
/// if they do not match the required literal value.
/// Returns Ok(true) if any domain changed, Ok(false) otherwise.
pub fn prune_by_literal_value(
    state: &mut SolverState,
    _indexes: &ProverIndexes, // Might not be needed
    constraints: &[Constraint],
) -> Result<bool, ProverError> {
    let mut changed = false;

    for constraint in constraints {
        if let Constraint::LiteralValue {
            wildcard,
            literal_value,
        } = constraint
        {
            if let Some((domain, expected_type)) = state.domains.get_mut(wildcard) {
                // This should only apply to Val domains
                if *expected_type != ExpectedType::Val {
                    // This might indicate an issue in constraint generation or type inference
                    // if a non-Val wildcard gets a LiteralValue constraint.
                    // For now, we'll just skip, assuming type pruning handled it.
                    continue;
                }

                let initial_size = domain.len();

                // Retain only the ConcreteValue::Val that matches the literal_value
                domain.retain(|value| match value {
                    ConcreteValue::Val(v) => v == literal_value,
                    _ => false, // Remove non-Val values (should be gone after prune_by_type)
                });

                if domain.is_empty() {
                    return Err(ProverError::Unsatisfiable(format!(
                        "LiteralValue constraint ('{}' = {:?}) made domain empty",
                        wildcard.name, literal_value
                    )));
                }

                if domain.len() < initial_size {
                    changed = true;
                }
            } else {
                return Err(ProverError::Internal(format!(
                    "Wildcard '{}' from LiteralValue constraint not found in domains",
                    wildcard.name
                )));
            }
        }
    }

    Ok(changed)
}

/// Runs the initial set of pruning functions iteratively until a fixed point is reached.
/// Returns Ok(true) if any domain changed during the process, Ok(false) otherwise.
pub(super) fn prune_initial_domains(
    state: &mut SolverState,
    indexes: &ProverIndexes,
) -> Result<bool, ProverError> {
    let mut overall_changed = false;
    let mut changed_this_pass = true;
    // Keep track of constraints to avoid re-processing simple ones unnecessarily
    // More complex propagation might need a different approach
    let mut processed_type_pruning = false; // Track if type pruning has run and made changes

    while changed_this_pass {
        changed_this_pass = false;

        // Apply type constraints first (modifies domains in place)
        if !processed_type_pruning && prune_by_type(state)? {
            changed_this_pass = true;
            overall_changed = true;
            processed_type_pruning = true; // Only mark after first change
        }

        // Apply other literal constraints
        // Clone constraints to avoid borrowing state mutably and immutably simultaneously
        // We might need to re-run these if type pruning (or other pruning) changed domains.
        let current_constraints = state.constraints.clone();

        if prune_by_literal_key(state, indexes, &current_constraints)? {
            changed_this_pass = true;
            overall_changed = true;
        }

        if prune_by_literal_origin(state, indexes, &current_constraints)? {
            changed_this_pass = true;
            overall_changed = true;
        }

        if prune_by_literal_value(state, indexes, &current_constraints)? {
            changed_this_pass = true;
            overall_changed = true;
        }

        // Reset type pruning check if other constraints made changes, potentially enabling more type pruning
        if changed_this_pass {
            processed_type_pruning = false;
        }
    }
    Ok(overall_changed) // Return whether *any* change occurred
}

/// Applies pruning logic directly based on a newly proven statement and its associated bindings.
/// Returns Ok(true) if any domain changed, Ok(false) otherwise.
pub(super) fn prune_domains_after_proof(
    state: &mut SolverState,
    proven_template: &StatementTmpl,
    _proven_statement: &Statement, // Concrete statement might be useful for value checks later
    bindings: &HashMap<Wildcard, ConcreteValue>,
    _indexes: &ProverIndexes,
) -> Result<bool, ProverError> {
    let mut changed = false;

    match proven_template.pred {
        // Match on the *template's* predicate
        Predicate::Native(NativePredicate::Equal) => {
            if proven_template.args.len() == 2 {
                // Get wildcards involved in arg1 and arg2 from the template
                let wildcards1 = get_wildcards_from_tmpl_arg(&proven_template.args[0]);
                let wildcards2 = get_wildcards_from_tmpl_arg(&proven_template.args[1]);

                // Propagate/intersect based on wildcard type (Pod, Key)
                // This assumes wildcards bind directly to components.
                for wc1_pod in &wildcards1.pod_wcs {
                    for wc2_pod in &wildcards2.pod_wcs {
                        // If ?A[?] == ?B[?], propagate/intersect domains of ?A and ?B
                        changed |= propagate_or_intersect(&mut state.domains, wc1_pod, wc2_pod)?;
                    }
                }
                for wc1_key in &wildcards1.key_wcs {
                    for wc2_key in &wildcards2.key_wcs {
                        // If ?[?X] == ?[?Y], propagate/intersect domains of ?X and ?Y
                        changed |= propagate_or_intersect(&mut state.domains, wc1_key, wc2_key)?;
                    }
                }
                // Value wildcards usually aren't directly equated in Equal statements (which take AKs)
                // but handle if necessary.
                for wc1_val in &wildcards1.val_wcs {
                    for wc2_val in &wildcards2.val_wcs {
                        changed |= propagate_or_intersect(&mut state.domains, wc1_val, wc2_val)?;
                    }
                }
            }
        }
        Predicate::Native(NativePredicate::NotEqual) => {
            // Apply NotEqual singleton removal logic.
            if proven_template.args.len() == 2 {
                let wildcards1 = get_wildcards_from_tmpl_arg(&proven_template.args[0]);
                let wildcards2 = get_wildcards_from_tmpl_arg(&proven_template.args[1]);
                for wc1_pod in &wildcards1.pod_wcs {
                    for wc2_pod in &wildcards2.pod_wcs {
                        changed |= remove_singleton(&mut state.domains, wc1_pod, wc2_pod)?;
                        changed |= remove_singleton(&mut state.domains, wc2_pod, wc1_pod)?;
                    }
                }
                for wc1_key in &wildcards1.key_wcs {
                    for wc2_key in &wildcards2.key_wcs {
                        changed |= remove_singleton(&mut state.domains, wc1_key, wc2_key)?;
                        changed |= remove_singleton(&mut state.domains, wc2_key, wc1_key)?;
                    }
                }
                for wc1_val in &wildcards1.val_wcs {
                    for wc2_val in &wildcards2.val_wcs {
                        changed |= remove_singleton(&mut state.domains, wc1_val, wc2_val)?;
                        changed |= remove_singleton(&mut state.domains, wc2_val, wc1_val)?;
                    }
                }
            }
        }
        Predicate::Native(NativePredicate::Gt) | Predicate::Native(NativePredicate::Lt) => {
            // Apply NotEqual singleton removal logic first.
            let mut neq_changed = false;
            if proven_template.args.len() == 2 {
                let wildcards1 = get_wildcards_from_tmpl_arg(&proven_template.args[0]);
                let wildcards2 = get_wildcards_from_tmpl_arg(&proven_template.args[1]);
                // Apply NEq logic based on AK wildcards (Pod/Key components)
                for wc1 in wildcards1.pod_wcs.iter().chain(wildcards1.key_wcs.iter()) {
                    for wc2 in wildcards2.pod_wcs.iter().chain(wildcards2.key_wcs.iter()) {
                        neq_changed |= remove_singleton(&mut state.domains, wc1, wc2)?;
                        neq_changed |= remove_singleton(&mut state.domains, wc2, wc1)?;
                    }
                }
                // Apply NEq logic based on Value wildcards (less common for Gt/Lt)
                for wc1_val in &wildcards1.val_wcs {
                    for wc2_val in &wildcards2.val_wcs {
                        neq_changed |= remove_singleton(&mut state.domains, wc1_val, wc2_val)?;
                        neq_changed |= remove_singleton(&mut state.domains, wc2_val, wc1_val)?;
                    }
                }
                // Now, apply value-based pruning if applicable
                if let (Some(tmpl_arg1), Some(tmpl_arg2)) =
                    (proven_template.args.get(0), proven_template.args.get(1))
                {
                    // Extract value wildcards associated with the Gt/Lt arguments
                    let val_wcs1 = get_wildcards_from_tmpl_arg(tmpl_arg1).val_wcs;
                    let val_wcs2 = get_wildcards_from_tmpl_arg(tmpl_arg2).val_wcs;
                    for wc1 in &val_wcs1 {
                        for wc2 in &val_wcs2 {
                            // Attempt value-based pruning between wc1 and wc2
                            if let Predicate::Native(native_pred) = proven_template.pred {
                                changed |=
                                    prune_gt_lt_values(&mut state.domains, wc1, wc2, native_pred)?;
                            }
                        }
                    }
                }
            }
            changed |= neq_changed; // Combine results
        }
        Predicate::Native(NativePredicate::ValueOf) => {
            // ValueOf(?A[?X], ?V) or ValueOf(Literal, ?V) etc.
            if proven_template.args.len() == 2 {
                // The second argument is the value argument.
                if let Some(value_arg_tmpl) = proven_template.args.get(1) {
                    let value_wildcards = get_wildcards_from_tmpl_arg(value_arg_tmpl);
                    for wc_val in value_wildcards.val_wcs {
                        // Find the concrete value this wildcard bound to
                        if let Some(concrete_value) = bindings.get(&wc_val) {
                            if let ConcreteValue::Val(bound_val) = concrete_value {
                                // Prune the domain of wc_val to only this bound_val
                                if let Some((domain, _)) = state.domains.get_mut(&wc_val) {
                                    let initial_len = domain.len();
                                    let target_cv = ConcreteValue::Val(bound_val.clone());
                                    domain.retain(|cv| cv == &target_cv);
                                    if domain.is_empty() {
                                        return Err(ProverError::Unsatisfiable(format!(
                                            "Dynamic pruning (ValueOf) emptied domain for {}",
                                            wc_val.name
                                        )));
                                    }
                                    if domain.len() < initial_len {
                                        changed = true;
                                    }
                                }
                            }
                        }
                    }
                }
            }
        }
        Predicate::Native(NativePredicate::SumOf) => {
            // SumOf(?Sum, ?Add1, ?Add2)
            if proven_template.args.len() == 3 {
                changed |= prune_arithmetic(
                    &mut state.domains,
                    NativePredicate::SumOf,
                    &proven_template.args[0],
                    &proven_template.args[1],
                    &proven_template.args[2],
                    bindings,
                    |a, b| a + b, // Summation
                )?;
            }
        }
        Predicate::Native(NativePredicate::ProductOf) => {
            // ProductOf(?Prod, ?Fac1, ?Fac2)
            if proven_template.args.len() == 3 {
                changed |= prune_arithmetic(
                    &mut state.domains,
                    NativePredicate::ProductOf,
                    &proven_template.args[0],
                    &proven_template.args[1],
                    &proven_template.args[2],
                    bindings,
                    |a, b| a * b, // Multiplication
                )?;
            }
        }
        Predicate::Native(NativePredicate::MaxOf) => {
            // MaxOf(?Max, ?Op1, ?Op2)
            if proven_template.args.len() == 3 {
                changed |= prune_arithmetic(
                    &mut state.domains,
                    NativePredicate::MaxOf,
                    &proven_template.args[0],
                    &proven_template.args[1],
                    &proven_template.args[2],
                    bindings,
                    std::cmp::max, // Max function
                )?;
            }
        }
        // TODO: Implement dynamic pruning for Contains/NotContains if beneficial
        // Predicate::Native(NativePredicate::Contains)
        // | Predicate::Native(NativePredicate::NotContains) => {
        //     println!("Warning: Dynamic pruning for Contains/NotContains not yet implemented.");
        // }
        Predicate::Native(NativePredicate::Contains) => {
            // Contains(?Container, ?Key, ?Value)
            if proven_template.args.len() == 3 {
                let container_arg = &proven_template.args[0];
                let key_arg = &proven_template.args[1];
                let value_arg = &proven_template.args[2];

                let wcs_c = get_wildcards_from_tmpl_arg(container_arg);
                let wcs_k = get_wildcards_from_tmpl_arg(key_arg);
                let wcs_v = get_wildcards_from_tmpl_arg(value_arg);

                // Get bound singleton values (if any)
                let bound_container = wcs_c
                    .val_wcs
                    .get(0)
                    .and_then(|wc| bindings.get(wc))
                    .and_then(|cv| match cv {
                        ConcreteValue::Val(v) => Some(v.clone()),
                        _ => None,
                    });
                let bound_key = wcs_k
                    .val_wcs
                    .get(0)
                    .and_then(|wc| bindings.get(wc))
                    .and_then(|cv| match cv {
                        ConcreteValue::Val(v) => Some(v.clone()),
                        _ => None,
                    });
                let bound_value = wcs_v
                    .val_wcs
                    .get(0)
                    .and_then(|wc| bindings.get(wc))
                    .and_then(|cv| match cv {
                        ConcreteValue::Val(v) => Some(v.clone()),
                        _ => None,
                    });

                // --- Pruning based on bound container ---
                if let Some(container) = bound_container {
                    // Prune Key wildcard domain
                    for wc_k in &wcs_k.val_wcs {
                        if let Some((domain_k, _)) = state.domains.get_mut(wc_k) {
                            changed |= prune_domain_by_container_existence(
                                domain_k, &container, true, // Keep keys that DO exist
                            )?;
                        }
                    }
                    // Prune Value wildcard domain
                    for wc_v in &wcs_v.val_wcs {
                        if let Some((domain_v, _)) = state.domains.get_mut(wc_v) {
                            // Prune value domain based on the known container
                            // Keep only values that exist somewhere in the container
                            changed |= prune_domain_by_container_value_existence(
                                domain_v, &container, true, // Keep values that DO exist
                            )?
                        }
                    }
                }

                // --- Pruning based on bound key ---
                if let Some(key) = bound_key {
                    // Prune Container wildcard domain
                    for wc_c in &wcs_c.val_wcs {
                        if let Some((domain_c, _)) = state.domains.get_mut(wc_c) {
                            changed |= prune_container_domain_by_key_existence(
                                domain_c, &key,
                                true, // Keep containers that DO contain the key
                            )?;
                        }
                    }
                    // Prune Value wildcard domain (based on Key)
                    for wc_v in &wcs_v.val_wcs {
                        if let Some((domain_v, _)) = state.domains.get_mut(wc_v) {
                            // Collect expected values associated with this key across possible containers
                            let mut possible_values = HashSet::new();
                            let wc_c_target = wcs_c.val_wcs.get(0); // Assume single container wildcard
                            if let Some(wc_c_concrete) = wc_c_target {
                                // Immutable borrow needed here
                                let container_domain_view = state.domains.get(wc_c_concrete);
                                if let Some((domain_c_concrete, _)) = container_domain_view {
                                    for cv_c in domain_c_concrete {
                                        // Iterate over immutable view
                                        if let ConcreteValue::Val(container_val) = cv_c {
                                            // cv_c is &ConcreteValue
                                            // Use the bound key (&Value) for prove_existence. `key` is already &Value
                                            if let Ok((val, _)) =
                                                container_val.prove_existence(&key)
                                            {
                                                possible_values
                                                    .insert(ConcreteValue::Val(val.clone()));
                                            }
                                        }
                                    }
                                }
                            }

                            if !possible_values.is_empty() {
                                // Re-borrow state.domains mutably
                                if let Some((domain_v_mut, _)) = state.domains.get_mut(wc_v) {
                                    let initial_len = domain_v_mut.len();
                                    domain_v_mut.retain(|cv| possible_values.contains(cv)); // Use collected set
                                    if domain_v_mut.is_empty() {
                                        return Err(ProverError::Unsatisfiable(format!(
                                            "Dynamic pruning (Contains/Key->Value) emptied domain for {}",
                                            wc_v.name
                                        )));
                                    }
                                    if domain_v_mut.len() < initial_len {
                                        changed = true;
                                    }
                                }
                            }
                        }
                    }
                }

                // --- Pruning based on bound value ---
                if let Some(value) = bound_value {
                    // Prune Container wildcard domain
                    for wc_c in &wcs_c.val_wcs {
                        if let Some((domain_c, _)) = state.domains.get_mut(wc_c) {
                            changed |= prune_container_domain_by_value_existence(
                                domain_c, &value,
                                true, // Keep containers that DO contain the value
                            )?;
                        }
                    }
                    // Prune Key wildcard domain (based on Value) - More complex, requires iterating container domain
                    // This is less likely to be a strong pruning step. Skip for now.
                }
            }
        }
        Predicate::Native(NativePredicate::NotContains) => {
            // NotContains(?Container, ?Key)
            if proven_template.args.len() == 2 {
                let container_arg = &proven_template.args[0];
                let key_arg = &proven_template.args[1];

                let wcs_c = get_wildcards_from_tmpl_arg(container_arg);
                let wcs_k = get_wildcards_from_tmpl_arg(key_arg);

                // Get bound singleton values (if any)
                let bound_container = wcs_c
                    .val_wcs
                    .get(0)
                    .and_then(|wc| bindings.get(wc))
                    .and_then(|cv| match cv {
                        ConcreteValue::Val(v) => Some(v.clone()),
                        _ => None,
                    });
                let bound_key = wcs_k
                    .val_wcs
                    .get(0)
                    .and_then(|wc| bindings.get(wc))
                    .and_then(|cv| match cv {
                        ConcreteValue::Val(v) => Some(v.clone()),
                        _ => None,
                    });

                // --- Pruning based on bound container ---
                if let Some(container) = bound_container {
                    // Prune Key wildcard domain
                    for wc_k in &wcs_k.val_wcs {
                        if let Some((domain_k, _)) = state.domains.get_mut(wc_k) {
                            changed |= prune_domain_by_container_existence(
                                domain_k, &container, false, // Keep keys that DO NOT exist
                            )?;
                        }
                    }
                }

                // --- Pruning based on bound key ---
                if let Some(key) = bound_key {
                    // Prune Container wildcard domain
                    for wc_c in &wcs_c.val_wcs {
                        if let Some((domain_c, _)) = state.domains.get_mut(wc_c) {
                            changed |= prune_container_domain_by_key_existence(
                                domain_c, &key,
                                false, // Keep containers that DO NOT contain the key
                            )?;
                        }
                    }
                }
            }
        }
        Predicate::Custom(_) | Predicate::BatchSelf(_) => {
            // Dynamic pruning for custom predicates would involve applying the logic
            // based on the *internal* structure of the proven custom predicate. Complex.
            println!("Warning: Dynamic pruning for Custom predicates not yet implemented.");
        }
        // Add back the catch-all for other unhandled predicates
        _ => {}
    }

    Ok(changed)
}

// --- NEW Helper Struct and Functions ---

#[derive(Default)]
pub(super) struct ExtractedWildcards {
    pub pod_wcs: Vec<Wildcard>,
    pub key_wcs: Vec<Wildcard>,
    pub val_wcs: Vec<Wildcard>,
}

/// Extracts all wildcards from a StatementTmplArg.
pub(super) fn get_wildcards_from_tmpl_arg(arg_tmpl: &StatementTmplArg) -> ExtractedWildcards {
    let mut wcs = ExtractedWildcards::default();
    match arg_tmpl {
        StatementTmplArg::Key(wc_pod, key_or_wc) => {
            wcs.pod_wcs.push(wc_pod.clone());
            if let KeyOrWildcard::Wildcard(wc_key) = key_or_wc {
                wcs.key_wcs.push(wc_key.clone());
            }
        }
        StatementTmplArg::WildcardLiteral(wc_val) => {
            wcs.val_wcs.push(wc_val.clone());
        }
        StatementTmplArg::Literal(_) | StatementTmplArg::None => {}
    }
    wcs
}

/// Helper to propagate a singleton domain or intersect two domains.
/// Modifies `domains` in place. Returns Ok(true) if domains changed.
pub(super) fn propagate_or_intersect(
    domains: &mut HashMap<Wildcard, (Domain, ExpectedType)>,
    wc1: &Wildcard,
    wc2: &Wildcard,
) -> Result<bool, ProverError> {
    if !domains.contains_key(wc1) || !domains.contains_key(wc2) {
        return Ok(false); // Cannot prune if domains don't exist
    }

    let len1 = domains[wc1].0.len();
    let len2 = domains[wc2].0.len();
    let mut changed = false;

    if len1 == 1 && len2 > 1 {
        let singleton_val = domains[wc1].0.iter().next().unwrap().clone();
        let (domain2_mut, _) = domains.get_mut(wc2).unwrap();
        let initial_len = domain2_mut.len();
        domain2_mut.retain(|v| v == &singleton_val);
        if domain2_mut.is_empty() {
            return Err(ProverError::Unsatisfiable(format!(
                "Dynamic pruning (propagate/intersect) emptied domain for {}",
                wc2.name
            )));
        }
        if domain2_mut.len() < initial_len {
            changed = true;
        }
    } else if len2 == 1 && len1 > 1 {
        let singleton_val = domains[wc2].0.iter().next().unwrap().clone();
        let (domain1_mut, _) = domains.get_mut(wc1).unwrap();
        let initial_len = domain1_mut.len();
        domain1_mut.retain(|v| v == &singleton_val);
        if domain1_mut.is_empty() {
            return Err(ProverError::Unsatisfiable(format!(
                "Dynamic pruning (propagate/intersect) emptied domain for {}",
                wc1.name
            )));
        }
        if domain1_mut.len() < initial_len {
            changed = true;
        }
    } else if len1 > 1 && len2 > 1 {
        let intersection: Domain = {
            let (domain1, _) = domains.get(wc1).unwrap();
            let (domain2, _) = domains.get(wc2).unwrap();
            domain1.intersection(domain2).cloned().collect()
        };
        if intersection.is_empty() {
            return Err(ProverError::Unsatisfiable(format!("Dynamic pruning (propagate/intersect) resulted in empty domain intersection for {} and {}", wc1.name, wc2.name)));
        }

        let (domain1_mut, _) = domains.get_mut(wc1).unwrap();
        if intersection.len() < domain1_mut.len() {
            *domain1_mut = intersection.clone();
            changed = true;
        }
        let (domain2_mut, _) = domains.get_mut(wc2).unwrap();
        if intersection.len() < domain2_mut.len() {
            *domain2_mut = intersection;
            changed = true; // Mark changed even if only domain2 changed
        }
    }
    Ok(changed)
}

/// Helper to remove a singleton value from another domain (for NotEqual).
/// Modifies `domains` in place. Returns Ok(true) if domain changed.
pub(super) fn remove_singleton(
    domains: &mut HashMap<Wildcard, (Domain, ExpectedType)>,
    wc_singleton: &Wildcard, // Wildcard whose singleton value should be removed
    wc_target: &Wildcard,    // Wildcard whose domain should be pruned
) -> Result<bool, ProverError> {
    if !domains.contains_key(wc_singleton) || !domains.contains_key(wc_target) {
        return Ok(false);
    }
    if domains[wc_singleton].0.len() == 1 && !domains[wc_target].0.is_empty() {
        // Ensure target is not empty
        let val_to_remove = domains[wc_singleton].0.iter().next().unwrap().clone();
        let (target_domain_mut, _) = domains.get_mut(wc_target).unwrap();
        let initial_len = target_domain_mut.len();
        target_domain_mut.remove(&val_to_remove); // remove returns bool, but we check length change
        if target_domain_mut.is_empty() {
            return Err(ProverError::Unsatisfiable(format!(
                "Dynamic pruning (remove singleton) emptied domain for {}",
                wc_target.name
            )));
        }
        if target_domain_mut.len() < initial_len {
            return Ok(true);
        }
    }
    Ok(false)
}

// --- NEW Arithmetic Helper ---
/// Prunes domains based on arithmetic operations like SumOf, ProductOf, MaxOf.
/// Assumes operation is Result = Op(Arg1, Arg2) structure.
fn prune_arithmetic(
    domains: &mut HashMap<Wildcard, (Domain, ExpectedType)>,
    predicate: NativePredicate,
    result_arg: &StatementTmplArg,
    op1_arg: &StatementTmplArg,
    op2_arg: &StatementTmplArg,
    bindings: &HashMap<Wildcard, ConcreteValue>,
    operation: fn(i64, i64) -> i64,
) -> Result<bool, ProverError> {
    let mut changed = false;

    // Helper to get bound i64 value or None
    let get_bound_int = |wc_opt: Option<&Wildcard>| -> Option<&i64> {
        let wc = wc_opt?; // Get &Wildcard or return None
        let cv = bindings.get(wc)?; // Get &ConcreteValue or return None
        match cv {
            ConcreteValue::Val(v) => match v.typed() {
                TypedValue::Int(i) => Some(i),
                _ => None,
            },
            _ => None,
        }
    };

    // Extract wildcards first to avoid temporary borrow issues
    let wcs_res = get_wildcards_from_tmpl_arg(result_arg);
    let wcs_op1 = get_wildcards_from_tmpl_arg(op1_arg);
    let wcs_op2 = get_wildcards_from_tmpl_arg(op2_arg);

    let wc_res_opt = wcs_res.val_wcs.get(0);
    let wc_op1_opt = wcs_op1.val_wcs.get(0);
    let wc_op2_opt = wcs_op2.val_wcs.get(0);

    let res_val_ref = get_bound_int(wc_res_opt);
    let op1_val_ref = get_bound_int(wc_op1_opt);
    let op2_val_ref = get_bound_int(wc_op2_opt);

    // Case 1: Op1 and Op2 are known, prune Result
    if let (Some(wc_res), Some(v1), Some(v2)) =
        (wc_res_opt, op1_val_ref.copied(), op2_val_ref.copied())
    {
        let expected_res = operation(v1, v2);
        changed |= prune_domain_to_single_int(domains, wc_res, expected_res)?;
    }
    // Case 2: Result and Op1 are known (Attempt to prune Op2)
    if let (Some(wc_op2), Some(res), Some(v1)) =
        (wc_op2_opt, res_val_ref.copied(), op1_val_ref.copied())
    {
        // Only prune operand if it's SumOf
        if predicate == NativePredicate::SumOf {
            let expected_op2 = res.wrapping_sub(v1);
            changed |= prune_domain_to_single_int(domains, wc_op2, expected_op2)?;
        }
    }
    // Case 3: Result and Op2 are known (Attempt to prune Op1)
    if let (Some(wc_op1), Some(res), Some(v2)) =
        (wc_op1_opt, res_val_ref.copied(), op2_val_ref.copied())
    {
        // Only prune operand if it's SumOf
        if predicate == NativePredicate::SumOf {
            let expected_op1 = res.wrapping_sub(v2);
            changed |= prune_domain_to_single_int(domains, wc_op1, expected_op1)?;
        }
    }

    Ok(changed)
}

// --- NEW Int Pruning Helper ---
/// Helper to prune a domain associated with a wildcard to a single i64 value.
fn prune_domain_to_single_int(
    domains: &mut HashMap<Wildcard, (Domain, ExpectedType)>,
    wildcard: &Wildcard,
    target_int: i64,
) -> Result<bool, ProverError> {
    if let Some((domain, _)) = domains.get_mut(wildcard) {
        let target_cv = ConcreteValue::Val(Value::from(target_int));
        if domain.len() > 1 || !domain.contains(&target_cv) {
            let initial_len = domain.len();
            domain.retain(|cv| cv == &target_cv);
            if domain.is_empty() {
                return Err(ProverError::Unsatisfiable(format!(
                    "Dynamic pruning (arithmetic) emptied domain for {}",
                    wildcard.name
                )));
            }
            if domain.len() < initial_len {
                return Ok(true);
            }
        }
    }
    Ok(false)
}

// --- NEW Gt/Lt Value Pruning Helper ---
/// Prunes integer domains based on Gt/Lt constraints.
fn prune_gt_lt_values(
    domains: &mut HashMap<Wildcard, (Domain, ExpectedType)>,
    wc1: &Wildcard,
    wc2: &Wildcard,
    predicate: NativePredicate, // Gt or Lt
) -> Result<bool, ProverError> {
    let mut changed = false;

    // --- Calculate Min/Max using Immutable Borrows ---
    let (min_d1_opt, max_d1_opt, min_d2_opt, max_d2_opt): (
        Option<i64>,
        Option<i64>,
        Option<i64>,
        Option<i64>,
    ) = {
        let domain1_ints: Vec<&i64> = domains
            .get(wc1)
            .filter(|(_, et)| *et == ExpectedType::Val)
            .map(|(domain, _)| {
                domain
                    .iter()
                    .filter_map(|cv| match cv {
                        ConcreteValue::Val(v) => match v.typed() {
                            TypedValue::Int(i) => Some(i),
                            _ => None,
                        },
                        _ => None,
                    })
                    .collect()
            })
            .unwrap_or_default();

        let domain2_ints: Vec<&i64> = domains
            .get(wc2)
            .filter(|(_, et)| *et == ExpectedType::Val)
            .map(|(domain, _)| {
                domain
                    .iter()
                    .filter_map(|cv| match cv {
                        ConcreteValue::Val(v) => match v.typed() {
                            TypedValue::Int(i) => Some(i),
                            _ => None,
                        },
                        _ => None,
                    })
                    .collect()
            })
            .unwrap_or_default();

        if domain1_ints.is_empty() || domain2_ints.is_empty() {
            (None, None, None, None)
        } else {
            (
                domain1_ints.iter().min().copied().copied(),
                domain1_ints.iter().max().copied().copied(),
                domain2_ints.iter().min().copied().copied(),
                domain2_ints.iter().max().copied().copied(),
            )
        }
    }; // Immutable borrows end here. min_d1_opt etc are now Option<i64>.

    // Now, perform mutable borrows and pruning using the copied i64 values.
    if let (Some(min_d1), Some(max_d1), Some(min_d2), Some(max_d2)) =
        (min_d1_opt, max_d1_opt, min_d2_opt, max_d2_opt)
    {
        // Prune domain1
        if let Some((domain1_mut, _)) = domains.get_mut(wc1) {
            let initial_len1 = domain1_mut.len();
            if predicate == NativePredicate::Gt {
                domain1_mut.retain(|cv| match cv {
                    ConcreteValue::Val(v) => match v.typed() {
                        TypedValue::Int(v1) => *v1 > max_d2,
                        _ => true,
                    },
                    _ => true,
                });
            } else {
                domain1_mut.retain(|cv| match cv {
                    ConcreteValue::Val(v) => match v.typed() {
                        TypedValue::Int(v1) => *v1 < min_d2,
                        _ => true,
                    },
                    _ => true,
                });
            }
            if domain1_mut.is_empty() {
                return Err(ProverError::Unsatisfiable(format!(
                    "Dynamic pruning (Gt/Lt values) emptied domain for {}",
                    wc1.name
                )));
            }
            if domain1_mut.len() < initial_len1 {
                changed = true;
            }
        }

        // Prune domain2
        if let Some((domain2_mut, _)) = domains.get_mut(wc2) {
            let initial_len2 = domain2_mut.len();
            if predicate == NativePredicate::Gt {
                domain2_mut.retain(|cv| match cv {
                    ConcreteValue::Val(v) => match v.typed() {
                        TypedValue::Int(v2) => *v2 < min_d1,
                        _ => true,
                    },
                    _ => true,
                });
            } else {
                domain2_mut.retain(|cv| match cv {
                    ConcreteValue::Val(v) => match v.typed() {
                        TypedValue::Int(v2) => *v2 > max_d1,
                        _ => true,
                    },
                    _ => true,
                });
            }
            if domain2_mut.is_empty() {
                return Err(ProverError::Unsatisfiable(format!(
                    "Dynamic pruning (Gt/Lt values) emptied domain for {}",
                    wc2.name
                )));
            }
            if domain2_mut.len() < initial_len2 {
                changed = true;
            }
        }
    }

    Ok(changed)
}

// --- NEW Helper Functions for Contains/NotContains Pruning ---

/// Prunes a domain of potential keys (Value::String representing key names) based on
/// whether they exist (or not) in a specific container.
fn prune_domain_by_container_existence(
    domain: &mut Domain,
    container: &Value,
    keep_existing: bool, // true for Contains, false for NotContains
) -> Result<bool, ProverError> {
    let initial_len = domain.len();
    domain.retain(|cv| match cv {
        ConcreteValue::Key(key_string) => {
            let key_value = Value::from(key_string.clone()); // Create Value from key string
            match container.prove_existence(&key_value) {
                Ok(_) => keep_existing,   // Key exists, keep if keep_existing is true
                Err(_) => !keep_existing, // Key doesn't exist, keep if keep_existing is false
            }
        }
        _ => true, // Retain non-Key types (shouldn't be here for key domain)
    });
    if domain.is_empty() {
        return Err(ProverError::Unsatisfiable(
            "Dynamic pruning (Contains/NotContains Key) emptied domain".to_string(),
        ));
    }
    Ok(domain.len() < initial_len)
}

/// Prunes a domain of potential values based on whether they exist as values (or not)
/// within a specific container.
fn prune_domain_by_container_value_existence(
    domain: &mut Domain,
    container: &Value,
    keep_existing: bool, // true for Contains, false for NotContains
) -> Result<bool, ProverError> {
    let initial_len = domain.len();
    let existing_values: HashSet<Value> = match container.typed() {
        TypedValue::Array(a) => a.array().iter().cloned().collect(),
        TypedValue::Set(s) => s.set().iter().cloned().collect(),
        TypedValue::Dictionary(d) => d.kvs().values().cloned().collect(),
        _ => HashSet::new(),
    };

    domain.retain(|cv| match cv {
        ConcreteValue::Val(value) => {
            let value_exists = existing_values.contains(value);
            (value_exists && keep_existing) || (!value_exists && !keep_existing)
        }
        _ => true, // Retain non-Value types
    });
    if domain.is_empty() {
        return Err(ProverError::Unsatisfiable(
            "Dynamic pruning (Contains/NotContains Value) emptied domain".to_string(),
        ));
    }
    Ok(domain.len() < initial_len)
}

/// Prunes a domain of potential container Values based on whether they contain
/// (or do not contain) a specific key.
fn prune_container_domain_by_key_existence(
    domain: &mut Domain,
    key: &Value,
    keep_containing: bool, // true for Contains, false for NotContains
) -> Result<bool, ProverError> {
    let initial_len = domain.len();
    domain.retain(|cv| match cv {
        ConcreteValue::Val(container_val) => {
            // Use the Value::prove_existence method directly
            match container_val.prove_existence(key) {
                Ok(_) => keep_containing,   // Key exists, keep if keep_containing is true
                Err(_) => !keep_containing, // Key doesn't exist, keep if keep_containing is false
            }
        }
        _ => true, // Retain non-Val types
    });
    if domain.is_empty() {
        return Err(ProverError::Unsatisfiable(
            "Dynamic pruning (Contains/NotContains Container by Key) emptied domain".to_string(),
        ));
    }
    Ok(domain.len() < initial_len)
}

/// Prunes a domain of potential container Values based on whether they contain
/// (or do not contain) a specific value among their elements.
fn prune_container_domain_by_value_existence(
    domain: &mut Domain,
    value: &Value,
    keep_containing: bool, // true for Contains
) -> Result<bool, ProverError> {
    if !keep_containing {
        // Pruning containers that *don't* contain a specific value is complex and less useful.
        // Only implement the `keep_containing = true` case for Contains.
        println!("Warning: Pruning container domain by non-existence of value is not implemented.");
        return Ok(false);
    }

    let initial_len = domain.len();
    domain.retain(|cv| match cv {
        ConcreteValue::Val(container_val) => {
            // Check if the target value exists in the container_val.
            // Use the specific methods for each container type.
            match container_val.typed() {
                TypedValue::Array(a) => a.array().contains(value),
                TypedValue::Set(s) => s.set().contains(value),
                TypedValue::Dictionary(d) => d.kvs().values().any(|v| v == value),
                _ => false, // Not a container type
            }
        }
        _ => true, // Retain non-Val types
    });
    if domain.is_empty() {
        return Err(ProverError::Unsatisfiable(
            "Dynamic pruning (Contains Container by Value) emptied domain".to_string(),
        ));
    }
    Ok(domain.len() < initial_len)
}
