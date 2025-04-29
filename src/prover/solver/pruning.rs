use std::collections::HashSet;

use super::{
    types::{Constraint, ExpectedType},
    SolverState,
};
use crate::{
    middleware::PodId,
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
        if !processed_type_pruning {
            if prune_by_type(state)? {
                changed_this_pass = true;
                overall_changed = true;
                processed_type_pruning = true; // Only mark after first change
            }
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
