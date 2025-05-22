use std::collections::{HashMap, HashSet};

use log::{debug, warn};

use super::{
    types::{Constraint, Domain, ExpectedType},
    SolverState,
};
use crate::{
    middleware::{
        Key, KeyOrWildcard, NativePredicate, PodId, Predicate, Statement, StatementTmpl,
        StatementTmplArg, TypedValue, Value, Wildcard,
    },
    prover::{error::ProverError, indexing::ProverIndexes, types::ConcreteValue},
};

/// Applies type constraints, removing incompatible ConcreteValue variants from domains.
/// Returns Ok(true) if any domain changed, Ok(false) otherwise.
pub fn prune_by_type(state: &mut SolverState) -> Result<bool, ProverError> {
    debug!("Pruning: Applying type constraints.");
    let mut changed = false;
    for (wildcard, (domain, expected_type_ref)) in state.domains.iter_mut() {
        let expected_type = *expected_type_ref;
        if expected_type == ExpectedType::Unknown {
            continue; // Skip if type is not yet known
        }
        let initial_size = domain.len();

        // Retain only values matching the expected type
        domain.retain(|value| {
            matches!(
                (expected_type, value),
                (ExpectedType::Pod, ConcreteValue::Pod(_))
                    | (ExpectedType::Key, ConcreteValue::Key(_))
                    | (ExpectedType::Val, ConcreteValue::Val(_))
                    | (ExpectedType::Unknown, _)
            )
        });

        if domain.is_empty() {
            warn!(
                "Pruning: Type pruning made domain for WC '{}' empty (expected {:?}). Initial size: {}.",
                wildcard.name, expected_type, initial_size
            );
            return Err(ProverError::Unsatisfiable(format!(
                "Type pruning made domain for wildcard '{}' empty (expected {:?})",
                wildcard.name, expected_type
            )));
        }

        if domain.len() < initial_size {
            debug!(
                "  Pruning: WC '{}' domain size reduced by type {:?} from {} to {}.",
                wildcard.name,
                expected_type,
                initial_size,
                domain.len()
            );
            changed = true;
        }
    }
    debug!(
        "Pruning: Type constraints application complete. Changed: {}",
        changed
    );
    Ok(changed)
}

/// Applies literal key constraints (e.g., from `?A["foo"]`), removing PodIds from
/// the domain of `?A` if they are not known to have the key "foo".
/// Returns Ok(true) if any domain changed, Ok(false) otherwise.
pub fn prune_by_literal_key(
    state: &mut SolverState,
    indexes: &ProverIndexes,
    constraints: &[Constraint],
) -> Result<bool, ProverError> {
    let mut overall_changed_by_this_fn = false;
    for constraint in constraints {
        if let Constraint::LiteralKey {
            pod_wildcard,
            literal_key,
        } = constraint
        {
            debug!(
                "Pruning: Applying LiteralKey constraint: WC '{}' must have key '{}'.",
                pod_wildcard.name, literal_key
            );
            if let Some((domain, expected_type)) = state.domains.get_mut(pod_wildcard) {
                if *expected_type != ExpectedType::Pod {
                    debug!(
                        "  Pruning: Skipping LiteralKey for WC '{}', not Pod type (is {:?}).",
                        pod_wildcard.name, expected_type
                    );
                    continue;
                }

                let initial_size = domain.len();

                // Find PodIds that have this literal_key
                let middleware_key = Key::new(literal_key.clone());
                let allowed_pod_ids: HashSet<PodId> = indexes
                    .get_anchored_keys_for_key(&middleware_key)
                    .map(|anchored_keys| anchored_keys.iter().map(|ak| ak.pod_id).collect())
                    .unwrap_or_default();

                domain.retain(|value| match value {
                    ConcreteValue::Pod(pod_id) => {
                        if *pod_id == crate::middleware::SELF {
                            // If the pod_id is SELF, we assume the literal_key is valid if defined by a ValueOf.
                            // This pruning step might be too aggressive for SELF if the ValueOf facts for SELF
                            // are not yet fully incorporated into `indexes` in the same way as other pods.
                            // For now, let's not prune SELF based on this rule, assuming `potential_constant_info` handles it.
                            true
                        } else {
                            allowed_pod_ids.contains(pod_id)
                        }
                    }
                    _ => false, // Should not happen if type is Pod
                });

                debug!(
                    "  Pruning: WC '{}' (key '{}') allowed PodIds: {:?}. Retained: {:?}",
                    pod_wildcard.name,
                    literal_key,
                    allowed_pod_ids.iter().collect::<Vec<_>>(),
                    domain.iter().collect::<Vec<_>>()
                );

                if domain.is_empty() {
                    warn!(
                        "Pruning: LiteralKey constraint ('{}[{}]') made domain empty. Initial size: {}.",
                        pod_wildcard.name, literal_key, initial_size
                    );
                    return Err(ProverError::Unsatisfiable(format!(
                        "LiteralKey constraint ('{}[{}]') made domain empty",
                        pod_wildcard.name, literal_key
                    )));
                }

                if domain.len() < initial_size {
                    debug!(
                        "  Pruning: WC '{}' domain size reduced by LiteralKey '{}' from {} to {}.",
                        pod_wildcard.name,
                        literal_key,
                        initial_size,
                        domain.len()
                    );
                    overall_changed_by_this_fn = true;
                }
            } else {
                warn!(
                    "Pruning: WC '{}' from LiteralKey constraint not found in domains.",
                    pod_wildcard.name
                );
                return Err(ProverError::Internal(format!(
                    "Wildcard '{}' from LiteralKey constraint not found in domains",
                    pod_wildcard.name
                )));
            }
        }
    }
    Ok(overall_changed_by_this_fn)
}

/// Applies literal origin constraints (e.g., from `PodX[?Y]`), removing Keys from
/// the domain of `?Y` if they are not known to exist within the literal `PodX`.
/// Returns Ok(true) if any domain changed, Ok(false) otherwise.
pub fn prune_by_literal_origin(
    state: &mut SolverState,
    indexes: &ProverIndexes,
    constraints: &[Constraint],
) -> Result<bool, ProverError> {
    let mut overall_changed_by_this_fn = false;
    for constraint in constraints {
        if let Constraint::LiteralOrigin {
            key_wildcard,
            literal_pod_id,
        } = constraint
        {
            debug!(
                "Pruning: Applying LiteralOrigin constraint: Key WC '{}' must exist in Pod {:?}.",
                key_wildcard.name, literal_pod_id
            );
            if let Some((domain, expected_type)) = state.domains.get_mut(key_wildcard) {
                if *expected_type != ExpectedType::Key {
                    debug!(
                        "  Pruning: Skipping LiteralOrigin for WC '{}', not Key type (is {:?}).",
                        key_wildcard.name, expected_type
                    );
                    continue;
                }

                let initial_size = domain.len();

                // Find Keys that exist in this literal_pod_id
                let allowed_keys: HashSet<String> = indexes
                    .get_anchored_keys_for_pod_id(literal_pod_id)
                    .map(|anchored_keys| {
                        anchored_keys
                            .iter()
                            .map(|ak| ak.key.name().to_string())
                            .collect()
                    })
                    .unwrap_or_default();

                domain.retain(|value| match value {
                    ConcreteValue::Key(key_string) => allowed_keys.contains(key_string),
                    _ => false,
                });

                debug!(
                    "  Pruning: Key WC '{}' (Pod {:?}) allowed keys: {:?}. Retained: {:?}.",
                    key_wildcard.name,
                    literal_pod_id,
                    allowed_keys.iter().collect::<Vec<_>>(),
                    domain.iter().collect::<Vec<_>>()
                );

                if domain.is_empty() {
                    warn!(
                        "Pruning: LiteralOrigin constraint (Pod {:?}, Key WC '{}') made domain empty. Initial size: {}.",
                        literal_pod_id, key_wildcard.name, initial_size
                    );
                    return Err(ProverError::Unsatisfiable(format!(
                        "LiteralOrigin constraint ('{:?}[?{}]') made domain empty",
                        literal_pod_id, key_wildcard.name
                    )));
                }

                if domain.len() < initial_size {
                    debug!(
                        "  Pruning: Key WC '{}' domain size reduced by LiteralOrigin (Pod {:?}) from {} to {}.",
                        key_wildcard.name, literal_pod_id, initial_size, domain.len()
                    );
                    overall_changed_by_this_fn = true;
                }
            } else {
                warn!(
                    "Pruning: WC '{}' from LiteralOrigin constraint not found in domains.",
                    key_wildcard.name
                );
                return Err(ProverError::Internal(format!(
                    "Wildcard '{}' from LiteralOrigin constraint not found in domains",
                    key_wildcard.name
                )));
            }
        }
    }
    Ok(overall_changed_by_this_fn)
}

/// Applies literal value constraints, removing Values from the domain of a wildcard
/// if they do not match the required literal value.
/// Returns Ok(true) if any domain changed, Ok(false) otherwise.
pub fn prune_by_literal_value(
    state: &mut SolverState,
    constraints: &[Constraint],
) -> Result<bool, ProverError> {
    let mut changed = false;
    for constraint in constraints {
        if let Constraint::LiteralValue {
            wildcard,
            literal_value,
        } = constraint
        {
            debug!(
                "Pruning: Applying LiteralValue constraint: WC '{}' must be {:?}.",
                wildcard.name, literal_value
            );
            if let Some((domain, expected_type)) = state.domains.get_mut(wildcard) {
                if *expected_type != ExpectedType::Val {
                    debug!(
                        "  Pruning: Skipping LiteralValue for WC '{}', not Val type (is {:?}).",
                        wildcard.name, expected_type
                    );
                    continue;
                }

                let initial_size = domain.len();

                domain.retain(|value| match value {
                    ConcreteValue::Val(v) => v == literal_value,
                    _ => false,
                });

                if domain.is_empty() {
                    warn!(
                        "Pruning: LiteralValue constraint ('{}' = {:?}) made domain empty. Initial size: {}.",
                        wildcard.name, literal_value, initial_size
                    );
                    return Err(ProverError::Unsatisfiable(format!(
                        "LiteralValue constraint ('{}' = {:?}) made domain empty",
                        wildcard.name, literal_value
                    )));
                }

                if domain.len() < initial_size {
                    debug!(
                        "  Pruning: WC '{}' domain size reduced by LiteralValue {:?} from {} to {}.",
                        wildcard.name, literal_value, initial_size, domain.len()
                    );
                    changed = true;
                }
            } else {
                warn!(
                    "Pruning: WC '{}' from LiteralValue constraint not found in domains.",
                    wildcard.name
                );
                return Err(ProverError::Internal(format!(
                    "Wildcard '{}' from LiteralValue constraint not found in domains",
                    wildcard.name
                )));
            }
        }
    }
    Ok(changed)
}

/// Applies wildcard origin constraints (?A[?K]), removing Keys from ?K's domain
/// if ?A's domain becomes a singleton PodId and the Key doesn't exist in that Pod.
/// Returns Ok(true) if any domain changed, Ok(false) otherwise.
pub fn prune_by_wildcard_origin(
    state: &mut SolverState,
    indexes: &ProverIndexes,
    constraints: &[Constraint],
) -> Result<bool, ProverError> {
    let mut overall_changed_by_this_fn = false;
    for constraint in constraints {
        if let Constraint::WildcardOrigin {
            key_wildcard,
            pod_wildcard,
        } = constraint
        {
            debug!(
                "Pruning: Applying WildcardOrigin constraint: Key WC '{}' must exist in Pod WC '{}'.",
                key_wildcard.name, pod_wildcard.name
            );
            // Check if pod_wildcard domain is a singleton PodId
            let mut literal_pod_id_opt: Option<PodId> = None;
            if let Some((pod_domain, pod_expected_type)) = state.domains.get(pod_wildcard) {
                if *pod_expected_type == ExpectedType::Pod && pod_domain.len() == 1 {
                    if let Some(ConcreteValue::Pod(id)) = pod_domain.iter().next() {
                        literal_pod_id_opt = Some(*id);
                    }
                }
            }

            if let Some(literal_pod_id) = literal_pod_id_opt {
                if let Some((key_domain, key_expected_type)) = state.domains.get_mut(key_wildcard) {
                    if *key_expected_type != ExpectedType::Key {
                        debug!(
                            "  Pruning: Skipping WildcardOrigin for Key WC '{}', not Key type (is {:?}).",
                            key_wildcard.name, key_expected_type
                        );
                        continue;
                    }

                    let initial_size = key_domain.len();

                    let allowed_keys: HashSet<String> = indexes
                        .get_anchored_keys_for_pod_id(&literal_pod_id)
                        .map(|anchored_keys| {
                            anchored_keys
                                .iter()
                                .map(|ak| ak.key.name().to_string())
                                .collect()
                        })
                        .unwrap_or_default();

                    key_domain.retain(|value| match value {
                        ConcreteValue::Key(key_string) => allowed_keys.contains(key_string),
                        _ => false,
                    });

                    debug!(
                        "  Pruning: Key WC '{}' (Pod WC '{}' resolved to {:?}) allowed keys: {:?}. Retained: {:?}.",
                        key_wildcard.name, pod_wildcard.name, literal_pod_id, allowed_keys.iter().collect::<Vec<_>>(), key_domain.iter().collect::<Vec<_>>()
                    );

                    if key_domain.is_empty() {
                        warn!(
                            "Pruning: WildcardOrigin constraint (Pod WC '{}' -> {:?}, Key WC '{}') made key domain empty. Initial size: {}.",
                            pod_wildcard.name, literal_pod_id, key_wildcard.name, initial_size
                        );
                        return Err(ProverError::Unsatisfiable(format!(
                            "WildcardOrigin constraint (pod='{}', key='{}') made key domain empty",
                            pod_wildcard.name, key_wildcard.name
                        )));
                    }

                    if key_domain.len() < initial_size {
                        debug!(
                            "  Pruning: Key WC '{}' domain size reduced by WildcardOrigin (Pod WC '{}' -> {:?}) from {} to {}.",
                            key_wildcard.name, pod_wildcard.name, literal_pod_id, initial_size, key_domain.len()
                        );
                        overall_changed_by_this_fn = true;
                    }
                }
            } else {
                debug!(
                    "  Pruning: WildcardOrigin: Pod WC '{}' domain not yet singleton or not Pod type.",
                    pod_wildcard.name
                );
            }
        }
    }
    Ok(overall_changed_by_this_fn)
}

/// Runs the initial set of pruning functions iteratively until a fixed point is reached.
/// Returns Ok(true) if any domain changed during the process, Ok(false) otherwise.
pub(super) fn prune_initial_domains(
    state: &mut SolverState,
    indexes: &ProverIndexes,
    equality_pairs: &[(Wildcard, Wildcard)],
    inequality_pairs: &[(Wildcard, Wildcard)],
    constraints: &[Constraint],
) -> Result<bool, ProverError> {
    debug!(
        "Pruning: Entering prune_initial_domains. Equality pairs: {}, Inequality pairs: {}, Explicit constraints: {}",
        equality_pairs.len(), inequality_pairs.len(), constraints.len()
    );
    let mut overall_changed = false;
    let mut changed_this_pass = true;
    let mut processed_type_pruning = false;
    let mut pass_num = 0;

    while changed_this_pass {
        pass_num += 1;
        debug!("  Pruning: prune_initial_domains pass #{}.", pass_num);
        changed_this_pass = false;

        // Apply type constraints first
        if !processed_type_pruning {
            debug!("    Pruning: Applying type pruning (pass #{}).", pass_num);
            if prune_by_type(state)? {
                debug!("      Pruning: Type pruning reported changes.");
                changed_this_pass = true;
                overall_changed = true;
                processed_type_pruning = true; // Mark as processed for this outer loop iteration
            } else {
                debug!("      Pruning: Type pruning reported NO changes.");
                // If type pruning makes no change, it might not need to run again until other pruners make progress.
                // However, other pruners might change types implicitly, so always allow it to run if `processed_type_pruning` is reset.
            }
        }

        // Apply explicit constraints
        let mut explicit_constraints_changed_this_pass = false;
        for constraint in constraints {
            let mut constraint_changed_current_iter = false;
            match constraint {
                Constraint::LiteralKey { .. } => {
                    debug!(
                        "    Pruning: Applying LiteralKey constraints (pass #{}).",
                        pass_num
                    );
                    constraint_changed_current_iter =
                        prune_by_literal_key(state, indexes, std::slice::from_ref(constraint))?;
                }
                Constraint::LiteralOrigin { .. } => {
                    debug!(
                        "    Pruning: Applying LiteralOrigin constraints (pass #{}).",
                        pass_num
                    );
                    constraint_changed_current_iter =
                        prune_by_literal_origin(state, indexes, std::slice::from_ref(constraint))?;
                }
                Constraint::WildcardOrigin { .. } => {
                    debug!(
                        "    Pruning: Applying WildcardOrigin constraints (pass #{}).",
                        pass_num
                    );
                    constraint_changed_current_iter =
                        prune_by_wildcard_origin(state, indexes, std::slice::from_ref(constraint))?;
                }
                Constraint::LiteralValue { .. } => {
                    debug!(
                        "    Pruning: Applying LiteralValue constraints (pass #{}).",
                        pass_num
                    );
                    constraint_changed_current_iter =
                        prune_by_literal_value(state, std::slice::from_ref(constraint))?;
                }
                Constraint::Type { .. } => { /* Already handled by prune_by_type */ }
            };
            if constraint_changed_current_iter {
                debug!(
                    "      Pruning: Explicit constraint {:?} reported changes.",
                    constraint
                );
                explicit_constraints_changed_this_pass = true;
            }
        }
        if explicit_constraints_changed_this_pass {
            changed_this_pass = true;
            overall_changed = true;
        }

        // Apply implicit equality constraints
        let mut equality_changed_this_pass = false;
        if !equality_pairs.is_empty() {
            debug!("    Pruning: Applying equality pairs (pass #{}).", pass_num);
            for (wc1, wc2) in equality_pairs {
                if propagate_or_intersect(&mut state.domains, wc1, wc2)? {
                    debug!(
                        "      Pruning: Propagate/intersect for ({}, {}) reported changes.",
                        wc1.name, wc2.name
                    );
                    equality_changed_this_pass = true;
                }
            }
        }
        if equality_changed_this_pass {
            changed_this_pass = true;
            overall_changed = true;
        }

        // Apply implicit inequality constraints
        let mut inequality_changed_this_pass = false;
        if !inequality_pairs.is_empty() {
            debug!(
                "    Pruning: Applying inequality pairs (pass #{}).",
                pass_num
            );
            for (wc1, wc2) in inequality_pairs {
                if remove_singleton(&mut state.domains, wc1, wc2)? {
                    debug!(
                        "      Pruning: Remove_singleton for ({}, {}) reported changes.",
                        wc1.name, wc2.name
                    );
                    inequality_changed_this_pass = true;
                }
                if remove_singleton(&mut state.domains, wc2, wc1)? {
                    debug!(
                        "      Pruning: Remove_singleton for ({}, {}) reported changes.",
                        wc2.name, wc1.name
                    );
                    inequality_changed_this_pass = true;
                }
            }
        }
        if inequality_changed_this_pass {
            changed_this_pass = true;
            overall_changed = true;
        }

        if changed_this_pass {
            debug!(
                "    Pruning: Pass #{} made changes, resetting processed_type_pruning.",
                pass_num
            );
            processed_type_pruning = false; // If any other pruner made a change, re-check types.
        } else {
            debug!("    Pruning: Pass #{} made NO changes.", pass_num);
        }
    }
    debug!(
        "Pruning: Exiting prune_initial_domains. Overall changed: {}. Total passes: {}",
        overall_changed, pass_num
    );
    Ok(overall_changed)
}

/// Applies pruning logic directly based on a newly proven statement and its associated bindings.
/// Returns Ok(true) if any domain changed, Ok(false) otherwise.
pub(super) fn prune_domains_after_proof(
    state: &mut SolverState,
    proven_template: &StatementTmpl,
    proven_statement: &Statement,
    bindings: &HashMap<Wildcard, ConcreteValue>,
) -> Result<bool, ProverError> {
    debug!(
        "Pruning: prune_domains_after_proof for template {:?}, concrete stmt: {:?}",
        proven_template.pred, proven_statement
    );
    let mut changed = false;

    match proven_template.pred {
        Predicate::Native(NativePredicate::Equal) => {
            if proven_template.args.len() == 2 {
                let wildcards1 = get_wildcards_from_tmpl_arg(&proven_template.args[0]);
                let wildcards2 = get_wildcards_from_tmpl_arg(&proven_template.args[1]);
                debug!(
                    "  Pruning (Equal): Wildcards involved: wc1_pods: {:?}, wc1_keys: {:?}, wc1_vals: {:?}; wc2_pods: {:?}, wc2_keys: {:?}, wc2_vals: {:?}",
                    wildcards1.pod_wcs.iter().map(|w|w.name.clone()).collect::<Vec<_>>(),
                    wildcards1.key_wcs.iter().map(|w|w.name.clone()).collect::<Vec<_>>(),
                    wildcards1.val_wcs.iter().map(|w|w.name.clone()).collect::<Vec<_>>(),
                    wildcards2.pod_wcs.iter().map(|w|w.name.clone()).collect::<Vec<_>>(),
                    wildcards2.key_wcs.iter().map(|w|w.name.clone()).collect::<Vec<_>>(),
                    wildcards2.val_wcs.iter().map(|w|w.name.clone()).collect::<Vec<_>>()
                );

                // For Equal predicates, only propagate/intersect for wildcards directly representing values.
                // Equality of AnchoredKeys (e.g., Equal(P1[K1], P2[K2])) means the *values*
                // at those anchored keys are equal. This equality is handled by DSU updates
                // in the indexing phase or by EqualFromEntries in the proof phase.
                // We should not attempt to equate the domains of P1 and P2, or K1 and K2 here.
                for wc1_val in &wildcards1.val_wcs {
                    for wc2_val in &wildcards2.val_wcs {
                        changed |= propagate_or_intersect(&mut state.domains, wc1_val, wc2_val)?;
                    }
                }
            }
        }
        Predicate::Native(NativePredicate::NotEqual) => {
            if proven_template.args.len() == 2 {
                let wildcards1 = get_wildcards_from_tmpl_arg(&proven_template.args[0]);
                let wildcards2 = get_wildcards_from_tmpl_arg(&proven_template.args[1]);
                debug!(
                    "  Pruning (NotEqual): Wildcards involved: wc1_pods: {:?}, wc1_keys: {:?}, wc1_vals: {:?}; wc2_pods: {:?}, wc2_keys: {:?}, wc2_vals: {:?}",
                    wildcards1.pod_wcs.iter().map(|w|w.name.clone()).collect::<Vec<_>>(),
                    wildcards1.key_wcs.iter().map(|w|w.name.clone()).collect::<Vec<_>>(),
                    wildcards1.val_wcs.iter().map(|w|w.name.clone()).collect::<Vec<_>>(),
                    wildcards2.pod_wcs.iter().map(|w|w.name.clone()).collect::<Vec<_>>(),
                    wildcards2.key_wcs.iter().map(|w|w.name.clone()).collect::<Vec<_>>(),
                    wildcards2.val_wcs.iter().map(|w|w.name.clone()).collect::<Vec<_>>()
                );
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
            let mut neq_changed = false;
            if proven_template.args.len() == 2 {
                let wildcards1 = get_wildcards_from_tmpl_arg(&proven_template.args[0]);
                let wildcards2 = get_wildcards_from_tmpl_arg(&proven_template.args[1]);
                debug!(
                    "  Pruning (Gt/Lt): Wildcards involved: wc1_pods: {:?}, wc1_keys: {:?}, wc1_vals: {:?}; wc2_pods: {:?}, wc2_keys: {:?}, wc2_vals: {:?}",
                    wildcards1.pod_wcs.iter().map(|w|w.name.clone()).collect::<Vec<_>>(),
                    wildcards1.key_wcs.iter().map(|w|w.name.clone()).collect::<Vec<_>>(),
                    wildcards1.val_wcs.iter().map(|w|w.name.clone()).collect::<Vec<_>>(),
                    wildcards2.pod_wcs.iter().map(|w|w.name.clone()).collect::<Vec<_>>(),
                    wildcards2.key_wcs.iter().map(|w|w.name.clone()).collect::<Vec<_>>(),
                    wildcards2.val_wcs.iter().map(|w|w.name.clone()).collect::<Vec<_>>()
                );
                for wc1 in wildcards1.pod_wcs.iter().chain(wildcards1.key_wcs.iter()) {
                    for wc2 in wildcards2.pod_wcs.iter().chain(wildcards2.key_wcs.iter()) {
                        neq_changed |= remove_singleton(&mut state.domains, wc1, wc2)?;
                        neq_changed |= remove_singleton(&mut state.domains, wc2, wc1)?;
                    }
                }
                for wc1_val in &wildcards1.val_wcs {
                    for wc2_val in &wildcards2.val_wcs {
                        neq_changed |= remove_singleton(&mut state.domains, wc1_val, wc2_val)?;
                        neq_changed |= remove_singleton(&mut state.domains, wc2_val, wc1_val)?;
                    }
                }
                if let (Some(tmpl_arg1), Some(tmpl_arg2)) =
                    (proven_template.args.get(0), proven_template.args.get(1))
                {
                    let val_wcs1 = get_wildcards_from_tmpl_arg(tmpl_arg1).val_wcs;
                    let val_wcs2 = get_wildcards_from_tmpl_arg(tmpl_arg2).val_wcs;
                    for wc1 in &val_wcs1 {
                        for wc2 in &val_wcs2 {
                            if let Predicate::Native(native_pred) = proven_template.pred {
                                changed |=
                                    prune_gt_lt_values(&mut state.domains, wc1, wc2, native_pred)?;
                            }
                        }
                    }
                }
            }
            changed |= neq_changed;
        }
        Predicate::Native(NativePredicate::ValueOf) => {
            if proven_template.args.len() == 2 {
                if let Some(value_arg_tmpl) = proven_template.args.get(1) {
                    let value_wildcards = get_wildcards_from_tmpl_arg(value_arg_tmpl);
                    for wc_val in value_wildcards.val_wcs {
                        if let Some(ConcreteValue::Val(bound_val)) = bindings.get(&wc_val) {
                            debug!(
                                "  Pruning (ValueOf): WC '{}' bound to {:?}. Setting domain to this value.",
                                wc_val.name, bound_val
                            );
                            if let Some((domain, _)) = state.domains.get_mut(&wc_val) {
                                let initial_len = domain.len();
                                let target_cv = ConcreteValue::Val(bound_val.clone());
                                domain.retain(|cv| cv == &target_cv);
                                if domain.is_empty() {
                                    warn!(
                                        "Dynamic pruning (ValueOf) for WC '{}' (target {:?}) emptied domain. Initial size: {}.",
                                        wc_val.name, target_cv, initial_len
                                    );
                                    return Err(ProverError::Unsatisfiable(format!(
                                        "Dynamic pruning (ValueOf) emptied domain for {}",
                                        wc_val.name
                                    )));
                                }
                                if domain.len() < initial_len {
                                    debug!(
                                        "    Pruning (ValueOf): WC '{}' domain reduced from {} to {} (target {:?}).",
                                        wc_val.name, initial_len, domain.len(), target_cv
                                    );
                                    changed = true;
                                }
                            }
                        }
                    }
                }
            }
        }
        Predicate::Native(NativePredicate::SumOf) => {
            if proven_template.args.len() == 3 {
                changed |= prune_arithmetic(
                    &mut state.domains,
                    NativePredicate::SumOf,
                    &proven_template.args[0],
                    &proven_template.args[1],
                    &proven_template.args[2],
                    bindings,
                    |a, b| a + b,
                )?;
                debug!("  Pruning (SumOf): prune_arithmetic changed: {}", changed);
            }
        }
        Predicate::Native(NativePredicate::ProductOf) => {
            if proven_template.args.len() == 3 {
                changed |= prune_arithmetic(
                    &mut state.domains,
                    NativePredicate::ProductOf,
                    &proven_template.args[0],
                    &proven_template.args[1],
                    &proven_template.args[2],
                    bindings,
                    |a, b| a * b,
                )?;
                debug!(
                    "  Pruning (ProductOf): prune_arithmetic changed: {}",
                    changed
                );
            }
        }
        Predicate::Native(NativePredicate::MaxOf) => {
            if proven_template.args.len() == 3 {
                changed |= prune_arithmetic(
                    &mut state.domains,
                    NativePredicate::MaxOf,
                    &proven_template.args[0],
                    &proven_template.args[1],
                    &proven_template.args[2],
                    bindings,
                    std::cmp::max,
                )?;
                debug!("  Pruning (MaxOf): prune_arithmetic changed: {}", changed);
            }
        }
        Predicate::Native(NativePredicate::Contains) => {
            if proven_template.args.len() == 3 {
                let container_arg = &proven_template.args[0];
                let key_arg = &proven_template.args[1];
                let value_arg = &proven_template.args[2];

                let wcs_c = get_wildcards_from_tmpl_arg(container_arg);
                let wcs_k = get_wildcards_from_tmpl_arg(key_arg);
                let wcs_v = get_wildcards_from_tmpl_arg(value_arg);

                let bound_container = wcs_c
                    .val_wcs
                    .get(0)
                    .and_then(|wc| bindings.get(wc))
                    .and_then(|cv| match cv {
                        ConcreteValue::Val(v) => {
                            debug!(
                                "  Pruning (Contains): Bound container for WC '{}' is {:?}",
                                wcs_c
                                    .val_wcs
                                    .get(0)
                                    .map(|w| w.name.as_str())
                                    .unwrap_or("<bound_directly>"),
                                v
                            );
                            Some(v.clone())
                        }
                        _ => None,
                    });
                let bound_key = wcs_k
                    .val_wcs
                    .get(0)
                    .and_then(|wc| bindings.get(wc))
                    .and_then(|cv| match cv {
                        ConcreteValue::Val(v) => {
                            debug!(
                                "  Pruning (Contains): Bound key for WC '{}' is {:?}",
                                wcs_k
                                    .val_wcs
                                    .get(0)
                                    .map(|w| w.name.as_str())
                                    .unwrap_or("<bound_directly>"),
                                v
                            );
                            Some(v.clone())
                        }
                        _ => None,
                    });
                let bound_value = wcs_v
                    .val_wcs
                    .get(0)
                    .and_then(|wc| bindings.get(wc))
                    .and_then(|cv| match cv {
                        ConcreteValue::Val(v) => {
                            debug!(
                                "  Pruning (Contains): Bound value for WC '{}' is {:?}",
                                wcs_v
                                    .val_wcs
                                    .get(0)
                                    .map(|w| w.name.as_str())
                                    .unwrap_or("<bound_directly>"),
                                v
                            );
                            Some(v.clone())
                        }
                        _ => None,
                    });

                if let Some(container) = bound_container {
                    for wc_k in &wcs_k.val_wcs {
                        if let Some((domain_k, _)) = state.domains.get_mut(wc_k) {
                            changed |=
                                prune_domain_by_container_existence(domain_k, &container, true)?;
                        }
                    }
                    for wc_v in &wcs_v.val_wcs {
                        if let Some((domain_v, _)) = state.domains.get_mut(wc_v) {
                            changed |= prune_domain_by_container_value_existence(
                                domain_v, &container, true,
                            )?
                        }
                    }
                }

                if let Some(key) = bound_key {
                    for wc_c in &wcs_c.val_wcs {
                        if let Some((domain_c, _)) = state.domains.get_mut(wc_c) {
                            changed |=
                                prune_container_domain_by_key_existence(domain_c, &key, true)?;
                        }
                    }
                    for wc_v in &wcs_v.val_wcs {
                        if state.domains.contains_key(wc_v) {
                            let mut possible_values = HashSet::new();
                            let wc_c_target = wcs_c.val_wcs.get(0);
                            if let Some(wc_c_concrete) = wc_c_target {
                                let container_domain_view = state.domains.get(wc_c_concrete);
                                if let Some((domain_c_concrete, _)) = container_domain_view {
                                    for cv_c in domain_c_concrete {
                                        if let ConcreteValue::Val(container_val) = cv_c {
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
                                if let Some((domain_v_mut, _)) = state.domains.get_mut(wc_v) {
                                    let initial_len = domain_v_mut.len();
                                    domain_v_mut.retain(|cv| possible_values.contains(cv));
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

                if let Some(value) = bound_value {
                    for wc_c in &wcs_c.val_wcs {
                        if let Some((domain_c, _)) = state.domains.get_mut(wc_c) {
                            changed |=
                                prune_container_domain_by_value_existence(domain_c, &value, true)?;
                        }
                    }
                    if let Some(wc_k) = wcs_k.val_wcs.get(0) {
                        if let Some(wc_c) = wcs_c.val_wcs.get(0) {
                            let mut allowed_keys: HashSet<ConcreteValue> = HashSet::new();

                            if let Some((container_domain, _)) = state.domains.get(wc_c) {
                                for cv_container in container_domain {
                                    if let ConcreteValue::Val(container_val) = cv_container {
                                        match container_val.typed() {
                                            TypedValue::Dictionary(dict) => {
                                                for (key, val) in dict.kvs() {
                                                    if val == &value {
                                                        allowed_keys.insert(ConcreteValue::Val(
                                                            Value::from(key.name()),
                                                        ));
                                                    }
                                                }
                                            }
                                            TypedValue::Array(arr) => {
                                                for (idx, val) in arr.array().iter().enumerate() {
                                                    if val == &value {
                                                        allowed_keys.insert(ConcreteValue::Val(
                                                            Value::from(idx as i64),
                                                        ));
                                                    }
                                                }
                                            }
                                            TypedValue::Set(_) => {}
                                            _ => {}
                                        }
                                    }
                                }
                            }

                            if let Some((key_domain, _)) = state.domains.get_mut(wc_k) {
                                let initial_len = key_domain.len();
                                if allowed_keys.is_empty() {
                                    if initial_len > 0 {
                                        key_domain.clear();
                                        return Err(ProverError::Unsatisfiable(format!(
                                            "Dynamic pruning (Contains/Value->Key) found no valid keys for value {:?}, emptied domain for {}",
                                            value, wc_k.name
                                        )));
                                    }
                                } else {
                                    key_domain.retain(|cv_key| allowed_keys.contains(cv_key));
                                    if key_domain.is_empty() && initial_len > 0 {
                                        return Err(ProverError::Unsatisfiable(format!(
                                            "Dynamic pruning (Contains/Value->Key) emptied domain for {} after filtering",
                                            wc_k.name
                                        )));
                                    }
                                    if key_domain.len() < initial_len {
                                        changed = true;
                                    }
                                }
                            }
                        }
                    }
                }
            }
        }
        Predicate::Native(NativePredicate::NotContains) => {
            if proven_template.args.len() == 2 {
                let container_arg = &proven_template.args[0];
                let key_arg = &proven_template.args[1];

                let wcs_c = get_wildcards_from_tmpl_arg(container_arg);
                let wcs_k = get_wildcards_from_tmpl_arg(key_arg);

                let bound_container = wcs_c
                    .val_wcs
                    .get(0)
                    .and_then(|wc| bindings.get(wc))
                    .and_then(|cv| match cv {
                        ConcreteValue::Val(v) => {
                            debug!(
                                "  Pruning (NotContains): Bound container for WC '{}' is {:?}",
                                wcs_c
                                    .val_wcs
                                    .get(0)
                                    .map(|w| w.name.as_str())
                                    .unwrap_or("<bound_directly>"),
                                v
                            );
                            Some(v.clone())
                        }
                        _ => None,
                    });
                let bound_key = wcs_k
                    .val_wcs
                    .get(0)
                    .and_then(|wc| bindings.get(wc))
                    .and_then(|cv| match cv {
                        ConcreteValue::Val(v) => {
                            debug!(
                                "  Pruning (NotContains): Bound key for WC '{}' is {:?}",
                                wcs_k
                                    .val_wcs
                                    .get(0)
                                    .map(|w| w.name.as_str())
                                    .unwrap_or("<bound_directly>"),
                                v
                            );
                            Some(v.clone())
                        }
                        _ => None,
                    });

                if let Some(container) = bound_container {
                    for wc_k in &wcs_k.val_wcs {
                        if let Some((domain_k, _)) = state.domains.get_mut(wc_k) {
                            changed |=
                                prune_domain_by_container_existence(domain_k, &container, false)?;
                        }
                    }
                }

                if let Some(key) = bound_key {
                    for wc_c in &wcs_c.val_wcs {
                        if let Some((domain_c, _)) = state.domains.get_mut(wc_c) {
                            changed |=
                                prune_container_domain_by_key_existence(domain_c, &key, false)?;
                        }
                    }
                }
            }
        }
        Predicate::Custom(_) | Predicate::BatchSelf(_) => {
            warn!(
                "Dynamic pruning for Custom/BatchSelf predicates not yet implemented: {:?}",
                proven_template.pred
            );
        }
        _ => {}
    }
    debug!(
        "Pruning: prune_domains_after_proof for {:?} complete. Changed: {}",
        proven_template.pred, changed
    );

    Ok(changed)
}

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
    if wc1 == wc2 {
        return Ok(false);
    } // Optimization
    if !domains.contains_key(wc1) || !domains.contains_key(wc2) {
        debug!(
            "  Pruning (propagate_or_intersect): Skipping ({}, {}), one or both not in domains.",
            wc1.name, wc2.name
        );
        return Ok(false);
    }

    let (domain1_view, type1) = domains.get(wc1).unwrap();
    let (domain2_view, type2) = domains.get(wc2).unwrap();

    if type1 != type2 && *type1 != ExpectedType::Unknown && *type2 != ExpectedType::Unknown {
        warn!(
            "  Pruning (propagate_or_intersect): Type mismatch between {} ({:?}) and {} ({:?}). Skipping.",
            wc1.name, type1, wc2.name, type2
        );
        return Ok(false); // Cannot intersect domains of different concrete types
    }

    let len1 = domain1_view.len();
    let len2 = domain2_view.len();
    let mut changed = false;

    if len1 == 1 && len2 > 1 {
        let singleton_val = domain1_view.iter().next().unwrap().clone();
        debug!(
            "  Pruning (propagate_or_intersect): WC '{}' is singleton ({:?}). Setting WC '{}' domain.",
            wc1.name, singleton_val, wc2.name
        );
        let (domain2_mut, _) = domains.get_mut(wc2).unwrap();
        let initial_len = domain2_mut.len();
        domain2_mut.retain(|v| v == &singleton_val);
        if domain2_mut.is_empty() {
            warn!(
                "Pruning: propagate_or_intersect for ({}, {}) emptied domain for {}. Singleton was {:?}.",
                wc1.name, wc2.name, wc2.name, singleton_val
            );
            return Err(ProverError::Unsatisfiable(format!(
                "Dynamic pruning (propagate/intersect) emptied domain for {}",
                wc2.name
            )));
        }
        if domain2_mut.len() < initial_len {
            debug!(
                "    Pruning (propagate_or_intersect): WC '{}' domain reduced from {} to {} by WC '{}' singleton.",
                wc2.name, initial_len, domain2_mut.len(), wc1.name
            );
            changed = true;
        }
    } else if len2 == 1 && len1 > 1 {
        let singleton_val = domain2_view.iter().next().unwrap().clone();
        debug!(
            "  Pruning (propagate_or_intersect): WC '{}' is singleton ({:?}). Setting WC '{}' domain.",
            wc2.name, singleton_val, wc1.name
        );
        let (domain1_mut, _) = domains.get_mut(wc1).unwrap();
        let initial_len = domain1_mut.len();
        domain1_mut.retain(|v| v == &singleton_val);
        if domain1_mut.is_empty() {
            warn!(
                "Pruning: propagate_or_intersect for ({}, {}) emptied domain for {}. Singleton was {:?}.",
                wc1.name, wc2.name, wc1.name, singleton_val
            );
            return Err(ProverError::Unsatisfiable(format!(
                "Dynamic pruning (propagate/intersect) emptied domain for {}",
                wc1.name
            )));
        }
        if domain1_mut.len() < initial_len {
            debug!(
                "    Pruning (propagate_or_intersect): WC '{}' domain reduced from {} to {} by WC '{}' singleton.",
                wc1.name, initial_len, domain1_mut.len(), wc2.name
            );
            changed = true;
        }
    } else if len1 > 1 && len2 > 1 {
        // Intersect non-singleton domains
        let intersection: Domain = domain1_view.intersection(domain2_view).cloned().collect();
        debug!(
            "  Pruning (propagate_or_intersect): Intersecting domains for WC '{}' (size {}) and WC '{}' (size {}). Intersection size: {}.",
            wc1.name, len1, wc2.name, len2, intersection.len()
        );

        if intersection.is_empty() {
            warn!(
                "Pruning: propagate_or_intersect resulted in empty domain intersection for {} and {}.",
                wc1.name, wc2.name
            );
            return Err(ProverError::Unsatisfiable(format!(
                "Dynamic pruning (propagate/intersect) resulted in empty domain intersection for {} and {}",
                wc1.name,
                wc2.name
            )));
        }

        let (domain1_mut, _) = domains.get_mut(wc1).unwrap();
        if intersection.len() < domain1_mut.len() {
            debug!(
                "    Pruning (propagate_or_intersect): WC '{}' domain reduced from {} to {} by intersection with WC '{}'.",
                wc1.name, domain1_mut.len(), intersection.len(), wc2.name
            );
            *domain1_mut = intersection.clone();
            changed = true;
        }
        let (domain2_mut, _) = domains.get_mut(wc2).unwrap();
        if intersection.len() < domain2_mut.len() {
            debug!(
                "    Pruning (propagate_or_intersect): WC '{}' domain reduced from {} to {} by intersection with WC '{}'.",
                wc2.name, domain2_mut.len(), intersection.len(), wc1.name
            );
            *domain2_mut = intersection;
            changed = true;
        }
    } else {
        debug!(
            "  Pruning (propagate_or_intersect): No action for WC '{}' (len {}) and WC '{}' (len {}).",
            wc1.name, len1, wc2.name, len2
        );
    }
    Ok(changed)
}

/// Helper to remove a singleton value from another domain (for NotEqual).
/// Modifies `domains` in place. Returns Ok(true) if domain changed.
pub(super) fn remove_singleton(
    domains: &mut HashMap<Wildcard, (Domain, ExpectedType)>,
    wc_singleton: &Wildcard,
    wc_target: &Wildcard,
) -> Result<bool, ProverError> {
    if wc_singleton == wc_target {
        return Ok(false);
    } // Optimization
    if !domains.contains_key(wc_singleton) || !domains.contains_key(wc_target) {
        debug!(
            "  Pruning (remove_singleton): Skipping ({}, {}), one or both not in domains.",
            wc_singleton.name, wc_target.name
        );
        return Ok(false);
    }
    if domains[wc_singleton].0.len() == 1 && !domains[wc_target].0.is_empty() {
        let val_to_remove = domains[wc_singleton].0.iter().next().unwrap().clone();
        debug!(
            "  Pruning (remove_singleton): WC '{}' is singleton ({:?}). Attempting to remove from WC '{}' domain.",
            wc_singleton.name, val_to_remove, wc_target.name
        );
        let (target_domain_mut, _) = domains.get_mut(wc_target).unwrap();
        let initial_len = target_domain_mut.len();
        target_domain_mut.remove(&val_to_remove);
        if target_domain_mut.is_empty() {
            warn!(
                "Pruning: remove_singleton for ({}, target {}) emptied target domain. Value removed: {:?}.",
                wc_singleton.name, wc_target.name, val_to_remove
            );
            return Err(ProverError::Unsatisfiable(format!(
                "Dynamic pruning (remove singleton) emptied domain for {}",
                wc_target.name
            )));
        }
        if target_domain_mut.len() < initial_len {
            debug!(
                "    Pruning (remove_singleton): WC '{}' domain reduced from {} to {} by removing {:?} (from WC '{}').",
                wc_target.name, initial_len, target_domain_mut.len(), val_to_remove, wc_singleton.name
            );
            return Ok(true);
        }
    }
    Ok(false)
}

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
    debug!(
        "Pruning: prune_arithmetic for {:?}. Result: {:?}, Op1: {:?}, Op2: {:?}",
        predicate, result_arg, op1_arg, op2_arg
    );
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
        debug!(
            "  Pruning (arithmetic): Op1 ({:?}) and Op2 ({:?}) known. Expected result for WC '{}': {}.",
            v1, v2, wc_res.name, expected_res
        );
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

    debug!(
        "Pruning: prune_arithmetic for {:?} complete. Changed: {}",
        predicate, changed
    );

    Ok(changed)
}

/// Helper to prune a domain associated with a wildcard to a single i64 value.
fn prune_domain_to_single_int(
    domains: &mut HashMap<Wildcard, (Domain, ExpectedType)>,
    wildcard: &Wildcard,
    target_int: i64,
) -> Result<bool, ProverError> {
    debug!(
        "  Pruning (single_int): Attempting to prune WC '{}' domain to {}.",
        wildcard.name, target_int
    );
    if let Some((domain, _)) = domains.get_mut(wildcard) {
        let target_cv = ConcreteValue::Val(Value::from(target_int));
        if domain.len() > 1 || !domain.contains(&target_cv) {
            let initial_len = domain.len();
            domain.retain(|cv| cv == &target_cv);
            if domain.is_empty() {
                warn!(
                    "Pruning: prune_domain_to_single_int for WC '{}' (target {}) emptied domain. Initial size: {}.",
                    wildcard.name, target_int, initial_len
                );
                return Err(ProverError::Unsatisfiable(format!(
                    "Dynamic pruning (arithmetic) emptied domain for {}",
                    wildcard.name
                )));
            }
            if domain.len() < initial_len {
                debug!(
                    "    Pruning (single_int): WC '{}' domain reduced from {} to {} (target {}).",
                    wildcard.name,
                    initial_len,
                    domain.len(),
                    target_int
                );
                return Ok(true);
            }
        }
    }
    debug!(
        "  Pruning (single_int): WC '{}' domain already '{}' or no change needed.",
        wildcard.name, target_int
    );
    Ok(false)
}

/// Prunes integer domains based on Gt/Lt constraints.
fn prune_gt_lt_values(
    domains: &mut HashMap<Wildcard, (Domain, ExpectedType)>,
    wc1: &Wildcard,
    wc2: &Wildcard,
    predicate: NativePredicate, // Gt or Lt
) -> Result<bool, ProverError> {
    let mut changed = false;
    debug!(
        "Pruning: prune_gt_lt_values for {:?}. WC1: '{}', WC2: '{}'.",
        predicate, wc1.name, wc2.name
    );

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
    debug!(
        "  Pruning (Gt/Lt): Min/Max values: d1_min: {:?}, d1_max: {:?}, d2_min: {:?}, d2_max: {:?}.",
        min_d1_opt, max_d1_opt, min_d2_opt, max_d2_opt
    );

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
                        TypedValue::Int(v1) => *v1 > min_d2,
                        _ => true,
                    },
                    _ => true,
                });
            } else {
                domain1_mut.retain(|cv| match cv {
                    ConcreteValue::Val(v) => match v.typed() {
                        TypedValue::Int(v1) => *v1 < max_d2,
                        _ => true,
                    },
                    _ => true,
                });
            }
            if domain1_mut.is_empty() {
                warn!(
                    "Pruning: prune_gt_lt_values for {:?} emptied domain for WC '{}'. Pred: {:?}. Initial len: {}. Bounds: d1({:?}-{:?}), d2({:?}-{:?})",
                    predicate, wc1.name, predicate, initial_len1, min_d1_opt, max_d1_opt, min_d2_opt, max_d2_opt
                );
                return Err(ProverError::Unsatisfiable(format!(
                    "Dynamic pruning (Gt/Lt values) emptied domain for {}",
                    wc1.name
                )));
            }
            if domain1_mut.len() < initial_len1 {
                debug!(
                    "    Pruning (Gt/Lt): WC '{}' domain reduced from {} to {} by {:?}.",
                    wc1.name,
                    initial_len1,
                    domain1_mut.len(),
                    predicate
                );
                changed = true;
            }
        }

        // Prune domain2
        if let Some((domain2_mut, _)) = domains.get_mut(wc2) {
            let initial_len2 = domain2_mut.len();
            if predicate == NativePredicate::Gt {
                domain2_mut.retain(|cv| match cv {
                    ConcreteValue::Val(v) => match v.typed() {
                        TypedValue::Int(v2) => *v2 < max_d1,
                        _ => true,
                    },
                    _ => true,
                });
            } else {
                domain2_mut.retain(|cv| match cv {
                    ConcreteValue::Val(v) => match v.typed() {
                        TypedValue::Int(v2) => *v2 > min_d1,
                        _ => true,
                    },
                    _ => true,
                });
            }
            if domain2_mut.is_empty() {
                warn!(
                    "Pruning: prune_gt_lt_values for {:?} emptied domain for WC '{}'. Pred: {:?}. Initial len: {}. Bounds: d1({:?}-{:?}), d2({:?}-{:?})",
                    predicate, wc2.name, predicate, initial_len2, min_d1_opt, max_d1_opt, min_d2_opt, max_d2_opt
                );
                return Err(ProverError::Unsatisfiable(format!(
                    "Dynamic pruning (Gt/Lt values) emptied domain for {}",
                    wc2.name
                )));
            }
            if domain2_mut.len() < initial_len2 {
                debug!(
                    "    Pruning (Gt/Lt): WC '{}' domain reduced from {} to {} by {:?}.",
                    wc2.name,
                    initial_len2,
                    domain2_mut.len(),
                    predicate
                );
                changed = true;
            }
        }
    }
    debug!(
        "Pruning: prune_gt_lt_values for {:?} complete. Changed: {}",
        predicate, changed
    );

    Ok(changed)
}

/// Prunes a domain of potential keys (Values representing key names) based on
/// whether they exist (or not) in a specific container.
fn prune_domain_by_container_existence(
    domain: &mut Domain,
    container: &Value,
    keep_existing: bool, // true for Contains, false for NotContains
) -> Result<bool, ProverError> {
    let initial_len = domain.len();
    debug!(
        "  Pruning (domain_by_container_existence): Container: {:?}, Keep existing: {}. Initial domain len: {}",
        container, keep_existing, initial_len
    );
    domain.retain(|cv| match cv {
        // Match on ConcreteValue::Val, as the key is represented as a Value
        ConcreteValue::Val(key_value) => {
            // Use the key_value directly for the existence check
            match container.prove_existence(key_value) {
                // Pass &Value directly
                Ok(_) => keep_existing, // Key exists, keep if keep_existing is true
                Err(_) => !keep_existing, // Key doesn't exist, keep if keep_existing is false
            }
        }
        _ => true, // Retain other types (e.g., Key, Pod) - though domain should only have Val
    });
    if domain.is_empty() {
        warn!(
            "Pruning: domain_by_container_existence for container {:?} (keep_existing: {}) emptied domain. Initial len: {}.",
            container, keep_existing, initial_len
        );
        return Err(ProverError::Unsatisfiable(
            "Dynamic pruning (Contains/NotContains Key) emptied domain".to_string(),
        ));
    }
    debug!(
        "    Pruning (domain_by_container_existence): Final domain len: {}. Changed: {}",
        domain.len(),
        domain.len() < initial_len
    );
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
    debug!(
        "  Pruning (domain_by_container_value_existence): Container: {:?}, Keep existing: {}. Initial domain len: {}",
        container, keep_existing, initial_len
    );
    let existing_values: HashSet<Value> = match container.typed() {
        TypedValue::Array(a) => a.array().iter().cloned().collect(),
        TypedValue::Set(s) => s.set().iter().cloned().collect(),
        TypedValue::Dictionary(d) => d.kvs().values().cloned().collect(),
        _ => HashSet::new(),
    };
    debug!("    Existing values in container: {:?}", existing_values);

    domain.retain(|cv| match cv {
        ConcreteValue::Val(value) => {
            let value_exists = existing_values.contains(value);
            (value_exists && keep_existing) || (!value_exists && !keep_existing)
        }
        _ => true, // Retain non-Value types
    });
    if domain.is_empty() {
        warn!(
            "Pruning: domain_by_container_value_existence for container {:?} (keep_existing: {}) emptied domain. Initial len: {}.",
            container, keep_existing, initial_len
        );
        return Err(ProverError::Unsatisfiable(
            "Dynamic pruning (Contains/NotContains Value) emptied domain".to_string(),
        ));
    }
    debug!(
        "    Pruning (domain_by_container_value_existence): Final domain len: {}. Changed: {}",
        domain.len(),
        domain.len() < initial_len
    );
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
    debug!(
        "  Pruning (container_domain_by_key_existence): Key: {:?}, Keep containing: {}. Initial domain len: {}",
        key, keep_containing, initial_len
    );
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
        warn!(
            "Pruning: container_domain_by_key_existence for key {:?} (keep_containing: {}) emptied domain. Initial len: {}.",
            key, keep_containing, initial_len
        );
        return Err(ProverError::Unsatisfiable(
            "Dynamic pruning (Contains/NotContains Container by Key) emptied domain".to_string(),
        ));
    }
    debug!(
        "    Pruning (container_domain_by_key_existence): Final domain len: {}. Changed: {}",
        domain.len(),
        domain.len() < initial_len
    );
    Ok(domain.len() < initial_len)
}

/// Prunes a domain of potential container Values based on whether they contain
/// (or do not contain) a specific value among their elements.
fn prune_container_domain_by_value_existence(
    domain: &mut Domain,
    value: &Value,
    keep_containing: bool, // true for Contains
) -> Result<bool, ProverError> {
    debug!(
        "  Pruning (container_domain_by_value_existence): Value: {:?}, Keep containing: {}. Initial domain len: {}",
        value, keep_containing, domain.len()
    );
    if !keep_containing {
        // Pruning containers that *don't* contain a specific value is complex and less useful.
        // Only implement the `keep_containing = true` case for Contains.
        warn!("Pruning container domain by non-existence of value is not implemented.");
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
        warn!(
            "Pruning: container_domain_by_value_existence for value {:?} (keep_containing: {}) emptied domain. Initial len: {}.",
            value, keep_containing, initial_len
        );
        return Err(ProverError::Unsatisfiable(
            "Dynamic pruning (Contains Container by Value) emptied domain".to_string(),
        ));
    }
    debug!(
        "    Pruning (container_domain_by_value_existence): Final domain len: {}. Changed: {}",
        domain.len(),
        domain.len() < initial_len
    );
    Ok(domain.len() < initial_len)
}
