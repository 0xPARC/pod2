use std::collections::{HashMap, HashSet};

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
    let mut changed = false;
    for (wildcard, (domain, expected_type_ref)) in state.domains.iter_mut() {
        let expected_type = *expected_type_ref;
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
            return Err(ProverError::Unsatisfiable(format!(
                "Type pruning made domain for wildcard '{}' empty (expected {:?})",
                wildcard.name, expected_type
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
    constraints: &[Constraint],
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
                if *expected_type != ExpectedType::Pod {
                    continue; // Should have been caught by prune_by_type, but check defensively
                }

                let initial_size = domain.len();

                // Find PodIds that have this literal_key
                let middleware_key = Key::new(literal_key.clone());
                let allowed_pod_ids: HashSet<PodId> = indexes
                    .get_anchored_keys_for_key(&middleware_key)
                    .map(|anchored_keys| anchored_keys.iter().map(|ak| ak.pod_id).collect())
                    .unwrap_or_default();

                domain.retain(|value| match value {
                    ConcreteValue::Pod(pod_id) => allowed_pod_ids.contains(pod_id),
                    _ => false,
                });

                if domain.is_empty() {
                    return Err(ProverError::Unsatisfiable(format!(
                        "LiteralKey constraint ('{}[{}]') made domain empty",
                        pod_wildcard.name, literal_key
                    )));
                }

                if domain.len() < initial_size {
                    changed = true;
                }
            } else {
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
            if let Some((domain, expected_type)) = state.domains.get_mut(key_wildcard) {
                if *expected_type != ExpectedType::Key {
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

                if domain.is_empty() {
                    return Err(ProverError::Unsatisfiable(format!(
                        "LiteralOrigin constraint ('{}[?{}]') made domain empty",
                        literal_pod_id, key_wildcard.name
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
    _indexes: &ProverIndexes,
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
                if *expected_type != ExpectedType::Val {
                    continue;
                }

                let initial_size = domain.len();

                domain.retain(|value| match value {
                    ConcreteValue::Val(v) => v == literal_value,
                    _ => false,
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

/// Applies wildcard origin constraints (?A[?K]), removing Keys from ?K's domain
/// if ?A's domain becomes a singleton PodId and the Key doesn't exist in that Pod.
/// Returns Ok(true) if any domain changed, Ok(false) otherwise.
pub fn prune_by_wildcard_origin(
    state: &mut SolverState,
    indexes: &ProverIndexes,
    constraints: &[Constraint],
) -> Result<bool, ProverError> {
    let mut changed = false;

    for constraint in constraints {
        if let Constraint::WildcardOrigin {
            key_wildcard,
            pod_wildcard,
        } = constraint
        {
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

                    if key_domain.is_empty() {
                        return Err(ProverError::Unsatisfiable(format!(
                            "WildcardOrigin constraint (pod='{}', key='{}') made key domain empty",
                            pod_wildcard.name, key_wildcard.name
                        )));
                    }

                    if key_domain.len() < initial_size {
                        changed = true;
                    }
                }
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
    equality_pairs: &[(Wildcard, Wildcard)],
    inequality_pairs: &[(Wildcard, Wildcard)],
) -> Result<bool, ProverError> {
    let mut overall_changed = false;
    let mut changed_this_pass = true;
    let mut processed_type_pruning = false;

    while changed_this_pass {
        changed_this_pass = false;

        // Apply type constraints first
        if !processed_type_pruning && prune_by_type(state)? {
            changed_this_pass = true;
            overall_changed = true;
            processed_type_pruning = true;
        }

        let current_constraints = state.constraints.clone();

        // Apply explicit constraints
        for constraint in &current_constraints {
            let mut constraint_changed = false;
            match constraint {
                Constraint::LiteralKey { .. } => {
                    constraint_changed =
                        prune_by_literal_key(state, indexes, &[constraint.clone()])?;
                }
                Constraint::LiteralOrigin { .. } => {
                    constraint_changed =
                        prune_by_literal_origin(state, indexes, &[constraint.clone()])?;
                }
                Constraint::WildcardOrigin { .. } => {
                    constraint_changed =
                        prune_by_wildcard_origin(state, indexes, &[constraint.clone()])?;
                }
                Constraint::LiteralValue { .. } => {
                    constraint_changed =
                        prune_by_literal_value(state, indexes, &[constraint.clone()])?;
                }
                _ => {}
            };

            if constraint_changed {
                changed_this_pass = true;
                overall_changed = true;
            }
        }

        // Apply implicit equality constraints
        for (wc1, wc2) in equality_pairs {
            if propagate_or_intersect(&mut state.domains, wc1, wc2)? {
                changed_this_pass = true;
                overall_changed = true;
            }
        }

        // Apply implicit inequality constraints
        for (wc1, wc2) in inequality_pairs {
            if remove_singleton(&mut state.domains, wc1, wc2)? {
                changed_this_pass = true;
                overall_changed = true;
            }
            if remove_singleton(&mut state.domains, wc2, wc1)? {
                changed_this_pass = true;
                overall_changed = true;
            }
        }

        if changed_this_pass {
            processed_type_pruning = false;
        }
    }
    Ok(overall_changed)
}

/// Applies pruning logic directly based on a newly proven statement and its associated bindings.
/// Returns Ok(true) if any domain changed, Ok(false) otherwise.
pub(super) fn prune_domains_after_proof(
    state: &mut SolverState,
    proven_template: &StatementTmpl,
    _proven_statement: &Statement,
    bindings: &HashMap<Wildcard, ConcreteValue>,
    _indexes: &ProverIndexes,
) -> Result<bool, ProverError> {
    let mut changed = false;

    match proven_template.pred {
        Predicate::Native(NativePredicate::Equal) => {
            if proven_template.args.len() == 2 {
                let wildcards1 = get_wildcards_from_tmpl_arg(&proven_template.args[0]);
                let wildcards2 = get_wildcards_from_tmpl_arg(&proven_template.args[1]);

                for wc1_pod in &wildcards1.pod_wcs {
                    for wc2_pod in &wildcards2.pod_wcs {
                        changed |= propagate_or_intersect(&mut state.domains, wc1_pod, wc2_pod)?;
                    }
                }
                for wc1_key in &wildcards1.key_wcs {
                    for wc2_key in &wildcards2.key_wcs {
                        changed |= propagate_or_intersect(&mut state.domains, wc1_key, wc2_key)?;
                    }
                }
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
            println!("Warning: Dynamic pruning for Custom predicates not yet implemented.");
        }
        _ => {}
    }

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
    if !domains.contains_key(wc1) || !domains.contains_key(wc2) {
        return Ok(false);
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
            changed = true;
        }
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
    if !domains.contains_key(wc_singleton) || !domains.contains_key(wc_target) {
        return Ok(false);
    }
    if domains[wc_singleton].0.len() == 1 && !domains[wc_target].0.is_empty() {
        let val_to_remove = domains[wc_singleton].0.iter().next().unwrap().clone();
        let (target_domain_mut, _) = domains.get_mut(wc_target).unwrap();
        let initial_len = target_domain_mut.len();
        target_domain_mut.remove(&val_to_remove);
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

/// Prunes a domain of potential keys (Values representing key names) based on
/// whether they exist (or not) in a specific container.
fn prune_domain_by_container_existence(
    domain: &mut Domain,
    container: &Value,
    keep_existing: bool, // true for Contains, false for NotContains
) -> Result<bool, ProverError> {
    let initial_len = domain.len();
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

#[cfg(test)]
mod tests {
    use std::collections::HashSet;

    use super::*;
    use crate::{
        middleware::{self, Key, PodId},
        prover::solver::tests::{ak, cv_key, cv_pod, pod, solver_state_with_domains, val, wc},
    };

    // Helper to create ProverIndexes with specific base facts
    fn setup_indexes_with_facts(facts: Vec<(PodId, Statement)>) -> ProverIndexes {
        let params = middleware::Params::default();
        ProverIndexes::build(params, &facts)
    }

    #[test]
    fn test_prune_wildcard_origin_interaction() {
        let w_pod = wc("A", 0);
        let w_key = wc("K", 0);
        let p1 = pod(1);
        let p2 = pod(2);
        let k_foo = Key::new("foo".to_string());

        // Facts: p1 has keys "foo", "bar". p2 has key "baz".
        let facts = vec![
            (p1, Statement::ValueOf(ak(1, "foo"), val(10))),
            (p1, Statement::ValueOf(ak(1, "bar"), val(20))),
            (p2, Statement::ValueOf(ak(2, "baz"), val(30))),
        ];
        let indexes = setup_indexes_with_facts(facts);

        // Initial state: ?A={p1, p2}, ?K={"foo", "bar", "baz"}
        let mut state = solver_state_with_domains(vec![
            (
                w_pod.clone(),
                HashSet::from([cv_pod(1), cv_pod(2)]),
                ExpectedType::Pod,
            ),
            (
                w_key.clone(),
                HashSet::from([cv_key("foo"), cv_key("bar"), cv_key("baz")]),
                ExpectedType::Key,
            ),
        ]);

        // Constraints:
        // 1. ?A[?K] (WildcardOrigin)
        // 2. ?A["foo"] (LiteralKey, will prune ?A to p1)
        state.constraints = vec![
            Constraint::WildcardOrigin {
                key_wildcard: w_key.clone(),
                pod_wildcard: w_pod.clone(),
            },
            Constraint::LiteralKey {
                pod_wildcard: w_pod.clone(),
                literal_key: k_foo.name().to_string(),
            },
        ];

        // Run the full initial pruning loop
        let changed = prune_initial_domains(&mut state, &indexes, &[], &[]).unwrap();

        assert!(changed, "Domains should have changed");

        // Check final domains:
        // ?A should be pruned to p1 by LiteralKey
        assert_eq!(state.domains[&w_pod].0, HashSet::from([cv_pod(1)]));
        // ?K should be pruned to {"foo", "bar"} by WildcardOrigin (triggered after ?A became singleton p1)
        assert_eq!(
            state.domains[&w_key].0,
            HashSet::from([cv_key("foo"), cv_key("bar")])
        );
    }
}
