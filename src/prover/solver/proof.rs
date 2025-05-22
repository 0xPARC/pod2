use std::collections::{HashMap, HashSet};

use log::{debug, error, info, trace, warn};

use super::{
    types::{
        ExpectedType, GlobalContext, MemoizationKey, MemoizedProofOutcome, WildcardInterpretation,
    },
    SolverState,
};
use crate::{
    middleware::{
        statement::WildcardValue, CustomPredicateRef, KeyOrWildcard, NativeOperation,
        NativePredicate, OperationType, Predicate, Statement, StatementTmplArg, ToFields,
        TypedValue, Wildcard, SELF,
    },
    prover::{
        error::ProverError,
        types::{ConcreteValue, ProofChain, ProofStep},
    },
};

const MAX_CUSTOM_PREDICATE_RECURSION_DEPTH: usize = 20; // Max recursion for a single custom predicate chain

/// Attempts to find or generate a proof chain for a given target statement.
/// If successful, updates the solver state (proof_chains, scope) and returns the chain.
pub(super) fn try_prove_statement(
    state: &mut SolverState,
    target: &Statement,
    global_context: &GlobalContext<'_>,
    current_depth: usize,
) -> Result<ProofChain, ProverError> {
    debug!(
        "try_prove_statement (depth {}): Entered. Current state WC domains: {:?}.",
        current_depth,
        state
            .domains
            .iter()
            .map(|(wc, (d, t))| (wc.name.clone(), d.len(), t))
            .collect::<Vec<_>>()
    );

    if current_depth > MAX_CUSTOM_PREDICATE_RECURSION_DEPTH {
        warn!(
            "try_prove_statement (depth {}) reached MAX_CUSTOM_PREDICATE_RECURSION_DEPTH ({}).",
            current_depth, MAX_CUSTOM_PREDICATE_RECURSION_DEPTH
        );
        return Err(ProverError::MaxDepthExceeded(format!(
            "Max recursion depth ({}) exceeded while proving {:?}",
            MAX_CUSTOM_PREDICATE_RECURSION_DEPTH, target
        )));
    }

    if let Some(existing_chain) = state.proof_chains.get(target) {
        return Ok(existing_chain.clone());
    }

    if let Statement::ValueOf(target_ak, target_value) = target {
        // Check global potential constants first (these are from top-level REQUEST or scanned from all defs)
        if let Some((_holder_wc, const_key, _value)) = global_context
            .potential_constant_info
            .iter()
            .find(|(_, k, v)| k == &target_ak.key && v == target_value)
        {
            // This check implicitly assumes that if a global constant matches key and value,
            // and the target is ValueOf(SELF[key], value), it's a valid derivation.
            // This relies on the fact that global constants are treated as SELF facts.
            if target_ak.pod_id == SELF && const_key == &target_ak.key {
                // Ensure the key also matches
                let proof_step = ProofStep {
                    operation: OperationType::Native(NativeOperation::NewEntry), // Or CopyStatement if already in initial_facts by other means
                    inputs: vec![], // For NewEntry based on constant definition
                    output: target.clone(),
                };
                let proof_chain = ProofChain(vec![proof_step]);
                // state.proof_chains.insert(target.clone(), proof_chain.clone()); // Caller handles insertion
                return Ok(proof_chain);
            }
        }

        // Check local potential constants (these are from ValueOf templates within the current custom predicate's body)
        if target_ak.pod_id == SELF {
            // Only try to prove SELF facts this way
            for (local_wc_holder, local_key, local_value) in &state.local_potential_constant_info {
                if local_key == &target_ak.key && local_value == target_value {
                    // Now check if local_wc_holder is resolved to SELF in the current state.domains
                    if let Some((domain, _)) = state.domains.get(local_wc_holder) {
                        if domain.len() == 1 {
                            if let Some(ConcreteValue::Pod(pod_id)) = domain.iter().next() {
                                if *pod_id == SELF {
                                    // The wildcard holding the constant in the custom predicate's ValueOf template
                                    // is currently resolved to SELF. So, this locally defined constant
                                    // can prove the target ValueOf(SELF[...], ...).
                                    let proof_step = ProofStep {
                                        operation: OperationType::Native(NativeOperation::NewEntry),
                                        inputs: vec![],
                                        output: target.clone(),
                                    };
                                    let proof_chain = ProofChain(vec![proof_step]);
                                    return Ok(proof_chain);
                                }
                            }
                        }
                    }
                }
            }
        }
    }
    // Fallback: Check if the statement is a direct base fact from initial_facts (handled by caller in main try_prove_statement)
    // This function try_prove_value_of_statement is more about proving ValueOf from constant definitions.

    let base_fact = global_context
        .indexes
        .exact_statement_lookup
        .iter()
        .find(|(_pod_id, stmt)| stmt == target);

    if let Some((origin_pod_id, base_middleware_statement)) = base_fact {
        let base_statement_for_step = base_middleware_statement.clone();
        let operation = OperationType::Native(NativeOperation::CopyStatement);
        let proof_step = ProofStep {
            operation,
            inputs: vec![base_statement_for_step.clone()],
            output: target.clone(),
        };
        let proof_chain = ProofChain(vec![proof_step]);
        state
            .scope
            .insert((*origin_pod_id, base_statement_for_step));
        state
            .proof_chains
            .insert(target.clone(), proof_chain.clone());
        return Ok(proof_chain);
    }

    // --- Memoization Cache Key Calculation --- START ---
    let memo_key = match target {
        Statement::Custom(custom_ref, args) => {
            let predicate_variant = Predicate::Custom(custom_ref.clone());
            MemoizationKey::Custom {
                predicate_ref_id: predicate_variant.to_fields(global_context.params),
                args: args.clone(),
            }
        }
        native_stmt => MemoizationKey::Native(native_stmt.clone()),
    };
    // --- Memoization Cache Key Calculation --- END ---

    // --- Memoization Cache Check --- START ---
    if let Some(cached_outcome) = state.memoization_cache.get(&memo_key) {
        match cached_outcome {
            MemoizedProofOutcome::Success(chain, scope_fragment) => {
                state.scope.extend(scope_fragment.iter().cloned());
                return Ok(chain.clone());
            }
            MemoizedProofOutcome::Failure(err) => {
                return Err(err.clone());
            }
        }
    }
    // --- Memoization Cache Check --- END ---

    // --- Main Proof Logic (executed on cache miss) --- START ---
    let result: Result<ProofChain, ProverError> = match target.predicate() {
        Predicate::Native(native_pred) => match native_pred {
            NativePredicate::ValueOf => try_prove_value_of_statement(target, global_context),
            NativePredicate::Equal => {
                try_prove_equal_statement(state, target, global_context, current_depth)
            }
            NativePredicate::NotEqual => {
                try_prove_not_equal_statement(state, target, global_context, current_depth)
            }
            NativePredicate::Lt => try_prove_lt_statement(target, global_context),
            NativePredicate::SumOf => try_prove_sum_of_statement(target, global_context),
            NativePredicate::ProductOf => try_prove_product_of_statement(target, global_context),
            NativePredicate::Contains => try_prove_contains_statement(target, global_context),
            NativePredicate::NotContains => {
                try_prove_not_contains_statement(target, global_context)
            }
            NativePredicate::MaxOf => try_prove_max_of_statement(target, global_context),
            NativePredicate::HashOf => try_prove_hash_of_statement(target, global_context),
            NativePredicate::LtEq => try_prove_lt_eq_statement(target, global_context),
            _ => Err(ProverError::NotImplemented(format!(
                "Proof logic for native predicate {:?} in target {:?}",
                native_pred, target
            ))),
        },
        Predicate::Custom(custom_ref) => {
            // The existing try_prove_custom_predicate_statement_internal is complex and has its own depth tracking.
            // It also updates state.proof_chains and state.scope directly for sub-proofs.
            try_prove_custom_predicate_statement_internal(
                state,
                target,
                &custom_ref,
                global_context,
                current_depth,
            )
        }
        Predicate::BatchSelf(_) => Err(ProverError::Internal(
            "BatchSelf should have been resolved to Custom before proof attempt".to_string(),
        )),
    };
    // --- Main Proof Logic --- END ---

    // --- Memoization Cache Update --- START ---
    match &result {
        Ok(chain) => {
            let mut temp_fragment_scope = HashSet::new();
            chain.collect_scope(
                &mut temp_fragment_scope,
                &state.proof_chains,
                &global_context.indexes.exact_statement_lookup,
            );
            state.memoization_cache.insert(
                memo_key,
                MemoizedProofOutcome::Success(chain.clone(), temp_fragment_scope),
            );
        }
        Err(e) => match e {
            ProverError::Unsatisfiable(_)
            | ProverError::MaxDepthExceeded(_)
            | ProverError::Internal(_)
            | ProverError::NotImplemented(_) => {
                state
                    .memoization_cache
                    .insert(memo_key, MemoizedProofOutcome::Failure(e.clone()));
            }
            _ => {}
        },
    }
    // --- Memoization Cache Update --- END ---

    result
}

/// Tries to prove a ValueOf statement. This involves checking if the statement
/// already exists as a base fact.
fn try_prove_value_of_statement(
    target: &Statement,
    global_context: &GlobalContext<'_>,
) -> Result<ProofChain, ProverError> {
    trace!("Attempting to prove ValueOf: {:?}", target);
    if let Statement::ValueOf(ak, expected_value) = target {
        // Case 1: ValueOf is directly in initial_facts or from SELF constants
        if global_context
            .indexes
            .contains_exact_statement(&ak.pod_id, target)
            || (ak.pod_id == SELF
                && global_context
                    .potential_constant_info
                    .iter()
                    .any(|(_, k, v)| k == &ak.key && v == expected_value))
        {
            let operation = OperationType::Native(NativeOperation::CopyStatement); // Or NewEntry if it's a SELF const not in initial_facts
            let proof_step = ProofStep {
                operation,
                inputs: vec![target.clone()], // CopyStatement takes the statement itself as input for tracking
                output: target.clone(),
            };
            let chain = ProofChain(vec![proof_step]);
            // Scope is managed by the caller of try_prove_statement or by cache logic for base facts
            return Ok(chain);
        }
        // Case 2: Check if the value can be derived (e.g. from another ValueOf if keys are equal via DSU)
        // This might be too complex for a direct ValueOf proof here unless it's a CopyStatement.
        // ValueOf statements are usually base facts or proven via NewEntry.
    }
    Err(ProverError::Unsatisfiable(format!(
        "Could not prove ValueOf: {:?}",
        target
    )))
}

// Placeholder for try_prove_equal_statement (and others)
// These would contain the original logic for proving each statement type
fn try_prove_equal_statement(
    state: &mut SolverState,
    target: &Statement,
    global_context: &GlobalContext<'_>,
    current_depth: usize,
) -> Result<ProofChain, ProverError> {
    // Original logic for proving Equal statements...
    // This will involve checking DSU, value_map, and potentially recursive calls for TransitiveEq
    if let Statement::Equal(ak1, ak2) = target {
        // 1. Check direct value equality from ValueOf entries
        if let (Some(v1), Some(v2)) = (
            global_context.indexes.get_value(ak1),
            global_context.indexes.get_value(ak2),
        ) {
            if v1 == v2 {
                let input1 = Statement::ValueOf(ak1.clone(), v1.clone());
                let input2 = Statement::ValueOf(ak2.clone(), v2.clone());
                if global_context
                    .indexes
                    .get_exact_statement(&ak1.pod_id, &input1)
                    && global_context
                        .indexes
                        .get_exact_statement(&ak2.pod_id, &input2)
                {
                    let operation = OperationType::Native(NativeOperation::EqualFromEntries);
                    let proof_step = ProofStep {
                        operation,
                        inputs: vec![input1, input2],
                        output: target.clone(),
                    };
                    return Ok(ProofChain(vec![proof_step]));
                }
            }
        }
        // 2. Check DSU for existing equality (potentially from other Equal statements)
        if global_context.indexes.are_equal(ak1, ak2) {
            // If DSU says they are equal, and it's not from direct value check, it implies a path exists.
            // Try to find a path via TransitiveEqualFromStatements or CopyStatement if target itself is a base fact.
            if global_context
                .indexes
                .get_exact_statement(&ak1.pod_id, target)
                || global_context
                    .indexes
                    .get_exact_statement(&ak2.pod_id, target)
            {
                // Crude check for pod_id
                let operation = OperationType::Native(NativeOperation::CopyStatement);
                let proof_step = ProofStep {
                    operation,
                    inputs: vec![target.clone()],
                    output: target.clone(),
                };
                return Ok(ProofChain(vec![proof_step]));
            }
            // Simplified: if DSU says equal, assume a transitive path can be built or copied.
            // A full implementation would search for the actual intermediate Equal statements.
            // For now, if DSU says yes, and it's not from entries, let's try to find a path via a middle term.
            // This is a very simplified transitive search placeholder.
            for common_key_id in 0..global_context.indexes.id_to_key.len() {
                let ak_mid = &global_context.indexes.id_to_key[common_key_id];
                if ak_mid == ak1 || ak_mid == ak2 {
                    continue;
                }

                let stmt1_mid = Statement::Equal(ak1.clone(), ak_mid.clone());
                let stmt_mid_2 = Statement::Equal(ak_mid.clone(), ak2.clone());

                if let Ok(chain1) =
                    try_prove_statement(state, &stmt1_mid, global_context, current_depth + 1)
                {
                    if let Ok(chain2) =
                        try_prove_statement(state, &stmt_mid_2, global_context, current_depth + 1)
                    {
                        let mut steps = chain1.0;
                        steps.extend(chain2.0);
                        steps.push(ProofStep {
                            operation: OperationType::Native(
                                NativeOperation::TransitiveEqualFromStatements,
                            ),
                            inputs: vec![stmt1_mid, stmt_mid_2],
                            output: target.clone(),
                        });
                        return Ok(ProofChain(steps));
                    }
                }
            }
        }
    }
    Err(ProverError::Unsatisfiable("Cannot prove Equal".to_string()))
}

fn try_prove_not_equal_statement(
    state: &mut SolverState,
    target: &Statement,
    global_context: &GlobalContext<'_>,
    current_depth: usize,
) -> Result<ProofChain, ProverError> {
    if let Statement::NotEqual(ak1, ak2) = target {
        // 1. From different values in ValueOf entries
        if let (Some(v1), Some(v2)) = (
            global_context.indexes.get_value(ak1),
            global_context.indexes.get_value(ak2),
        ) {
            if v1 != v2 {
                let input1 = Statement::ValueOf(ak1.clone(), v1.clone());
                let input2 = Statement::ValueOf(ak2.clone(), v2.clone());
                if global_context
                    .indexes
                    .get_exact_statement(&ak1.pod_id, &input1)
                    && global_context
                        .indexes
                        .get_exact_statement(&ak2.pod_id, &input2)
                {
                    let operation = OperationType::Native(NativeOperation::NotEqualFromEntries);
                    let proof_step = ProofStep {
                        operation,
                        inputs: vec![input1, input2],
                        output: target.clone(),
                    };
                    return Ok(ProofChain(vec![proof_step]));
                }
            }
        }
        // 2. From Gt or Lt statements
        let stmt_lt1 = Statement::Lt(ak1.clone(), ak2.clone());
        if let Ok(chain_lt1) =
            try_prove_statement(state, &stmt_lt1, global_context, current_depth + 1)
        {
            let mut steps = chain_lt1.0;
            steps.push(ProofStep {
                operation: OperationType::Native(NativeOperation::LtToNotEqual),
                inputs: vec![stmt_lt1],
                output: target.clone(),
            });
            return Ok(ProofChain(steps));
        }
        let stmt_lt2 = Statement::Lt(ak2.clone(), ak1.clone());
        if let Ok(chain_lt2) =
            try_prove_statement(state, &stmt_lt2, global_context, current_depth + 1)
        {
            let mut steps = chain_lt2.0;
            steps.push(ProofStep {
                operation: OperationType::Native(NativeOperation::LtToNotEqual),
                inputs: vec![stmt_lt2],
                output: target.clone(),
            });
            return Ok(ProofChain(steps));
        }
        // 3. From explicit NotEqual in indexes (CopyStatement)
        if global_context.indexes.are_not_equal(ak1, ak2)
            && (global_context
                .indexes
                .get_exact_statement(&ak1.pod_id, target)
                || global_context
                    .indexes
                    .get_exact_statement(&ak2.pod_id, target))
        {
            let operation = OperationType::Native(NativeOperation::CopyStatement);
            let proof_step = ProofStep {
                operation,
                inputs: vec![target.clone()],
                output: target.clone(),
            };
            return Ok(ProofChain(vec![proof_step]));
        }
    }
    Err(ProverError::Unsatisfiable(
        "Cannot prove NotEqual".to_string(),
    ))
}

/// Tries to prove a LessThan statement.
fn try_prove_lt_statement(
    target: &Statement,
    global_context: &GlobalContext<'_>,
) -> Result<ProofChain, ProverError> {
    trace!("Attempting to prove Lt: {:?}", target);
    if let Statement::Lt(ak1, ak2) = target {
        if let (Some(TypedValue::Int(v1)), Some(TypedValue::Int(v2))) = (
            global_context.indexes.get_value(ak1).map(|v| v.typed()),
            global_context.indexes.get_value(ak2).map(|v| v.typed()),
        ) {
            if v1 < v2 {
                let val1 = global_context.indexes.get_value(ak1).unwrap().clone();
                let val2 = global_context.indexes.get_value(ak2).unwrap().clone();
                let input1 = Statement::ValueOf(ak1.clone(), val1);
                let input2 = Statement::ValueOf(ak2.clone(), val2);
                if global_context
                    .indexes
                    .get_exact_statement(&ak1.pod_id, &input1)
                    && global_context
                        .indexes
                        .get_exact_statement(&ak2.pod_id, &input2)
                {
                    let operation = OperationType::Native(NativeOperation::LtFromEntries);
                    let proof_step = ProofStep {
                        operation,
                        inputs: vec![input1, input2],
                        output: target.clone(),
                    };
                    return Ok(ProofChain(vec![proof_step]));
                }
            }
        }
    }
    Err(ProverError::Unsatisfiable("Cannot prove Lt".to_string()))
}

/// Tries to prove a SumOf statement. This checks if the values at the anchored keys
/// of the first two arguments sum up to the value at the anchored key of the third argument.
fn try_prove_sum_of_statement(
    target: &Statement,
    global_context: &GlobalContext<'_>,
) -> Result<ProofChain, ProverError> {
    trace!("Attempting to prove SumOf: {:?}", target);
    if let Statement::SumOf(ak_sum, ak_add1, ak_add2) = target {
        if let (
            Some(TypedValue::Int(v_sum)),
            Some(TypedValue::Int(v_add1)),
            Some(TypedValue::Int(v_add2)),
        ) = (
            global_context.indexes.get_value(ak_sum).map(|v| v.typed()),
            global_context.indexes.get_value(ak_add1).map(|v| v.typed()),
            global_context.indexes.get_value(ak_add2).map(|v| v.typed()),
        ) {
            if *v_sum == *v_add1 + *v_add2 {
                let val_sum = global_context.indexes.get_value(ak_sum).unwrap().clone();
                let val_add1 = global_context.indexes.get_value(ak_add1).unwrap().clone();
                let val_add2 = global_context.indexes.get_value(ak_add2).unwrap().clone();
                let input_sum = Statement::ValueOf(ak_sum.clone(), val_sum);
                let input_add1 = Statement::ValueOf(ak_add1.clone(), val_add1);
                let input_add2 = Statement::ValueOf(ak_add2.clone(), val_add2);
                if global_context
                    .indexes
                    .get_exact_statement(&ak_sum.pod_id, &input_sum)
                    && global_context
                        .indexes
                        .get_exact_statement(&ak_add1.pod_id, &input_add1)
                    && global_context
                        .indexes
                        .get_exact_statement(&ak_add2.pod_id, &input_add2)
                {
                    let operation = OperationType::Native(NativeOperation::SumOf);
                    let proof_step = ProofStep {
                        operation,
                        inputs: vec![input_sum, input_add1, input_add2],
                        output: target.clone(),
                    };
                    return Ok(ProofChain(vec![proof_step]));
                }
            }
        }
    }
    Err(ProverError::Unsatisfiable("Cannot prove SumOf".to_string()))
}

/// Tries to prove a ProductOf statement. This checks if the values at the anchored keys
/// of the first two arguments multiply to the value at the anchored key of the third argument.
fn try_prove_product_of_statement(
    target: &Statement,
    global_context: &GlobalContext<'_>,
) -> Result<ProofChain, ProverError> {
    trace!("Attempting to prove ProductOf: {:?}", target);
    if let Statement::ProductOf(ak_prod, ak_fac1, ak_fac2) = target {
        if let (
            Some(TypedValue::Int(v_prod)),
            Some(TypedValue::Int(v_fac1)),
            Some(TypedValue::Int(v_fac2)),
        ) = (
            global_context.indexes.get_value(ak_prod).map(|v| v.typed()),
            global_context.indexes.get_value(ak_fac1).map(|v| v.typed()),
            global_context.indexes.get_value(ak_fac2).map(|v| v.typed()),
        ) {
            if *v_prod == *v_fac1 * *v_fac2 {
                let val_prod = global_context.indexes.get_value(ak_prod).unwrap().clone();
                let val_fac1 = global_context.indexes.get_value(ak_fac1).unwrap().clone();
                let val_fac2 = global_context.indexes.get_value(ak_fac2).unwrap().clone();
                let input_prod = Statement::ValueOf(ak_prod.clone(), val_prod);
                let input_fac1 = Statement::ValueOf(ak_fac1.clone(), val_fac1);
                let input_fac2 = Statement::ValueOf(ak_fac2.clone(), val_fac2);
                if global_context
                    .indexes
                    .get_exact_statement(&ak_prod.pod_id, &input_prod)
                    && global_context
                        .indexes
                        .get_exact_statement(&ak_fac1.pod_id, &input_fac1)
                    && global_context
                        .indexes
                        .get_exact_statement(&ak_fac2.pod_id, &input_fac2)
                {
                    let operation = OperationType::Native(NativeOperation::ProductOf);
                    let proof_step = ProofStep {
                        operation,
                        inputs: vec![input_prod, input_fac1, input_fac2],
                        output: target.clone(),
                    };
                    return Ok(ProofChain(vec![proof_step]));
                }
            }
        }
    }
    Err(ProverError::Unsatisfiable(
        "Cannot prove ProductOf".to_string(),
    ))
}

/// Tries to prove a Contains statement. (Currently focused on Dict)
fn try_prove_contains_statement(
    target: &Statement,
    global_context: &GlobalContext<'_>,
) -> Result<ProofChain, ProverError> {
    trace!("Attempting to prove Contains: {:?}", target);
    if let Statement::Contains(ak_container, ak_key, ak_value) = target {
        if let (Some(val_container), Some(val_key), Some(val_value)) = (
            global_context.indexes.get_value(ak_container),
            global_context.indexes.get_value(ak_key),
            global_context.indexes.get_value(ak_value),
        ) {
            if let Ok((proven_value, _merkle_proof)) = val_container.prove_existence(val_key) {
                if *proven_value == *val_value {
                    let input_container =
                        Statement::ValueOf(ak_container.clone(), val_container.clone());
                    let input_key = Statement::ValueOf(ak_key.clone(), val_key.clone());
                    let input_value = Statement::ValueOf(ak_value.clone(), val_value.clone());
                    if global_context
                        .indexes
                        .get_exact_statement(&ak_container.pod_id, &input_container)
                        && global_context
                            .indexes
                            .get_exact_statement(&ak_key.pod_id, &input_key)
                        && global_context
                            .indexes
                            .get_exact_statement(&ak_value.pod_id, &input_value)
                    {
                        let operation = OperationType::Native(NativeOperation::ContainsFromEntries);
                        let proof_step = ProofStep {
                            operation,
                            inputs: vec![input_container, input_key, input_value],
                            output: target.clone(),
                        };
                        return Ok(ProofChain(vec![proof_step]));
                    }
                }
            }
        }
    }
    Err(ProverError::Unsatisfiable(
        "Cannot prove Contains".to_string(),
    ))
}

/// Tries to prove a NotContains statement. (Currently focused on Dict)
fn try_prove_not_contains_statement(
    target: &Statement,
    global_context: &GlobalContext<'_>,
) -> Result<ProofChain, ProverError> {
    trace!("Attempting to prove NotContains: {:?}", target);
    if let Statement::NotContains(ak_container, ak_key) = target {
        if let (Some(val_container), Some(val_key)) = (
            global_context.indexes.get_value(ak_container),
            global_context.indexes.get_value(ak_key),
        ) {
            if val_container.prove_nonexistence(val_key).is_ok() {
                let input_container =
                    Statement::ValueOf(ak_container.clone(), val_container.clone());
                let input_key = Statement::ValueOf(ak_key.clone(), val_key.clone());
                if global_context
                    .indexes
                    .get_exact_statement(&ak_container.pod_id, &input_container)
                    && global_context
                        .indexes
                        .get_exact_statement(&ak_key.pod_id, &input_key)
                {
                    let operation = OperationType::Native(NativeOperation::NotContainsFromEntries);
                    let proof_step = ProofStep {
                        operation,
                        inputs: vec![input_container, input_key],
                        output: target.clone(),
                    };
                    return Ok(ProofChain(vec![proof_step]));
                }
            }
        }
    }
    Err(ProverError::Unsatisfiable(
        "Cannot prove NotContains".to_string(),
    ))
}

/// Tries to prove a MaxOf statement. This checks if the value at the anchored key
/// of the third argument is the maximum of the values at the anchored keys of the
/// first two arguments.
fn try_prove_max_of_statement(
    target: &Statement,
    global_context: &GlobalContext<'_>,
) -> Result<ProofChain, ProverError> {
    trace!("Attempting to prove MaxOf: {:?}", target);
    if let Statement::MaxOf(ak_max, ak_op1, ak_op2) = target {
        if let (
            Some(TypedValue::Int(v_max)),
            Some(TypedValue::Int(v_op1)),
            Some(TypedValue::Int(v_op2)),
        ) = (
            global_context.indexes.get_value(ak_max).map(|v| v.typed()),
            global_context.indexes.get_value(ak_op1).map(|v| v.typed()),
            global_context.indexes.get_value(ak_op2).map(|v| v.typed()),
        ) {
            if v_max == std::cmp::max(v_op1, v_op2) {
                let val_max = global_context.indexes.get_value(ak_max).unwrap().clone();
                let val_op1 = global_context.indexes.get_value(ak_op1).unwrap().clone();
                let val_op2 = global_context.indexes.get_value(ak_op2).unwrap().clone();
                let input_max = Statement::ValueOf(ak_max.clone(), val_max);
                let input_op1 = Statement::ValueOf(ak_op1.clone(), val_op1);
                let input_op2 = Statement::ValueOf(ak_op2.clone(), val_op2);
                if global_context
                    .indexes
                    .get_exact_statement(&ak_max.pod_id, &input_max)
                    && global_context
                        .indexes
                        .get_exact_statement(&ak_op1.pod_id, &input_op1)
                    && global_context
                        .indexes
                        .get_exact_statement(&ak_op2.pod_id, &input_op2)
                {
                    let operation = OperationType::Native(NativeOperation::MaxOf);
                    let proof_step = ProofStep {
                        operation,
                        inputs: vec![input_max, input_op1, input_op2],
                        output: target.clone(),
                    };
                    return Ok(ProofChain(vec![proof_step]));
                }
            }
        }
    }
    Err(ProverError::Unsatisfiable("Cannot prove MaxOf".to_string()))
}

/// Tries to prove a HashOf statement.
fn try_prove_hash_of_statement(
    target: &Statement,
    global_context: &GlobalContext<'_>,
) -> Result<ProofChain, ProverError> {
    trace!("Attempting to prove HashOf: {:?}", target);
    if let Statement::HashOf(ak_hash, ak_preimage1, ak_preimage2) = target {
        if let (Some(val_hash), Some(val_preimage1), Some(val_preimage2)) = (
            global_context.indexes.get_value(ak_hash),
            global_context.indexes.get_value(ak_preimage1),
            global_context.indexes.get_value(ak_preimage2),
        ) {
            // Simplified: Assume if ValueOf for hash and preimages exist, it's provable by a direct operation.
            // let computed_hash_val = Value::hash_concat(&[&val_preimage1, &val_preimage2], &global_context.params); // Updated
            // if val_hash == &computed_hash_val {
            // For now, we'll just check if the ValueOf statements for inputs exist.
            // A real implementation would need to verify the hash computation.
            let input_hash = Statement::ValueOf(ak_hash.clone(), val_hash.clone());
            let input_preimage1 = Statement::ValueOf(ak_preimage1.clone(), val_preimage1.clone());
            let input_preimage2 = Statement::ValueOf(ak_preimage2.clone(), val_preimage2.clone());
            if global_context
                .indexes
                .get_exact_statement(&ak_hash.pod_id, &input_hash)
                && global_context
                    .indexes
                    .get_exact_statement(&ak_preimage1.pod_id, &input_preimage1)
                && global_context
                    .indexes
                    .get_exact_statement(&ak_preimage2.pod_id, &input_preimage2)
            {
                let operation = OperationType::Native(NativeOperation::HashOf); // Assuming a direct HashOf operation exists
                let proof_step = ProofStep {
                    operation,
                    inputs: vec![input_hash, input_preimage1, input_preimage2],
                    output: target.clone(),
                };
                return Ok(ProofChain(vec![proof_step]));
            }
            // }
        }
    }
    Err(ProverError::Unsatisfiable(
        "Cannot prove HashOf (simplified logic)".to_string(),
    ))
}

/// Tries to prove a LessThanOrEqual statement.
fn try_prove_lt_eq_statement(
    _target: &Statement,
    _global_context: &GlobalContext<'_>,
) -> Result<ProofChain, ProverError> {
    // LtEq(A,B) can be Lt(A,B) OR Equal(A,B)
    // Operations LtToLtEq and EqToLtEq are assumed not to exist for now.
    // if let Statement::LtEq(ak1, ak2) = target {
    // Try Lt(A,B)
    // let stmt_lt = Statement::Lt(ak1.clone(), ak2.clone());
    // if let Ok(chain_lt) = try_prove_statement(state, &stmt_lt, global_context, current_depth + 1) {
    // If Lt(A,B) is proven, then LtEq(A,B) is proven via LtToLtEq
    // let mut steps = chain_lt.0;
    // steps.push(ProofStep {
    //     operation: OperationType::Native(NativeOperation::LtToLtEq),
    //     inputs: vec![stmt_lt],
    //     output: target.clone(),
    // });
    // return Ok(ProofChain(steps));
    // }
    // Try Equal(A,B)
    // let stmt_eq = Statement::Equal(ak1.clone(), ak2.clone());
    // if let Ok(chain_eq) = try_prove_statement(state, &stmt_eq, global_context, current_depth + 1) {
    // If Equal(A,B) is proven, then LtEq(A,B) is proven via EqToLtEq
    // let mut steps = chain_eq.0;
    // steps.push(ProofStep {
    //     operation: OperationType::Native(NativeOperation::EqToLtEq),
    //     inputs: vec![stmt_eq],
    //     output: target.clone(),
    // });
    // return Ok(ProofChain(steps));
    // }
    // }
    Err(ProverError::NotImplemented(
        "LtEq proof (LtToLtEq/EqToLtEq operations missing)".to_string(),
    ))
}

fn try_prove_custom_predicate_statement_internal(
    state: &mut SolverState,
    target_custom_statement: &Statement,
    target_custom_ref: &CustomPredicateRef,
    global_context: &GlobalContext<'_>,
    current_depth: usize,
) -> Result<ProofChain, ProverError> {
    let concrete_args_for_log = match target_custom_statement {
        Statement::Custom(_, args) => args.clone(),
        _ => vec![], // Should not happen
    };
    debug!(
        "proof.rs: Attempting to prove Custom Predicate (depth {}): {:?} with concrete args: {:?}",
        current_depth,
        target_custom_statement.predicate(),
        concrete_args_for_log
    );

    if current_depth > MAX_CUSTOM_PREDICATE_RECURSION_DEPTH {
        warn!(
            "proof.rs: Max depth {} reached for custom predicate: {:?}. Aborting.",
            MAX_CUSTOM_PREDICATE_RECURSION_DEPTH, target_custom_statement
        );
        return Err(ProverError::MaxDepthExceeded(format!(
            "Max depth {} reached trying to prove custom predicate: {:?}",
            MAX_CUSTOM_PREDICATE_RECURSION_DEPTH, target_custom_statement
        )));
    }

    if let Some(existing_chain) = state.proof_chains.get(target_custom_statement) {
        return Ok(existing_chain.clone());
    }

    let memo_key = MemoizationKey::Custom {
        predicate_ref_id: Predicate::Custom(target_custom_ref.clone())
            .to_fields(global_context.params),
        args: concrete_args_for_log.clone(),
    };

    // --- Cycle Detection Check ---
    if state.active_custom_calls.contains(&memo_key) {
        return Err(ProverError::MaxDepthExceeded(format!(
            "Cycle detected trying to prove custom predicate: {:?} with key {:?}",
            target_custom_statement, memo_key
        )));
    }

    // --- Memoization Cache Check ---
    if let Some(cached_outcome) = state.memoization_cache.get(&memo_key) {
        return match cached_outcome {
            MemoizedProofOutcome::Success(chain, scope_fragment) => {
                state.scope.extend(scope_fragment.iter().cloned());
                // Potentially merge proof_chains if needed, though top-level try_prove_statement handles its own chains.
                // For custom predicates, the chain is what matters.
                Ok(chain.clone())
            }
            MemoizedProofOutcome::Failure(err) => Err(err.clone()),
        };
    }

    // Add to active calls before diving deeper
    state.active_custom_calls.insert(memo_key.clone());

    let predicate_key =
        Predicate::Custom(target_custom_ref.clone()).to_fields(global_context.params);
    let (custom_pred_def, _batch_arc) = match global_context.custom_definitions.get(&predicate_key)
    {
        Some(def) => def.clone(),
        None => {
            state.active_custom_calls.remove(&memo_key);
            error!(
                "proof.rs: Custom predicate definition not found for ref: {:?} (key: {:?})",
                target_custom_ref, predicate_key
            );
            return Err(ProverError::Internal(format!(
                "Custom predicate definition not found for ref: {:?} (key: {:?})",
                target_custom_ref, predicate_key
            )));
        }
    };

    debug!(
        "proof.rs: Processing Custom Predicate '{}' (depth {}). Conjunction: {}. Args: {:?}",
        custom_pred_def.name, current_depth, custom_pred_def.conjunction, concrete_args_for_log
    );

    // Log if this is eth_dos_distance and arguments match hypothesis
    if custom_pred_def.name == "eth_dos_distance" && concrete_args_for_log.len() >= 6 {
        // Assuming distance_ori is arg 4 (index 4), distance_key is arg 5 (index 5)
        // Need to adjust if this assumption is wrong based on definition parsing
        let dist_ori_arg = &concrete_args_for_log[4]; // 5th argument
        let dist_key_arg = &concrete_args_for_log[5]; // 6th argument
        if let (WildcardValue::PodId(pid), WildcardValue::Key(k)) = (dist_ori_arg, dist_key_arg) {
            if *pid == SELF && k.name() == "one" {
                info!(
                    "proof.rs: eth_dos_distance called with distance_ori=SELF, distance_key='one' (depth {})",
                    current_depth
                );
            }
        }
    }

    // --- Create ResolveScope for the custom predicate's body ---
    let mut wildcard_interpretation_map_for_body = HashMap::new();
    let mut public_arg_bindings_for_body = HashMap::new();

    // Map public arguments from the call to their indexes for public_arg_bindings
    for (idx, arg_val) in concrete_args_for_log.iter().enumerate() {
        if idx < custom_pred_def.args_len {
            public_arg_bindings_for_body.insert(idx, arg_val.clone());
        }
    }

    // Define all wildcards within the custom predicate's body statements
    // and map them appropriately (PublicArg or PrivateLocal)
    let mut all_wcs_in_body = HashSet::new();
    for stmt_tmpl in &custom_pred_def.statements {
        for arg_tmpl in &stmt_tmpl.args {
            match arg_tmpl {
                StatementTmplArg::Key(wc, k_or_wc) => {
                    all_wcs_in_body.insert(wc.clone());
                    if let KeyOrWildcard::Wildcard(ref k_wc) = k_or_wc {
                        all_wcs_in_body.insert(k_wc.clone());
                    }
                }
                StatementTmplArg::WildcardLiteral(wc) => {
                    all_wcs_in_body.insert(wc.clone());
                }
                _ => {}
            }
        }
    }

    for wc_in_body in all_wcs_in_body {
        // A wildcard in the body is a PublicArg if its index matches one of the custom_pred_def.args_len
        // AND its name matches a convention for arguments (e.g. ?0, ?1 or specific names if defined).
        // For simplicity here, we assume wildcards with index < args_len are public args.
        // A more robust mapping would involve parsing pred_def.arg_names if available.
        if wc_in_body.index < custom_pred_def.args_len {
            // Check if it's actually one of the defined arguments for this predicate.
            // This requires ensuring wc_in_body is actually used AS an argument placeholder in the definition.
            // The .index < args_len is a heuristic.
            // A better check: is this wc_in_body one of the `Wildcard` objects that represent the formal parameters of custom_pred_def?
            // This information isn't directly in CustomPredicate struct today.
            // Assuming for now that if index < args_len, it's a public arg placeholder.
            wildcard_interpretation_map_for_body.insert(
                wc_in_body.clone(),
                WildcardInterpretation::PublicArg(wc_in_body.index),
            );
        } else {
            // Otherwise, it's a private local wildcard to this custom predicate definition.
            // We need to give it a unique identity if it's not already in solver_state.domains or make sure it maps to an existing private one.
            // For now, just map to PrivateLocal. `generate_constraints_for_resolve_scope` will add it to solver_state.domains if new.
            wildcard_interpretation_map_for_body.insert(
                wc_in_body.clone(),
                WildcardInterpretation::PrivateLocal(wc_in_body),
            );
        }
    }

    let mut private_search_targets_for_body = HashSet::new();
    for interp_wc in wildcard_interpretation_map_for_body.values() {
        if let WildcardInterpretation::PrivateLocal(actual_wc) = interp_wc {
            private_search_targets_for_body.insert(actual_wc.clone());
        }
        // Note: prover.md mentions "global wildcards (specific to that custom predicate's scope)".
        // Given current interpretation map logic, these are handled as PrivateLocal if not public args.
        // If WildcardInterpretation::Global were to appear here, it should also be added.
    }

    let mut resolve_scope_for_body = crate::prover::solver::types::ResolveScope {
        templates_to_resolve: &custom_pred_def.statements,
        constraints: Vec::new(), // Will be populated by generate_constraints_for_resolve_scope
        search_targets: Some(private_search_targets_for_body.clone()), // MODIFIED: Set search targets
        wildcard_interpretation_map: wildcard_interpretation_map_for_body,
        public_arg_bindings: Some(&public_arg_bindings_for_body),
        current_depth: current_depth + 1,
        parent_custom_call_key: Some(memo_key.clone()),
    };
    // --- End ResolveScope Creation ---

    let mut operation_inputs: Vec<Statement> = Vec::new(); // These will be the *concrete statements* proven from custom_pred_def.statements

    // The state for the custom predicate body starts as a clone of the current state.
    // Domains for newly introduced private local wildcards will be added by generate_constraints.
    let state_for_custom_pred_body_initial_clone = state.clone_state_for_search(); // Clone for the custom pred context

    // Capture the wildcards known to the caller *before* diving into the custom predicate's body resolution.
    // These are the only wildcards whose domains should be updated in the caller's state.
    let caller_known_wildcards: HashSet<Wildcard> = state.domains.keys().cloned().collect();

    if custom_pred_def.conjunction {
        // AND logic: Call resolve_templates once for all statements in the body.
        debug!(
            "proof.rs: Custom Predicate '{}' (AND logic, depth {}): Attempting to resolve body.",
            custom_pred_def.name, current_depth
        );
        match crate::prover::solver::resolve_templates(
            global_context,
            &mut resolve_scope_for_body,
            state_for_custom_pred_body_initial_clone.clone_state_for_search(), // Pass a further clone to resolve_templates
        ) {
            Ok(resolved_body_state) => {
                // Moved check: After successful resolution of an AND branch, check for unused private wildcards FIRST.
                for private_wc in &private_search_targets_for_body {
                    if let Some((_domain, wc_type)) = resolved_body_state.domains.get(private_wc) {
                        if *wc_type == ExpectedType::Unknown {
                            state.active_custom_calls.remove(&memo_key);
                            let err_msg = format!(
                                "Private wildcard '{}' in custom predicate '{}' has an unresolved type 'Unknown' after body resolution.",
                                private_wc.name, custom_pred_def.name
                            );
                            error!("proof.rs: {}", err_msg);
                            let err = ProverError::InconsistentWildcard(err_msg);
                            state.memoization_cache.insert(
                                memo_key.clone(),
                                MemoizedProofOutcome::Failure(err.clone()),
                            );
                            return Err(err);
                        }
                    }
                    // If a private_wc is NOT in resolved_body_state.domains, it implies it was truly unused
                    // (not even appearing as a WildcardLiteral to be defaulted to Unknown).
                    // This could also be an error condition if all declared private WCs must be used.
                    // However, `private_search_targets_for_body` is built from WCs found in body templates,
                    // so they should be in domains if `generate_constraints_for_resolve_scope` worked.
                }

                // All statements in the conjunction must now be provable with the resolved_body_state.
                // Collect the concrete versions of custom_pred_def.statements as operation_inputs.
                for tmpl in &custom_pred_def.statements {
                    match crate::prover::solver::try_generate_concrete_candidate_and_bindings(
                        tmpl,
                        &resolved_body_state,
                        &resolve_scope_for_body,
                        global_context,
                    ) {
                        Ok(Some((concrete_stmt, _))) => {
                            if resolved_body_state
                                .proof_chains
                                .contains_key(&concrete_stmt)
                                || global_context
                                    .indexes
                                    .exact_statement_lookup
                                    .iter()
                                    .any(|(_, s)| s == &concrete_stmt)
                            {
                                operation_inputs.push(concrete_stmt.clone());
                                debug!(
                                    "proof.rs: Custom Predicate '{}' (AND logic, depth {}): Successfully proved sub-statement {:?} (from template {:?})",
                                    custom_pred_def.name, current_depth, concrete_stmt, tmpl.pred
                                );
                            } else {
                                state.active_custom_calls.remove(&memo_key);
                                let err_msg = format!(
                                    "Custom Predicate (AND) {} sub-statement {:?} (from {:?}) not found in proof_chains after resolve_templates.",
                                    custom_pred_def.name, concrete_stmt, tmpl
                                );
                                error!("proof.rs: {}", err_msg);
                                let err = ProverError::Internal(err_msg);
                                state.memoization_cache.insert(
                                    memo_key.clone(),
                                    MemoizedProofOutcome::Failure(err.clone()),
                                );
                                return Err(err);
                            }
                        }
                        Ok(None) => {
                            state.active_custom_calls.remove(&memo_key);
                            let err_msg = format!(
                                "Custom Predicate (AND) {}: Failed to generate concrete sub-statement from {:?} after resolve_templates.",
                                custom_pred_def.name, tmpl
                            );
                            error!("proof.rs: {}", err_msg);
                            let err = ProverError::Internal(err_msg);
                            state.memoization_cache.insert(
                                memo_key.clone(),
                                MemoizedProofOutcome::Failure(err.clone()),
                            );
                            return Err(err);
                        }
                        Err(e) => {
                            error!(
                                "proof.rs: Custom Predicate '{}' (AND logic, depth {}): Error generating concrete sub-statement from {:?}: {:?}",
                                custom_pred_def.name, current_depth, tmpl, e
                            );
                            state.active_custom_calls.remove(&memo_key);
                            state
                                .memoization_cache
                                .insert(memo_key.clone(), MemoizedProofOutcome::Failure(e.clone()));
                            return Err(e);
                        }
                    }
                }
                // Merge the successful state changes selectively
                // Domains:
                for (wc, (new_domain, new_et)) in resolved_body_state.domains {
                    if caller_known_wildcards.contains(&wc) {
                        if let Some((current_domain, current_et)) = state.domains.get_mut(&wc) {
                            *current_domain = new_domain;
                            *current_et = new_et;
                        } else {
                            // This should ideally not happen if caller_known_wildcards was derived from state.domains.keys()
                            // If it does, it implies wc was in keys but now entry is gone, or a logic error.
                            warn!("Solver: Wildcard {} was known to caller but not found in state.domains during merge for custom predicate {}.", wc.name, custom_pred_def.name);
                        }
                    }
                }
                state.proof_chains.extend(resolved_body_state.proof_chains);
                state.scope.extend(resolved_body_state.scope);
                state
                    .memoization_cache
                    .extend(resolved_body_state.memoization_cache);
                // Not merging local_potential_constant_info from resolved_body_state for now.
            }
            Err(e) => {
                // Error from resolve_templates for the AND body
                error!(
                    "proof.rs: Custom Predicate '{}' (AND logic, depth {}): resolve_templates for body failed: {:?}",
                    custom_pred_def.name, current_depth, e
                );
                state.active_custom_calls.remove(&memo_key);
                state
                    .memoization_cache
                    .insert(memo_key.clone(), MemoizedProofOutcome::Failure(e.clone()));
                return Err(e);
            }
        }
    } else {
        // OR logic: Try each statement template in the body one by one.
        let mut or_proof_succeeded = false;
        let mut first_or_error: Option<ProverError> = None;

        for (tmpl_idx, tmpl) in custom_pred_def.statements.iter().enumerate() {
            debug!(
                "proof.rs: Custom Predicate '{}' (OR logic, depth {}): Trying branch #{} (template: {:?})",
                custom_pred_def.name, current_depth, tmpl_idx, tmpl.pred
            );
            // For OR, each branch is independent. We need a fresh ResolveScope for each attempt.
            let mut temp_resolve_scope_for_or_branch = crate::prover::solver::types::ResolveScope {
                templates_to_resolve: std::slice::from_ref(tmpl), // Only this template
                constraints: Vec::<crate::prover::solver::types::Constraint>::new(), // Fully qualified path
                search_targets: Some(private_search_targets_for_body.clone()), // MODIFIED: Set search targets for OR branch too
                wildcard_interpretation_map: resolve_scope_for_body
                    .wildcard_interpretation_map
                    .clone(),
                public_arg_bindings: Some(&public_arg_bindings_for_body),
                current_depth: current_depth + 1, // Depth for this specific branch
                parent_custom_call_key: Some(memo_key.clone()),
            };

            // Try to resolve and prove this single template branch.
            match crate::prover::solver::resolve_templates(
                global_context,
                &mut temp_resolve_scope_for_or_branch,
                state_for_custom_pred_body_initial_clone.clone_state_for_search(), // Start from the state before this OR branch
            ) {
                Ok(resolved_or_branch_state) => {
                    debug!(
                        "proof.rs: Custom Predicate '{}' (OR branch #{}, depth {}): resolve_templates succeeded.",
                        custom_pred_def.name, tmpl_idx, current_depth
                    );

                    // Check for unused private wildcards within this successful OR branch
                    for private_wc in &private_search_targets_for_body {
                        if let Some((_domain, wc_type)) =
                            resolved_or_branch_state.domains.get(private_wc)
                        {
                            if *wc_type == ExpectedType::Unknown {
                                // No need to remove from active_custom_calls or update memo_cache here, as this OR branch will be skipped
                                let err_msg = format!(
                                    "Private wildcard '{}' in custom predicate '{}' (OR branch #{}) has an unresolved type 'Unknown' after body resolution.",
                                    private_wc.name, custom_pred_def.name, tmpl_idx
                                );
                                error!("proof.rs: {}", err_msg);
                                if first_or_error.is_none() {
                                    first_or_error =
                                        Some(ProverError::InconsistentWildcard(err_msg));
                                }
                                continue; // Move to check the next private_wc or fail this OR branch
                            }
                        }
                        // Similar to AND, if not in domains, it might be an issue, but less likely here.
                    }
                    if first_or_error.is_some() {
                        // If an unused private WC was found in this OR branch
                        debug!(
                            "proof.rs: Custom Predicate '{}' (OR branch #{}, depth {}): Unused private wildcard detected. Skipping this branch.",
                            custom_pred_def.name, tmpl_idx, current_depth
                        );
                        continue; // Skip to the next OR branch
                    }

                    // The single template in this OR branch must now be provable.
                    match crate::prover::solver::try_generate_concrete_candidate_and_bindings(
                        tmpl,
                        &resolved_or_branch_state,
                        &temp_resolve_scope_for_or_branch,
                        global_context,
                    ) {
                        Ok(Some((concrete_stmt, _))) => {
                            if resolved_or_branch_state
                                .proof_chains
                                .contains_key(&concrete_stmt)
                                || global_context
                                    .indexes
                                    .exact_statement_lookup
                                    .iter()
                                    .any(|(_, s)| s == &concrete_stmt)
                            {
                                operation_inputs.push(concrete_stmt.clone());
                                debug!(
                                    "proof.rs: Custom Predicate '{}' (OR branch #{}, depth {}): Successfully proved sub-statement {:?} (from template {:?})",
                                    custom_pred_def.name, tmpl_idx, current_depth, concrete_stmt, tmpl.pred
                                );
                                // Commit the state from this successful OR branch selectively
                                for (wc, (new_domain, new_et)) in resolved_or_branch_state.domains {
                                    if caller_known_wildcards.contains(&wc) {
                                        if let Some((current_domain, current_et)) =
                                            state.domains.get_mut(&wc)
                                        {
                                            *current_domain = new_domain;
                                            *current_et = new_et;
                                        } else {
                                            warn!("Solver: Wildcard {} was known to caller but not found in state.domains during OR branch merge for custom predicate {}.", wc.name, custom_pred_def.name);
                                        }
                                    }
                                }
                                state
                                    .proof_chains
                                    .extend(resolved_or_branch_state.proof_chains);
                                state.scope.extend(resolved_or_branch_state.scope);
                                state
                                    .memoization_cache
                                    .extend(resolved_or_branch_state.memoization_cache);
                                // Not merging local_potential_constant_info

                                or_proof_succeeded = true;
                                break; // Found a successful branch for OR
                            } else {
                                let msg = format!(
                                    "Custom Predicate (OR branch {}) {}: sub-statement {:?} not in proof_chains after resolve_templates.",
                                    tmpl_idx, custom_pred_def.name, concrete_stmt
                                );
                                if first_or_error.is_none() {
                                    first_or_error = Some(ProverError::Internal(msg.clone()));
                                }
                                debug!("proof.rs: {}", msg);
                                // Continue to next OR branch
                            }
                        }
                        Ok(None) => {
                            let msg = format!(
                                "Custom Predicate (OR branch {}) {}: Failed to generate concrete sub-statement from {:?} after resolve_templates.",
                                tmpl_idx, custom_pred_def.name, tmpl
                            );
                            if first_or_error.is_none() {
                                first_or_error = Some(ProverError::Internal(msg.clone()));
                            }
                            debug!("proof.rs: {}", msg);
                            // Continue to next OR branch
                        }
                        Err(e) => {
                            debug!(
                                "proof.rs: Custom Predicate '{}' (OR branch #{}, depth {}): Error generating concrete sub-statement from {:?}: {:?}",
                                custom_pred_def.name, tmpl_idx, current_depth, tmpl, e
                            );
                            if first_or_error.is_none() {
                                first_or_error = Some(e);
                            }
                            // Continue to next OR branch
                        }
                    }
                }
                Err(e) => {
                    debug!(
                        "proof.rs: Custom Predicate '{}' (OR branch #{}, depth {}): resolve_templates failed: {:?}",
                        custom_pred_def.name, tmpl_idx, current_depth, e
                    );
                    // Error from resolve_templates for this OR branch
                    if first_or_error.is_none() {
                        first_or_error = Some(e);
                    }
                    // Continue to the next OR branch
                }
            }
            if or_proof_succeeded {
                break;
            }
        }

        if !or_proof_succeeded {
            state.active_custom_calls.remove(&memo_key);
            let err = first_or_error.unwrap_or_else(|| {
                ProverError::Unsatisfiable(format!(
                    "All OR branches failed for custom predicate: {:?}",
                    target_custom_statement
                ))
            });
            error!(
                "proof.rs: Custom Predicate '{}' (OR logic, depth {}): All branches failed. Final error: {:?}",
                custom_pred_def.name, current_depth, err
            );
            state
                .memoization_cache
                .insert(memo_key.clone(), MemoizedProofOutcome::Failure(err.clone()));
            return Err(err);
        }
    }

    // If proof succeeded (either all AND branches or one OR branch):
    // The actual proof steps for the sub-statements are already in state.proof_chains (added by try_prove_statement calls within resolve_templates).
    // We just need to create the final ProofStep for the custom predicate itself.
    let final_custom_pred_chain = ProofChain(vec![ProofStep {
        operation: OperationType::Custom(target_custom_ref.clone()),
        inputs: operation_inputs, // These are the proven sub-statements
        output: target_custom_statement.clone(),
    }]);

    debug!(
        "proof.rs: Successfully proved Custom Predicate '{}' (depth {}). Output: {:?}. Chain length: 1 (plus inputs)",
        custom_pred_def.name, current_depth, target_custom_statement
    );

    // Collect the scope fragment for this custom predicate's proof.
    // This comprises the scopes of its direct input statements.
    let mut custom_pred_scope_fragment = HashSet::new();
    if let Some(custom_proof_step) = final_custom_pred_chain.0.get(0) {
        for input_stmt in &custom_proof_step.inputs {
            if let Some(input_chain) = state.proof_chains.get(input_stmt) {
                // Recursively collect scope for this input's chain
                input_chain.collect_scope(
                    &mut custom_pred_scope_fragment,
                    &state.proof_chains,
                    &global_context.indexes.exact_statement_lookup,
                );
            } else if let Some((pod_id, base_stmt)) = global_context
                .indexes
                .exact_statement_lookup
                .iter()
                .find(|(_, stmt)| stmt == input_stmt)
            {
                // If the input is a base fact not part of another chain (e.g. direct from initial facts)
                custom_pred_scope_fragment.insert((*pod_id, base_stmt.clone()));
            }
            // If an input_stmt is neither in proof_chains nor a base_fact,
            // it implies an issue, as it should have been proven or be a base fact.
            // However, `try_prove_statement` for sub-targets should have handled this.
        }
    }

    let success_outcome = MemoizedProofOutcome::Success(
        final_custom_pred_chain.clone(),
        custom_pred_scope_fragment, // Use the collected scope fragment
    );
    state
        .memoization_cache
        .insert(memo_key.clone(), success_outcome);
    state.active_custom_calls.remove(&memo_key); // Remove from active calls on success

    Ok(final_custom_pred_chain)
}
