use std::collections::{HashMap, HashSet};

use super::{
    types::{MemoizationKey, MemoizedProofOutcome},
    SolverState,
};
use crate::{
    middleware::{
        statement::{StatementArg, WildcardValue},
        AnchoredKey, CustomPredicate, CustomPredicateBatch, CustomPredicateRef, Key, KeyOrWildcard,
        NativeOperation, NativePredicate, OperationType, PodId, Predicate, Statement,
        StatementTmpl, StatementTmplArg, ToFields, TypedValue, Value, Wildcard, SELF,
    },
    prover::{
        error::ProverError,
        indexing::ProverIndexes,
        types::{ConcreteValue, CustomDefinitions, ProofChain, ProofStep},
    },
};

const MAX_SOLVER_DEPTH: usize = 50; // Max recursion depth for the main solver
const MAX_CUSTOM_PREDICATE_RECURSION_DEPTH: usize = 20; // Max recursion for a single custom predicate chain

/// Attempts to find or generate a proof chain for a given target statement.
/// If successful, updates the solver state (proof_chains, scope) and returns the chain.
pub(super) fn try_prove_statement(
    state: &mut SolverState,
    target: &Statement,
    indexes: &ProverIndexes,
    custom_definitions: &CustomDefinitions,
    potential_constant_info: &[(Wildcard, Key, Value)],
    current_depth: usize,
) -> Result<ProofChain, ProverError> {
    if current_depth > MAX_CUSTOM_PREDICATE_RECURSION_DEPTH {
        return Err(ProverError::MaxDepthExceeded(format!(
            "Max recursion depth ({}) exceeded while proving {:?}",
            MAX_CUSTOM_PREDICATE_RECURSION_DEPTH, target
        )));
    }

    if let Some(existing_chain) = state.proof_chains.get(target) {
        return Ok(existing_chain.clone());
    }

    if let Statement::ValueOf(target_ak, target_value) = target {
        if let Some((_holder_wc, const_key, _value)) = potential_constant_info
            .iter()
            .find(|(_, k, v)| k == &target_ak.key && v == target_value)
        {
            if target_ak.pod_id == SELF {
                let self_output_ak = AnchoredKey::new(SELF, const_key.clone());
                let self_output_stmt = Statement::ValueOf(self_output_ak, target_value.clone());
                let proof_step = ProofStep {
                    operation: OperationType::Native(NativeOperation::NewEntry),
                    inputs: vec![],
                    output: self_output_stmt.clone(),
                };
                let proof_chain = ProofChain(vec![proof_step]);
                state
                    .proof_chains
                    .insert(self_output_stmt.clone(), proof_chain.clone());
                return Ok(proof_chain);
            }
        }
    }

    let base_fact = indexes
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
                predicate_ref_id: predicate_variant.to_fields(&state.params),
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
            NativePredicate::ValueOf => {
                try_prove_value_of_statement(state, target, indexes, potential_constant_info)
            }
            NativePredicate::Equal => try_prove_equal_statement(
                state,
                target,
                indexes,
                custom_definitions,
                potential_constant_info,
                current_depth,
            ),
            NativePredicate::NotEqual => try_prove_not_equal_statement(
                state,
                target,
                indexes,
                custom_definitions,
                potential_constant_info,
                current_depth,
            ),
            NativePredicate::Lt => try_prove_lt_statement(
                state,
                target,
                indexes,
                custom_definitions,
                potential_constant_info,
                current_depth,
            ),
            NativePredicate::SumOf => {
                try_prove_sum_of_statement(state, target, indexes, potential_constant_info)
            }
            NativePredicate::ProductOf => {
                try_prove_product_of_statement(state, target, indexes, potential_constant_info)
            }
            NativePredicate::Contains => {
                try_prove_contains_statement(state, target, indexes, potential_constant_info)
            }
            NativePredicate::NotContains => {
                try_prove_not_contains_statement(state, target, indexes, potential_constant_info)
            }
            NativePredicate::MaxOf => {
                try_prove_max_of_statement(state, target, indexes, potential_constant_info)
            }
            NativePredicate::HashOf => {
                try_prove_hash_of_statement(state, target, indexes, potential_constant_info)
            }
            NativePredicate::LtEq => try_prove_lt_eq_statement(
                state,
                target,
                indexes,
                custom_definitions,
                potential_constant_info,
                current_depth,
            ),
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
                custom_definitions,
                indexes,
                potential_constant_info,
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
                &indexes.exact_statement_lookup,
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

fn build_concrete_statement_from_bindings(
    tmpl: &StatementTmpl,
    public_bindings: &HashMap<usize, WildcardValue>,
    state: &SolverState,
    outer_context: Option<(&CustomPredicate, std::sync::Arc<CustomPredicateBatch>)>,
) -> Result<Statement, ProverError> {
    let outer_args_len = outer_context.as_ref().map(|(def, _)| def.args_len);

    match &tmpl.pred {
        Predicate::Native(_) => {
            let mut concrete_args = Vec::with_capacity(tmpl.args.len());
            for (arg_idx, arg_tmpl) in tmpl.args.iter().enumerate() {
                match arg_tmpl {
                    StatementTmplArg::Key(wc_pod, key_or_wc) => {
                        let outer_predicate_args_len =
                            outer_context.as_ref().map_or(0, |(def, _)| def.args_len);
                        let is_private_wc_in_valueof_key_arg = tmpl.pred
                            == Predicate::Native(NativePredicate::ValueOf)
                            && arg_idx == 0
                            && outer_context.is_some()
                            && wc_pod.index >= outer_predicate_args_len;

                        let pod_id_result = if is_private_wc_in_valueof_key_arg {
                            Ok(crate::middleware::SELF)
                        } else {
                            match outer_args_len {
                                Some(args_len) if wc_pod.index < args_len => {
                                    match public_bindings.get(&wc_pod.index) {
                                        Some(WildcardValue::PodId(id)) => Ok(*id),
                                        _ => Err(ProverError::Internal(format!(
                                            "Missing/wrong public binding for Pod WC {}",
                                            wc_pod
                                        ))),
                                    }
                                }
                                Some(_) | None => {
                                    // Private WC
                                    match state.domains.get(wc_pod) {
                                        Some((domain, _)) if domain.len() == 1 => match domain.iter().next().unwrap() {
                                                    ConcreteValue::Pod(id) => Ok(*id),
                                                    cv => Err(ProverError::Internal(format!("Private Pod WC {} resolved to non-Pod ConcreteValue: {:?} in singleton domain", wc_pod.name, cv))),
                                                },
                                        Some((domain, _)) if domain.len() > 1 => Err(ProverError::ProofDeferred(format!(
                                                    "Private Pod WC {} in custom predicate {} has non-singleton domain (size {}), deferring.",
                                                    wc_pod.name,
                                                    outer_context.as_ref().map_or("<unknown_pred>", |(def, _)| def.name.as_str()),
                                                    domain.len()
                                                ))),
                                        Some((domain, _)) => Err(ProverError::Unsatisfiable(format!(
                                                    "Private Pod WC {} in custom predicate {} has empty domain.",
                                                    wc_pod.name,
                                                    outer_context.as_ref().map_or("<unknown_pred>", |(def, _)| def.name.as_str())
                                                ))),
                                        None => Err(ProverError::Internal(format!(
                                            "Private Pod WC {} not found in solver state domains for custom predicate {}.",
                                            wc_pod.name,
                                            outer_context.as_ref().map_or("<unknown_pred>", |(def, _)| def.name.as_str())
                                        ))),
                                    }
                                }
                            }
                        };
                        let pod_id = pod_id_result?;

                        let key = match key_or_wc {
                            KeyOrWildcard::Key(k) => k.clone(),
                            KeyOrWildcard::Wildcard(wc_key) => {
                                match outer_args_len {
                                    Some(args_len) if wc_key.index < args_len => {
                                        match public_bindings.get(&wc_key.index) {
                                            Some(WildcardValue::Key(k)) => k.clone(),
                                            _ => {
                                                return Err(ProverError::Internal(format!(
                                                    "Missing/wrong public binding for Key WC {}",
                                                    wc_key
                                                )))
                                            }
                                        }
                                    }
                                    Some(_) | None => {
                                        // Private WC for Key
                                        match state.domains.get(wc_key) {
                                            Some((domain, _)) if domain.len() == 1 => match domain.iter().next().unwrap() {
                                                        ConcreteValue::Key(k_str) => Key::new(k_str.clone()),
                                                        cv => {
                                                            return Err(ProverError::Internal(format!(
                                                                "Private Key WC {} resolved to non-Key ConcreteValue: {:?} in singleton domain",
                                                                wc_key.name, cv
                                                            )))
                                                        }
                                                    },
                                            Some((domain, _)) if domain.len() > 1 => {
                                                return Err(ProverError::ProofDeferred(format!(
                                                    "Private Key WC {} in custom predicate {} has non-singleton domain (size {}), deferring.",
                                                    wc_key.name,
                                                    outer_context.as_ref().map_or("<unknown_pred>", |(def, _)| def.name.as_str()),
                                                    domain.len()
                                                )));
                                            }
                                            Some((domain, _)) => {
                                                // domain is empty
                                                return Err(ProverError::Unsatisfiable(format!(
                                                    "Private Key WC {} in custom predicate {} has empty domain.",
                                                    wc_key.name,
                                                    outer_context.as_ref().map_or("<unknown_pred>", |(def, _)| def.name.as_str())
                                                )));
                                            }
                                            None => {
                                                return Err(ProverError::Internal(format!(
                                                    "Private Key WC {} not found in solver state domains for custom predicate {}.",
                                                    wc_key.name,
                                                    outer_context.as_ref().map_or("<unknown_pred>", |(def, _)| def.name.as_str())
                                                )));
                                            }
                                        }
                                    }
                                }
                            }
                        };
                        concrete_args.push(StatementArg::Key(AnchoredKey::new(pod_id, key)));
                    }
                    StatementTmplArg::WildcardLiteral(wc_val) => {
                        match outer_args_len {
                            Some(args_len) if wc_val.index < args_len => return Err(ProverError::Internal(format!("Invalid Use: StatementTmplArg::WildcardLiteral ({}) used for public index", wc_val))),
                            _ => { // Private WC for Value
                                match state.domains.get(wc_val) {
                                    Some((domain, _)) if domain.len() == 1 => match domain.iter().next().unwrap() {
                                                ConcreteValue::Val(v) => concrete_args.push(StatementArg::Literal(v.clone())),
                                                cv => return Err(ProverError::Internal(format!("Private Value WC {} resolved to non-Val ConcreteValue: {:?} in singleton domain", wc_val.name, cv))),
                                            },
                                    Some((domain, _)) if domain.len() > 1 => {
                                        return Err(ProverError::ProofDeferred(format!(
                                            "Private Value WC {} in custom predicate {} has non-singleton domain (size {}), deferring.",
                                            wc_val.name,
                                            outer_context.as_ref().map_or("<unknown_pred>", |(def, _)| def.name.as_str()),
                                            domain.len()
                                        )));
                                    }
                                    Some((domain, _)) => { // domain is empty
                                        return Err(ProverError::Unsatisfiable(format!(
                                            "Private Value WC {} in custom predicate {} has empty domain.",
                                            wc_val.name,
                                            outer_context.as_ref().map_or("<unknown_pred>", |(def, _)| def.name.as_str())
                                        )));
                                    }
                                    None => {
                                        return Err(ProverError::Internal(format!(
                                            "Private Value WC {} not found in solver state domains for custom predicate {}.",
                                            wc_val.name,
                                            outer_context.as_ref().map_or("<unknown_pred>", |(def, _)| def.name.as_str())
                                        )));
                                    }
                                }
                            }
                        }
                    }
                    StatementTmplArg::Literal(v) => {
                        concrete_args.push(StatementArg::Literal(v.clone()))
                    }
                    StatementTmplArg::None => {}
                }
            }
            crate::prover::solver::build_concrete_statement(tmpl.pred.clone(), concrete_args)
        }
        Predicate::Custom(custom_ref) => {
            // Nested Custom Predicate Call
            let mut nested_call_args = Vec::with_capacity(tmpl.args.len());
            for arg_tmpl in &tmpl.args {
                match arg_tmpl {
                    StatementTmplArg::WildcardLiteral(wc) => {
                        let wc_val = match outer_args_len {
                            Some(args_len) if wc.index < args_len => {
                                public_bindings.get(&wc.index).cloned().ok_or_else(|| {
                                    ProverError::Internal(format!(
                                        "Missing public binding for WC {} for nested call",
                                        wc
                                    ))
                                })?
                            }
                            _ => {
                                // Private WC from outer scope passed to nested call
                                match state.domains.get(wc) {
                                    Some((domain, _)) if domain.len() == 1 => match domain.iter().next().unwrap() {
                                        ConcreteValue::Pod(id) => WildcardValue::PodId(*id),
                                        ConcreteValue::Key(k_name) => WildcardValue::Key(Key::new(k_name.clone())),
                                        ConcreteValue::Val(_) => return Err(ProverError::Internal(format!("Cannot pass Value type via WildcardLiteral to nested custom for WC {}", wc))),
                                    },
                                    _ => return Err(ProverError::ProofDeferred(format!("Private WC {} for nested call not singleton", wc))), // TODO: Lookahead
                                }
                            }
                        };
                        nested_call_args.push(wc_val);
                    }
                    StatementTmplArg::Literal(value) => match value.typed() {
                        TypedValue::String(s) => {
                            nested_call_args.push(WildcardValue::Key(Key::new(s.clone())))
                        }
                        _ => {
                            return Err(ProverError::Internal(format!(
                                "Unsupported Literal Value type {:?} for custom call arg",
                                value.typed()
                            )))
                        }
                    },
                    _ => {
                        return Err(ProverError::Internal(format!(
                            "Unsupported arg type {:?} for custom call",
                            arg_tmpl
                        )))
                    }
                }
            }
            let nested_pred_def = custom_ref
                .batch
                .predicates
                .get(custom_ref.index)
                .ok_or_else(|| {
                    ProverError::Internal(format!(
                        "Custom ref index {} out of bounds",
                        custom_ref.index
                    ))
                })?;
            if nested_call_args.len() != nested_pred_def.args_len {
                return Err(ProverError::Internal(
                    "Arg length mismatch for nested custom call".to_string(),
                ));
            }
            Ok(Statement::Custom(custom_ref.clone(), nested_call_args))
        }
        Predicate::BatchSelf(idx) => {
            // Nested BatchSelf Call
            let (_outer_pred_def, batch_arc) = outer_context.ok_or_else(|| {
                ProverError::Internal("Missing outer context for BatchSelf".to_string())
            })?;
            let mut nested_call_args = Vec::with_capacity(tmpl.args.len());
            for arg_tmpl in &tmpl.args {
                match arg_tmpl {
                    StatementTmplArg::WildcardLiteral(wc) => {
                        let wc_val = match outer_args_len {
                            Some(args_len) if wc.index < args_len => {
                                public_bindings.get(&wc.index).cloned().ok_or_else(|| {
                                    ProverError::Internal(format!(
                                        "Missing public binding for WC {} for BatchSelf call",
                                        wc
                                    ))
                                })?
                            }
                            _ => {
                                // Private WC from outer scope
                                match state.domains.get(wc) {
                                    Some((domain, _)) if domain.len() == 1 => match domain.iter().next().unwrap() {
                                        ConcreteValue::Pod(id) => WildcardValue::PodId(*id),
                                        ConcreteValue::Key(k_name) => WildcardValue::Key(Key::new(k_name.clone())),
                                        ConcreteValue::Val(_) => return Err(ProverError::Internal(format!("Cannot pass Value type via WildcardLiteral to BatchSelf for WC {}", wc))),
                                    },
                                     _ => return Err(ProverError::ProofDeferred(format!("Private WC {} for BatchSelf call not singleton", wc))), // TODO: Lookahead
                                }
                            }
                        };
                        nested_call_args.push(wc_val);
                    }
                    StatementTmplArg::Literal(value) => match value.typed() {
                        TypedValue::String(s) => {
                            nested_call_args.push(WildcardValue::Key(Key::new(s.clone())))
                        }
                        _ => {
                            return Err(ProverError::Internal(format!(
                                "Unsupported Literal Value type {:?} for BatchSelf call arg",
                                value.typed()
                            )))
                        }
                    },
                    _ => {
                        return Err(ProverError::Internal(format!(
                            "Unsupported arg type {:?} for BatchSelf call",
                            arg_tmpl
                        )))
                    }
                }
            }
            let concrete_custom_ref = CustomPredicateRef {
                batch: batch_arc.clone(),
                index: *idx,
            };
            let resolved_pred_def = batch_arc.predicates.get(*idx).ok_or_else(|| {
                ProverError::Internal(format!("BatchSelf index {} out of bounds", idx))
            })?;
            if nested_call_args.len() != resolved_pred_def.args_len {
                return Err(ProverError::Internal(
                    "Arg length mismatch for BatchSelf call".to_string(),
                ));
            }
            Ok(Statement::Custom(concrete_custom_ref, nested_call_args))
        }
    }
}

// Helper function to try proving a ValueOf statement
fn try_prove_value_of_statement(
    state: &mut SolverState,
    target: &Statement,
    indexes: &ProverIndexes,
    potential_constant_info: &[(Wildcard, Key, Value)],
) -> Result<ProofChain, ProverError> {
    if let Statement::ValueOf(ak, expected_value) = target {
        // Case 1: ValueOf is directly in initial_facts or from SELF constants
        if indexes.contains_exact_statement(&ak.pod_id, target)
            || (ak.pod_id == SELF
                && potential_constant_info
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
    indexes: &ProverIndexes,
    custom_definitions: &CustomDefinitions,
    _potential_constant_info: &[(Wildcard, Key, Value)],
    current_depth: usize,
) -> Result<ProofChain, ProverError> {
    // Original logic for proving Equal statements...
    // This will involve checking DSU, value_map, and potentially recursive calls for TransitiveEq
    if let Statement::Equal(ak1, ak2) = target {
        // 1. Check direct value equality from ValueOf entries
        if let (Some(v1), Some(v2)) = (indexes.get_value(ak1), indexes.get_value(ak2)) {
            if v1 == v2 {
                let input1 = Statement::ValueOf(ak1.clone(), v1.clone());
                let input2 = Statement::ValueOf(ak2.clone(), v2.clone());
                if indexes.get_exact_statement(&ak1.pod_id, &input1)
                    && indexes.get_exact_statement(&ak2.pod_id, &input2)
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
        if indexes.are_equal(ak1, ak2) {
            // If DSU says they are equal, and it's not from direct value check, it implies a path exists.
            // Try to find a path via TransitiveEqualFromStatements or CopyStatement if target itself is a base fact.
            if indexes.get_exact_statement(&ak1.pod_id, target)
                || indexes.get_exact_statement(&ak2.pod_id, target)
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
            for common_key_id in 0..indexes.id_to_key.len() {
                let ak_mid = &indexes.id_to_key[common_key_id];
                if ak_mid == ak1 || ak_mid == ak2 {
                    continue;
                }

                let stmt1_mid = Statement::Equal(ak1.clone(), ak_mid.clone());
                let stmt_mid_2 = Statement::Equal(ak_mid.clone(), ak2.clone());

                if let Ok(chain1) = try_prove_statement(
                    state,
                    &stmt1_mid,
                    indexes,
                    custom_definitions,
                    &[],
                    current_depth + 1,
                ) {
                    if let Ok(chain2) = try_prove_statement(
                        state,
                        &stmt_mid_2,
                        indexes,
                        custom_definitions,
                        &[],
                        current_depth + 1,
                    ) {
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
    indexes: &ProverIndexes,
    custom_definitions: &CustomDefinitions,
    _potential_constant_info: &[(Wildcard, Key, Value)],
    current_depth: usize,
) -> Result<ProofChain, ProverError> {
    if let Statement::NotEqual(ak1, ak2) = target {
        // 1. From different values in ValueOf entries
        if let (Some(v1), Some(v2)) = (indexes.get_value(ak1), indexes.get_value(ak2)) {
            if v1 != v2 {
                let input1 = Statement::ValueOf(ak1.clone(), v1.clone());
                let input2 = Statement::ValueOf(ak2.clone(), v2.clone());
                if indexes.get_exact_statement(&ak1.pod_id, &input1)
                    && indexes.get_exact_statement(&ak2.pod_id, &input2)
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
        if let Ok(chain_lt1) = try_prove_statement(
            state,
            &stmt_lt1,
            indexes,
            custom_definitions,
            &[],
            current_depth + 1,
        ) {
            let mut steps = chain_lt1.0;
            steps.push(ProofStep {
                operation: OperationType::Native(NativeOperation::LtToNotEqual),
                inputs: vec![stmt_lt1],
                output: target.clone(),
            });
            return Ok(ProofChain(steps));
        }
        let stmt_lt2 = Statement::Lt(ak2.clone(), ak1.clone());
        if let Ok(chain_lt2) = try_prove_statement(
            state,
            &stmt_lt2,
            indexes,
            custom_definitions,
            &[],
            current_depth + 1,
        ) {
            let mut steps = chain_lt2.0;
            steps.push(ProofStep {
                operation: OperationType::Native(NativeOperation::LtToNotEqual),
                inputs: vec![stmt_lt2],
                output: target.clone(),
            });
            return Ok(ProofChain(steps));
        }
        // 3. From explicit NotEqual in indexes (CopyStatement)
        if indexes.are_not_equal(ak1, ak2)
            && (indexes.get_exact_statement(&ak1.pod_id, target)
                || indexes.get_exact_statement(&ak2.pod_id, target))
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

fn try_prove_lt_statement(
    state: &mut SolverState,
    target: &Statement,
    indexes: &ProverIndexes,
    _custom_definitions: &CustomDefinitions,
    _potential_constant_info: &[(Wildcard, Key, Value)],
    _current_depth: usize,
) -> Result<ProofChain, ProverError> {
    if let Statement::Lt(ak1, ak2) = target {
        if let (Some(TypedValue::Int(v1)), Some(TypedValue::Int(v2))) = (
            indexes.get_value(ak1).map(|v| v.typed()),
            indexes.get_value(ak2).map(|v| v.typed()),
        ) {
            if v1 < v2 {
                let val1 = indexes.get_value(ak1).unwrap().clone();
                let val2 = indexes.get_value(ak2).unwrap().clone();
                let input1 = Statement::ValueOf(ak1.clone(), val1);
                let input2 = Statement::ValueOf(ak2.clone(), val2);
                if indexes.get_exact_statement(&ak1.pod_id, &input1)
                    && indexes.get_exact_statement(&ak2.pod_id, &input2)
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

fn try_prove_sum_of_statement(
    _state: &mut SolverState,
    target: &Statement,
    indexes: &ProverIndexes,
    _potential_constant_info: &[(Wildcard, Key, Value)],
) -> Result<ProofChain, ProverError> {
    if let Statement::SumOf(ak_sum, ak_add1, ak_add2) = target {
        if let (
            Some(TypedValue::Int(v_sum)),
            Some(TypedValue::Int(v_add1)),
            Some(TypedValue::Int(v_add2)),
        ) = (
            indexes.get_value(ak_sum).map(|v| v.typed()),
            indexes.get_value(ak_add1).map(|v| v.typed()),
            indexes.get_value(ak_add2).map(|v| v.typed()),
        ) {
            if *v_sum == *v_add1 + *v_add2 {
                let val_sum = indexes.get_value(ak_sum).unwrap().clone();
                let val_add1 = indexes.get_value(ak_add1).unwrap().clone();
                let val_add2 = indexes.get_value(ak_add2).unwrap().clone();
                let input_sum = Statement::ValueOf(ak_sum.clone(), val_sum);
                let input_add1 = Statement::ValueOf(ak_add1.clone(), val_add1);
                let input_add2 = Statement::ValueOf(ak_add2.clone(), val_add2);
                if indexes.get_exact_statement(&ak_sum.pod_id, &input_sum)
                    && indexes.get_exact_statement(&ak_add1.pod_id, &input_add1)
                    && indexes.get_exact_statement(&ak_add2.pod_id, &input_add2)
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

fn try_prove_product_of_statement(
    _state: &mut SolverState,
    target: &Statement,
    indexes: &ProverIndexes,
    _potential_constant_info: &[(Wildcard, Key, Value)],
) -> Result<ProofChain, ProverError> {
    if let Statement::ProductOf(ak_prod, ak_fac1, ak_fac2) = target {
        if let (
            Some(TypedValue::Int(v_prod)),
            Some(TypedValue::Int(v_fac1)),
            Some(TypedValue::Int(v_fac2)),
        ) = (
            indexes.get_value(ak_prod).map(|v| v.typed()),
            indexes.get_value(ak_fac1).map(|v| v.typed()),
            indexes.get_value(ak_fac2).map(|v| v.typed()),
        ) {
            if *v_prod == *v_fac1 * *v_fac2 {
                let val_prod = indexes.get_value(ak_prod).unwrap().clone();
                let val_fac1 = indexes.get_value(ak_fac1).unwrap().clone();
                let val_fac2 = indexes.get_value(ak_fac2).unwrap().clone();
                let input_prod = Statement::ValueOf(ak_prod.clone(), val_prod);
                let input_fac1 = Statement::ValueOf(ak_fac1.clone(), val_fac1);
                let input_fac2 = Statement::ValueOf(ak_fac2.clone(), val_fac2);
                if indexes.get_exact_statement(&ak_prod.pod_id, &input_prod)
                    && indexes.get_exact_statement(&ak_fac1.pod_id, &input_fac1)
                    && indexes.get_exact_statement(&ak_fac2.pod_id, &input_fac2)
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

fn try_prove_contains_statement(
    _state: &mut SolverState,
    target: &Statement,
    indexes: &ProverIndexes,
    _potential_constant_info: &[(Wildcard, Key, Value)],
) -> Result<ProofChain, ProverError> {
    if let Statement::Contains(ak_container, ak_key, ak_value) = target {
        if let (Some(val_container), Some(val_key), Some(val_value)) = (
            indexes.get_value(ak_container),
            indexes.get_value(ak_key),
            indexes.get_value(ak_value),
        ) {
            if let Ok((proven_value, _merkle_proof)) = val_container.prove_existence(val_key) {
                if *proven_value == *val_value {
                    let input_container =
                        Statement::ValueOf(ak_container.clone(), val_container.clone());
                    let input_key = Statement::ValueOf(ak_key.clone(), val_key.clone());
                    let input_value = Statement::ValueOf(ak_value.clone(), val_value.clone());
                    if indexes.get_exact_statement(&ak_container.pod_id, &input_container)
                        && indexes.get_exact_statement(&ak_key.pod_id, &input_key)
                        && indexes.get_exact_statement(&ak_value.pod_id, &input_value)
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

fn try_prove_not_contains_statement(
    _state: &mut SolverState,
    target: &Statement,
    indexes: &ProverIndexes,
    _potential_constant_info: &[(Wildcard, Key, Value)],
) -> Result<ProofChain, ProverError> {
    if let Statement::NotContains(ak_container, ak_key) = target {
        if let (Some(val_container), Some(val_key)) =
            (indexes.get_value(ak_container), indexes.get_value(ak_key))
        {
            if val_container.prove_nonexistence(val_key).is_ok() {
                let input_container =
                    Statement::ValueOf(ak_container.clone(), val_container.clone());
                let input_key = Statement::ValueOf(ak_key.clone(), val_key.clone());
                if indexes.get_exact_statement(&ak_container.pod_id, &input_container)
                    && indexes.get_exact_statement(&ak_key.pod_id, &input_key)
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

fn try_prove_max_of_statement(
    _state: &mut SolverState,
    target: &Statement,
    indexes: &ProverIndexes,
    _potential_constant_info: &[(Wildcard, Key, Value)],
) -> Result<ProofChain, ProverError> {
    if let Statement::MaxOf(ak_max, ak_op1, ak_op2) = target {
        if let (
            Some(TypedValue::Int(v_max)),
            Some(TypedValue::Int(v_op1)),
            Some(TypedValue::Int(v_op2)),
        ) = (
            indexes.get_value(ak_max).map(|v| v.typed()),
            indexes.get_value(ak_op1).map(|v| v.typed()),
            indexes.get_value(ak_op2).map(|v| v.typed()),
        ) {
            if v_max == std::cmp::max(v_op1, v_op2) {
                let val_max = indexes.get_value(ak_max).unwrap().clone();
                let val_op1 = indexes.get_value(ak_op1).unwrap().clone();
                let val_op2 = indexes.get_value(ak_op2).unwrap().clone();
                let input_max = Statement::ValueOf(ak_max.clone(), val_max);
                let input_op1 = Statement::ValueOf(ak_op1.clone(), val_op1);
                let input_op2 = Statement::ValueOf(ak_op2.clone(), val_op2);
                if indexes.get_exact_statement(&ak_max.pod_id, &input_max)
                    && indexes.get_exact_statement(&ak_op1.pod_id, &input_op1)
                    && indexes.get_exact_statement(&ak_op2.pod_id, &input_op2)
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

fn try_prove_hash_of_statement(
    _state: &mut SolverState,
    target: &Statement,
    indexes: &ProverIndexes,
    _potential_constant_info: &[(Wildcard, Key, Value)],
) -> Result<ProofChain, ProverError> {
    if let Statement::HashOf(ak_hash, ak_preimage1, ak_preimage2) = target {
        if let (Some(val_hash), Some(val_preimage1), Some(val_preimage2)) = (
            indexes.get_value(ak_hash),
            indexes.get_value(ak_preimage1),
            indexes.get_value(ak_preimage2),
        ) {
            // Simplified: Assume if ValueOf for hash and preimages exist, it's provable by a direct operation.
            // let computed_hash_val = Value::hash_concat(&[&val_preimage1, &val_preimage2], &indexes.params); // Assuming this was the intent
            // if val_hash == &computed_hash_val {
            // For now, we'll just check if the ValueOf statements for inputs exist.
            // A real implementation would need to verify the hash computation.
            let input_hash = Statement::ValueOf(ak_hash.clone(), val_hash.clone());
            let input_preimage1 = Statement::ValueOf(ak_preimage1.clone(), val_preimage1.clone());
            let input_preimage2 = Statement::ValueOf(ak_preimage2.clone(), val_preimage2.clone());
            if indexes.get_exact_statement(&ak_hash.pod_id, &input_hash)
                && indexes.get_exact_statement(&ak_preimage1.pod_id, &input_preimage1)
                && indexes.get_exact_statement(&ak_preimage2.pod_id, &input_preimage2)
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

fn try_prove_lt_eq_statement(
    _state: &mut SolverState,
    _target: &Statement,
    _indexes: &ProverIndexes,
    _custom_definitions: &CustomDefinitions,
    _potential_constant_info: &[(Wildcard, Key, Value)],
    _current_depth: usize,
) -> Result<ProofChain, ProverError> {
    // LtEq(A,B) can be Lt(A,B) OR Equal(A,B)
    // Operations LtToLtEq and EqToLtEq are assumed not to exist for now.
    // if let Statement::LtEq(ak1, ak2) = target {
    // Try Lt(A,B)
    // let stmt_lt = Statement::Lt(ak1.clone(), ak2.clone());
    // if let Ok(chain_lt) = try_prove_statement(state, &stmt_lt, indexes, custom_definitions, &[], current_depth + 1) {
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
    // if let Ok(chain_eq) = try_prove_statement(state, &stmt_eq, indexes, custom_definitions, &[], current_depth + 1) {
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
    custom_definitions: &CustomDefinitions,
    indexes: &ProverIndexes,
    potential_constant_info: &[(Wildcard, Key, Value)],
    current_depth: usize,
) -> Result<ProofChain, ProverError> {
    if current_depth > MAX_CUSTOM_PREDICATE_RECURSION_DEPTH {
        return Err(ProverError::MaxDepthExceeded(format!(
            "Max depth {} reached trying to prove custom predicate: {:?}",
            MAX_CUSTOM_PREDICATE_RECURSION_DEPTH, target_custom_statement
        )));
    }

    let concrete_args = match target_custom_statement {
        Statement::Custom(_, args) => args.clone(),
        _ => {
            return Err(ProverError::Internal(
                "Expected Custom statement".to_string(),
            ))
        }
    };

    let memo_key = MemoizationKey::Custom {
        predicate_ref_id: Predicate::Custom(target_custom_ref.clone()).to_fields(&state.params),
        args: concrete_args.clone(),
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

    let predicate_key = Predicate::Custom(target_custom_ref.clone()).to_fields(&state.params);
    let (custom_pred_def, batch_arc) = match custom_definitions.get(&predicate_key) {
        Some(def) => def.clone(), // Clone to avoid lifetime issues with outer_context
        None => {
            state.active_custom_calls.remove(&memo_key); // Remove before erroring
            return Err(ProverError::Internal(format!(
                "Custom predicate definition not found for ref: {:?} (key: {:?})",
                target_custom_ref, predicate_key
            )));
        }
    };

    let mut combined_proof_chain_steps = Vec::new();
    let mut current_scope_fragment_for_custom_pred: HashSet<(PodId, Statement)> = HashSet::new();
    let mut operation_inputs = Vec::new();

    if custom_pred_def.conjunction {
        // AND
        for tmpl in &custom_pred_def.statements {
            // Construct public_bindings for the call to build_concrete_statement_from_bindings
            let mut public_bindings_for_tmpl = HashMap::new();
            for (arg_idx, arg_val) in concrete_args.iter().enumerate() {
                if arg_idx < custom_pred_def.args_len {
                    public_bindings_for_tmpl.insert(arg_idx, arg_val.clone());
                }
            }

            let sub_target_statement = match build_concrete_statement_from_bindings(
                tmpl,
                &public_bindings_for_tmpl,
                state, // Current solver state
                Some((&custom_pred_def, batch_arc.clone())),
            ) {
                Ok(stmt) => stmt,
                Err(ProverError::ProofDeferred(msg)) => {
                    // If a sub-statement defers, the whole custom predicate defers for this path.
                    state.active_custom_calls.remove(&memo_key);
                    // No caching of deferred as failure for the *custom predicate itself* yet,
                    // as other branches of search might resolve the deferral.
                    // The deferral is for the *sub-statement*.
                    return Err(ProverError::ProofDeferred(format!(
                        "Custom predicate {}: sub-statement deferred: {}",
                        custom_pred_def.name, msg
                    )));
                }
                Err(e) => {
                    // Any other error (Unsatisfiable, Internal)
                    state.active_custom_calls.remove(&memo_key);
                    // Cache this error for the custom predicate itself
                    state
                        .memoization_cache
                        .insert(memo_key.clone(), MemoizedProofOutcome::Failure(e.clone()));
                    return Err(e);
                }
            };

            match try_prove_statement(
                state,
                &sub_target_statement,
                indexes,
                custom_definitions,
                potential_constant_info,
                current_depth + 1,
            ) {
                Ok(chain) => {
                    operation_inputs.push(sub_target_statement.clone());
                    combined_proof_chain_steps.extend(chain.0);
                    // Scope for sub-proofs is managed by the recursive call to try_prove_statement,
                    // which updates `state.scope`. We need to collect the *specific* scope items
                    // that were added for *this sub-proof* if we want to attribute them to the custom predicate's scope_fragment.
                    // For now, `state.scope` is the global scope.
                }
                Err(e) => {
                    state.active_custom_calls.remove(&memo_key); // Remove on failure
                                                                 // Cache failure for this custom predicate call
                    state
                        .memoization_cache
                        .insert(memo_key.clone(), MemoizedProofOutcome::Failure(e.clone()));
                    return Err(e);
                }
            }
        }
    } else {
        // OR
        let mut or_proof_succeeded = false;
        let mut first_or_error = None;

        for tmpl in &custom_pred_def.statements {
            // Construct public_bindings for the call to build_concrete_statement_from_bindings
            let mut public_bindings_for_tmpl = HashMap::new();
            for (arg_idx, arg_val) in concrete_args.iter().enumerate() {
                if arg_idx < custom_pred_def.args_len {
                    public_bindings_for_tmpl.insert(arg_idx, arg_val.clone());
                }
            }

            // For OR, we need to be careful with state modifications if a branch fails.
            // We should try proving one branch. If it works, great. If not, state changes should be reverted.
            // This suggests cloning the state for each OR branch attempt.
            let mut temp_state_for_or_branch = state.clone_state_for_search();
            // Ensure the active_custom_calls for the *current* predicate is part of the temp state's active set
            // It was added to `state` before, so `clone_state_for_search` should copy it.

            let sub_target_statement = match build_concrete_statement_from_bindings(
                tmpl,
                &public_bindings_for_tmpl,
                &temp_state_for_or_branch, // Use the temporary state for concretization attempt
                Some((&custom_pred_def, batch_arc.clone())),
            ) {
                Ok(stmt) => stmt,
                Err(ProverError::ProofDeferred(msg)) => {
                    if first_or_error.is_none() {
                        first_or_error = Some(ProverError::ProofDeferred(format!(
                            "Custom predicate {}: OR branch sub-statement deferred: {}",
                            custom_pred_def.name, msg
                        )));
                    }
                    continue; // Try next OR branch, this one deferred.
                }
                Err(e) => {
                    // Any other error (Unsatisfiable, Internal)
                    if first_or_error.is_none() {
                        first_or_error = Some(e);
                    }
                    continue; // Try next OR branch
                }
            };

            match try_prove_statement(
                &mut temp_state_for_or_branch, // Use a temporary state for proving this branch
                &sub_target_statement,
                indexes,
                custom_definitions,
                potential_constant_info,
                current_depth + 1,
            ) {
                Ok(chain) => {
                    // A branch of the OR succeeded. Commit its changes to the main state.
                    state
                        .proof_chains
                        .extend(temp_state_for_or_branch.proof_chains);
                    state.scope.extend(temp_state_for_or_branch.scope);
                    // The memoization cache from temp_state should also be merged if it contains new useful entries.
                    // For simplicity, we'll only merge the main cache for now, but this could be more granular.
                    state
                        .memoization_cache
                        .extend(temp_state_for_or_branch.memoization_cache);

                    operation_inputs.push(sub_target_statement.clone());
                    combined_proof_chain_steps.extend(chain.0);
                    or_proof_succeeded = true;
                    break; // Found a successful branch for OR
                }
                Err(e) => {
                    if first_or_error.is_none() {
                        first_or_error = Some(e);
                    }
                    // Continue to the next OR branch
                }
            }
        }
        if !or_proof_succeeded {
            state.active_custom_calls.remove(&memo_key); // Remove on failure
            let err = first_or_error.unwrap_or_else(|| {
                ProverError::Unsatisfiable(format!(
                    "All OR branches failed for custom predicate: {:?}",
                    target_custom_statement
                ))
            });
            state
                .memoization_cache
                .insert(memo_key.clone(), MemoizedProofOutcome::Failure(err.clone()));
            return Err(err);
        }
    }

    // If proof succeeded (either all AND branches or one OR branch):
    let final_chain_for_custom_pred = ProofChain(vec![ProofStep {
        operation: OperationType::Custom(target_custom_ref.clone()),
        inputs: operation_inputs, // These are the proven sub-statements
        output: target_custom_statement.clone(),
    }]);

    // Collect the scope fragment for this custom predicate's proof.
    // This comprises the scopes of its direct input statements.
    let mut custom_pred_scope_fragment = HashSet::new();
    if let Some(custom_proof_step) = final_chain_for_custom_pred.0.get(0) {
        for input_stmt in &custom_proof_step.inputs {
            if let Some(input_chain) = state.proof_chains.get(input_stmt) {
                // Recursively collect scope for this input's chain
                input_chain.collect_scope(
                    &mut custom_pred_scope_fragment,
                    &state.proof_chains,
                    &indexes.exact_statement_lookup,
                );
            } else if let Some((pod_id, base_stmt)) = indexes
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
        final_chain_for_custom_pred.clone(),
        custom_pred_scope_fragment, // Use the collected scope fragment
    );
    state
        .memoization_cache
        .insert(memo_key.clone(), success_outcome);
    state.active_custom_calls.remove(&memo_key); // Remove from active calls on success

    Ok(final_chain_for_custom_pred)
}
