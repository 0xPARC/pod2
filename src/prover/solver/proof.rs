use std::collections::HashMap;

use super::SolverState;
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
        solver::build_concrete_statement,
        types::{ConcreteValue, CustomDefinitions, ProofChain, ProofStep},
    },
};

const MAX_CUSTOM_PREDICATE_RECURSION_DEPTH: usize = 20;

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

    match target.predicate() {
        Predicate::Native(NativePredicate::Equal) => {
            if let Statement::Equal(ak1, ak2) = target {
                if let (Some(v1), Some(v2)) = (indexes.get_value(ak1), indexes.get_value(ak2)) {
                    if v1 == v2 {
                        let input1 = Statement::ValueOf(ak1.clone(), v1.clone());
                        let input2 = Statement::ValueOf(ak2.clone(), v2.clone());
                        let operation = OperationType::Native(NativeOperation::EqualFromEntries);
                        let proof_step = ProofStep {
                            operation,
                            inputs: vec![input1.clone(), input2.clone()],
                            output: target.clone(),
                        };
                        let proof_chain = ProofChain(vec![proof_step]);
                        if let Some((pod_id1, _)) = indexes
                            .exact_statement_lookup
                            .iter()
                            .find(|(_, stmt)| stmt == &input1)
                        {
                            state.scope.insert((*pod_id1, input1));
                        } else {
                            return Err(ProverError::Internal(format!(
                                "Could not find origin Pod for ValueOf: {:?}",
                                input1
                            )));
                        }
                        if let Some((pod_id2, _)) = indexes
                            .exact_statement_lookup
                            .iter()
                            .find(|(_, stmt)| stmt == &input2)
                        {
                            state.scope.insert((*pod_id2, input2));
                        } else {
                            return Err(ProverError::Internal(format!(
                                "Could not find origin Pod for ValueOf: {:?}",
                                input2
                            )));
                        }
                        state
                            .proof_chains
                            .insert(target.clone(), proof_chain.clone());
                        return Ok(proof_chain);
                    }
                }
                let maybe_id1 = indexes.get_key_index(ak1);
                let maybe_id2 = indexes.get_key_index(ak2);
                if let (Some(id1), Some(id2)) = (maybe_id1, maybe_id2) {
                    let rep1 = indexes.dsu.find(id1);
                    let rep2 = indexes.dsu.find(id2);
                    if rep1 != rep2 {
                        return Err(ProverError::Unsatisfiable(format!(
                            "Cannot prove Equal({:?}, {:?}) transitively: not in same DSU set (roots: {}, {})",
                            ak1, ak2, rep1, rep2
                        )));
                    } else {
                        let all_known_keys = indexes.get_all_known_keys();
                        for ak_mid in all_known_keys {
                            if ak_mid == ak1 || ak_mid == ak2 {
                                continue;
                            }
                            if indexes.get_key_index(ak_mid).is_none() {
                                continue;
                            }
                            let target1_mid = Statement::Equal(ak1.clone(), ak_mid.clone());
                            let target_mid_2 = Statement::Equal(ak_mid.clone(), ak2.clone());
                            match try_prove_statement(
                                state,
                                &target1_mid,
                                indexes,
                                custom_definitions,
                                &[],
                                current_depth + 1,
                            ) {
                                Ok(chain1) => {
                                    match try_prove_statement(
                                        state,
                                        &target_mid_2,
                                        indexes,
                                        custom_definitions,
                                        &[],
                                        current_depth + 1,
                                    ) {
                                        Ok(chain2) => {
                                            let mut combined_steps = chain1.0;
                                            combined_steps.extend(chain2.0);
                                            let transitive_step = ProofStep {
                                                operation: OperationType::Native(
                                                    NativeOperation::TransitiveEqualFromStatements,
                                                ),
                                                inputs: vec![
                                                    target1_mid.clone(),
                                                    target_mid_2.clone(),
                                                ],
                                                output: target.clone(),
                                            };
                                            combined_steps.push(transitive_step);
                                            let final_chain = ProofChain(combined_steps);
                                            state
                                                .proof_chains
                                                .insert(target.clone(), final_chain.clone());
                                            return Ok(final_chain);
                                        }
                                        Err(ProverError::MaxDepthExceeded(msg)) => {
                                            return Err(ProverError::MaxDepthExceeded(msg));
                                        }
                                        Err(_) => {}
                                    }
                                }
                                Err(ProverError::MaxDepthExceeded(msg)) => {
                                    return Err(ProverError::MaxDepthExceeded(msg));
                                }
                                Err(_) => {}
                            }
                        }
                    }
                }
            }
        }
        Predicate::Native(NativePredicate::NotEqual) => {
            if let Statement::NotEqual(ak1, ak2) = target {
                if let (Some(v1), Some(v2)) = (indexes.get_value(ak1), indexes.get_value(ak2)) {
                    if v1 != v2 {
                        let input1 = Statement::ValueOf(ak1.clone(), v1.clone());
                        let input2 = Statement::ValueOf(ak2.clone(), v2.clone());
                        let operation = OperationType::Native(NativeOperation::NotEqualFromEntries);
                        let proof_step = ProofStep {
                            operation,
                            inputs: vec![input1.clone(), input2.clone()],
                            output: target.clone(),
                        };
                        let proof_chain = ProofChain(vec![proof_step]);
                        if let Some((pod_id1, _)) = indexes
                            .exact_statement_lookup
                            .iter()
                            .find(|(_, stmt)| stmt == &input1)
                        {
                            state.scope.insert((*pod_id1, input1));
                        } else {
                            return Err(ProverError::Internal(format!(
                                "Could not find origin Pod for ValueOf: {:?}",
                                input1
                            )));
                        }
                        if let Some((pod_id2, _)) = indexes
                            .exact_statement_lookup
                            .iter()
                            .find(|(_, stmt)| stmt == &input2)
                        {
                            state.scope.insert((*pod_id2, input2));
                        } else {
                            return Err(ProverError::Internal(format!(
                                "Could not find origin Pod for ValueOf: {:?}",
                                input2
                            )));
                        }
                        state
                            .proof_chains
                            .insert(target.clone(), proof_chain.clone());
                        return Ok(proof_chain);
                    }
                }
                let target_lt1 = Statement::Lt(ak1.clone(), ak2.clone());
                let target_lt2 = Statement::Lt(ak2.clone(), ak1.clone());
                if let Ok(lt_chain1) = try_prove_statement(
                    state,
                    &target_lt1,
                    indexes,
                    custom_definitions,
                    &[],
                    current_depth + 1,
                ) {
                    let mut combined_steps = lt_chain1.0;
                    let neq_step = ProofStep {
                        operation: OperationType::Native(NativeOperation::LtToNotEqual),
                        inputs: vec![target_lt1.clone()],
                        output: target.clone(),
                    };
                    combined_steps.push(neq_step);
                    let final_chain = ProofChain(combined_steps);
                    state
                        .proof_chains
                        .insert(target.clone(), final_chain.clone());
                    return Ok(final_chain);
                }
                if let Ok(lt_chain2) = try_prove_statement(
                    state,
                    &target_lt2,
                    indexes,
                    custom_definitions,
                    &[],
                    current_depth + 1,
                ) {
                    let mut combined_steps = lt_chain2.0;
                    let neq_step = ProofStep {
                        operation: OperationType::Native(NativeOperation::LtToNotEqual),
                        inputs: vec![target_lt2.clone()],
                        output: target.clone(),
                    };
                    combined_steps.push(neq_step);
                    let final_chain = ProofChain(combined_steps);
                    state
                        .proof_chains
                        .insert(target.clone(), final_chain.clone());
                    return Ok(final_chain);
                }
            }
        }
        Predicate::Native(NativePredicate::Lt) => {
            if let Statement::Lt(ak1, ak2) = target {
                if let (Some(TypedValue::Int(int1)), Some(TypedValue::Int(int2))) = (
                    indexes.get_value(ak1).map(|v| v.typed()),
                    indexes.get_value(ak2).map(|v| v.typed()),
                ) {
                    if int1 < int2 {
                        let input1_val = indexes.get_value(ak1).unwrap().clone();
                        let input2_val = indexes.get_value(ak2).unwrap().clone();
                        let input1 = Statement::ValueOf(ak1.clone(), input1_val);
                        let input2 = Statement::ValueOf(ak2.clone(), input2_val);
                        let operation = OperationType::Native(NativeOperation::LtFromEntries);
                        let proof_step = ProofStep {
                            operation,
                            inputs: vec![input1.clone(), input2.clone()],
                            output: target.clone(),
                        };
                        let proof_chain = ProofChain(vec![proof_step]);
                        if let Some((pod_id1, _)) = indexes
                            .exact_statement_lookup
                            .iter()
                            .find(|(_, stmt)| stmt == &input1)
                        {
                            state.scope.insert((*pod_id1, input1));
                        } else {
                            return Err(ProverError::Internal(format!(
                                "Could not find origin Pod for ValueOf: {:?}",
                                input1
                            )));
                        }
                        if let Some((pod_id2, _)) = indexes
                            .exact_statement_lookup
                            .iter()
                            .find(|(_, stmt)| stmt == &input2)
                        {
                            state.scope.insert((*pod_id2, input2));
                        } else {
                            return Err(ProverError::Internal(format!(
                                "Could not find origin Pod for ValueOf: {:?}",
                                input2
                            )));
                        }
                        state
                            .proof_chains
                            .insert(target.clone(), proof_chain.clone());
                        return Ok(proof_chain);
                    }
                }
            }
        }
        Predicate::Native(NativePredicate::SumOf) => {
            if let Statement::SumOf(ak_sum, ak_add1, ak_add2) = target {
                if let (
                    Some(TypedValue::Int(sum)),
                    Some(TypedValue::Int(add1)),
                    Some(TypedValue::Int(add2)),
                ) = (
                    indexes.get_value(ak_sum).map(|v| v.typed()),
                    indexes.get_value(ak_add1).map(|v| v.typed()),
                    indexes.get_value(ak_add2).map(|v| v.typed()),
                ) {
                    if *sum == *add1 + *add2 {
                        let input_sum_val = indexes.get_value(ak_sum).unwrap().clone();
                        let input_add1_val = indexes.get_value(ak_add1).unwrap().clone();
                        let input_add2_val = indexes.get_value(ak_add2).unwrap().clone();
                        let input_sum = Statement::ValueOf(ak_sum.clone(), input_sum_val);
                        let input_add1 = Statement::ValueOf(ak_add1.clone(), input_add1_val);
                        let input_add2 = Statement::ValueOf(ak_add2.clone(), input_add2_val);
                        let operation = OperationType::Native(NativeOperation::SumOf);
                        let proof_step = ProofStep {
                            operation,
                            inputs: vec![input_sum.clone(), input_add1.clone(), input_add2.clone()],
                            output: target.clone(),
                        };
                        let proof_chain = ProofChain(vec![proof_step]);
                        if let Some((pod_id, _)) = indexes
                            .exact_statement_lookup
                            .iter()
                            .find(|(_, stmt)| stmt == &input_sum)
                        {
                            state.scope.insert((*pod_id, input_sum));
                        } else {
                            return Err(ProverError::Internal("Missing origin Pod".to_string()));
                        }
                        if let Some((pod_id, _)) = indexes
                            .exact_statement_lookup
                            .iter()
                            .find(|(_, stmt)| stmt == &input_add1)
                        {
                            state.scope.insert((*pod_id, input_add1));
                        } else {
                            return Err(ProverError::Internal("Missing origin Pod".to_string()));
                        }
                        if let Some((pod_id, _)) = indexes
                            .exact_statement_lookup
                            .iter()
                            .find(|(_, stmt)| stmt == &input_add2)
                        {
                            state.scope.insert((*pod_id, input_add2));
                        } else {
                            return Err(ProverError::Internal("Missing origin Pod".to_string()));
                        }
                        state
                            .proof_chains
                            .insert(target.clone(), proof_chain.clone());
                        return Ok(proof_chain);
                    }
                }
            }
        }
        Predicate::Native(NativePredicate::ProductOf) => {
            if let Statement::ProductOf(ak_prod, ak_fac1, ak_fac2) = target {
                if let (
                    Some(TypedValue::Int(prod)),
                    Some(TypedValue::Int(fac1)),
                    Some(TypedValue::Int(fac2)),
                ) = (
                    indexes.get_value(ak_prod).map(|v| v.typed()),
                    indexes.get_value(ak_fac1).map(|v| v.typed()),
                    indexes.get_value(ak_fac2).map(|v| v.typed()),
                ) {
                    if *prod == *fac1 * *fac2 {
                        let input_prod_val = indexes.get_value(ak_prod).unwrap().clone();
                        let input_fac1_val = indexes.get_value(ak_fac1).unwrap().clone();
                        let input_fac2_val = indexes.get_value(ak_fac2).unwrap().clone();
                        let input_prod = Statement::ValueOf(ak_prod.clone(), input_prod_val);
                        let input_fac1 = Statement::ValueOf(ak_fac1.clone(), input_fac1_val);
                        let input_fac2 = Statement::ValueOf(ak_fac2.clone(), input_fac2_val);
                        let operation = OperationType::Native(NativeOperation::ProductOf);
                        let proof_step = ProofStep {
                            operation,
                            inputs: vec![
                                input_prod.clone(),
                                input_fac1.clone(),
                                input_fac2.clone(),
                            ],
                            output: target.clone(),
                        };
                        let proof_chain = ProofChain(vec![proof_step]);
                        if let Some((pod_id, _)) = indexes
                            .exact_statement_lookup
                            .iter()
                            .find(|(_, stmt)| stmt == &input_prod)
                        {
                            state.scope.insert((*pod_id, input_prod));
                        } else {
                            return Err(ProverError::Internal("Missing origin Pod".to_string()));
                        }
                        if let Some((pod_id, _)) = indexes
                            .exact_statement_lookup
                            .iter()
                            .find(|(_, stmt)| stmt == &input_fac1)
                        {
                            state.scope.insert((*pod_id, input_fac1));
                        } else {
                            return Err(ProverError::Internal("Missing origin Pod".to_string()));
                        }
                        if let Some((pod_id, _)) = indexes
                            .exact_statement_lookup
                            .iter()
                            .find(|(_, stmt)| stmt == &input_fac2)
                        {
                            state.scope.insert((*pod_id, input_fac2));
                        } else {
                            return Err(ProverError::Internal("Missing origin Pod".to_string()));
                        }
                        state
                            .proof_chains
                            .insert(target.clone(), proof_chain.clone());
                        return Ok(proof_chain);
                    }
                }
            }
        }
        Predicate::Native(NativePredicate::MaxOf) => {
            if let Statement::MaxOf(ak_max, ak_op1, ak_op2) = target {
                if let (
                    Some(TypedValue::Int(max_val)),
                    Some(TypedValue::Int(op1)),
                    Some(TypedValue::Int(op2)),
                ) = (
                    indexes.get_value(ak_max).map(|v| v.typed()),
                    indexes.get_value(ak_op1).map(|v| v.typed()),
                    indexes.get_value(ak_op2).map(|v| v.typed()),
                ) {
                    if *max_val == std::cmp::max(*op1, *op2) {
                        let input_max_val = indexes.get_value(ak_max).unwrap().clone();
                        let input_op1_val = indexes.get_value(ak_op1).unwrap().clone();
                        let input_op2_val = indexes.get_value(ak_op2).unwrap().clone();
                        let input_max = Statement::ValueOf(ak_max.clone(), input_max_val);
                        let input_op1 = Statement::ValueOf(ak_op1.clone(), input_op1_val);
                        let input_op2 = Statement::ValueOf(ak_op2.clone(), input_op2_val);
                        let operation = OperationType::Native(NativeOperation::MaxOf);
                        let proof_step = ProofStep {
                            operation,
                            inputs: vec![input_max.clone(), input_op1.clone(), input_op2.clone()],
                            output: target.clone(),
                        };
                        let proof_chain = ProofChain(vec![proof_step]);
                        if let Some((pod_id, _)) = indexes
                            .exact_statement_lookup
                            .iter()
                            .find(|(_, stmt)| stmt == &input_max)
                        {
                            state.scope.insert((*pod_id, input_max));
                        } else {
                            return Err(ProverError::Internal("Missing origin Pod".to_string()));
                        }
                        if let Some((pod_id, _)) = indexes
                            .exact_statement_lookup
                            .iter()
                            .find(|(_, stmt)| stmt == &input_op1)
                        {
                            state.scope.insert((*pod_id, input_op1));
                        } else {
                            return Err(ProverError::Internal("Missing origin Pod".to_string()));
                        }
                        if let Some((pod_id, _)) = indexes
                            .exact_statement_lookup
                            .iter()
                            .find(|(_, stmt)| stmt == &input_op2)
                        {
                            state.scope.insert((*pod_id, input_op2));
                        } else {
                            return Err(ProverError::Internal("Missing origin Pod".to_string()));
                        }
                        state
                            .proof_chains
                            .insert(target.clone(), proof_chain.clone());
                        return Ok(proof_chain);
                    }
                }
            }
        }
        Predicate::Native(NativePredicate::Contains) => {
            if let Statement::Contains(container_ak, key_ak, value_ak) = target {
                if let Some(container_val) = indexes.get_value(container_ak) {
                    let mut needed_inputs = vec![];
                    let key_value_opt = indexes.get_value(key_ak).cloned();
                    if let Some(ref kv) = key_value_opt {
                        needed_inputs.push(Statement::ValueOf(key_ak.clone(), kv.clone()));
                    }
                    let target_value_opt = indexes.get_value(value_ak).cloned();
                    if let Some(ref tv) = target_value_opt {
                        needed_inputs.push(Statement::ValueOf(value_ak.clone(), tv.clone()));
                    }

                    if let (Some(key_value), Some(target_value)) = (key_value_opt, target_value_opt)
                    {
                        match container_val.prove_existence(&key_value) {
                            Ok((proven_value, _merkle_proof)) if proven_value == &target_value => {
                                let input_container =
                                    Statement::ValueOf(container_ak.clone(), container_val.clone());
                                let mut i = vec![input_container.clone()];
                                i.extend(needed_inputs.clone());
                                let operation =
                                    OperationType::Native(NativeOperation::ContainsFromEntries);
                                let proof_step = ProofStep {
                                    operation,
                                    inputs: i,
                                    output: target.clone(),
                                };
                                let proof_chain = ProofChain(vec![proof_step]);
                                if let Some((pod_id, _)) = indexes
                                    .exact_statement_lookup
                                    .iter()
                                    .find(|(_, stmt)| stmt == &input_container)
                                {
                                    state.scope.insert((*pod_id, input_container));
                                } else {
                                    return Err(ProverError::Internal(format!(
                                        "Missing origin Pod for container ValueOf: {:?}",
                                        input_container
                                    )));
                                }
                                for input_stmt in needed_inputs {
                                    if let Some((pod_id, _)) = indexes
                                        .exact_statement_lookup
                                        .iter()
                                        .find(|(_, stmt)| stmt == &input_stmt)
                                    {
                                        state.scope.insert((*pod_id, input_stmt));
                                    } else {
                                        return Err(ProverError::Internal(format!(
                                            "Missing origin Pod for input ValueOf: {:?}",
                                            input_stmt
                                        )));
                                    }
                                }
                                state
                                    .proof_chains
                                    .insert(target.clone(), proof_chain.clone());
                                return Ok(proof_chain);
                            }
                            _ => {}
                        }
                    }
                }
            }
        }
        Predicate::Native(NativePredicate::NotContains) => {
            if let Statement::NotContains(container_ak, key_ak) = target {
                if let Some(container_val) = indexes.get_value(container_ak) {
                    let mut needed_inputs = vec![];
                    let key_value_opt = indexes.get_value(key_ak).cloned();
                    if let Some(ref kv) = key_value_opt {
                        needed_inputs.push(Statement::ValueOf(key_ak.clone(), kv.clone()));
                    }

                    if let Some(key_value) = key_value_opt {
                        match container_val.prove_nonexistence(&key_value) {
                            Ok(_merkle_proof) => {
                                let input_container =
                                    Statement::ValueOf(container_ak.clone(), container_val.clone());
                                let mut i = vec![input_container.clone()];
                                i.extend(needed_inputs.clone());
                                let operation =
                                    OperationType::Native(NativeOperation::NotContainsFromEntries);
                                let proof_step = ProofStep {
                                    operation,
                                    inputs: i,
                                    output: target.clone(),
                                };
                                let proof_chain = ProofChain(vec![proof_step]);
                                if let Some((pod_id, _)) = indexes
                                    .exact_statement_lookup
                                    .iter()
                                    .find(|(_, stmt)| stmt == &input_container)
                                {
                                    state.scope.insert((*pod_id, input_container));
                                } else {
                                    return Err(ProverError::Internal(format!(
                                        "Missing origin Pod for container ValueOf: {:?}",
                                        input_container
                                    )));
                                }
                                for input_stmt in needed_inputs {
                                    if let Some((pod_id, _)) = indexes
                                        .exact_statement_lookup
                                        .iter()
                                        .find(|(_, stmt)| stmt == &input_stmt)
                                    {
                                        state.scope.insert((*pod_id, input_stmt));
                                    } else {
                                        return Err(ProverError::Internal(format!(
                                            "Missing origin Pod for input ValueOf: {:?}",
                                            input_stmt
                                        )));
                                    }
                                }
                                state
                                    .proof_chains
                                    .insert(target.clone(), proof_chain.clone());
                                return Ok(proof_chain);
                            }
                            _ => {}
                        }
                    }
                }
            }
        }
        Predicate::Custom(custom_ref) => {
            if let Statement::Custom(target_custom_ref, concrete_args) = target {
                if custom_ref != *target_custom_ref {
                    return Err(ProverError::Internal(
                        "Predicate mismatch in custom proof logic".to_string(),
                    ));
                }
                let pred_key = Predicate::Custom(custom_ref.clone()).to_fields(&state.params);
                if let Some((pred_def, batch_arc)) = custom_definitions.get(&pred_key) {
                    if pred_def.conjunction {
                        let mut combined_steps = Vec::new();
                        let mut sub_statement_inputs = Vec::new();
                        let public_bindings: HashMap<usize, WildcardValue> =
                            concrete_args.iter().cloned().enumerate().collect();

                        for internal_tmpl in &pred_def.statements {
                            let concrete_sub_stmt = match build_concrete_statement_from_bindings(
                                internal_tmpl,
                                concrete_args,
                                &public_bindings,
                                state,
                                Some((pred_def, batch_arc.clone())),
                                current_depth + 1,
                                indexes,
                                custom_definitions,
                            ) {
                                Ok(stmt) => stmt,
                                Err(ProverError::ProofDeferred(msg)) => {
                                    println!("Deferred building concrete sub-statement for Custom AND branch of {}: {} (tmpl: {:?})", pred_def.name, msg, internal_tmpl.pred);
                                    return Err(ProverError::ProofDeferred(format!("AND predicate {} deferred because internal statement build failed: {}", pred_def.name, msg)));
                                }
                                Err(e) => return Err(e),
                            };
                            sub_statement_inputs.push(concrete_sub_stmt.clone());
                            match try_prove_statement(
                                state,
                                &concrete_sub_stmt,
                                indexes,
                                custom_definitions,
                                &[],
                                current_depth + 1,
                            ) {
                                Ok(sub_chain) => {
                                    combined_steps.extend(sub_chain.0);
                                }
                                Err(ProverError::MaxDepthExceeded(msg)) => {
                                    return Err(ProverError::MaxDepthExceeded(msg));
                                }
                                Err(e) => {
                                    println!("Failed recursive proof for sub-statement {:?} of AND predicate {}: {:?}. Failing AND predicate.", concrete_sub_stmt, pred_def.name, e);
                                    return Err(e);
                                }
                            }
                        }
                        let final_custom_step = ProofStep {
                            operation: OperationType::Custom(custom_ref.clone()),
                            inputs: sub_statement_inputs,
                            output: target.clone(),
                        };
                        combined_steps.push(final_custom_step);
                        let final_chain = ProofChain(combined_steps);
                        state
                            .proof_chains
                            .insert(target.clone(), final_chain.clone());
                        return Ok(final_chain);
                    } else {
                        let public_bindings: HashMap<usize, WildcardValue> =
                            concrete_args.iter().cloned().enumerate().collect();
                        let mut or_branch_deferred_occurred = false;
                        let mut last_or_branch_error: Option<ProverError> = None;

                        for internal_tmpl in &pred_def.statements {
                            let mut current_branch_had_fatal_error = false;

                            let concrete_sub_stmt_res = build_concrete_statement_from_bindings(
                                internal_tmpl,
                                concrete_args,
                                &public_bindings,
                                state,
                                Some((pred_def, batch_arc.clone())),
                                current_depth + 1,
                                indexes,
                                custom_definitions,
                            );

                            if let Ok(concrete_sub_stmt) = concrete_sub_stmt_res.as_ref() {
                                match try_prove_statement(
                                    state,
                                    concrete_sub_stmt,
                                    indexes,
                                    custom_definitions,
                                    &[],
                                    current_depth + 1,
                                ) {
                                    Ok(sub_chain) => {
                                        let mut combined_steps = sub_chain.0;
                                        let final_custom_step = ProofStep {
                                            operation: OperationType::Custom(custom_ref.clone()),
                                            inputs: vec![concrete_sub_stmt.clone()],
                                            output: target.clone(),
                                        };
                                        combined_steps.push(final_custom_step);
                                        let final_chain = ProofChain(combined_steps);
                                        state
                                            .proof_chains
                                            .insert(target.clone(), final_chain.clone());
                                        return Ok(final_chain);
                                    }
                                    Err(prove_err) => {
                                        println!("OR branch proof failed for sub-statement {:?} of {}: {:?}", concrete_sub_stmt, pred_def.name, prove_err);
                                        last_or_branch_error = Some(prove_err.clone());
                                        match prove_err {
                                            ProverError::ProofDeferred(_) => {
                                                or_branch_deferred_occurred = true;
                                            }
                                            ProverError::Internal(_)
                                            | ProverError::MaxDepthExceeded(_)
                                            | ProverError::NotImplemented(_)
                                            | ProverError::Configuration(_)
                                            | ProverError::FrontendError(_)
                                            | ProverError::Serialization(_)
                                            | ProverError::Io(_)
                                            | ProverError::Other(_) => {
                                                current_branch_had_fatal_error = true;
                                            }
                                            ProverError::Unsatisfiable(_)
                                            | ProverError::InconsistentWildcard(_) => {}
                                        }
                                    }
                                }
                            } else {
                                let build_err = concrete_sub_stmt_res.unwrap_err();
                                println!("OR branch failed to build concrete sub-statement from template {:?} for {}: {:?}", internal_tmpl.pred, pred_def.name, build_err);
                                last_or_branch_error = Some(build_err.clone());
                                match build_err {
                                    ProverError::ProofDeferred(_) => {
                                        or_branch_deferred_occurred = true;
                                    }
                                    ProverError::Internal(_)
                                    | ProverError::MaxDepthExceeded(_)
                                    | ProverError::NotImplemented(_)
                                    | ProverError::Configuration(_)
                                    | ProverError::FrontendError(_)
                                    | ProverError::Serialization(_)
                                    | ProverError::Io(_)
                                    | ProverError::Other(_) => {
                                        current_branch_had_fatal_error = true;
                                    }
                                    ProverError::Unsatisfiable(_)
                                    | ProverError::InconsistentWildcard(_) => {}
                                }
                            }

                            if current_branch_had_fatal_error {
                                println!(
                                    "OR predicate {} failed due to a fatal error in one of its branches: {:?}",
                                    pred_def.name, last_or_branch_error.as_ref().unwrap()
                                );
                                return Err(last_or_branch_error.unwrap());
                            }
                        }

                        if or_branch_deferred_occurred {
                            return Err(last_or_branch_error.unwrap_or_else(|| ProverError::ProofDeferred(format!(
                                "All OR branches for {} either failed (softly) or were deferred, with at least one deferral, but no fatal error or specific deferred error recorded.",
                                 pred_def.name
                            ))));
                        }

                        if let Some(err) = last_or_branch_error {
                            println!("All OR branches for custom predicate {} resulted in failure. Last error: {:?}", pred_def.name, err);
                            return Err(err);
                        } else {
                            println!("All OR branches for custom predicate {:?} failed (or no branches were viable/produced a specific error). Defaulting to Unsatisfiable.", custom_ref);
                            return Err(ProverError::Unsatisfiable(format!(
                                "No satisfiable OR branch found for {} (no errors, deferrals, or fatal issues reported from branches).",
                                pred_def.name
                            )));
                        }
                    }
                } else {
                    return Err(ProverError::Internal(format!(
                        "Custom predicate definition not found for ref: {:?}",
                        custom_ref
                    )));
                }
            }
        }
        _ => {}
    }

    Err(ProverError::Unsatisfiable(format!(
        "Could not find or derive proof for: {:?}",
        target
    )))
}

fn build_concrete_statement_from_bindings(
    tmpl: &StatementTmpl,
    _public_args: &[WildcardValue],
    public_bindings: &HashMap<usize, WildcardValue>,
    state: &SolverState,
    outer_context: Option<(&CustomPredicate, std::sync::Arc<CustomPredicateBatch>)>,
    current_depth: usize,
    indexes: &ProverIndexes,
    custom_definitions: &CustomDefinitions,
) -> Result<Statement, ProverError> {
    let outer_args_len = outer_context.as_ref().map(|(def, _)| def.args_len);

    match &tmpl.pred {
        Predicate::Native(_) => {
            let mut concrete_args = Vec::with_capacity(tmpl.args.len());
            for (arg_idx, arg_tmpl) in tmpl.args.iter().enumerate() {
                match arg_tmpl {
                    StatementTmplArg::Key(wc_pod, key_or_wc) => {
                        let outer_predicate_args_len = outer_context.as_ref().map_or(0, |(def, _)| def.args_len);
                        let is_private_wc_in_valueof_key_arg = tmpl.pred == Predicate::Native(NativePredicate::ValueOf) &&
                                                               arg_idx == 0 &&
                                                               outer_context.is_some() &&
                                                               wc_pod.index >= outer_predicate_args_len;

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
                                    match state.domains.get(wc_pod) {
                                        Some((domain, _)) if domain.len() == 1 => {
                                            match domain.iter().next().unwrap() {
                                                ConcreteValue::Pod(id) => Ok(*id),
                                                _ => Err(ProverError::Internal(format!("Private Pod WC {} domain wrong type", wc_pod))),
                                            }
                                        }
                                        Some((domain, _)) if outer_context.is_some() => {
                                            let (outer_pred_def, _) = outer_context.as_ref().unwrap();
                                            let mut resolved_candidate_pod_ids = Vec::new();
                                            for candidate_cv in domain {
                                                if let ConcreteValue::Pod(candidate_pod_id) = candidate_cv {
                                                    let mut consistent_candidate = true;
                                                    for internal_stmt_tmpl in &outer_pred_def.statements {
                                                        if !check_consistency_for_lookahead(
                                                            internal_stmt_tmpl, wc_pod, *candidate_pod_id,
                                                            public_bindings, outer_pred_def.args_len, state, indexes
                                                        ) {
                                                            consistent_candidate = false;
                                                            break;
                                                        }
                                                    }
                                                    if consistent_candidate {
                                                        resolved_candidate_pod_ids.push(*candidate_pod_id);
                                                    }
                                                }
                                            }
                                            if resolved_candidate_pod_ids.len() == 1 {
                                                Ok(resolved_candidate_pod_ids[0])
                                            } else {
                                                Err(ProverError::ProofDeferred(format!(
                                                    "Private Pod WC {} in {} domain has {} candidates after lookahead (domain size {}), expected 1.",
                                                    wc_pod.name, outer_pred_def.name, resolved_candidate_pod_ids.len(), domain.len()
                                                )))
                                            }
                                        }
                                        _ => Err(ProverError::ProofDeferred(format!(
                                            "Private Pod WC {} in {} domain not singleton and lookahead not applicable/failed (domain size {}).",
                                            wc_pod.name, outer_context.as_ref().map_or("<unknown>", |(d,_)|d.name.as_str()), state.domains.get(wc_pod).map_or(0, |(d,_)|d.len())
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
                                        match state.domains.get(wc_key) {
                                            Some((dom, _)) if dom.len() == 1 => {
                                                match dom.iter().next().unwrap() {
                                                    ConcreteValue::Key(k_str) => {
                                                        Key::new(k_str.clone())
                                                    }
                                                    _ => {
                                                        return Err(ProverError::Internal(format!(
                                                            "Private Key WC {} domain wrong type",
                                                            wc_key
                                                        )))
                                                    }
                                                }
                                            }
                                            _ => {
                                                return Err(ProverError::ProofDeferred(
                                                    "Lookahead: Other private Key WC not singleton"
                                                        .to_string(),
                                                ))
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
                            _ => {
                                match state.domains.get(wc_val) {
                                    Some((domain, _)) if domain.len() == 1 => {
                                        match domain.iter().next().unwrap() {
                                            ConcreteValue::Val(v) => concrete_args.push(StatementArg::Literal(v.clone())),
                                            _ => return Err(ProverError::Internal(format!("Private Value WC {} domain wrong type", wc_val))),
                                        }
                                    }
                                    _ => return Err(ProverError::ProofDeferred(format!("Private Value WC {} domain not singleton", wc_val))),
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

// Helper for build_concrete_statement_from_bindings lookahead
fn check_consistency_for_lookahead(
    internal_tmpl: &StatementTmpl,
    private_wc_being_resolved: &Wildcard,
    candidate_value_for_private_wc: PodId, // Assuming PodId for now, generalize if needed
    public_bindings: &HashMap<usize, WildcardValue>,
    outer_predicate_args_len: usize,
    state: &SolverState, // Main solver state for other private WCs
    indexes: &ProverIndexes,
) -> bool {
    // This function tries to evaluate `internal_tmpl` by substituting:
    // 1. `private_wc_being_resolved` with `candidate_value_for_private_wc`.
    // 2. Public wildcards of the outer predicate (from `public_bindings`).
    // 3. Other private wildcards of the outer predicate (must be singleton in `state`).
    // Then checks if the resulting (hopefully) concrete statement holds against `indexes`.

    match &internal_tmpl.pred {
        Predicate::Native(NativePredicate::Equal) => {
            if internal_tmpl.args.len() == 2 {
                let arg0 = &internal_tmpl.args[0];
                let arg1 = &internal_tmpl.args[1];

                // Try to get concrete values for both sides of the Equal
                let val0_opt = resolve_tmpl_arg_to_value(
                    arg0,
                    private_wc_being_resolved,
                    candidate_value_for_private_wc,
                    public_bindings,
                    outer_predicate_args_len,
                    state,
                    indexes,
                );
                let val1_opt = resolve_tmpl_arg_to_value(
                    arg1,
                    private_wc_being_resolved,
                    candidate_value_for_private_wc,
                    public_bindings,
                    outer_predicate_args_len,
                    state,
                    indexes,
                );

                match (val0_opt, val1_opt) {
                    (Ok(Some(val0)), Ok(Some(val1))) => return val0 == val1,
                    (Err(ProverError::ProofDeferred(_)), _)
                    | (_, Err(ProverError::ProofDeferred(_))) => {
                        // If resolving an arg part of the internal check itself defers, this candidate is not (yet) verifiable.
                        return false; // Treat as not consistent for this candidate
                    }
                    (Err(_), _) | (_, Err(_)) => return false, // Hard error during resolution
                    _ => return true, // Cannot form a concrete check from this internal_tmpl, assume consistent by default (conservative)
                                      // Or, could return false if strict checking is required.
                                      // For eth_friend, we need this to be strict: if we can't verify, it's not a match.
                                      // Let's make it false if not fully resolvable to concrete values.
                                      // This means resolve_tmpl_arg_to_value must not return Ok(None) if it was expected to resolve.
                }
            }
        }
        // TODO: Handle other native predicates if needed for more complex lookaheads.
        _ => return true, // For non-Equal or complex internal statements, assume consistent by default for this simplified lookahead.
    }
    true // Default if not an Equal or not fitting pattern
}

// Helper to resolve a StatementTmplArg to a concrete Value for lookahead
fn resolve_tmpl_arg_to_value(
    arg: &StatementTmplArg,
    private_wc_being_resolved: &Wildcard,
    candidate_value_for_private_wc: PodId, // Assuming PodId
    public_bindings: &HashMap<usize, WildcardValue>,
    outer_predicate_args_len: usize,
    state: &SolverState,
    indexes: &ProverIndexes,
) -> Result<Option<Value>, ProverError> {
    match arg {
        StatementTmplArg::Key(wc_pod, key_or_wc) => {
            let pod_id = if wc_pod == private_wc_being_resolved {
                candidate_value_for_private_wc
            } else if wc_pod.index < outer_predicate_args_len {
                // Public pod wildcard
                match public_bindings.get(&wc_pod.index) {
                    Some(WildcardValue::PodId(id)) => *id,
                    _ => {
                        return Err(ProverError::Internal(
                            "Lookahead: Public Pod WC binding error".to_string(),
                        ))
                    }
                }
            } else {
                // Other private pod wildcard
                match state.domains.get(wc_pod) {
                    Some((dom, _)) if dom.len() == 1 => match dom.iter().next().unwrap() {
                        ConcreteValue::Pod(id) => *id,
                        _ => {
                            return Err(ProverError::Internal(
                                "Lookahead: Other private Pod WC type error".to_string(),
                            ))
                        }
                    },
                    _ => {
                        return Err(ProverError::ProofDeferred(
                            "Lookahead: Other private Pod WC not singleton".to_string(),
                        ))
                    }
                }
            };

            let key_name = match key_or_wc {
                KeyOrWildcard::Key(k) => k.name().to_string(),
                KeyOrWildcard::Wildcard(wc_key) => {
                    // Assuming wc_key is NOT private_wc_being_resolved (which is a PodId wildcard)
                    if wc_key.index < outer_predicate_args_len {
                        // Public key wildcard
                        match public_bindings.get(&wc_key.index) {
                            Some(WildcardValue::Key(k)) => k.name().to_string(),
                            _ => {
                                return Err(ProverError::Internal(
                                    "Lookahead: Public Key WC binding error".to_string(),
                                ))
                            }
                        }
                    } else {
                        // Other private key wildcard
                        match state.domains.get(wc_key) {
                            Some((dom, _)) if dom.len() == 1 => match dom.iter().next().unwrap() {
                                ConcreteValue::Key(k_str) => k_str.clone(),
                                _ => {
                                    return Err(ProverError::Internal(
                                        "Lookahead: Other private Key WC type error".to_string(),
                                    ))
                                }
                            },
                            _ => {
                                return Err(ProverError::ProofDeferred(
                                    "Lookahead: Other private Key WC not singleton".to_string(),
                                ))
                            }
                        }
                    }
                }
            };
            Ok(indexes
                .get_value(&AnchoredKey::new(pod_id, Key::new(key_name)))
                .cloned())
        }
        StatementTmplArg::Literal(val) => Ok(Some(val.clone())),
        StatementTmplArg::WildcardLiteral(wc_val) => {
            // Note: `wc_val` represents a Value-typed wildcard.
            // It is distinct from `private_wc_being_resolved`, which is the PodId-typed wildcard
            // currently undergoing lookahead.
            if wc_val.index < outer_predicate_args_len {
                // Public value wildcard `wc_val`.
                // `public_bindings` stores arguments passed to the custom predicate as `WildcardValue`.
                // `WildcardValue` can only be `PodId` or `Key`.
                // `resolve_tmpl_arg_to_value` needs to return an `Option<Value>`.
                // A `Value` cannot be directly resolved from a `PodId` or `Key` in this context
                // if `wc_val` (a Value-typed wildcard) is expected.
                // This indicates a type mismatch in how the public argument is used or defined.
                Err(ProverError::Internal(format!(
                    "Lookahead: Cannot resolve Value-typed public argument '{}' (wc_val) from its PodId/Key representation in public_bindings for custom predicate.",
                    wc_val.name
                )))
            } else {
                // Other private value wildcard
                match state.domains.get(wc_val) {
                    Some((dom, _)) if dom.len() == 1 => match dom.iter().next().unwrap() {
                        ConcreteValue::Val(v) => Ok(Some(v.clone())),
                        _ => Err(ProverError::Internal(
                            "Lookahead: Other private Val WC type error".to_string(),
                        )),
                    },
                    _ => Err(ProverError::ProofDeferred(
                        "Lookahead: Other private Val WC not singleton".to_string(),
                    )),
                }
            }
        }
        StatementTmplArg::None => Ok(None),
    }
}

impl StatementTmplArg {
    fn get_pod_wildcard(&self) -> Option<Wildcard> {
        match self {
            StatementTmplArg::Key(wc_pod, _) => Some(wc_pod.clone()),
            _ => None,
        }
    }
}
