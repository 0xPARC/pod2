use std::collections::HashMap;

use super::SolverState;
use crate::{
    middleware::{
        statement::{StatementArg, WildcardValue},
        AnchoredKey, CustomPredicate, CustomPredicateBatch, CustomPredicateRef, Key, KeyOrWildcard,
        NativeOperation, NativePredicate, OperationType, Predicate, Statement, StatementTmpl,
        StatementTmplArg, ToFields, TypedValue, Value, Wildcard, SELF,
    },
    prover::{
        error::ProverError,
        indexing::ProverIndexes,
        solver::build_concrete_statement,
        types::{ConcreteValue, CustomDefinitions, ProofChain, ProofStep},
    },
};

const MAX_CUSTOM_PREDICATE_RECURSION_DEPTH: usize = 20; // Define the constant

/// Attempts to find or generate a proof chain for a given target statement.
/// If successful, updates the solver state (proof_chains, scope) and returns the chain.
pub(super) fn try_prove_statement(
    state: &mut SolverState,
    target: &Statement,
    indexes: &ProverIndexes,
    custom_definitions: &CustomDefinitions,
    potential_constant_info: &[(Wildcard, Key, Value)],
    current_depth: usize, // New parameter
) -> Result<ProofChain, ProverError> {
    // Add Depth Check
    if current_depth > MAX_CUSTOM_PREDICATE_RECURSION_DEPTH {
        return Err(ProverError::MaxDepthExceeded(format!(
            "Max recursion depth ({}) exceeded while proving {:?}",
            MAX_CUSTOM_PREDICATE_RECURSION_DEPTH, target
        )));
    }

    // 1. Check if proof already exists
    if let Some(existing_chain) = state.proof_chains.get(target) {
        return Ok(existing_chain.clone());
    }

    // --- Check for potential SELF constant generation (for ValueOf) ---
    if let Statement::ValueOf(target_ak, target_value) = target {
        // Check if this (key, value) pair corresponds to a potential constant
        if let Some((holder_wc, const_key, _value)) = potential_constant_info
            .iter()
            // Find the entry matching the target key and value
            .find(|(_, k, v)| k == &target_ak.key && v == target_value)
        {
            // Check if the holder domain allows SELF
            if state
                .domains
                .get(holder_wc)
                .is_some_and(|(dom, _)| dom.contains(&ConcreteValue::Pod(SELF)))
            {
                // Prefer generating this constant via NewEntry for SELF

                // IMPORTANT: Create the output statement with SELF pod_id
                let self_output_ak = AnchoredKey::new(SELF, const_key.clone());
                let self_output_stmt = Statement::ValueOf(self_output_ak, target_value.clone());

                let proof_step = ProofStep {
                    operation: OperationType::Native(NativeOperation::NewEntry),
                    inputs: vec![], // NewEntry has no statement inputs
                    output: self_output_stmt.clone(), // Output is ValueOf(SELF, ...)
                };
                let proof_chain = ProofChain(vec![proof_step]);

                // Add to proof chains (use the SELF version as the key)
                state
                    .proof_chains
                    .insert(self_output_stmt.clone(), proof_chain.clone());

                // Note: We don't add to scope here, as NewEntry doesn't consume base facts.
                // The pod_building stage will handle adding the actual NewEntry op.

                // Crucially, return success *even if the original target had a different pod_id*.
                // The solver might have requested ValueOf(ExternalPod[const_key], val) but we satisfy it
                // via ValueOf(SELF[const_key], val). The binding/pruning logic should handle this.
                // TODO: Revisit if this interaction causes issues with binding/pruning.
                // println!("Proving ValueOf via SELF NewEntry: {:?}", self_output_stmt);
                return Ok(proof_chain);
            }
        }
    }
    // --- End SELF Check ---

    // 2. Check if it's a base fact (CopyStatement)
    let target_middleware_statement = target;

    let base_fact = indexes
        .exact_statement_lookup
        .iter()
        .find(|(_pod_id, stmt)| stmt == target_middleware_statement);

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

    // 3. Attempt other proof methods (FromEntries, Transitive, Custom, etc.)
    match target.predicate() {
        Predicate::Native(NativePredicate::Equal) => {
            if let Statement::Equal(ak1, ak2) = target {
                // Attempt 1: Prove via EqualFromEntries
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
                // End of EqualFromEntries attempt

                // --- Transitive Equality Logic ---
                // Attempt 2: Prove via TransitiveEqualFromStatements

                // Get DSU IDs, requires keys to be indexed
                let maybe_id1 = indexes.get_key_index(ak1);
                let maybe_id2 = indexes.get_key_index(ak2);

                if let (Some(id1), Some(id2)) = (maybe_id1, maybe_id2) {
                    let rep1 = indexes.dsu.find(id1);
                    let rep2 = indexes.dsu.find(id2);

                    // Optimization: If not in the same DSU set already, transitivity isn't provable this way.
                    if rep1 != rep2 {
                        // Note: This path is hit BEFORE the generic fallback error at the end.
                        return Err(ProverError::Unsatisfiable(format!(
                            "Cannot prove Equal({:?}, {:?}) transitively: not in same DSU set (roots: {}, {})",
                            ak1, ak2, rep1, rep2
                        )));
                    } else {
                        // Iterate through known keys as potential intermediaries (ak_mid)
                        let all_known_keys = indexes.get_all_known_keys();

                        for ak_mid in all_known_keys {
                            // Avoid trivial cases: A = A = C or A = C = C
                            if ak_mid == ak1 || ak_mid == ak2 {
                                continue;
                            }

                            // Ensure the intermediate key is also indexed before proceeding
                            if indexes.get_key_index(ak_mid).is_none() {
                                continue;
                            }

                            // Recursive calls: Try proving Eq(ak1, ak_mid) and Eq(ak_mid, ak2)
                            let target1_mid = Statement::Equal(ak1.clone(), ak_mid.clone());
                            let target_mid_2 = Statement::Equal(ak_mid.clone(), ak2.clone());

                            // Use temporary state clones or a more sophisticated recursive strategy
                            // if state modification during recursion is problematic. For now, assume
                            // try_prove_statement correctly handles caching or avoids bad state.
                            match try_prove_statement(
                                state,
                                &target1_mid,
                                indexes,
                                custom_definitions,
                                &[],               // Pass empty potential_constant_info
                                current_depth + 1, // Increment depth
                            ) {
                                Ok(chain1) => {
                                    // Now try the second part
                                    match try_prove_statement(
                                        state,
                                        &target_mid_2,
                                        indexes,
                                        custom_definitions,
                                        &[],               // Pass empty potential_constant_info
                                        current_depth + 1, // Increment depth
                                    ) {
                                        Ok(chain2) => {
                                            // Found transitive path: A=Mid and Mid=C
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
                                            // This branch failed due to depth, try the next one. Log the error.
                                            println!(
                                                "Sub-proof for AND branch sub-statement {:?} failed due to max depth (depth {}): {}",
                                                target_mid_2, current_depth + 1, msg
                                            );
                                            return Err(ProverError::MaxDepthExceeded(msg));
                                        }
                                        Err(e) => {
                                            // Second part Eq(Mid, C) failed, continue search for ak_mid
                                        }
                                    }
                                }
                                Err(ProverError::MaxDepthExceeded(msg)) => {
                                    // This branch failed due to depth, try the next one. Log the error.
                                    println!(
                                        "Sub-proof for AND branch sub-statement {:?} failed due to max depth (depth {}): {}",
                                        target1_mid, current_depth + 1, msg
                                    );
                                    return Err(ProverError::MaxDepthExceeded(msg));
                                }
                                Err(e) => {
                                    // First part Eq(A, Mid) failed, continue search for ak_mid
                                }
                            }
                        }
                        // If loop finishes, no transitive path found via this method.
                        // Fall through to the generic Unsatisfiable error.
                    }
                } else {
                    // If either key wasn't indexed, transitive proof via DSU/iteration is not possible.
                    // Fall through to the generic Unsatisfiable error.
                    println!("Skipping transitive check for Equal({:?}, {:?}) as one or both keys not indexed.", ak1, ak2);
                }
                // --- END Transitive Equality Logic ---
            }
        }
        Predicate::Native(NativePredicate::NotEqual) => {
            if let Statement::NotEqual(ak1, ak2) = target {
                // Attempt 1: Prove via NotEqualFromEntries
                if let (Some(v1), Some(v2)) = (indexes.get_value(ak1), indexes.get_value(ak2)) {
                    if v1 != v2 {
                        // Proof via NotEqualFromEntries
                        let input1 = Statement::ValueOf(ak1.clone(), v1.clone());
                        let input2 = Statement::ValueOf(ak2.clone(), v2.clone());
                        let operation = OperationType::Native(NativeOperation::NotEqualFromEntries);
                        let proof_step = ProofStep {
                            operation,
                            inputs: vec![input1.clone(), input2.clone()],
                            output: target.clone(),
                        };
                        let proof_chain = ProofChain(vec![proof_step]);

                        // Find origin PodIds for ValueOf statements
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
                    // If v1 == v2, NotEqualFromEntries fails, continue to other methods.
                }
                // End of NotEqualFromEntries attempt

                // // --- GtToNotEqual / LtToNotEqual Logic ---
                // // Attempt 2: Prove via GtToNotEqual (A > B implies A != B)
                // let target_gt1 = Statement::Gt(ak1.clone(), ak2.clone());
                // let target_gt2 = Statement::Gt(ak2.clone(), ak1.clone()); // Check both directions

                // if let Ok(gt_chain1) = try_prove_statement(
                //     state,
                //     &target_gt1,
                //     indexes,
                //     custom_definitions,
                //     &[], // Pass empty
                //     current_depth + 1, // Increment depth
                // ) {
                //     let mut combined_steps = gt_chain1.0;
                //     let neq_step = ProofStep {
                //         operation: OperationType::Native(NativeOperation::GtToNotEqual),
                //         inputs: vec![target_gt1.clone()],
                //         output: target.clone(),
                //     };
                //     combined_steps.push(neq_step);
                //     let final_chain = ProofChain(combined_steps);
                //     state
                //         .proof_chains
                //         .insert(target.clone(), final_chain.clone());
                //     return Ok(final_chain);
                // }

                // // Try proving Gt(ak2, ak1)
                // if let Ok(gt_chain2) = try_prove_statement(
                //     state,
                //     &target_gt2,
                //     indexes,
                //     custom_definitions,
                //     &[], // Pass empty
                //     current_depth + 1, // Increment depth
                // ) {
                //     let mut combined_steps = gt_chain2.0;
                //     let neq_step = ProofStep {
                //         operation: OperationType::Native(NativeOperation::GtToNotEqual),
                //         inputs: vec![target_gt2.clone()],
                //         output: target.clone(),
                //     };
                //     combined_steps.push(neq_step);
                //     let final_chain = ProofChain(combined_steps);
                //     state
                //         .proof_chains
                //         .insert(target.clone(), final_chain.clone());
                //     return Ok(final_chain);
                // }

                // Attempt 3: Prove via LtToNotEqual
                let target_lt1 = Statement::Lt(ak1.clone(), ak2.clone());
                let target_lt2 = Statement::Lt(ak2.clone(), ak1.clone()); // Check both directions

                // Try proving Lt(ak1, ak2)
                if let Ok(lt_chain1) = try_prove_statement(
                    state,
                    &target_lt1,
                    indexes,
                    custom_definitions,
                    &[],               // Pass empty
                    current_depth + 1, // Increment depth
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

                // Try proving Lt(ak2, ak1)
                if let Ok(lt_chain2) = try_prove_statement(
                    state,
                    &target_lt2,
                    indexes,
                    custom_definitions,
                    &[],               // Pass empty
                    current_depth + 1, // Increment depth
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
                // --- END GtToNotEqual / LtToNotEqual Logic ---
            }
        }
        // Predicate::Native(NativePredicate::Gt) => {
        //     if let Statement::Gt(ak1, ak2) = target {
        //         // Correctly extract and compare integers from Value -> TypedValue::Int
        //         if let (Some(TypedValue::Int(int1)), Some(TypedValue::Int(int2))) = (
        //             indexes.get_value(ak1).map(|v| v.typed()), // Get &TypedValue
        //             indexes.get_value(ak2).map(|v| v.typed()), // Get &TypedValue
        //         ) {
        //             if int1 > int2 {
        //                 // Proof via GtFromEntries
        //                 let input1_val = indexes.get_value(ak1).unwrap().clone(); // Already checked Some
        //                 let input2_val = indexes.get_value(ak2).unwrap().clone();
        //                 let input1 = Statement::ValueOf(ak1.clone(), input1_val);
        //                 let input2 = Statement::ValueOf(ak2.clone(), input2_val);
        //                 let operation = OperationType::Native(NativeOperation::GtFromEntries);
        //                 let proof_step = ProofStep {
        //                     operation,
        //                     inputs: vec![input1.clone(), input2.clone()],
        //                     output: target.clone(),
        //                 };
        //                 let proof_chain = ProofChain(vec![proof_step]);

        //                 // Find origin PodIds for ValueOf statements
        //                 if let Some((pod_id1, _)) = indexes
        //                     .exact_statement_lookup
        //                     .iter()
        //                     .find(|(_, stmt)| stmt == &input1)
        //                 {
        //                     state.scope.insert((*pod_id1, input1));
        //                 } else {
        //                     return Err(ProverError::Internal(format!(
        //                         "Could not find origin Pod for ValueOf: {:?}",
        //                         input1
        //                     )));
        //                 }
        //                 if let Some((pod_id2, _)) = indexes
        //                     .exact_statement_lookup
        //                     .iter()
        //                     .find(|(_, stmt)| stmt == &input2)
        //                 {
        //                     state.scope.insert((*pod_id2, input2));
        //                 } else {
        //                     return Err(ProverError::Internal(format!(
        //                         "Could not find origin Pod for ValueOf: {:?}",
        //                         input2
        //                     )));
        //                 }

        //                 state
        //                     .proof_chains
        //                     .insert(target.clone(), proof_chain.clone());
        //                 return Ok(proof_chain);
        //             }
        //         }
        //     }
        // }
        Predicate::Native(NativePredicate::Lt) => {
            if let Statement::Lt(ak1, ak2) = target {
                // Correctly extract and compare integers from Value -> TypedValue::Int
                if let (Some(TypedValue::Int(int1)), Some(TypedValue::Int(int2))) = (
                    indexes.get_value(ak1).map(|v| v.typed()), // Get &TypedValue
                    indexes.get_value(ak2).map(|v| v.typed()), // Get &TypedValue
                ) {
                    if int1 < int2 {
                        // Proof via LtFromEntries
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

                        // Find origin PodIds for ValueOf statements
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
                        // Proof via SumOf (from entries implicitly)
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

                        // Find origin PodIds
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
                        // Proof via ProductOf
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

                        // Find origin PodIds
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
                        // Proof via MaxOf
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

                        // Find origin PodIds
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
            // Statement::Contains takes AnchoredKeys directly
            if let Statement::Contains(container_ak, key_ak, value_ak) = target {
                if let Some(container_val) = indexes.get_value(container_ak) {
                    let mut needed_inputs = vec![];
                    let key_value = match indexes.get_value(key_ak) {
                        Some(v) => {
                            needed_inputs.push(Statement::ValueOf(key_ak.clone(), v.clone()));
                            Some(v.clone())
                        }
                        None => None,
                    };
                    let target_value = match indexes.get_value(value_ak) {
                        Some(v) => {
                            needed_inputs.push(Statement::ValueOf(value_ak.clone(), v.clone()));
                            Some(v.clone())
                        }
                        None => None,
                    };

                    if let (Some(key_value), Some(target_value)) = (key_value, target_value) {
                        match container_val.prove_existence(&key_value) {
                            Ok((proven_value, _merkle_proof)) if proven_value == &target_value => {
                                let input_container =
                                    Statement::ValueOf(container_ak.clone(), container_val.clone());

                                // Inputs: ValueOf(container), plus ValueOf(key) and ValueOf(value) if resolved
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
                                // Add origins for key/value_target inputs
                                for input_stmt in needed_inputs {
                                    if let Some((pod_id, _)) = indexes
                                        .exact_statement_lookup
                                        .iter()
                                        .find(|(_, stmt)| stmt == &input_stmt)
                                    {
                                        state.scope.insert((*pod_id, input_stmt));
                                    } else {
                                        // This should ideally not happen if get_value succeeded earlier
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
                            Ok(_) => { /* Value exists but doesn't match target */ }
                            Err(_) => { /* Key does not exist or other error */ }
                        }
                    }
                }
            }
        }
        Predicate::Native(NativePredicate::NotContains) => {
            // Statement::NotContains takes AnchoredKeys directly
            if let Statement::NotContains(container_ak, key_ak) = target {
                if let Some(container_val) = indexes.get_value(container_ak) {
                    let mut needed_inputs = vec![];
                    let key_value = match indexes.get_value(key_ak) {
                        Some(v) => {
                            needed_inputs.push(Statement::ValueOf(key_ak.clone(), v.clone()));
                            Some(v.clone())
                        }
                        None => None,
                    };

                    if let Some(key_value) = key_value {
                        match container_val.prove_nonexistence(&key_value) {
                            Ok(_merkle_proof) => {
                                let input_container =
                                    Statement::ValueOf(container_ak.clone(), container_val.clone());

                                // Inputs: ValueOf(container) and ValueOf(key)
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
                                // Add origins for key input
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
                            Err(_) => { /* Key might exist or other error */ }
                        }
                    }
                }
            }
        }
        // --- START: Custom Predicate Logic ---
        Predicate::Custom(custom_ref) => {
            if let Statement::Custom(target_custom_ref, concrete_args) = target {
                if custom_ref != *target_custom_ref {
                    return Err(ProverError::Internal(
                        "Predicate mismatch in custom proof logic".to_string(),
                    ));
                }

                // 1. Lookup definition and batch Arc
                let pred_key = Predicate::Custom(custom_ref.clone()).to_fields(&state.params);
                if let Some((pred_def, batch_arc)) = custom_definitions.get(&pred_key) {
                    // 2. Check conjunction (handle AND first)
                    if pred_def.conjunction {
                        // --- AND Logic ---
                        let mut combined_steps = Vec::new();
                        let mut sub_statement_inputs = Vec::new();
                        let mut succeeded = true;

                        // Build public bindings map (index -> value)
                        // Assuming for now that `concrete_args` aligns positionally with public wildcards (index 0 to args_len-1).
                        let public_bindings: HashMap<usize, WildcardValue> =
                            concrete_args.iter().cloned().enumerate().collect();

                        // 3. Iterate through internal templates
                        for internal_tmpl in &pred_def.statements {
                            // 4. Determine concrete sub-statement (Si)
                            let concrete_sub_stmt = match build_concrete_statement_from_bindings(
                                internal_tmpl,
                                concrete_args,
                                &public_bindings,
                                state,
                                Some((pred_def, batch_arc.clone())),
                                current_depth + 1, // Increment depth
                            ) {
                                Ok(stmt) => stmt,
                                Err(e @ ProverError::Unsatisfiable(_)) => {
                                    // If a private wildcard wasn't singleton, this specific path fails
                                    println!("Failed to build concrete sub-statement due to non-singleton private wildcard: {:?}", e);
                                    succeeded = false;
                                    break; // Cannot prove this AND branch
                                }
                                Err(e) => return Err(e), // Propagate other errors
                            };

                            sub_statement_inputs.push(concrete_sub_stmt.clone()); // Collect for final step

                            // 5. Recursively call try_prove_statement(Si)
                            match try_prove_statement(
                                state,
                                &concrete_sub_stmt,
                                indexes,
                                custom_definitions,
                                &[],               // Pass empty potential_constant_info
                                current_depth + 1, // Increment depth
                            ) {
                                Ok(sub_chain) => {
                                    combined_steps.extend(sub_chain.0);
                                }
                                Err(ProverError::MaxDepthExceeded(msg)) => {
                                    // This branch failed due to depth, try the next one. Log the error.
                                    println!(
                                        "Sub-proof for AND branch sub-statement {:?} failed due to max depth (depth {}): {}",
                                        concrete_sub_stmt, current_depth + 1, msg
                                    );
                                    return Err(ProverError::MaxDepthExceeded(msg));
                                }
                                Err(e) => {
                                    // If any sub-proof fails in an AND, the whole thing fails.
                                    // Propagate the specific error from the sub-proof directly.
                                    println!(
                                        "Failed recursive proof for sub-statement {:?}: {:?}. Failing AND predicate.",
                                        concrete_sub_stmt, e
                                    );
                                    // Return the error immediately
                                    return Err(e);
                                }
                            }
                        }

                        // 6. Combine chains and add final step (if all sub-proofs succeeded)
                        if succeeded {
                            let final_custom_step = ProofStep {
                                operation: OperationType::Custom(custom_ref.clone()),
                                inputs: sub_statement_inputs, // The concrete sub-statements
                                output: target.clone(),
                            };
                            combined_steps.push(final_custom_step);

                            let final_chain = ProofChain(combined_steps);
                            state
                                .proof_chains
                                .insert(target.clone(), final_chain.clone());
                            return Ok(final_chain);
                        }
                        // If !succeeded, fall through to generic unsatisfiable error
                    } else {
                        // --- OR Logic ---
                        let public_bindings: HashMap<usize, WildcardValue> =
                            concrete_args.iter().cloned().enumerate().collect();

                        for internal_tmpl in &pred_def.statements {
                            // Try to build concrete sub-statement for this branch
                            let concrete_sub_stmt_res = build_concrete_statement_from_bindings(
                                internal_tmpl,
                                concrete_args,
                                &public_bindings,
                                state,
                                Some((pred_def, batch_arc.clone())),
                                current_depth + 1, // Increment depth
                            );

                            if let Ok(concrete_sub_stmt) = concrete_sub_stmt_res {
                                // Attempt to prove this branch's sub-statement
                                match try_prove_statement(
                                    state,
                                    &concrete_sub_stmt,
                                    indexes,
                                    custom_definitions,
                                    &[],               // Pass empty potential_constant_info
                                    current_depth + 1, // Increment depth
                                ) {
                                    Ok(sub_chain) => {
                                        // SUCCESS! First successful branch wins.
                                        let mut combined_steps = sub_chain.0;
                                        let final_custom_step = ProofStep {
                                            operation: OperationType::Custom(custom_ref.clone()),
                                            inputs: vec![concrete_sub_stmt.clone()], // Input is the successfully proven sub-statement
                                            output: target.clone(),
                                        };
                                        combined_steps.push(final_custom_step);

                                        let final_chain = ProofChain(combined_steps);
                                        state
                                            .proof_chains
                                            .insert(target.clone(), final_chain.clone());
                                        return Ok(final_chain);
                                    }
                                    Err(ProverError::MaxDepthExceeded(msg)) => {
                                        // This branch failed due to depth, try the next one. Log the error.
                                        println!(
                                            "OR branch failed for sub-statement {:?} due to max depth (depth {}): {}. Trying next branch.",
                                            concrete_sub_stmt, current_depth + 1, msg
                                        );
                                        // No return Err here, just continue to next iteration of OR loop
                                    }
                                    Err(e) => {
                                        // This branch failed for other reasons, try the next one. Log the error.
                                        println!(
                                            "OR branch failed for sub-statement {:?}: {:?}",
                                            concrete_sub_stmt, e
                                        );
                                    }
                                }
                            } else {
                                // Failed to build concrete statement for this branch (e.g., private WC not singleton). Try next branch.
                                println!("OR branch failed to build concrete sub-statement from template {:?}: {:?}", internal_tmpl, concrete_sub_stmt_res.err());
                            }
                        }
                        // If loop finishes, no OR branch succeeded. Fall through to generic unsatisfiable error.
                        println!(
                            "All OR branches failed for custom predicate: {:?}",
                            custom_ref
                        );
                    }
                } else {
                    return Err(ProverError::Internal(format!(
                        "Custom predicate definition not found for ref: {:?}",
                        custom_ref
                    )));
                }
            }
        }
        // --- END: Custom Predicate Logic ---
        _ => {
            // Continue to other proof methods if applicable (already handled above)
        }
    }

    // If no proof method succeeds, use Unsatisfiable error
    Err(ProverError::Unsatisfiable(format!(
        "Could not find or derive proof for: {:?}",
        target
    )))
}

// Helper function to build a concrete statement from a template and bindings
// This needs access to the full solver state for private wildcards.
fn build_concrete_statement_from_bindings(
    tmpl: &StatementTmpl,
    _public_args: &[WildcardValue], // Values provided to the target Custom statement (Might not be needed directly here)
    // Map from public WC index to its concrete value from target statement
    public_bindings: &HashMap<usize, WildcardValue>,
    // Full solver state for private wildcard resolution
    state: &SolverState,
    // Context: The predicate definition and batch Arc containing this template
    outer_context: Option<(&CustomPredicate, std::sync::Arc<CustomPredicateBatch>)>,
    current_depth: usize, // New parameter
) -> Result<Statement, ProverError> {
    let outer_args_len = outer_context.as_ref().map(|(def, _)| def.args_len);

    match &tmpl.pred {
        Predicate::Native(_) => {
            // --- Build args for Native Predicates ---
            let mut concrete_args = Vec::with_capacity(tmpl.args.len());
            for arg_tmpl in &tmpl.args {
                match arg_tmpl {
                    StatementTmplArg::Key(wc_pod, key_or_wc) => {
                        let pod_id = match outer_args_len {
                            Some(args_len) if wc_pod.index < args_len => {
                                // Public WC
                                match public_bindings.get(&wc_pod.index) {
                                    Some(WildcardValue::PodId(id)) => *id,
                                    _ => {
                                        return Err(ProverError::Internal(format!(
                                            "Missing/wrong public binding for Pod WC {}",
                                            wc_pod
                                        )))
                                    }
                                }
                            }
                            Some(_) | None => {
                                // Private WC or no outer context (should be private)
                                match state.domains.get(wc_pod) {
                                    Some((domain, _)) if domain.len() == 1 => {
                                        match domain.iter().next().unwrap() {
                                            ConcreteValue::Pod(id) => *id,
                                            _ => return Err(ProverError::Internal(format!(
                                                    "Private Pod WC {} domain wrong type", wc_pod
                                            )))
                                        }
                                    }
                                    _ => return Err(ProverError::Unsatisfiable(format!(
                                            "Private Pod WC {} domain not singleton or outer context missing", wc_pod
                                    )))
                                }
                            }
                        };
                        let key = match key_or_wc {
                            KeyOrWildcard::Key(k) => k.clone(),
                            KeyOrWildcard::Wildcard(wc_key) => {
                                match outer_args_len {
                                    Some(args_len) if wc_key.index < args_len => {
                                        // Public WC
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
                                        // Private WC or no outer context
                                        match state.domains.get(wc_key) {
                                            Some((domain, _)) if domain.len() == 1 => {
                                                match domain.iter().next().unwrap() {
                                                     ConcreteValue::Key(k_name) => {
                                                         Key::new(k_name.clone())
                                                     }
                                                     _ => return Err(ProverError::Internal(format!(
                                                             "Private Key WC {} domain wrong type", wc_key
                                                     )))
                                                }
                                            }
                                            _ => return Err(ProverError::Unsatisfiable(format!(
                                                     "Private Key WC {} domain not singleton or outer context missing", wc_key
                                            )))
                                        }
                                    }
                                }
                            }
                        };
                        concrete_args.push(StatementArg::Key(AnchoredKey::new(pod_id, key)));
                    }
                    StatementTmplArg::WildcardLiteral(wc_val) => {
                        // This arm is for resolving PRIVATE value wildcards for native predicates
                        match outer_args_len {
                            Some(args_len) if wc_val.index < args_len => {
                                return Err(ProverError::Internal(format!(
                                    "Invalid Use: StatementTmplArg::WildcardLiteral ({}) used for public index in native predicate template.",
                                    wc_val
                                )));
                            }
                            Some(_) | None => {
                                // Private WC or no outer context
                                let value = match state.domains.get(wc_val) {
                                    Some((domain, _)) if domain.len() == 1 => {
                                        match domain.iter().next().unwrap() {
                                            ConcreteValue::Val(v) => v.clone(),
                                            _ => return Err(ProverError::Internal(format!(
                                                    "Private Value WC {} domain wrong type", wc_val
                                            )))
                                        }
                                    }
                                     _ => return Err(ProverError::Unsatisfiable(format!(
                                             "Private Value WC {} domain not singleton or outer context missing", wc_val
                                     )))
                                };
                                concrete_args.push(StatementArg::Literal(value));
                            }
                        }
                    }
                    StatementTmplArg::Literal(v) => {
                        concrete_args.push(StatementArg::Literal(v.clone()));
                    }
                    StatementTmplArg::None => {}
                }
            }
            build_concrete_statement(tmpl.pred.clone(), concrete_args)
        }
        Predicate::Custom(custom_ref) => {
            // --- Build args for Nested Custom Predicate Call ---
            let current_outer_args_len = outer_context.as_ref().map(|(def, _)| def.args_len);
            let mut nested_call_args: Vec<WildcardValue> = Vec::with_capacity(tmpl.args.len());

            for arg_tmpl in &tmpl.args {
                // Resolve the wildcard used in the argument template based on the *current* context
                let resolved_wc_value = match arg_tmpl {
                    StatementTmplArg::WildcardLiteral(wc) => {
                         // Resolve the wildcard (could be public or private in the *outer* scope)
                         match current_outer_args_len {
                              Some(args_len) if wc.index < args_len => { // Public in outer scope
                                  public_bindings.get(&wc.index).cloned().ok_or_else(|| ProverError::Internal(format!(
                                      "Missing public binding for WC {} needed for nested call arg", wc
                                  )))?
                              }
                              Some(_) | None => { // Private in outer scope or no outer context
                                  match state.domains.get(wc) {
                                      Some((domain, _)) if domain.len() == 1 => match domain.iter().next().unwrap() {
                                          ConcreteValue::Pod(id) => WildcardValue::PodId(*id),
                                          ConcreteValue::Key(k_name) => WildcardValue::Key(Key::new(k_name.clone())),
                                          ConcreteValue::Val(_) => return Err(ProverError::Internal(format!(
                                              "Cannot pass Value type via WildcardLiteral to nested custom predicate for WC {}", wc
                                          )))
                                      },
                                      _ => return Err(ProverError::Unsatisfiable(format!(
                                          "Private WC {} for nested call arg not singleton or outer context missing", wc
                                      )))
                                  }
                              }
                         }
                    }
                    _ => return Err(ProverError::Internal(format!(
                        "Unsupported argument type {:?} used when calling nested custom predicate in template", arg_tmpl
                    )))
                };
                nested_call_args.push(resolved_wc_value);
            }

            // Check if args length matches the *nested* predicate being called
            let nested_pred_def = custom_ref
                .batch
                .predicates
                .get(custom_ref.index)
                .ok_or_else(|| {
                    ProverError::Internal(format!(
                        "Custom ref index {} out of bounds for batch '{}'",
                        custom_ref.index, custom_ref.batch.name
                    ))
                })?;
            if nested_call_args.len() != nested_pred_def.args_len {
                return Err(ProverError::Internal(format!(
                    "Argument length mismatch calling Custom predicate '{}'. Template provided {} args, but predicate requires {}.",
                     nested_pred_def.name, nested_call_args.len(), nested_pred_def.args_len
                 )));
            }

            // For Predicate::Custom, the concrete CustomPredicateRef is the one from the template.
            Ok(Statement::Custom(custom_ref.clone(), nested_call_args))
        }
        Predicate::BatchSelf(idx) => {
            // --- Build args for Nested BatchSelf Predicate Call --- (Modified logic)
            let current_outer_args_len = outer_context.as_ref().map(|(def, _)| def.args_len);
            let mut nested_call_args: Vec<WildcardValue> = Vec::with_capacity(tmpl.args.len());

            for arg_tmpl in &tmpl.args {
                // Resolve the wildcard used in the argument template based on the *current* context
                // (Same logic as in the Predicate::Custom arm above)
                let resolved_wc_value = match arg_tmpl {
                    StatementTmplArg::WildcardLiteral(wc) => {
                         match current_outer_args_len {
                             Some(args_len) if wc.index < args_len => { // Public in outer scope
                                 public_bindings.get(&wc.index).cloned().ok_or_else(|| ProverError::Internal(format!(
                                     "Missing public binding for WC {} needed for nested call arg", wc
                                 )))?
                             }
                             Some(_) | None => { // Private in outer scope or no outer context
                                 match state.domains.get(wc) {
                                     Some((domain, _)) if domain.len() == 1 => match domain.iter().next().unwrap() {
                                         ConcreteValue::Pod(id) => WildcardValue::PodId(*id),
                                         ConcreteValue::Key(k_name) => WildcardValue::Key(Key::new(k_name.clone())),
                                         ConcreteValue::Val(_) => return Err(ProverError::Internal(format!(
                                             "Cannot pass Value type via WildcardLiteral to nested custom predicate for WC {}", wc
                                         )))
                                     },
                                     _ => return Err(ProverError::Unsatisfiable(format!(
                                         "Private WC {} for nested call arg not singleton or outer context missing", wc
                                     )))
                                 }
                             }
                         }
                    }
                    _ => return Err(ProverError::Internal(format!(
                        "Unsupported argument type {:?} used when calling nested custom predicate in template", arg_tmpl
                    )))
                };
                nested_call_args.push(resolved_wc_value);
            }

            // Determine the correct CustomPredicateRef for the concrete BatchSelf statement
            let (_outer_pred_def, batch_arc) = outer_context.ok_or_else(|| {
                ProverError::Internal(
                    "Missing outer context needed to resolve BatchSelf predicate in template"
                        .to_string(),
                )
            })?;

            let concrete_custom_ref = CustomPredicateRef {
                batch: batch_arc.clone(), // Use the Arc from the context
                index: *idx,
            };

            let resolved_pred_def = batch_arc.predicates.get(*idx).ok_or_else(|| {
                ProverError::Internal(format!(
                    "BatchSelf index {} out of bounds for batch '{}'",
                    idx, batch_arc.name
                ))
            })?;
            if nested_call_args.len() != resolved_pred_def.args_len {
                return Err(ProverError::Internal(format!(
                    "Argument length mismatch when resolving BatchSelf({}). Template provided {} args, but predicate '{}' requires {}.",
                     idx, nested_call_args.len(), resolved_pred_def.name, resolved_pred_def.args_len
                 )));
            }

            // Note: The concrete *Statement* is still Statement::Custom, even if the template used BatchSelf
            Ok(Statement::Custom(concrete_custom_ref, nested_call_args))
        }
    }
}
