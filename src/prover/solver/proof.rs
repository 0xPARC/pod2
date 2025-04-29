use super::SolverState;
use crate::{
    middleware::{
        NativeOperation, NativePredicate, OperationType, Predicate, Statement, TypedValue,
    },
    prover::{
        error::ProverError,
        indexing::ProverIndexes,
        types::{CustomDefinitions, ProofChain, ProofStep},
    },
};

/// Attempts to find or generate a proof chain for a given target statement.
/// If successful, updates the solver state (proof_chains, scope) and returns the chain.
pub(super) fn try_prove_statement(
    state: &mut SolverState,
    target: &Statement,
    indexes: &ProverIndexes,
    custom_definitions: &CustomDefinitions,
) -> Result<ProofChain, ProverError> {
    // 1. Check if proof already exists
    if let Some(existing_chain) = state.proof_chains.get(target) {
        return Ok(existing_chain.clone());
    }

    // 2. Check if it's a base fact (CopyStatement)
    let target_middleware_statement = target;

    // --> ENHANCED DEBUGGING <--
    println!(
        "DEBUG CopyStatement: Target = {:?}",
        target_middleware_statement
    );
    println!(
        "DEBUG CopyStatement: Index contains = {:?}",
        indexes.exact_statement_lookup
    );

    let base_fact = indexes
        .exact_statement_lookup
        .iter()
        .find(|(_pod_id, stmt)| stmt == target_middleware_statement);

    if let Some((origin_pod_id, base_middleware_statement)) = base_fact {
        let base_statement_for_step = base_middleware_statement.clone();

        println!(
            "DEBUG: CopyStatement found base fact: {:?} for target {:?}",
            base_middleware_statement, target
        );

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

        println!(
            "Proved (CopyStatement): {:?} from Pod {} (found base fact: {:?})",
            target, origin_pod_id, base_middleware_statement
        );
        return Ok(proof_chain);
    }

    // 3. Attempt other proof methods (...FromEntries, GtToNEq, Transitive, Custom)
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
                        println!("Proved (EqualFromEntries): {:?}", target);
                        return Ok(proof_chain);
                    }
                }
                // End of EqualFromEntries attempt

                // --- START: Transitive Equality Logic ---
                // Attempt 2: If EqualFromEntries didn't work, try TransitiveEqualFromStatements
                println!("Attempting TransitiveEqualFromStatements for: {:?}", target);

                // Get the DSU representatives (find)
                // First get the internal usize indices for the keys from ProverIndexes
                let Some(idx1) = indexes.get_key_index(ak1) else {
                    println!("  - Key {:?} not found in DSU index", ak1);
                    // Fall through to final Unsatisfiable
                    return Err(ProverError::Internal(format!(
                        "Key {:?} not found in DSU index for transitive check",
                        ak1
                    ))); // Or handle more gracefully?
                };
                let Some(idx2) = indexes.get_key_index(ak2) else {
                    println!("  - Key {:?} not found in DSU index", ak2);
                    // Fall through to final Unsatisfiable
                    return Err(ProverError::Internal(format!(
                        "Key {:?} not found in DSU index for transitive check",
                        ak2
                    ))); // Or handle more gracefully?
                };

                let rep1 = indexes.dsu.find(idx1);
                let rep2 = indexes.dsu.find(idx2);

                // Optimization: If not in the same DSU set already, transitivity isn't provable this way.
                if rep1 != rep2 {
                    println!("  - DSU check failed: {:?} != {:?}", rep1, rep2);
                    // Fall through to the final Unsatisfiable error (outside this block)
                } else {
                    // Iterate through known keys as potential intermediaries (ak_mid)
                    // --- SIMPLIFIED APPROACH FOR NOW: --- Iterate through *all* keys known to the indexer
                    // TODO: Implement and use `indexes.get_keys_in_dsu_set(&rep1)` for efficiency.
                    let all_known_keys = indexes.get_all_known_keys(); // Assumes this helper exists

                    // --> ADD THIS PRINT <--
                    println!(
                        "  --> DEBUG: Keys to check as intermediate: {:?}",
                        indexes.get_all_known_keys().collect::<Vec<_>>() // Collect into a Vec
                    );

                    for ak_mid in all_known_keys {
                        // Avoid trivial cases: A = A = C or A = C = C
                        if ak_mid == ak1 || ak_mid == ak2 {
                            continue;
                        }

                        println!("  - Trying intermediate key: {:?}", ak_mid);

                        // Recursive calls: Try proving Eq(ak1, ak_mid) and Eq(ak_mid, ak2)
                        let target1_mid = Statement::Equal(ak1.clone(), ak_mid.clone());
                        let target_mid_2 = Statement::Equal(ak_mid.clone(), ak2.clone());

                        // --> DEBUG: Show the sub-targets being attempted <--
                        println!("  --> DEBUG: Attempting sub-target 1: {:?}", target1_mid);

                        // --> DEBUG: Show proof_chains state before recursive call 1 <--
                        println!(
                            "  --> DEBUG: state.proof_chains before call 1 = {:?}",
                            state.proof_chains
                        );

                        match try_prove_statement(state, &target1_mid, indexes, custom_definitions)
                        {
                            Ok(chain1) => {
                                println!("    - Proved step 1: {:?}", target1_mid);
                                // Now try the second part
                                match try_prove_statement(
                                    state,
                                    &target_mid_2,
                                    indexes,
                                    custom_definitions,
                                ) {
                                    Ok(chain2) => {
                                        println!("    - Proved step 2: {:?}", target_mid_2);
                                        // SUCCESS! Combine chains and add the transitive step.

                                        let mut combined_steps = chain1.0;
                                        combined_steps.extend(chain2.0);

                                        let transitive_step = ProofStep {
                                            operation: OperationType::Native(
                                                NativeOperation::TransitiveEqualFromStatements,
                                            ),
                                            inputs: vec![target1_mid.clone(), target_mid_2.clone()],
                                            output: target.clone(),
                                        };
                                        combined_steps.push(transitive_step);

                                        let final_chain = ProofChain(combined_steps);

                                        state
                                            .proof_chains
                                            .insert(target.clone(), final_chain.clone());

                                        // --> ADD PRINT BEFORE RETURN <--
                                        println!("  --> DEBUG: About to return Ok from Transitive");
                                        println!("Proved (TransitiveEqual): {:?}", target);
                                        return Ok(final_chain);
                                    }
                                    Err(_) => {
                                        println!("    - Failed step 2: {:?}", target_mid_2);
                                    }
                                }
                            }
                            Err(_) => {
                                // First part failed, continue search for ak_mid
                            }
                        }
                    }
                    // If loop finishes without returning, no transitive path was found.
                    println!("  - No suitable intermediate key found for transitivity.");
                }
                // --- END: Transitive Equality Logic ---
            }
        }
        Predicate::Native(NativePredicate::NotEqual) => {
            if let Statement::NotEqual(ak1, ak2) = target {
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
                        println!("Proved (NotEqualFromEntries): {:?}", target);
                        return Ok(proof_chain);
                    }
                }
            }
        }
        Predicate::Native(NativePredicate::Gt) => {
            if let Statement::Gt(ak1, ak2) = target {
                // Correctly extract and compare integers from Value -> TypedValue::Int
                if let (Some(TypedValue::Int(int1)), Some(TypedValue::Int(int2))) = (
                    indexes.get_value(ak1).map(|v| v.typed()), // Get &TypedValue
                    indexes.get_value(ak2).map(|v| v.typed()), // Get &TypedValue
                ) {
                    if int1 > int2 {
                        // Proof via GtFromEntries
                        let input1_val = indexes.get_value(ak1).unwrap().clone(); // Already checked Some
                        let input2_val = indexes.get_value(ak2).unwrap().clone();
                        let input1 = Statement::ValueOf(ak1.clone(), input1_val);
                        let input2 = Statement::ValueOf(ak2.clone(), input2_val);
                        let operation = OperationType::Native(NativeOperation::GtFromEntries);
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
                        println!("Proved (GtFromEntries): {:?}", target);
                        return Ok(proof_chain);
                    }
                }
            }
        }
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
                        println!("Proved (LtFromEntries): {:?}", target);
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
                        println!("Proved (SumOf): {:?}", target);
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
                        println!("Proved (ProductOf): {:?}", target);
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
                        println!("Proved (MaxOf): {:?}", target);
                        return Ok(proof_chain);
                    }
                }
            }
        }
        Predicate::Native(NativePredicate::Contains) => {
            // Statement::Contains takes AnchoredKeys directly
            if let Statement::Contains(container_ak, key_ak, value_ak) = target {
                if let Some(container_val) = indexes.get_value(container_ak) {
                    // Get the Value for the key_ak and value_ak
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

                    // Now proceed with the check using the resolved values
                    if let (Some(key_value), Some(target_value)) = (key_value, target_value) {
                        match container_val.prove_existence(&key_value) {
                            // Use resolved key_value
                            Ok((proven_value, _merkle_proof)) if proven_value == &target_value => {
                                // Compare resolved target_value
                                // Proof via ContainsFromEntries
                                let input_container =
                                    Statement::ValueOf(container_ak.clone(), container_val.clone());

                                // Inputs are ValueOf for container AND the resolved AKs for key/value_target
                                let mut i = vec![input_container.clone()];
                                i.extend(needed_inputs.clone()); // Adds ValueOf for key_ak and value_ak
                                let operation =
                                    OperationType::Native(NativeOperation::ContainsFromEntries);
                                let proof_step = ProofStep {
                                    operation,
                                    inputs: i,
                                    output: target.clone(),
                                };
                                let proof_chain = ProofChain(vec![proof_step]);

                                // Find origin PodId for the container ValueOf statement
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
                                // Add origins for key/value_target inputs (already in needed_inputs)
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
                                println!("Proved (ContainsFromEntries): {:?}", target);
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
                    // Get the Value for the key_ak
                    let mut needed_inputs = vec![];
                    let key_value = match indexes.get_value(key_ak) {
                        Some(v) => {
                            needed_inputs.push(Statement::ValueOf(key_ak.clone(), v.clone()));
                            Some(v.clone())
                        }
                        None => None,
                    };

                    // Now proceed with the check using the resolved key_value
                    if let Some(key_value) = key_value {
                        match container_val.prove_nonexistence(&key_value) {
                            // Use resolved key_value
                            Ok(_merkle_proof) => {
                                // Proof via NotContainsFromEntries
                                let input_container =
                                    Statement::ValueOf(container_ak.clone(), container_val.clone());

                                // Inputs are ValueOf for container AND the resolved AK for key input
                                let mut i = vec![input_container.clone()];
                                i.extend(needed_inputs.clone()); // Adds ValueOf for key_ak
                                let operation =
                                    OperationType::Native(NativeOperation::NotContainsFromEntries);
                                let proof_step = ProofStep {
                                    operation,
                                    inputs: i,
                                    output: target.clone(),
                                };
                                let proof_chain = ProofChain(vec![proof_step]);

                                // Find origin PodId for the container ValueOf statement
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
                                // Add origins for key input (already in needed_inputs)
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
                                println!("Proved (NotContainsFromEntries): {:?}", target);
                                return Ok(proof_chain);
                            }
                            Err(_) => { /* Key might exist or other error */ }
                        }
                    }
                }
            }
        }
        _ => {
            // Continue to other proof methods if applicable
        }
    }

    // If no proof method succeeds, use Unsatisfiable error
    Err(ProverError::Unsatisfiable(format!(
        "Could not find or derive proof for: {:?}",
        target
    )))
}
