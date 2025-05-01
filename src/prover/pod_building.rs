use std::{
    collections::{HashMap, HashSet},
    sync::Arc, // Import Arc
};

use crate::{
    frontend::{
        self, MainPodBuilder, Operation as FrontendOperation, SignedPod as FrontendSignedPod,
    },
    middleware::{self, OperationAux, OperationType, Pod, PodId, Statement},
    prover::{
        error::ProverError,
        types::{ProofSolution, ProofStep},
    },
};

/// Builds a frontend::MainPod from a successfully solved ProofSolution.
///
/// # Arguments
///
/// * `solution` - The ProofSolution containing bindings, scope, and proof chains.
/// * `original_signed_pods` - Map from PodId to original SignedPod objects.
/// * `original_main_pods` - Map from PodId to original MainPod objects.
/// * `params` - Middleware parameters.
///
/// # Returns
///
/// A Result containing the built frontend::MainPod or a ProverError.
pub fn build_main_pod_from_solution(
    solution: &ProofSolution,
    original_signed_pods: &HashMap<PodId, Arc<FrontendSignedPod>>,
    original_main_pods: &HashMap<PodId, Arc<frontend::MainPod>>,
    params: &middleware::Params,
) -> Result<frontend::MainPod, ProverError> {
    println!("Building MainPod from solution...");

    let mut builder = MainPodBuilder::new(params);

    // 1. Add references to input PODs based on the scope
    let mut referenced_pod_ids = HashSet::new();
    for (pod_id, _) in &solution.scope {
        if referenced_pod_ids.insert(*pod_id) {
            // Check if it's a known SignedPod
            if let Some(signed_pod_arc) = original_signed_pods.get(pod_id) {
                // Pass the actual SignedPod reference
                builder.add_signed_pod(signed_pod_arc);
                println!("  Added reference for SignedPod: {:?}", pod_id);
            } else if let Some(main_pod_arc) = original_main_pods.get(pod_id) {
                // Pass the actual MainPod reference
                builder.add_main_pod(main_pod_arc.as_ref().clone()); // Clone the MainPod if needed by builder
                println!("  Added reference for MainPod: {:?}", pod_id);
            } else {
                // This indicates an inconsistency: a PodId from the scope wasn't in either input map
                return Err(ProverError::Internal(format!(
                    "Original pod not found for ID required by scope: {:?}",
                    pod_id
                )));
            }
        }
    }
    // TODO: Check if SELF needs explicit reference

    // 2. Translate ProofChain steps and add operations to builder
    let mut generated_statements = HashSet::new();

    // TODO: Determine correct order of processing steps (e.g., topological sort)
    // For now, iterate through chains, hoping dependencies are met.
    for chain in solution.proof_chains.values() {
        for step in &chain.0 {
            if generated_statements.contains(&step.output) {
                continue; // Already generated this statement
            }

            let (op_type, op_args) = translate_step_to_frontend_op_args(step)?;

            let frontend_op = FrontendOperation(op_type, op_args, OperationAux::None);

            // Determine if the output statement is a final target
            let is_public = solution.proof_chains.contains_key(&step.output);

            println!(
                "  Adding Op (public={}): {:?} -> {:?}",
                is_public, frontend_op, step.output
            );
            // Use pub_op or priv_op based on whether the output is a target statement
            let _generated_statement = if is_public {
                builder.pub_op(frontend_op)?
            } else {
                builder.priv_op(frontend_op)?
            };
            // We might want to verify that _generated_statement == step.output

            generated_statements.insert(step.output.clone());
        }
    }

    // 3. Mark public statements (REMOVED - handled by builder.op)

    // 4. Invoke the backend prover
    println!("Invoking backend prover...");
    // TODO: Use the actual prover instance passed in or created
    let mut prover = crate::backends::plonky2::mock::mainpod::MockProver {}; // Example
    builder
        .prove(&mut prover, params)
        .map_err(ProverError::FrontendError) // Use From trait via variant name
}

/// Helper function to translate a prover::ProofStep into the components
/// needed for a frontend::Operation (op_type, Vec<OperationArg>).
fn translate_step_to_frontend_op_args(
    step: &ProofStep,
) -> Result<(middleware::OperationType, Vec<frontend::OperationArg>), ProverError> {
    // Map the prover OperationType to the middleware OperationType
    let op_type = match &step.operation {
        // Use middleware::OperationType which should be public
        OperationType::Native(native_op) => middleware::OperationType::Native(*native_op),
        OperationType::Custom(custom_ref) => middleware::OperationType::Custom(custom_ref.clone()),
    };

    // Map Vec<middleware::Statement> inputs to Vec<frontend::OperationArg>
    let op_args: Vec<frontend::OperationArg> = step
        .inputs
        .iter()
        .map(|stmt| frontend::OperationArg::Statement(stmt.clone())) // Clone statement
        .collect();

    // OperationAux is handled by the builder's op/pub_op/priv_op methods.
    Ok((op_type, op_args))
}

#[cfg(test)]
mod tests {
    use std::{collections::HashMap, sync::Arc};

    use super::*;
    use crate::{
        backends::plonky2::mock::{mainpod::MockProver, signedpod::MockSigner},
        frontend::{self, SignedPodBuilder},
        middleware::{self, AnchoredKey, Key, NativeOperation, NativePredicate, Value},
        prover::types::{ProofChain, ProofSolution, ProofStep},
    };

    // Helper to create simple SignedPods for testing
    fn create_test_signed_pod(
        params: &middleware::Params,
        signer_pk: &str,
        kvs: Vec<(&str, Value)>,
    ) -> Arc<frontend::SignedPod> {
        let mut builder = SignedPodBuilder::new(params);
        for (k, v) in kvs {
            builder.insert(k, v);
        }
        let mut signer = MockSigner {
            pk: signer_pk.into(),
        };
        Arc::new(builder.sign(&mut signer).unwrap())
    }

    #[test]
    fn test_build_pod_simple_gt() {
        let params = middleware::Params::default();

        // 1. Create mock input PODs
        let pod_a = create_test_signed_pod(&params, "signer_a", vec![("foo", Value::from(10))]);
        let pod_b = create_test_signed_pod(&params, "signer_b", vec![("bar", Value::from(20))]);

        // 2. Construct the ProofSolution
        let ak_a_foo = AnchoredKey::new(pod_a.id(), Key::new("foo".to_string()));
        let ak_b_bar = AnchoredKey::new(pod_b.id(), Key::new("bar".to_string()));
        let val_a = Value::from(10);
        let val_b = Value::from(20);

        let stmt_val_a = Statement::ValueOf(ak_a_foo.clone(), val_a.clone());
        let stmt_val_b = Statement::ValueOf(ak_b_bar.clone(), val_b.clone());
        let target_stmt_gt = Statement::Gt(ak_b_bar.clone(), ak_a_foo.clone()); // Gt(B["bar"], A["foo"])

        let proof_step = ProofStep {
            // Use the aliased middleware type
            operation: OperationType::Native(NativeOperation::GtFromEntries),
            inputs: vec![stmt_val_b.clone(), stmt_val_a.clone()],
            output: target_stmt_gt.clone(),
        };

        let solution = ProofSolution {
            bindings: HashMap::new(), // No wildcards in this simple case
            // Collect scope into a HashSet
            scope: vec![(pod_a.id(), stmt_val_a), (pod_b.id(), stmt_val_b)]
                .into_iter()
                .collect(),
            proof_chains: HashMap::from([(target_stmt_gt.clone(), ProofChain(vec![proof_step]))]),
        };

        // 3. Prepare original pod maps
        let original_signed_pods = HashMap::from([(pod_a.id(), pod_a), (pod_b.id(), pod_b)]);
        let original_main_pods = HashMap::new(); // No main pods in this test

        // 4. Call the build function
        let result = build_main_pod_from_solution(
            &solution,
            &original_signed_pods,
            &original_main_pods,
            &params,
        );

        println!("Result: {:?}", result);

        println!(
            "Verify: {:?}",
            result.as_ref().unwrap().pod.verify().unwrap()
        );

        // 5. Assert expected error (due to unimplemented prove)
        assert!(result.is_err());
        match result.err().unwrap() {
            ProverError::FrontendError(frontend_err) => {
                // Check if the error message contains "not yet implemented" or similar
                // from the builder.prove() call or a mock prover error.
                let err_string = frontend_err.to_string();
                assert!(
                    err_string.contains("not yet implemented") || // From unimplemented!()
                    err_string.contains("MockProver error"), // Or a potential mock error
                    "Expected unimplemented or mock error, got: {}",
                    err_string
                );
            }
            e => panic!("Expected ProverError::FrontendError, got {:?}", e),
        }
    }
}
