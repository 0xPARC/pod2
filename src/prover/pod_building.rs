use std::{
    collections::{HashMap, HashSet, VecDeque},
    sync::Arc,
};

use crate::{
    frontend::{
        self, MainPodBuilder, Operation as FrontendOperation, SignedPod as FrontendSignedPod,
    },
    middleware::{self, OperationAux, OperationType, PodId, Statement},
    prover::{
        error::ProverError,
        solver::types::ExpectedType,
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
/// * `request_templates` - Templates for generating concrete target statements.
///
/// # Returns
///
/// A Result containing the built frontend::MainPod or a ProverError.
pub fn build_main_pod_from_solution(
    solution: &ProofSolution,
    original_signed_pods: &HashMap<PodId, Arc<FrontendSignedPod>>,
    original_main_pods: &HashMap<PodId, Arc<frontend::MainPod>>,
    params: &middleware::Params,
    request_templates: &[middleware::StatementTmpl],
) -> Result<frontend::MainPod, ProverError> {
    println!("Building MainPod from solution...");

    let mut builder = MainPodBuilder::new(params);

    // 1. Add references to input PODs based on the scope
    let mut referenced_pod_ids = HashSet::new();
    // Also collect base facts for dependency tracking
    let base_facts: HashSet<&Statement> = solution.scope.iter().map(|(_, stmt)| stmt).collect();

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

    // --- Generate Concrete Target Statements --- START ---
    let mut target_statements = HashSet::new();
    // Create a temporary solver state just for generating target statements from final bindings
    let final_state_for_generation = crate::prover::solver::SolverState {
        params: params.clone(),
        domains: solution
            .bindings
            .iter()
            .map(|(wc, cv)| {
                // Need to guess the ExpectedType, but it doesn't matter for generation
                (
                    wc.clone(),
                    (HashSet::from([cv.clone()]), ExpectedType::Unknown),
                )
            })
            .collect(),
        constraints: Vec::new(),
        proof_chains: HashMap::new(),
        scope: HashSet::new(),
    };

    for tmpl in request_templates {
        match crate::prover::solver::try_generate_concrete_candidate_and_bindings(
            tmpl,
            &final_state_for_generation,
        ) {
            Ok(Some((target_stmt, _))) => {
                println!("  Identified Target Statement: {:?}", target_stmt);
                target_statements.insert(target_stmt);
            }
            Ok(None) => {
                println!("Warning: Could not generate concrete target statement from template {:?} during build (should not happen if solve succeeded)", tmpl);
                // This might indicate an issue if the solver succeeded but we can't generate the target now.
                // Depending on desired strictness, could return an error here.
            }
            Err(e) => {
                println!("Error generating concrete target statement from template {:?} during build: {:?}", tmpl, e);
                return Err(e); // Propagate the error
            }
        }
    }
    // --- Generate Concrete Target Statements --- END ---

    // --- Topological Sort of Proof Steps --- START ---

    // 2a. Collect all unique derived steps, keyed by output statement
    let mut step_map: HashMap<Statement, ProofStep> = HashMap::new();
    for chain in solution.proof_chains.values() {
        for step in &chain.0 {
            // Only include steps that derive statements (ignore base fact Copy steps here,
            // as they don't have dependencies relevant to the sort among derived statements).
            // We only care about steps whose output is a key in proof_chains (derived targets)
            // or whose output is used as input to another step.
            if !base_facts.contains(&step.output) {
                // Avoid overwriting if multiple chains derive the same intermediate step (shouldn't happen?)
                step_map
                    .entry(step.output.clone())
                    .or_insert_with(|| step.clone());
            }
        }
    }

    // 2b. Build dependency graph (successors) and calculate in-degrees
    let mut successors: HashMap<Statement, HashSet<Statement>> = HashMap::new();
    let mut in_degree: HashMap<Statement, usize> = HashMap::new();

    for (output_stmt, step) in &step_map {
        // Ensure every derived statement has an in-degree entry (initially 0)
        in_degree.entry(output_stmt.clone()).or_insert(0);

        for input_stmt in &step.inputs {
            // Only consider dependencies on *other derived* statements
            if step_map.contains_key(input_stmt) {
                // Add edge input_stmt -> output_stmt
                successors
                    .entry(input_stmt.clone())
                    .or_default()
                    .insert(output_stmt.clone());
                // Increment in-degree of the output statement
                *in_degree.entry(output_stmt.clone()).or_insert(0) += 1;
            }
            // Base facts (not in step_map) don't contribute to the initial in-degree count
        }
    }

    // 2c. Initialize queue with nodes having in-degree 0
    let mut queue: VecDeque<Statement> = VecDeque::new();
    for (stmt, degree) in &in_degree {
        if *degree == 0 {
            queue.push_back(stmt.clone());
        }
    }

    // 2d. Process queue (Kahn's algorithm)
    let mut sorted_steps: Vec<ProofStep> = Vec::new();
    while let Some(stmt) = queue.pop_front() {
        if let Some(step_to_add) = step_map.get(&stmt) {
            sorted_steps.push(step_to_add.clone());

            if let Some(next_stmts) = successors.get(&stmt) {
                for successor_stmt in next_stmts {
                    if let Some(degree) = in_degree.get_mut(successor_stmt) {
                        *degree -= 1;
                        if *degree == 0 {
                            queue.push_back(successor_stmt.clone());
                        }
                    }
                }
            }
        } else {
            // This statement was likely a base fact implicitly added, skip.
        }
    }

    // 2e. Check for cycles
    if sorted_steps.len() != step_map.len() {
        return Err(ProverError::Internal(
            "Cycle detected in proof dependencies during topological sort".to_string(),
        ));
    }

    // --- Topological Sort of Proof Steps --- END ---

    // 3. Add topologically sorted operations to the builder
    // We use generated_statements to handle potential duplicates in `sorted_steps` if the same step
    // was somehow included multiple times despite the HashMap - defensive check.
    let mut generated_statements = HashSet::new();
    for step in sorted_steps {
        // Ensure we only add the operation for each unique output statement once.
        if !generated_statements.insert(step.output.clone()) {
            continue;
        }

        let (op_type, op_args) = translate_step_to_frontend_op_args(&step)?;
        let frontend_op = FrontendOperation(op_type, op_args, OperationAux::None);

        // Determine if the output statement is a final target required by the request
        let is_public = target_statements.contains(&step.output);

        println!(
            "  Adding Sorted Op (public={}): {:?} -> {:?}",
            is_public, frontend_op, step.output
        );

        // Add operation to builder
        let _generated_statement = if is_public {
            builder.pub_op(frontend_op)?
        } else {
            builder.priv_op(frontend_op)?
        };
    }

    // 4. Invoke the backend prover
    println!("Invoking backend prover...");
    // TODO: Use the actual prover instance passed in or created
    // In the meantime, MockProver should work identically to the real prover,
    // so it will return a valid MainPod.
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
