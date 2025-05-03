use std::collections::{HashMap, HashSet, VecDeque};

use crate::{
    backends::plonky2::mock::mainpod::MockProver,
    frontend::{self, MainPod, MainPodBuilder, Operation as FrontendOperation, SignedPod},
    middleware::{self, NativeOperation, OperationAux, OperationType, PodId, Statement, SELF},
    op,
    prover::{
        error::ProverError,
        solver::{self, types::ExpectedType, SolverState},
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
    original_signed_pods: &HashMap<PodId, SignedPod>,
    original_main_pods: &HashMap<PodId, MainPod>,
    params: &middleware::Params,
    request_templates: &[middleware::StatementTmpl],
) -> Result<MainPod, ProverError> {
    // println!("Building MainPod from solution...");

    let mut builder = MainPodBuilder::new(params);

    // 1. Add references to input PODs based on the scope
    let mut referenced_pod_ids = HashSet::new();
    // Also collect base facts and SELF facts for dependency tracking and op generation
    let mut self_value_facts = HashMap::new(); // Store SELF ValueOf facts: Key -> Value
    let base_facts: HashSet<&Statement> = solution
        .scope
        .iter()
        .map(|(pod_id, stmt)| {
            if *pod_id == SELF {
                if let Statement::ValueOf(ak, value) = stmt {
                    if ak.pod_id == SELF {
                        self_value_facts.insert(ak.key.clone(), value.clone());
                    }
                }
            }
            stmt // Collect all statements regardless of origin for now
        })
        .collect();

    for (pod_id, _) in &solution.scope {
        // Skip adding reference for SELF
        if *pod_id == SELF {
            continue;
        }

        if referenced_pod_ids.insert(*pod_id) {
            // Check if it's a known SignedPod
            if let Some(signed_pod) = original_signed_pods.get(pod_id) {
                // Pass the SignedPod reference
                builder.add_signed_pod(signed_pod);
            } else if let Some(main_pod) = original_main_pods.get(pod_id) {
                // Pass a clone of the MainPod
                builder.add_main_pod(main_pod.clone());
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
    let final_state_for_generation = SolverState {
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
        match solver::try_generate_concrete_candidate_and_bindings(
            tmpl,
            &final_state_for_generation,
        ) {
            Ok(Some((target_stmt, _))) => {
                // println!("  Identified Target Statement: {:?}", target_stmt);
                target_statements.insert(target_stmt);
            }
            Ok(None) => {
                // println!("Warning: Could not generate concrete target statement from template {:?} during build (should not happen if solve succeeded)", tmpl);
                // This might indicate an issue if the solver succeeded but we can't generate the target now.
            }
            Err(e) => {
                // println!("Error generating concrete target statement from template {:?} during build: {:?}", tmpl, e);
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
        }
    }

    // 2e. Check for cycles
    if sorted_steps.len() != step_map.len() {
        return Err(ProverError::Internal(
            "Cycle detected in proof dependencies during topological sort".to_string(),
        ));
    }

    // --- Topological Sort of Proof Steps --- END ---

    let mut generated_statements = HashSet::new(); // Keep track of handled statements

    // --- Process SELF Constant NewEntry Steps FIRST --- START ---
    for step in solution.proof_chains.values().flat_map(|chain| &chain.0) {
        if step.operation == OperationType::Native(NativeOperation::NewEntry) {
            if let Statement::ValueOf(ak_self, literal_value) = &step.output {
                if ak_self.pod_id == SELF {
                    // Ensure we only add the NewEntry once for this constant
                    if !generated_statements.insert(step.output.clone()) {
                        continue;
                    }

                    let new_entry_op = op!(new_entry, (ak_self.key.name(), literal_value.clone()));
                    let is_public = target_statements.contains(&step.output);
                    println!(
                        "  Adding PRE-SORT NewEntry Op (public={}): {:?} -> {:?}",
                        is_public, new_entry_op, step.output
                    );

                    let _added_statement = if is_public {
                        builder.pub_op(new_entry_op)?
                    } else {
                        builder.priv_op(new_entry_op)?
                    };
                }
            }
        }
    }
    // --- Process SELF Constant NewEntry Steps FIRST --- END ---

    // 3. Add topologically sorted derived operations to the builder
    // let mut generated_statements = HashSet::new(); // Moved up
    for step in sorted_steps {
        // Now only contains derived steps from step_map

        // Skip if output already handled (e.g., by the NewEntry pre-processing)
        if generated_statements.contains(&step.output) {
            println!("  Skipping already handled statement: {:?}", step.output);
            continue;
        }

        // Ensure we only add the operation for each unique output statement once.
        if !generated_statements.insert(step.output.clone()) {
            continue;
        }

        let (op_type, op_args) = translate_step_to_frontend_op_args(&step)?;
        let frontend_op = FrontendOperation(op_type, op_args, OperationAux::None);

        // Determine if the output statement is a final target required by the request
        let is_public = target_statements.contains(&step.output);

        // Add operation to builder
        let _generated_statement = if is_public {
            builder.pub_op(frontend_op)?
        } else {
            builder.priv_op(frontend_op)?
        };
    }

    // 4. Invoke the backend prover
    let mut prover = MockProver {}; // Example
    builder
        .prove(&mut prover, params)
        .map_err(ProverError::FrontendError) // Use From trait via variant name
}

/// Helper function to translate a prover::ProofStep into the components
/// needed for a frontend::Operation (op_type, Vec<OperationArg>).
fn translate_step_to_frontend_op_args(
    step: &ProofStep,
) -> Result<(OperationType, Vec<frontend::OperationArg>), ProverError> {
    // Map the prover OperationType to the middleware OperationType
    let op_type = match &step.operation {
        // Use middleware::OperationType which should be public
        OperationType::Native(native_op) => OperationType::Native(*native_op),
        OperationType::Custom(custom_ref) => OperationType::Custom(custom_ref.clone()),
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
