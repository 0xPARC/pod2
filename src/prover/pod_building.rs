use std::{
    collections::{HashMap, HashSet, VecDeque},
    sync::Arc,
};

use crate::{
    backends::plonky2::mock::mainpod::MockProver,
    frontend::{self, MainPod, MainPodBuilder, Operation as FrontendOperation, SignedPod},
    middleware::{
        self, KeyOrWildcard, NativeOperation, OperationAux, OperationType, PodId, Statement,
        StatementTmplArg, Wildcard, SELF,
    },
    op,
    prover::{
        error::ProverError,
        solver::{
            self,
            types::{ExpectedType, GlobalContext, ResolveScope, WildcardInterpretation},
            SolverState,
        },
        types::{ConcreteValue, ProofSolution, ProofStep},
    },
};

/// Builds a frontend::MainPod from a successfully solved ProofSolution.
///
/// This function reconstructs a MainPod by:
/// 1. Adding references to input PODs from the solution's scope
/// 2. Generating concrete target statements from templates
/// 3. Topologically sorting proof steps to ensure correct operation ordering
/// 4. Processing operations in the correct order to build the final POD
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
    original_signed_pods: &HashMap<PodId, &SignedPod>,
    original_main_pods: &HashMap<PodId, &MainPod>,
    params: &middleware::Params,
    request_templates: &[middleware::StatementTmpl],
) -> Result<MainPod, ProverError> {
    let mut builder = MainPodBuilder::new(params);

    // Track which PODs we've referenced to avoid duplicates
    let mut referenced_pod_ids = HashSet::new();
    // Store SELF ValueOf facts for later use in operation generation
    let mut self_value_facts = HashMap::new();
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
            stmt
        })
        .collect();

    for (pod_id, _) in &solution.scope {
        if *pod_id == SELF {
            continue;
        }

        if referenced_pod_ids.insert(*pod_id) {
            if let Some(signed_pod) = original_signed_pods.get(pod_id) {
                builder.add_signed_pod(signed_pod);
            } else if let Some(main_pod) = original_main_pods.get(pod_id) {
                builder.add_main_pod((*main_pod).clone());
            } else {
                return Err(ProverError::Internal(format!(
                    "Original pod not found for ID required by scope: {:?}",
                    pod_id
                )));
            }
        }
    }

    // Generate concrete target statements from templates using final bindings
    let mut target_statements = HashSet::new();
    let final_state_for_generation = SolverState {
        domains: solution
            .bindings
            .iter()
            .map(|(wc, cv)| {
                // Determine ExpectedType based on ConcreteValue variant
                (
                    wc.clone(),
                    (
                        HashSet::from([cv.clone()]),
                        match cv {
                            ConcreteValue::Pod(_) => ExpectedType::Pod,
                            ConcreteValue::Key(_) => ExpectedType::Key,
                            ConcreteValue::Val(_) => ExpectedType::Val,
                        },
                    ),
                )
            })
            .collect(),
        proof_chains: HashMap::new(), // Not needed for statement generation from bindings
        scope: HashSet::new(),        // Not needed for statement generation from bindings
        memoization_cache: HashMap::new(),
        active_custom_calls: HashSet::new(),
        local_potential_constant_info: Vec::new(), // Add the missing field
    };

    // Create a ResolveScope for generating final target statements
    let mut top_level_wildcard_interpretation_map = HashMap::new();
    let mut all_wcs_in_request = HashSet::new();
    for tmpl in request_templates {
        // Replicated logic from solver::mod::get_all_wildcards_from_tmpl
        for arg in &tmpl.args {
            match arg {
                StatementTmplArg::Key(w, kw_opt) => {
                    all_wcs_in_request.insert(w.clone());
                    if let KeyOrWildcard::Wildcard(ref kw) = kw_opt {
                        all_wcs_in_request.insert(kw.clone());
                    }
                }
                StatementTmplArg::WildcardLiteral(w) => {
                    all_wcs_in_request.insert(w.clone());
                }
                _ => {}
            }
        }
    }
    for wc in all_wcs_in_request {
        top_level_wildcard_interpretation_map
            .insert(wc.clone(), WildcardInterpretation::Global(wc));
    }

    let top_level_resolve_scope = ResolveScope {
        templates_to_resolve: request_templates, // Though we iterate them directly
        constraints: Vec::new(),                 // Not strictly needed for this generation step
        search_targets: None,
        wildcard_interpretation_map: top_level_wildcard_interpretation_map,
        public_arg_bindings: None,
        current_depth: 0, // Depth is not critical here
        parent_custom_call_key: None,
    };

    // Construct GlobalContext for the call to try_generate_concrete_candidate_and_bindings
    // This is a simplified construction for pod_building. A more robust solution
    // might involve passing more context from the solver.
    let facts_for_indexes: Vec<(PodId, Statement)> = solution.scope.iter().cloned().collect();
    let indexes_for_pod_building =
        crate::prover::indexing::ProverIndexes::build(params.clone(), &facts_for_indexes);
    let custom_definitions_for_pod_building = crate::prover::types::CustomDefinitions::new(); // Assuming empty for now
    let potential_constants_for_pod_building: Vec<(Wildcard, middleware::Key, middleware::Value)> =
        Vec::new(); // Assuming empty

    let global_context_for_pod_building = GlobalContext {
        indexes: &indexes_for_pod_building,
        custom_definitions: &custom_definitions_for_pod_building,
        params,
        potential_constant_info: &potential_constants_for_pod_building,
    };

    for tmpl in request_templates {
        match solver::try_generate_concrete_candidate_and_bindings(
            tmpl,
            &final_state_for_generation,
            &top_level_resolve_scope,
            &global_context_for_pod_building, // Pass the constructed GlobalContext
        ) {
            Ok(Some((target_stmt, _))) => {
                target_statements.insert(target_stmt);
            }
            Ok(None) => {
                // This should not happen if the solver succeeded
            }
            Err(e) => return Err(e),
        }
    }

    // Build dependency graph for topological sort of proof steps
    let mut step_map: HashMap<Statement, ProofStep> = HashMap::new();
    for chain in solution.proof_chains.values() {
        for step in &chain.0 {
            if !base_facts.contains(&step.output) {
                step_map
                    .entry(step.output.clone())
                    .or_insert_with(|| step.clone());
            }
        }
    }

    let mut successors: HashMap<Statement, HashSet<Statement>> = HashMap::new();
    let mut in_degree: HashMap<Statement, usize> = HashMap::new();

    for (output_stmt, step) in &step_map {
        in_degree.entry(output_stmt.clone()).or_insert(0);

        for input_stmt in &step.inputs {
            if step_map.contains_key(input_stmt) {
                successors
                    .entry(input_stmt.clone())
                    .or_default()
                    .insert(output_stmt.clone());
                *in_degree.entry(output_stmt.clone()).or_insert(0) += 1;
            }
        }
    }

    // Perform topological sort using Kahn's algorithm
    let mut queue: VecDeque<Statement> = VecDeque::new();
    for (stmt, degree) in &in_degree {
        if *degree == 0 {
            queue.push_back(stmt.clone());
        }
    }

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

    if sorted_steps.len() != step_map.len() {
        return Err(ProverError::Internal(
            "Cycle detected in proof dependencies during topological sort".to_string(),
        ));
    }

    // Track which statements have been processed to avoid duplicates
    let mut generated_statements = HashSet::new();

    // Process NewEntry operations first to ensure constants are available
    for step in solution.proof_chains.values().flat_map(|chain| &chain.0) {
        if step.operation == OperationType::Native(NativeOperation::NewEntry) {
            if let Statement::ValueOf(ak_self, literal_value) = &step.output {
                if ak_self.pod_id == SELF {
                    if !generated_statements.insert(step.output.clone()) {
                        continue;
                    }

                    let new_entry_op = op!(new_entry, (ak_self.key.name(), literal_value.clone()));
                    let is_public = target_statements.contains(&step.output);

                    let _added_statement = if is_public {
                        builder.pub_op(new_entry_op)?
                    } else {
                        builder.priv_op(new_entry_op)?
                    };
                }
            }
        }
    }

    // Process remaining operations in topological order
    for step in sorted_steps {
        if generated_statements.contains(&step.output) {
            continue;
        }

        if !generated_statements.insert(step.output.clone()) {
            continue;
        }

        let (op_type, op_args) = translate_step_to_frontend_op_args(&step)?;
        let frontend_op = FrontendOperation(op_type, op_args, OperationAux::None);

        let is_public = target_statements.contains(&step.output);
        let _generated_statement = if is_public {
            builder.pub_op(frontend_op)?
        } else {
            builder.priv_op(frontend_op)?
        };
    }

    // Invoke the backend prover to complete the POD construction
    let mut prover = MockProver {};
    builder
        .prove(&mut prover, params)
        .map_err(|e| ProverError::FrontendError(Arc::new(e)))
}

/// Translates a ProofStep into the components needed for a frontend::Operation.
///
/// This function maps the internal representation of operations to the frontend's
/// expected format, preserving the operation type and arguments while handling
/// the conversion of statements to operation arguments.
fn translate_step_to_frontend_op_args(
    step: &ProofStep,
) -> Result<(OperationType, Vec<frontend::OperationArg>), ProverError> {
    let op_type = match &step.operation {
        OperationType::Native(native_op) => OperationType::Native(*native_op),
        OperationType::Custom(custom_ref) => OperationType::Custom(custom_ref.clone()),
    };

    let op_args: Vec<frontend::OperationArg> = step
        .inputs
        .iter()
        .map(|stmt| frontend::OperationArg::Statement(stmt.clone()))
        .collect();

    Ok((op_type, op_args))
}
