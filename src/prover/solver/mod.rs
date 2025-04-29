use std::collections::{HashMap, HashSet};

use crate::{
    middleware,
    middleware::{
        AnchoredKey, KeyOrWildcard, NativeOperation, NativePredicate, OperationType, PodId,
        Predicate, Statement, StatementArg, StatementTmpl, StatementTmplArg, Wildcard,
    },
    prover::{
        error::ProverError,
        indexing::ProverIndexes,
        types::{CustomDefinitions, ProofChain, ProofSolution},
    },
};

// Import items from submodules
mod initialization;
mod proof;
mod pruning;
mod search;
pub mod types; // Make types public within the solver module

#[cfg(test)]
mod tests; // Keep tests private to the solver module

// Use items brought into scope by the submodules
use initialization::initialize_solver_state;
use proof::try_prove_statement; // Import try_prove_statement
use pruning::{prune_domains_after_proof, prune_initial_domains};
use search::perform_search;
use types::{Constraint, Domain, ExpectedType};

use crate::prover::types::ConcreteValue;

// Represents the overall state of the constraint solver
#[derive(Clone)]
pub struct SolverState {
    // Store Domain and its inferred ExpectedType together
    pub domains: HashMap<Wildcard, (Domain, ExpectedType)>,
    // Store structural constraints derived from templates
    pub constraints: Vec<Constraint>,
    // Store generated proof chains, mapping the derived statement to its proof
    pub proof_chains: HashMap<Statement, ProofChain>,
    // Store the set of base facts (from input PODs) used in the proofs
    // The PodId indicates the origin of the base fact.
    pub scope: HashSet<(PodId, Statement)>,
    // References to inputs: (Potentially add back if needed)
    // pub indexes: 'a ProverIndexes,
    // pub custom_definitions: 'a CustomDefinitions,
}

pub fn solve(
    request_templates: &[StatementTmpl],
    indexes: &ProverIndexes,
    custom_definitions: &CustomDefinitions,
) -> Result<ProofSolution, ProverError> {
    // 1. Initialization (Identify wildcards, initial domains, static constraints)
    let mut state = initialize_solver_state(request_templates, indexes)?;

    // Keep the original templates accessible for candidate generation
    let original_templates = request_templates.to_vec();

    // 2. Initial Domain Pruning (Static Unary Constraints)
    prune_initial_domains(&mut state, indexes)?;

    // 3. Iterative Constraint Propagation & Proof Generation (Loop)
    let mut changed_in_iteration = true;
    let mut iteration = 0;
    const MAX_ITERATIONS: usize = 100;

    while changed_in_iteration && iteration < MAX_ITERATIONS {
        changed_in_iteration = false;
        iteration += 1;
        println!("Solver iteration {}", iteration);

        // 3a. Re-apply basic pruning based on current domains
        let pruning_changed = prune_initial_domains(&mut state, indexes)?;
        if pruning_changed {
            println!("  - Pruning changed domains");
            changed_in_iteration = true;
        }

        // 3b. Generate candidate statements AND BINDINGS from templates if possible
        let mut new_proofs_found_this_iter = false; // Track changes within this specific iteration step

        for tmpl in &original_templates {
            // Iterate through original templates each time
            match try_generate_concrete_candidate_and_bindings(tmpl, &state) {
                Ok(Some((target_statement, bindings))) => {
                    // Successfully generated a concrete candidate and its bindings

                    // 3c. Attempt to prove candidate statements
                    // Skip if already proven
                    if state.proof_chains.contains_key(&target_statement) {
                        continue;
                    }

                    match try_prove_statement(
                        &mut state,
                        &target_statement,
                        indexes,
                        custom_definitions,
                    ) {
                        Ok(_proof_chain) => {
                            println!("  - Successfully proved: {:?}", target_statement);
                            new_proofs_found_this_iter = true;

                            // --- CALL NEW DYNAMIC PRUNING ---
                            // Note: The logic inside prune_domains_after_proof needs adjustment
                            //       to correctly use the template and bindings, but we call it here.
                            let pruned_dynamically = prune_domains_after_proof(
                                &mut state,
                                tmpl,              // Pass the template!
                                &target_statement, // Pass the concrete statement
                                &bindings,         // Pass the specific bindings
                                indexes,
                            )?; // Propagate errors

                            if pruned_dynamically {
                                println!("    - Dynamic pruning after proof changed domains.");
                                changed_in_iteration = true; // Mark change for the outer loop
                            }
                            // --- END DYNAMIC PRUNING CALL ---

                            // Optional: Re-run initial pruning immediately?
                            // let pruned_after_proof = prune_initial_domains(&mut state, indexes)?;
                            // if pruned_after_proof {
                            //     println!("    - Initial pruning after new proof changed domains");
                            //     changed_in_iteration = true;
                            // }
                        }
                        Err(ProverError::Unsatisfiable(msg)) => {
                            println!(
                                "  - Definitive failure proving required candidate {:?}: {}",
                                target_statement, msg
                            );
                            return Err(ProverError::Unsatisfiable(format!(
                                "Failed to prove required candidate statement derived from request templates: {:?}. Reason: {}",
                                target_statement,
                                msg
                            )));
                        }
                        Err(ProverError::NotImplemented(op)) => {
                            // If a specific operation needed for proof is not implemented,
                            // we might not be able to prove this candidate *now*, but maybe later.
                            // Log it but don't necessarily fail the whole solve yet.
                            println!(
                                "  - Could not prove candidate {:?} due to unimplemented operation: {}. Skipping for now.",
                                target_statement, op
                            );
                            // We don't return Err here, allowing the solver to continue with other candidates/iterations.
                        }
                        Err(e) => {
                            // Handle other potentially fatal errors
                            println!(
                                "  - Error proving candidate {:?}: {:?}",
                                target_statement, e
                            );
                            return Err(e); // Propagate other errors
                        }
                    }
                }
                Ok(None) => {
                    // Template wildcards were not all singletons, skip for this iteration
                }
                Err(e) => {
                    // Error during candidate generation itself
                    return Err(e);
                }
            }
        } // End loop through original_templates

        // If new proofs were found but didn't trigger dynamic pruning, still continue loop
        if new_proofs_found_this_iter && !changed_in_iteration {
            println!(
                "  - New proofs found, but dynamic pruning didn't change domains. Continuing loop."
            );
            changed_in_iteration = true;
        }

        // TODO: Add more sophisticated domain pruning logic here based on newly proven facts.
    }

    if iteration >= MAX_ITERATIONS {
        return Err(ProverError::Other(
            "Solver reached maximum iterations, likely an infinite loop or complex case."
                .to_string(),
        ));
    }

    println!(
        "Solver finished propagation after {} iterations.",
        iteration
    );

    // 4. Search (If Necessary)
    if state.domains.values().any(|(domain, _)| domain.len() > 1) {
        println!("Domains still contain multiple values, entering Search phase.");
        // Call the search function, taking ownership of the current state
        match perform_search(state, &original_templates, indexes, custom_definitions) {
            Ok(solved_state) => {
                println!("Search phase succeeded.");
                state = solved_state; // Update state with the solved one from search
            }
            Err(e) => {
                println!("Search phase failed: {:?}", e);
                return Err(e); // Propagate the search error (e.g., Unsatisfiable)
            }
        }
    } else {
        println!("No search needed, all domains are singletons after propagation.");
    }

    // 5. Solution Extraction
    println!("All domains have size 1, preparing for Solution Extraction.");

    let final_bindings: HashMap<Wildcard, ConcreteValue> = state.domains.iter()
        .filter_map(|(wc, (domain, _))| {
            if domain.len() == 1 {
                Some((wc.clone(), domain.iter().next().unwrap().clone()))
            } else {
                // Should not happen if search phase is complete or wasn't needed
                 println!("Warning: Wildcard {:?} ended with domain size != 1 ({:?}) after propagation/search.", wc.name, domain);
                None
            }
        })
        .collect();

    // Determine minimal scope based on proof chains for *requested* templates
    let mut final_scope = HashSet::new();
    for tmpl in &original_templates {
        // Re-generate the target statement based on final bindings
        // Use the final bindings derived from the potentially pruned state domains
        let temp_state_for_generation = SolverState {
            domains: final_bindings
                .iter()
                .map(|(wc, cv)| {
                    let expected_type = state
                        .domains
                        .get(wc)
                        .map_or(ExpectedType::Unknown, |(_, et)| *et);
                    (wc.clone(), (HashSet::from([cv.clone()]), expected_type))
                })
                .collect(),
            constraints: vec![],          // Not needed for generation
            proof_chains: HashMap::new(), // Not needed for generation
            scope: HashSet::new(),        // Not needed for generation
        };

        if let Ok(Some((target_stmt, _))) =
            try_generate_concrete_candidate_and_bindings(tmpl, &temp_state_for_generation)
        {
            if let Some(chain) = state.proof_chains.get(&target_stmt) {
                chain.collect_scope(
                    &mut final_scope,
                    &state.proof_chains,
                    &indexes.exact_statement_lookup,
                );
            } else {
                // This might happen if the final statement was a base fact itself
                if let Some((pod_id, base_stmt)) = indexes
                    .exact_statement_lookup
                    .iter()
                    .find(|(_, stmt)| stmt == &target_stmt)
                {
                    final_scope.insert((*pod_id, base_stmt.clone()));
                } else {
                    // If it wasn't proven and isn't a base fact, something went wrong or search is needed
                    // This could also happen if the concrete statement generated using final bindings
                    // is different from the one generated during the iterations (due to pruning)
                    println!("Warning: Could not find proof chain or base fact for final target statement: {:?}. This might indicate inconsistent state or needed search.", target_stmt);
                }
            }
        } else {
            // Could not generate concrete statement from template even at the end
            println!("Warning: Could not generate concrete statement from final template interpretation: {:?}", tmpl);
        }
    }

    Ok(ProofSolution {
        bindings: final_bindings,
        scope: final_scope.into_iter().collect(), // Convert HashSet to Vec
        proof_chains: state.proof_chains,         // Return all generated chains
    })
}

/// Tries to generate a concrete statement and its bindings from a template,
/// succeeding only if all involved wildcards have singleton domains.
pub(super) fn try_generate_concrete_candidate_and_bindings(
    tmpl: &StatementTmpl,
    state: &SolverState,
) -> Result<Option<(Statement, HashMap<Wildcard, ConcreteValue>)>, ProverError> {
    // Output includes bindings
    let mut concrete_args = Vec::with_capacity(tmpl.args.len());
    let mut bindings = HashMap::new(); // Track concrete values for this template

    // First pass: Check if all wildcards are singletons and collect bindings
    for arg_tmpl in &tmpl.args {
        match collect_singleton_bindings(arg_tmpl, state, &mut bindings) {
            Ok(true) => {}                // Singleton found or no wildcard, continue
            Ok(false) => return Ok(None), // Not a singleton, cannot generate concrete statement yet
            Err(e) => return Err(e),      // Error during binding collection
        }
    }

    // If we reach here, all necessary wildcards were singletons.
    // Second pass: Construct concrete arguments using the collected bindings
    for arg_tmpl in &tmpl.args {
        match construct_concrete_arg(arg_tmpl, &bindings) {
            Ok(Some(arg)) => concrete_args.push(arg),
            Ok(None) => { /* Skip None args */ }
            Err(e) => return Err(e), // Propagate construction errors
        }
    }

    // Construct the concrete statement
    let concrete_statement = build_concrete_statement(tmpl.pred.clone(), concrete_args)?;

    // Return the concrete statement and the bindings used to create it
    Ok(Some((concrete_statement, bindings)))
}

/// Helper to check domain size and collect singleton bindings for a template argument.
/// Returns Ok(true) if all involved wildcards are singletons, Ok(false) otherwise.
pub(super) fn collect_singleton_bindings(
    arg_tmpl: &StatementTmplArg,
    state: &SolverState,
    bindings: &mut HashMap<Wildcard, ConcreteValue>,
) -> Result<bool, ProverError> {
    match arg_tmpl {
        StatementTmplArg::Key(wc_pod, key_or_wc) => {
            if !check_and_bind_singleton(wc_pod, state, bindings)? {
                return Ok(false);
            }
            if let KeyOrWildcard::Wildcard(wc_key) = key_or_wc {
                if !check_and_bind_singleton(wc_key, state, bindings)? {
                    return Ok(false);
                }
            }
        }
        StatementTmplArg::WildcardLiteral(wc_val) => {
            if !check_and_bind_singleton(wc_val, state, bindings)? {
                return Ok(false);
            }
        }
        StatementTmplArg::Literal(_) | StatementTmplArg::None => { /* No wildcards */ }
    }
    Ok(true)
}

/// Checks if a wildcard's domain is a singleton and adds it to bindings if so.
pub(super) fn check_and_bind_singleton(
    wildcard: &Wildcard,
    state: &SolverState,
    bindings: &mut HashMap<Wildcard, ConcreteValue>,
) -> Result<bool, ProverError> {
    if let Some((domain, _)) = state.domains.get(wildcard) {
        if domain.len() == 1 {
            if !bindings.contains_key(wildcard) {
                // .next() is safe due to len() == 1 check
                let concrete_value = domain.iter().next().unwrap().clone();
                bindings.insert(wildcard.clone(), concrete_value);
            }
            Ok(true)
        } else {
            Ok(false) // Not a singleton
        }
    } else {
        // Wildcard from template not found in domains - should not happen after init
        Err(ProverError::Internal(format!(
            "Wildcard '{}' from template not found in solver state domains.",
            wildcard.name
        )))
    }
}

/// Helper to construct a concrete StatementArg from a template argument using bindings.
/// Note: Returns Ok(None) for StatementTmplArg::None
pub(super) fn construct_concrete_arg(
    arg_tmpl: &StatementTmplArg,
    bindings: &HashMap<Wildcard, ConcreteValue>,
) -> Result<Option<StatementArg>, ProverError> {
    // Return Option<StatementArg>
    match arg_tmpl {
        StatementTmplArg::Key(wc_pod, key_or_wc) => {
            let pod_id = match bindings.get(wc_pod) {
                Some(ConcreteValue::Pod(id)) => *id,
                _ => {
                    return Err(ProverError::Internal(format!(
                        "Binding for Pod wildcard '{}' not found or wrong type",
                        wc_pod.name
                    )))
                }
            };
            let key = match key_or_wc {
                KeyOrWildcard::Key(k) => k.clone(),
                KeyOrWildcard::Wildcard(wc_key) => match bindings.get(wc_key) {
                    Some(ConcreteValue::Key(k_name)) => middleware::Key::new(k_name.clone()),
                    _ => {
                        return Err(ProverError::Internal(format!(
                            "Binding for Key wildcard '{}' not found or wrong type",
                            wc_key.name
                        )))
                    }
                },
            };
            // Construct AnchoredKey directly
            Ok(Some(StatementArg::Key(AnchoredKey::new(pod_id, key)))) // Use StatementArg::Key
        }
        StatementTmplArg::WildcardLiteral(wc_val) => {
            match bindings.get(wc_val) {
                Some(ConcreteValue::Val(v)) => Ok(Some(StatementArg::Literal(v.clone()))), // Use StatementArg::Literal
                _ => Err(ProverError::Internal(format!(
                    "Binding for Value wildcard '{}' not found or wrong type",
                    wc_val.name
                ))),
            }
        }
        StatementTmplArg::Literal(v) => Ok(Some(StatementArg::Literal(v.clone()))), // Use StatementArg::Literal
        StatementTmplArg::None => Ok(None),
    }
}

/// Builds a concrete statement from a predicate and concrete arguments.
pub(super) fn build_concrete_statement(
    pred: Predicate,
    args: Vec<StatementArg>,
) -> Result<Statement, ProverError> {
    // This is tedious but necessary to map Predicate enum back to Statement enum variants.
    // We need to ensure the number and type of args match the expected structure for each predicate.
    match pred {
        Predicate::Native(NativePredicate::ValueOf) => {
            if args.len() == 2 {
                if let (StatementArg::Key(ak), StatementArg::Literal(val)) = (&args[0], &args[1]) {
                    Ok(Statement::ValueOf(ak.clone(), val.clone()))
                } else {
                    Err(ProverError::Internal(
                        "Invalid args for ValueOf".to_string(),
                    ))
                }
            } else {
                Err(ProverError::Internal(
                    "Invalid arg count for ValueOf".to_string(),
                ))
            }
        }
        Predicate::Native(NativePredicate::Equal) => {
            if args.len() == 2 {
                if let (StatementArg::Key(ak1), StatementArg::Key(ak2)) = (&args[0], &args[1]) {
                    Ok(Statement::Equal(ak1.clone(), ak2.clone()))
                } else {
                    Err(ProverError::Internal("Invalid args for Equal".to_string()))
                }
            } else {
                Err(ProverError::Internal(
                    "Invalid arg count for Equal".to_string(),
                ))
            }
        }
        Predicate::Native(NativePredicate::NotEqual) => {
            if args.len() == 2 {
                if let (StatementArg::Key(ak1), StatementArg::Key(ak2)) = (&args[0], &args[1]) {
                    Ok(Statement::NotEqual(ak1.clone(), ak2.clone()))
                } else {
                    Err(ProverError::Internal(
                        "Invalid args for NotEqual".to_string(),
                    ))
                }
            } else {
                Err(ProverError::Internal(
                    "Invalid arg count for NotEqual".to_string(),
                ))
            }
        }
        Predicate::Native(NativePredicate::Gt) => {
            if args.len() == 2 {
                if let (StatementArg::Key(ak1), StatementArg::Key(ak2)) = (&args[0], &args[1]) {
                    Ok(Statement::Gt(ak1.clone(), ak2.clone()))
                } else {
                    Err(ProverError::Internal("Invalid args for Gt".to_string()))
                }
            } else {
                Err(ProverError::Internal(
                    "Invalid arg count for Gt".to_string(),
                ))
            }
        }
        Predicate::Native(NativePredicate::Lt) => {
            if args.len() == 2 {
                if let (StatementArg::Key(ak1), StatementArg::Key(ak2)) = (&args[0], &args[1]) {
                    Ok(Statement::Lt(ak1.clone(), ak2.clone()))
                } else {
                    Err(ProverError::Internal("Invalid args for Lt".to_string()))
                }
            } else {
                Err(ProverError::Internal(
                    "Invalid arg count for Lt".to_string(),
                ))
            }
        }
        Predicate::Native(NativePredicate::SumOf) => {
            if args.len() == 3 {
                if let (StatementArg::Key(ak1), StatementArg::Key(ak2), StatementArg::Key(ak3)) =
                    (&args[0], &args[1], &args[2])
                {
                    Ok(Statement::SumOf(ak1.clone(), ak2.clone(), ak3.clone()))
                } else {
                    Err(ProverError::Internal("Invalid args for SumOf".to_string()))
                }
            } else {
                Err(ProverError::Internal(
                    "Invalid arg count for SumOf".to_string(),
                ))
            }
        }
        Predicate::Native(NativePredicate::ProductOf) => {
            if args.len() == 3 {
                if let (StatementArg::Key(ak1), StatementArg::Key(ak2), StatementArg::Key(ak3)) =
                    (&args[0], &args[1], &args[2])
                {
                    Ok(Statement::ProductOf(ak1.clone(), ak2.clone(), ak3.clone()))
                } else {
                    Err(ProverError::Internal(
                        "Invalid args for ProductOf".to_string(),
                    ))
                }
            } else {
                Err(ProverError::Internal(
                    "Invalid arg count for ProductOf".to_string(),
                ))
            }
        }
        Predicate::Native(NativePredicate::MaxOf) => {
            if args.len() == 3 {
                if let (StatementArg::Key(ak1), StatementArg::Key(ak2), StatementArg::Key(ak3)) =
                    (&args[0], &args[1], &args[2])
                {
                    Ok(Statement::MaxOf(ak1.clone(), ak2.clone(), ak3.clone()))
                } else {
                    Err(ProverError::Internal("Invalid args for MaxOf".to_string()))
                }
            } else {
                Err(ProverError::Internal(
                    "Invalid arg count for MaxOf".to_string(),
                ))
            }
        }
        Predicate::Native(NativePredicate::Contains) => {
            if args.len() == 3 {
                if let (StatementArg::Key(ak1), StatementArg::Key(ak2), StatementArg::Key(ak3)) =
                    (&args[0], &args[1], &args[2])
                {
                    Ok(Statement::Contains(ak1.clone(), ak2.clone(), ak3.clone()))
                } else {
                    Err(ProverError::Internal(
                        "Invalid args for Contains".to_string(),
                    ))
                }
            } else {
                Err(ProverError::Internal(
                    "Invalid arg count for Contains".to_string(),
                ))
            }
        }
        Predicate::Native(NativePredicate::NotContains) => {
            if args.len() == 2 {
                if let (StatementArg::Key(ak1), StatementArg::Key(ak2)) = (&args[0], &args[1]) {
                    Ok(Statement::NotContains(ak1.clone(), ak2.clone()))
                } else {
                    Err(ProverError::Internal(
                        "Invalid args for NotContains".to_string(),
                    ))
                }
            } else {
                Err(ProverError::Internal(
                    "Invalid arg count for NotContains".to_string(),
                ))
            }
        }
        Predicate::Custom(_) => {
            // Need CustomPredicateRef and concrete values.
            // TODO: Implement Custom statement construction.
            Err(ProverError::NotImplemented(
                "Building concrete Custom statements".to_string(),
            ))
        }
        Predicate::BatchSelf(_) => {
            // This shouldn't be directly constructed; it resolves to Custom.
            Err(ProverError::Internal(
                "Cannot directly build BatchSelf statement".to_string(),
            ))
        }
        // Add other native predicates if they exist
        _ => Err(ProverError::Internal(format!(
            "Unhandled predicate type in build_concrete_statement: {:?}",
            pred
        ))),
    }
}

// Helper function stub for ProofChain scope collection (needs proper implementation)
// Add this within the SolverState impl or as a free function if preferred
impl ProofChain {
    fn collect_scope(
        &self,
        final_scope: &mut HashSet<(PodId, Statement)>,
        all_chains: &HashMap<Statement, ProofChain>,
        base_facts: &HashSet<(PodId, Statement)>,
    ) {
        for step in &self.0 {
            // Ensure we don't revisit steps to prevent potential infinite loops if chains somehow became cyclic
            // This is a basic check; more robust cycle detection might be needed if complex recursive proofs arise.
            // We check if the output of this step *leading to a base fact* is already in scope.
            let is_base_copy =
                step.operation == OperationType::Native(NativeOperation::CopyStatement);
            let output_already_scoped = is_base_copy
                && base_facts.iter().any(|(pid, stmt)| {
                    stmt == &step.output && final_scope.contains(&(*pid, stmt.clone()))
                });

            if output_already_scoped {
                continue;
            }

            if is_base_copy {
                // Input is a base fact, find its origin PodId
                if let Some((pod_id, base_stmt)) =
                    base_facts.iter().find(|(_, stmt)| stmt == &step.inputs[0])
                {
                    final_scope.insert((*pod_id, base_stmt.clone()));
                } else {
                    println!("Warning: Could not find origin PodId for base fact in scope collection: {:?}", step.inputs[0]);
                }
            } else {
                // Recurse for inputs that were derived statements
                for input_stmt in &step.inputs {
                    // Check if the input itself is a base fact before looking for a chain
                    if let Some((pod_id, base_stmt)) =
                        base_facts.iter().find(|(_, stmt)| stmt == input_stmt)
                    {
                        final_scope.insert((*pod_id, base_stmt.clone()));
                    } else if let Some(input_chain) = all_chains.get(input_stmt) {
                        // Only recurse if the input statement's chain hasn't been processed leading to base facts yet.
                        // This simple check might not be perfect for complex shared sub-proofs.
                        // We need a way to mark nodes/chains as visited during the collection traversal.
                        // For now, recurse unconditionally, relying on HashSet uniqueness.
                        input_chain.collect_scope(final_scope, all_chains, base_facts);
                    } else {
                        println!("Warning: Could not find proof chain or base fact for input statement during scope collection: {:?}", input_stmt);
                    }
                }
            }
        }
    }
}
