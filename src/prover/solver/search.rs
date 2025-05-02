use std::collections::HashSet;

use super::{
    proof::try_prove_statement,
    pruning::{self, prune_initial_domains},
    try_generate_concrete_candidate_and_bindings, SolverState,
};
use crate::{
    middleware::{Key, NativePredicate, Predicate, StatementTmpl, Value, Wildcard},
    prover::{error::ProverError, indexing::ProverIndexes, types::CustomDefinitions},
};

/// Performs Depth-First Search (DFS) backtracking to find a consistent assignment
/// for wildcards with non-singleton domains.
///
/// Returns Ok(SolverState) if a solution is found, where the state's domains
/// all have size 1. Returns Err(ProverError::Unsatisfiable) if no solution exists.
pub(super) fn perform_search(
    initial_state: SolverState,          // Take ownership to modify clones
    request_templates: &[StatementTmpl], // <-- Add original templates
    indexes: &ProverIndexes,
    custom_definitions: &CustomDefinitions, // <-- Use this now
    equality_pairs: &[(Wildcard, Wildcard)],
    inequality_pairs: &[(Wildcard, Wildcard)],
    potential_constant_info: &[(Wildcard, Key, Value)], // Change Wildcard -> Value
) -> Result<SolverState, ProverError> {
    println!("Entering DFS Search...");

    // Check if already solved (base case for recursion)
    if initial_state
        .domains
        .values()
        .all(|(domain, _)| domain.len() == 1)
    {
        println!("  Base case: All domains singletons. Verifying proof...");

        // --- Verify Provability --- START ---
        // Need a mutable copy to pass to try_prove_statement
        let mut verification_state = initial_state.clone_state_for_search();
        for tmpl in request_templates {
            // Generate the concrete statement based on the current state's bindings
            match try_generate_concrete_candidate_and_bindings(tmpl, &verification_state) {
                Ok(Some((target_statement, _))) => {
                    // Attempt to prove this concrete statement
                    // Pass a mutable reference to the *verification* state
                    match try_prove_statement(
                        &mut verification_state, // Use mutable clone
                        &target_statement,
                        indexes,
                        custom_definitions,
                        potential_constant_info, // Pass down
                    ) {
                        Ok(_) => {
                            // This specific statement is provable with this assignment
                            println!("    - Verified: {:?}", target_statement);
                        }
                        Err(e) => {
                            // If *any* target statement cannot be proven, this assignment is invalid
                            println!(
                                "    - Verification Failed for {:?}: {:?}. Backtracking...",
                                target_statement, e
                            );
                            return Err(ProverError::Unsatisfiable(format!(
                                 "Search solution assignment failed final proof check for {:?}: {:?}",
                                 target_statement,
                                 e
                             )));
                        }
                    }
                }
                Ok(None) => {
                    // This shouldn't happen if all domains are singletons, but handle defensively
                    println!("    - Warning: Could not generate concrete statement from template {:?} in final check.", tmpl);
                    return Err(ProverError::Internal(format!(
                        "Failed to generate concrete statement in final verification: {:?}",
                        tmpl
                    )));
                }
                Err(e) => {
                    // Error during generation itself
                    println!(
                        "    - Error generating concrete statement in final check: {:?}",
                        e
                    );
                    return Err(e);
                }
            }
        }
        // If all templates were successfully proven
        println!("  Base case: Verification successful.");
        return Ok(verification_state); // <-- Return the state with the added proofs!
                                       // --- Verify Provability --- END ---

        // OLD Check (Removed): Kept for reference during development
        // if check_final_state_consistency(&initial_state, request_templates) {
        //      println!("  Base case: Already solved and consistent.");
        //      return Ok(initial_state);
        // } else {
        //     println!("  Base case: Solved but inconsistent with NEq templates. Failing.");
        //      return Err(ProverError::Unsatisfiable(
        //          "Search base case failed NotEqual constraint check".to_string(),
        //      ));
        // }
    }

    // 1. Select an unassigned variable (first one found with domain > 1)
    let (var_to_assign, (current_domain, _)) = initial_state
        .domains
        .iter()
        .find(|(_, (domain, _))| domain.len() > 1)
        .ok_or_else(|| {
            // Should not happen if the initial check passed, but good to handle
            ProverError::Internal("Search called but no variable needs assignment?".to_string())
        })?;

    let var_clone = var_to_assign.clone(); // Clone var name for printing/use
    let domain_clone = current_domain.clone(); // Clone domain to iterate over

    println!("  Selected variable: {}", var_clone.name);

    // 2. Iterate through values in the variable's domain
    for value in domain_clone {
        println!(
            "    Trying value: {:?} for variable {}",
            value, var_clone.name
        );

        // 3. Create a hypothetical state with the tentative assignment
        let mut hypothetical_state = initial_state.clone_state_for_search();
        let (target_domain, _) = hypothetical_state
            .domains
            .get_mut(&var_clone)
            .expect("Variable must exist in cloned state");
        *target_domain = HashSet::from([value.clone()]); // Assign the value

        // 4. Propagate constraints in the hypothetical state
        match prune_initial_domains(
            &mut hypothetical_state,
            indexes,
            equality_pairs,
            inequality_pairs,
        ) {
            Ok(_) => {
                // Propagation succeeded, no immediate contradiction
                println!("      Propagation succeeded.");

                // --- NEq Consistency Check (Kept for potential early exit) ---
                if !check_final_state_consistency(&hypothetical_state, request_templates) {
                    println!("      State inconsistent with NEq templates after propagation. Backtracking...");
                    continue; // Skip to the next value
                }
                // --- END: NEq Check ---

                // 5. Recursive call
                match perform_search(
                    hypothetical_state,
                    request_templates,
                    indexes,
                    custom_definitions,
                    equality_pairs,
                    inequality_pairs,
                    potential_constant_info, // Pass down (type should now match)
                ) {
                    // Pass custom_definitions
                    Ok(solved_state) => {
                        println!("      Recursive search found solution!");
                        return Ok(solved_state); // Solution found down this path
                    }
                    Err(ProverError::Unsatisfiable(_)) => {
                        println!("      Recursive search failed, backtracking...");
                        // Continue to the next value for var_to_assign
                    }
                    Err(e) => {
                        // Propagate other errors
                        println!("      Recursive search returned error: {:?}", e);
                        return Err(e);
                    }
                }
            }
            Err(ProverError::Unsatisfiable(msg)) => {
                // Propagation led to an empty domain (contradiction)
                println!(
                    "      Propagation failed for value {:?}: {}. Backtracking...",
                    value, msg
                );
                // Continue to the next value for var_to_assign
            }
            Err(e) => {
                // Other error during propagation
                println!("      Propagation returned error: {:?}", e);
                return Err(e);
            }
        }
    } // End loop through values

    // 6. If all values for the selected variable failed, backtrack
    println!(
        "  All values tried for variable {}, backtracking from this level.",
        var_clone.name
    );
    Err(ProverError::Unsatisfiable(format!(
        "Search failed: No consistent value found for variable '{}'",
        var_clone.name
    )))
}

/// Checks if a state (potentially partially assigned) violates NotEqual templates.
/// Returns true if consistent, false if a violation is found.
fn check_final_state_consistency(state: &SolverState, request_templates: &[StatementTmpl]) -> bool {
    for tmpl in request_templates {
        if tmpl.pred == Predicate::Native(NativePredicate::NotEqual) && tmpl.args.len() == 2 {
            // Get the relevant wildcards for the NEq arguments
            let wcs1 = pruning::get_wildcards_from_tmpl_arg(&tmpl.args[0]);
            let wcs2 = pruning::get_wildcards_from_tmpl_arg(&tmpl.args[1]);

            // Check Pod wildcards
            if let (Some(wc1), Some(wc2)) = (wcs1.pod_wcs.get(0), wcs2.pod_wcs.get(0)) {
                if !check_neq_consistency_for_pair(state, wc1, wc2) {
                    return false;
                }
            }
            // Check Key wildcards
            if let (Some(wc1), Some(wc2)) = (wcs1.key_wcs.get(0), wcs2.key_wcs.get(0)) {
                if !check_neq_consistency_for_pair(state, wc1, wc2) {
                    return false;
                }
            }
            // Check Value wildcards
            if let (Some(wc1), Some(wc2)) = (wcs1.val_wcs.get(0), wcs2.val_wcs.get(0)) {
                if !check_neq_consistency_for_pair(state, wc1, wc2) {
                    return false;
                }
            }
        }
        // Add checks for other constraints if needed
    }
    true // No inconsistency found
}

/// Helper for check_final_state_consistency.
/// Checks if two wildcards violate a NotEqual constraint.
fn check_neq_consistency_for_pair(state: &SolverState, wc1: &Wildcard, wc2: &Wildcard) -> bool {
    if let (Some((domain1, _)), Some((domain2, _))) =
        (state.domains.get(wc1), state.domains.get(wc2))
    {
        if domain1.len() == 1 && domain2.len() == 1 {
            let val1 = domain1.iter().next().unwrap();
            let val2 = domain2.iter().next().unwrap();
            if val1 == val2 {
                println!(
                    "    Consistency Check Failed: NEq violated between {} ({:?}) and {} ({:?})",
                    wc1.name, val1, wc2.name, val2
                );
                return false; // Domains are singletons and equal, violates NEq
            }
        }
    }
    true // Consistent or not enough info to determine inconsistency
}

// Add a basic clone method to SolverState, maybe move later
// This is a simplified clone for search purposes, might need refinement
impl SolverState {
    fn clone_state_for_search(&self) -> Self {
        SolverState {
            // Deep clone domains and constraints as they are modified
            domains: self.domains.clone(),
            constraints: self.constraints.clone(),
            // Proof chains and scope are built up, clone is okay for backtracking start point
            proof_chains: self.proof_chains.clone(),
            scope: self.scope.clone(),
            params: self.params.clone(),
        }
    }
}
