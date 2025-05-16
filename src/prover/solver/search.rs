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
    initial_state: SolverState,
    request_templates: &[StatementTmpl],
    indexes: &ProverIndexes,
    custom_definitions: &CustomDefinitions,
    equality_pairs: &[(Wildcard, Wildcard)],
    inequality_pairs: &[(Wildcard, Wildcard)],
    potential_constant_info: &[(Wildcard, Key, Value)],
    current_search_depth: usize,
) -> Result<SolverState, ProverError> {
    const MAX_SEARCH_DEPTH: usize = 50;
    if current_search_depth > MAX_SEARCH_DEPTH {
        return Err(ProverError::MaxDepthExceeded(format!(
            "Search recursion depth exceeded maximum of {}",
            MAX_SEARCH_DEPTH
        )));
    }

    // Base case: all domains are singletons
    if initial_state
        .domains
        .values()
        .all(|(domain, _)| domain.len() == 1)
    {
        // Verify that all statements can be proven with the current assignment
        let mut verification_state = initial_state.clone_state_for_search();
        for tmpl in request_templates {
            match try_generate_concrete_candidate_and_bindings(tmpl, &verification_state) {
                Ok(Some((target_statement, _))) => {
                    match try_prove_statement(
                        &mut verification_state,
                        &target_statement,
                        indexes,
                        custom_definitions,
                        potential_constant_info,
                        0,
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
                    println!("    - Warning: Could not generate concrete statement from template {:?} in final check.", tmpl);
                    return Err(ProverError::Internal(format!(
                        "Failed to generate concrete statement in final verification: {:?}",
                        tmpl
                    )));
                }
                Err(e) => {
                    println!(
                        "    - Error generating concrete statement in final check: {:?}",
                        e
                    );
                    return Err(e);
                }
            }
        }
        println!("  Base case: Verification successful.");
        return Ok(verification_state);
    }

    // Select first unassigned variable (domain size > 1)
    let (var_to_assign, (current_domain, _)) = initial_state
        .domains
        .iter()
        .find(|(_, (domain, _))| domain.len() > 1)
        .ok_or_else(|| {
            ProverError::Internal("Search called but no variable needs assignment?".to_string())
        })?;

    let var_clone = var_to_assign.clone();
    let domain_clone = current_domain.clone();

    println!("  Selected variable: {}", var_clone.name);

    // Try each value in the variable's domain
    for value in domain_clone {
        println!(
            "    Trying value: {:?} for variable {}",
            value, var_clone.name
        );

        // Create new state with tentative assignment
        let mut hypothetical_state = initial_state.clone_state_for_search();
        let (target_domain, _) = hypothetical_state
            .domains
            .get_mut(&var_clone)
            .expect("Variable must exist in cloned state");
        *target_domain = HashSet::from([value.clone()]);

        // Propagate constraints
        match prune_initial_domains(
            &mut hypothetical_state,
            indexes,
            equality_pairs,
            inequality_pairs,
        ) {
            Ok(_) => {
                println!("      Propagation succeeded.");

                // Check for NotEqual constraint violations
                if !check_final_state_consistency(&hypothetical_state, request_templates) {
                    println!("      State inconsistent with NEq templates after propagation. Backtracking...");
                    continue;
                }

                // Recursively search with new state
                match perform_search(
                    hypothetical_state,
                    request_templates,
                    indexes,
                    custom_definitions,
                    equality_pairs,
                    inequality_pairs,
                    potential_constant_info,
                    current_search_depth + 1,
                ) {
                    Ok(solved_state) => {
                        println!("      Recursive search found solution!");
                        return Ok(solved_state);
                    }
                    Err(ProverError::Unsatisfiable(_)) => {
                        println!("      Recursive search failed, backtracking...");
                    }
                    Err(e) => {
                        println!("      Recursive search returned error: {:?}", e);
                        return Err(e);
                    }
                }
            }
            Err(ProverError::Unsatisfiable(msg)) => {
                println!(
                    "      Propagation failed for value {:?}: {}. Backtracking...",
                    value, msg
                );
            }
            Err(e) => {
                println!("      Propagation returned error: {:?}", e);
                return Err(e);
            }
        }
    }

    // All values failed, backtrack
    println!(
        "  All values tried for variable {}, backtracking from this level.",
        var_clone.name
    );
    Err(ProverError::Unsatisfiable(format!(
        "Search failed: No consistent value found for variable '{}'",
        var_clone.name
    )))
}

/// Checks if a state violates NotEqual templates.
/// Returns true if consistent, false if a violation is found.
fn check_final_state_consistency(state: &SolverState, request_templates: &[StatementTmpl]) -> bool {
    for tmpl in request_templates {
        if tmpl.pred == Predicate::Native(NativePredicate::NotEqual) && tmpl.args.len() == 2 {
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
    }
    true
}

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
                return false;
            }
        }
    }
    true
}

// Simplified clone for search purposes
impl SolverState {
    fn clone_state_for_search(&self) -> Self {
        SolverState {
            domains: self.domains.clone(),
            constraints: self.constraints.clone(),
            proof_chains: self.proof_chains.clone(),
            scope: self.scope.clone(),
            params: self.params.clone(),
        }
    }
}
