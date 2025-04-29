use std::collections::{HashMap, HashSet};

use crate::{
    middleware,
    middleware::{
        AnchoredKey, Key, KeyOrWildcard, NativePredicate, PodId, Predicate, Statement,
        StatementArg, StatementTmpl, StatementTmplArg, TypedValue, Value, Wildcard,
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
pub mod types; // Make types public within the solver module

#[cfg(test)]
mod tests; // Keep tests private to the solver module

// Use items brought into scope by the submodules
use initialization::initialize_solver_state;
use proof::try_prove_statement; // Import try_prove_statement
use pruning::prune_initial_domains;
use types::{Constraint, Domain, ExpectedType};

use crate::prover::types::ConcreteValue;

// Represents the overall state of the constraint solver
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
    // pub indexes: &'a ProverIndexes,
    // pub custom_definitions: &'a CustomDefinitions,
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

        // 3b. Generate candidate statements based on constraints and current domains
        // This is the complex part: turning templates + domains -> concrete statements
        // --- Pass original templates to candidate generator ---
        let candidate_statements =
            match generate_candidates_from_templates(&original_templates, &state) {
                Ok(candidates) => candidates,
                Err(e) => return Err(e), // Propagate errors if candidate generation fails
            };

        println!(
            "  - Generated {} candidates from templates",
            candidate_statements.len()
        );

        // 3c. Attempt to prove candidate statements
        let mut new_proofs_found = false;
        for target_statement in candidate_statements {
            // Skip if already proven in a previous iteration or as a base fact
            if state.proof_chains.contains_key(&target_statement) {
                continue;
            }

            match try_prove_statement(&mut state, &target_statement, indexes, custom_definitions) {
                Ok(_proof_chain) => {
                    // Proof succeeded! try_prove_statement updated state.proof_chains and state.scope
                    println!("  - Successfully proved: {:?}", target_statement);
                    new_proofs_found = true;

                    // Re-run pruning immediately if the new proof might affect domains.
                    // This is a simple approach; more targeted pruning could be added later.
                    // For now, re-prune after any successful proof.
                    let pruned_after_proof = prune_initial_domains(&mut state, indexes)?;
                    if pruned_after_proof {
                        println!("  - Pruning after new proof changed domains");
                        changed_in_iteration = true;
                    }
                }
                Err(ProverError::Unsatisfiable(msg)) => {
                    // If a candidate generated directly from the request templates (all wildcards were singletons)
                    // fails definitively, then the entire request is unsatisfiable.
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
                Err(e) => {
                    println!(
                        "  - Error proving candidate {:?}: {:?}",
                        target_statement, e
                    );
                    return Err(e);
                }
            }
        }

        if new_proofs_found && !changed_in_iteration {
            println!(
                "  - New proofs found, but pruning didn't change domains yet. Continuing loop."
            );
            changed_in_iteration = true; // Force next iteration to re-evaluate candidates/pruning
        }

        // TODO: Add more sophisticated domain pruning logic here based on newly proven facts.
    }

    if iteration >= MAX_ITERATIONS {
        return Err(ProverError::Other(
            "Solver reached maximum iterations, likely an infinite loop or complex case."
                .to_string(),
        ));
    }

    println!("Solver finished after {} iterations.", iteration);

    // 4. Search (If Necessary)
    if state.domains.values().any(|(domain, _)| domain.len() > 1) {
        println!("Domains still contain multiple values, entering Search phase (Not Implemented).");
        return Err(ProverError::NotImplemented(
            "Solver stage 4 (Search)".to_string(),
        ));
    }

    // 5. Solution Extraction
    println!("All domains have size 1, entering Solution Extraction phase (Not Implemented).");
    // ... Solution extraction logic ...

    Err(ProverError::NotImplemented(
        "Solver stage 5 (Solution Extraction)".to_string(),
    ))
}

/// Generates concrete candidate statements from original templates if all their wildcards have singleton domains.
fn generate_candidates_from_templates(
    templates: &[StatementTmpl],
    state: &SolverState,
) -> Result<Vec<Statement>, ProverError> {
    let mut candidates = Vec::new();
    for tmpl in templates {
        let mut concrete_args = Vec::with_capacity(tmpl.args.len());
        let mut all_singletons = true;
        let mut bindings = HashMap::new(); // Track concrete values for this template

        // First pass: Check if all wildcards are singletons and collect bindings
        for arg_tmpl in &tmpl.args {
            if !collect_singleton_bindings(arg_tmpl, state, &mut bindings)? {
                all_singletons = false;
                break; // No need to check further for this template
            }
        }

        if !all_singletons {
            continue; // Move to the next template
        }

        // Second pass: Construct concrete arguments using the collected bindings
        for arg_tmpl in &tmpl.args {
            match construct_concrete_arg(arg_tmpl, &bindings) {
                Ok(Some(arg)) => concrete_args.push(arg),
                Ok(None) => { /* Skip None args */ }
                Err(e) => return Err(e), // Propagate construction errors
            }
        }

        // Construct the concrete statement based on the predicate
        // This requires matching on tmpl.pred and calling the correct Statement variant constructor.
        let concrete_statement = build_concrete_statement(tmpl.pred.clone(), concrete_args)?;

        // Add if not already proven
        if !state.proof_chains.contains_key(&concrete_statement) {
            candidates.push(concrete_statement);
        }
    }
    Ok(candidates)
}

/// Helper to check domain size and collect singleton bindings for a template argument.
/// Returns Ok(true) if all involved wildcards are singletons, Ok(false) otherwise.
fn collect_singleton_bindings(
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
fn check_and_bind_singleton(
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
fn construct_concrete_arg(
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
                _ => {
                    return Err(ProverError::Internal(format!(
                        "Binding for Value wildcard '{}' not found or wrong type",
                        wc_val.name
                    )))
                }
            }
        }
        StatementTmplArg::Literal(v) => Ok(Some(StatementArg::Literal(v.clone()))), // Use StatementArg::Literal
        StatementTmplArg::None => Ok(None),
    }
}

/// Builds a concrete statement from a predicate and concrete arguments.
fn build_concrete_statement(
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
