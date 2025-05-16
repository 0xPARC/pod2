use std::collections::{HashMap, HashSet};

use crate::{
    middleware,
    middleware::{
        AnchoredKey, NativeOperation, NativePredicate, OperationType, Params, PodId, Predicate,
        Statement, StatementArg, Wildcard, WildcardValue,
    },
    prover::{
        error::ProverError,
        indexing::ProverIndexes,
        types::{ProofChain, ProofSolution},
    },
};

// Import items from submodules
mod initialization;
mod proof;
mod pruning;
mod search;
pub mod types; // Make types public within the solver module

pub mod tests; // Declare the public tests module directory

// Use items brought into scope by the submodules
use initialization::{initialize_solver_state, SolverContext};
use proof::try_prove_statement; // Import try_prove_statement
use pruning::{get_wildcards_from_tmpl_arg, prune_domains_after_proof, prune_initial_domains}; // Import helper
use search::perform_search;
use types::{Constraint, Domain, ExpectedType};

use crate::prover::types::ConcreteValue;

/// Represents the state of the constraint solver during search and proof generation.
/// Contains domains for wildcards, structural constraints, and proof chains.
#[derive(Clone)]
pub struct SolverState {
    /// Configuration parameters for the solver
    pub params: Params,
    /// Maps wildcards to their possible values and inferred types
    pub domains: HashMap<Wildcard, (Domain, ExpectedType)>,
    /// Constraints derived from request templates
    pub constraints: Vec<Constraint>,
    /// Maps proven statements to their proof chains
    pub proof_chains: HashMap<Statement, ProofChain>,
    /// Base facts required to support the final proof chains
    pub scope: HashSet<(PodId, Statement)>,
}

impl SolverState {
    /// Creates a new empty solver state with the given parameters
    pub fn new(params: Params) -> Self {
        Self {
            params,
            domains: HashMap::new(),
            constraints: Vec::new(),
            proof_chains: HashMap::new(),
            scope: HashSet::new(),
        }
    }
}

/// Solves a set of request templates by finding a consistent assignment of values to wildcards
/// and generating proofs for the resulting statements.
pub fn solve(
    request_templates: &[middleware::StatementTmpl],
    initial_facts: &[(PodId, Statement)],
    params: &Params,
    custom_definitions: &super::types::CustomDefinitions,
) -> Result<super::types::ProofSolution, super::error::ProverError> {
    // Initialize solver state and gather constant information
    let (mut state, potential_constant_info, self_facts) = initialize_solver_state(
        request_templates,
        &SolverContext {
            initial_facts,
            params,
            custom_definitions,
        },
    )?;

    // Build indexes from combined facts
    let mut combined_facts = initial_facts.to_vec();
    combined_facts.extend(self_facts);
    let solver_indexes = ProverIndexes::build(params.clone(), &combined_facts);

    // Extract equality/inequality pairs and apply initial pruning
    let (equality_pairs, inequality_pairs) = extract_implied_pairs(request_templates);
    let original_templates = request_templates.to_vec();

    prune_initial_domains(
        &mut state,
        &solver_indexes,
        &equality_pairs,
        &inequality_pairs,
    )?;

    // Iteratively propagate constraints and generate proofs
    let mut changed_in_iteration = true;
    let mut iteration = 0;
    const MAX_ITERATIONS: usize = 20;

    while changed_in_iteration && iteration < MAX_ITERATIONS {
        changed_in_iteration = false;
        iteration += 1;
        println!("Solver iteration {}", iteration);

        // Re-apply basic pruning
        let pruning_changed = prune_initial_domains(
            &mut state,
            &solver_indexes,
            &equality_pairs,
            &inequality_pairs,
        )?;
        if pruning_changed {
            println!("  - Pruning changed domains");
            changed_in_iteration = true;
        }

        // Try to generate and prove concrete statements
        let mut new_proofs_found_this_iter = false;
        let mut unsatisfiable_request_found = false;

        for tmpl in &original_templates {
            if unsatisfiable_request_found {
                break;
            }

            match try_generate_concrete_candidate_and_bindings(tmpl, &state) {
                Ok(Some((target_statement, bindings))) => {
                    if state.proof_chains.contains_key(&target_statement) {
                        continue;
                    }

                    match try_prove_statement(
                        &mut state,
                        &target_statement,
                        &solver_indexes,
                        custom_definitions,
                        &potential_constant_info,
                        0,
                    ) {
                        Ok(chain) => {
                            println!(
                                "  \\-> Proof found for request template {:?} (concrete: {:?}) -> {:?}",
                                tmpl.pred,
                                target_statement,
                                chain
                            );
                            new_proofs_found_this_iter = true;
                            changed_in_iteration = true;

                            // Apply dynamic pruning after successful proof
                            let pruned_dynamically = prune_domains_after_proof(
                                &mut state,
                                tmpl,
                                &target_statement,
                                &bindings,
                                &solver_indexes,
                            )?;

                            if pruned_dynamically {
                                println!("    - Dynamic pruning after proof changed domains.");
                                changed_in_iteration = true;
                            }
                        }
                        Err(ProverError::Unsatisfiable(msg)) => {
                            println!(
                                "  -> Unsatisfiable for request template {:?} (concrete: {:?}): {}. This path fails.",
                                tmpl.pred,
                                target_statement,
                                msg
                            );
                            // This path is unsatisfiable, mark for this search branch and potentially backtrack/fail search.
                            unsatisfiable_request_found = true;
                            break; // Stop processing other templates for this search node if one is unsatisfiable
                        }
                        Err(ProverError::ProofDeferred(msg)) => {
                            println!(
                                "  -> ProofDeferred for request template {:?} (concrete: {:?}): {}. Will re-attempt later.",
                                tmpl.pred,
                                target_statement,
                                msg
                            );
                            // Don't mark as unsatisfiable, don't necessarily break.
                            // The proof might become available in a later iteration if other WCs get constrained.
                            // We also don't set new_proofs_found_this_iter = true for a deferral.
                        }
                        Err(ProverError::MaxDepthExceeded(msg)) => {
                            println!(
                                "  -> MaxDepthExceeded for request template {:?} (concrete: {:?}): {}. This path fails.",
                                tmpl.pred,
                                target_statement,
                                msg
                            );
                            unsatisfiable_request_found = true; // Treat as failure for this search path
                            break;
                            return Err(ProverError::MaxDepthExceeded(format!(
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
                Ok(None) => {}
                Err(e) => return Err(e),
            }
        }

        if new_proofs_found_this_iter && !changed_in_iteration {
            println!(
                "  - New proofs found, but dynamic pruning didn't change domains. Continuing loop."
            );
            changed_in_iteration = true;
        }
    }

    if iteration >= MAX_ITERATIONS {
        return Err(ProverError::Other(
            "Solver reached maximum iterations, likely an infinite loop or complex case."
                .to_string(),
        ));
    }

    // Perform search if domains are not all singletons
    if state.domains.values().any(|(domain, _)| domain.len() > 1) {
        match perform_search(
            state,
            &original_templates,
            &solver_indexes,
            custom_definitions,
            &equality_pairs,
            &inequality_pairs,
            &potential_constant_info,
            0,
        ) {
            Ok(solved_state) => {
                state = solved_state;
            }
            Err(e) => return Err(e),
        }
    }

    // Extract final bindings and scope
    let final_bindings: HashMap<Wildcard, ConcreteValue> = state
        .domains
        .iter()
        .filter_map(|(wc, (domain, _))| {
            if domain.len() == 1 {
                Some((wc.clone(), domain.iter().next().unwrap().clone()))
            } else {
                println!(
                    "Warning: Wildcard {:?} still has non-singleton domain ({:?}) after solve/search.",
                    wc, domain
                );
                None
            }
        })
        .collect();

    // Determine minimal scope based on proof chains
    let mut final_scope = HashSet::new();
    for tmpl in &original_templates {
        let temp_state_for_generation = SolverState {
            params: state.params.clone(),
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
            constraints: vec![],
            proof_chains: HashMap::new(),
            scope: HashSet::new(),
        };

        if let Ok(Some((target_stmt, _))) =
            try_generate_concrete_candidate_and_bindings(tmpl, &temp_state_for_generation)
        {
            if let Some(chain) = state.proof_chains.get(&target_stmt) {
                chain.collect_scope(
                    &mut final_scope,
                    &state.proof_chains,
                    &solver_indexes.exact_statement_lookup,
                );
            } else if let Some((pod_id, base_stmt)) = solver_indexes
                .exact_statement_lookup
                .iter()
                .find(|(_, stmt)| stmt == &target_stmt)
            {
                final_scope.insert((*pod_id, base_stmt.clone()));
            }
        }
    }

    Ok(ProofSolution {
        bindings: final_bindings,
        scope: final_scope.into_iter().collect(),
        proof_chains: state.proof_chains,
    })
}

type WildcardPair = (Wildcard, Wildcard);
type CandidateAndBindings = (Statement, HashMap<Wildcard, ConcreteValue>);

/// Extracts equality and inequality pairs from request templates
fn extract_implied_pairs(
    request_templates: &[middleware::StatementTmpl],
) -> (Vec<WildcardPair>, Vec<WildcardPair>) {
    let mut equality_pairs = Vec::new();
    let mut inequality_pairs = Vec::new();

    for tmpl in request_templates {
        let is_eq = tmpl.pred == Predicate::Native(NativePredicate::Equal);
        let is_neq = tmpl.pred == Predicate::Native(NativePredicate::NotEqual)
            || tmpl.pred == Predicate::Native(NativePredicate::Gt)
            || tmpl.pred == Predicate::Native(NativePredicate::Lt);

        if (is_eq || is_neq) && tmpl.args.len() == 2 {
            let wcs1 = get_wildcards_from_tmpl_arg(&tmpl.args[0]);
            let wcs2 = get_wildcards_from_tmpl_arg(&tmpl.args[1]);

            let add_pairs =
                |wc_list1: &[Wildcard],
                 wc_list2: &[Wildcard],
                 target_list: &mut Vec<(Wildcard, Wildcard)>| {
                    if let (Some(wc1), Some(wc2)) = (wc_list1.get(0), wc_list2.get(0)) {
                        if wc1 != wc2 {
                            if wc1.index <= wc2.index {
                                target_list.push((wc1.clone(), wc2.clone()));
                            } else {
                                target_list.push((wc2.clone(), wc1.clone()));
                            }
                        }
                    }
                };

            if is_eq {
                // For Equal predicates, only infer equality for wildcards directly representing values.
                // Equality of AnchoredKeys (e.g., Equal(?P1[?K1], ?P2[?K2])) means the *values*
                // at those anchored keys are equal, not necessarily that ?P1=?P2 or ?K1=?K2.
                add_pairs(&wcs1.val_wcs, &wcs2.val_wcs, &mut equality_pairs);
            }

            if is_neq {
                // For NotEqual, Gt, Lt, if the values at AnchoredKeys are different,
                // it's safer to infer potential distinctness for the component wildcards.
                add_pairs(&wcs1.pod_wcs, &wcs2.pod_wcs, &mut inequality_pairs);
                add_pairs(&wcs1.key_wcs, &wcs2.key_wcs, &mut inequality_pairs);
                add_pairs(&wcs1.val_wcs, &wcs2.val_wcs, &mut inequality_pairs);
            }
        }
    }

    equality_pairs.sort_unstable_by_key(|(a, b)| (a.index, b.index));
    equality_pairs.dedup();
    inequality_pairs.sort_unstable_by_key(|(a, b)| (a.index, b.index));
    inequality_pairs.dedup();

    (equality_pairs, inequality_pairs)
}

/// Tries to generate a concrete statement and its bindings from a template,
/// succeeding only if all involved wildcards have singleton domains.
pub(super) fn try_generate_concrete_candidate_and_bindings(
    tmpl: &middleware::StatementTmpl,
    state: &SolverState,
) -> Result<Option<CandidateAndBindings>, ProverError> {
    let mut bindings = HashMap::new();

    // Check if all wildcards are singletons and collect bindings
    for arg_tmpl in &tmpl.args {
        match collect_singleton_bindings(arg_tmpl, state, &mut bindings) {
            Ok(true) => {}
            Ok(false) => return Ok(None),
            Err(e) => return Err(e),
        }
    }

    // Construct concrete statement based on predicate type
    let concrete_statement = match &tmpl.pred {
        Predicate::Native(_) => {
            let mut concrete_args = Vec::with_capacity(tmpl.args.len());
            for arg_tmpl in &tmpl.args {
                match construct_concrete_arg(arg_tmpl, &bindings) {
                    Ok(Some(arg)) => concrete_args.push(arg),
                    Ok(None) => {}
                    Err(e) => return Err(e),
                }
            }
            build_concrete_statement(tmpl.pred.clone(), concrete_args)?
        }
        Predicate::Custom(custom_ref) => {
            let mut custom_args = Vec::with_capacity(tmpl.args.len());
            for arg_tmpl in &tmpl.args {
                match arg_tmpl {
                    middleware::StatementTmplArg::WildcardLiteral(wc) => {
                        let bound_value = bindings.get(wc).ok_or_else(|| {
                            ProverError::Internal(format!(
                                "Binding for wildcard '{}' not found during Custom statement construction",
                                wc.name
                            ))
                        })?;
                        let wc_value = match bound_value {
                            ConcreteValue::Pod(id) => WildcardValue::PodId(*id),
                            ConcreteValue::Key(k) => {
                                WildcardValue::Key(middleware::Key::new(k.clone()))
                            }
                            ConcreteValue::Val(v) => {
                                return Err(ProverError::Internal(format!(
                                    "Attempted to pass ConcreteValue::Val ({:?}) as WildcardValue for WC '{}' in Custom statement construction",
                                    v, wc.name
                                )));
                            }
                        };
                        custom_args.push(wc_value);
                    }
                    middleware::StatementTmplArg::Literal(value) => {
                        // Handle literal arguments when a template calls a custom predicate.
                        // Per user clarification, these literals are expected to be strings for Keys.
                        match value.typed() {
                            crate::middleware::TypedValue::String(s) => {
                                custom_args
                                    .push(WildcardValue::Key(middleware::Key::new(s.clone())));
                            }
                            _ => {
                                return Err(ProverError::Internal(format!(
                                    "Invalid literal argument type {:?} found in template for Custom predicate call. Expected String for Key.",
                                    value.typed()
                                )));
                            }
                        }
                    }
                    _ => {
                        return Err(ProverError::Internal(format!(
                            "Invalid argument type {:?} found in template for Custom predicate call",
                            arg_tmpl
                        )));
                    }
                }
            }
            Statement::Custom(custom_ref.clone(), custom_args)
        }
        Predicate::BatchSelf(_) => {
            return Err(ProverError::Internal(
                "Cannot directly construct concrete BatchSelf statement during generation"
                    .to_string(),
            ));
        }
    };

    Ok(Some((concrete_statement, bindings)))
}

/// Checks if a wildcard's domain is a singleton and adds it to bindings if so
pub(super) fn check_and_bind_singleton(
    wildcard: &Wildcard,
    state: &SolverState,
    bindings: &mut HashMap<Wildcard, ConcreteValue>,
) -> Result<bool, ProverError> {
    if let Some((domain, _)) = state.domains.get(wildcard) {
        if domain.len() == 1 {
            if !bindings.contains_key(wildcard) {
                let concrete_value = domain.iter().next().unwrap().clone();
                bindings.insert(wildcard.clone(), concrete_value);
            }
            Ok(true)
        } else {
            Ok(false)
        }
    } else {
        Err(ProverError::Internal(format!(
            "Wildcard '{}' from template not found in solver state domains.",
            wildcard.name
        )))
    }
}

/// Checks if all wildcards in a template argument are singletons and collects their bindings
pub(super) fn collect_singleton_bindings(
    arg_tmpl: &middleware::StatementTmplArg,
    state: &SolverState,
    bindings: &mut HashMap<Wildcard, ConcreteValue>,
) -> Result<bool, ProverError> {
    match arg_tmpl {
        middleware::StatementTmplArg::Key(wc_pod, key_or_wc) => {
            if !check_and_bind_singleton(wc_pod, state, bindings)? {
                return Ok(false);
            }
            if let middleware::KeyOrWildcard::Wildcard(wc_key) = key_or_wc {
                if !check_and_bind_singleton(wc_key, state, bindings)? {
                    return Ok(false);
                }
            }
        }
        middleware::StatementTmplArg::WildcardLiteral(wc_val) => {
            if !check_and_bind_singleton(wc_val, state, bindings)? {
                return Ok(false);
            }
        }
        middleware::StatementTmplArg::Literal(_) | middleware::StatementTmplArg::None => {}
    }
    Ok(true)
}

/// Constructs a concrete StatementArg from a template argument using bindings
pub(super) fn construct_concrete_arg(
    arg_tmpl: &middleware::StatementTmplArg,
    bindings: &HashMap<Wildcard, ConcreteValue>,
) -> Result<Option<StatementArg>, ProverError> {
    match arg_tmpl {
        middleware::StatementTmplArg::Key(wc_pod, key_or_wc) => {
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
                middleware::KeyOrWildcard::Key(k) => k.clone(),
                middleware::KeyOrWildcard::Wildcard(wc_key) => match bindings.get(wc_key) {
                    Some(ConcreteValue::Key(k_name)) => middleware::Key::new(k_name.clone()),
                    _ => {
                        return Err(ProverError::Internal(format!(
                            "Binding for Key wildcard '{}' not found or wrong type",
                            wc_key.name
                        )))
                    }
                },
            };
            Ok(Some(StatementArg::Key(AnchoredKey::new(pod_id, key))))
        }
        middleware::StatementTmplArg::WildcardLiteral(wc_val) => match bindings.get(wc_val) {
            Some(ConcreteValue::Val(v)) => Ok(Some(StatementArg::Literal(v.clone()))),
            _ => Err(ProverError::Internal(format!(
                "Binding for Value wildcard '{}' not found or wrong type",
                wc_val.name
            ))),
        },
        middleware::StatementTmplArg::Literal(v) => Ok(Some(StatementArg::Literal(v.clone()))),
        middleware::StatementTmplArg::None => Ok(None),
    }
}

/// Builds a concrete statement from a predicate and concrete arguments
pub(super) fn build_concrete_statement(
    pred: Predicate,
    args: Vec<StatementArg>,
) -> Result<Statement, ProverError> {
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
        // Predicate::Native(NativePredicate::Gt) => {
        //     if args.len() == 2 {
        //         if let (StatementArg::Key(ak1), StatementArg::Key(ak2)) = (&args[0], &args[1]) {
        //             Ok(Statement::Gt(ak1.clone(), ak2.clone()))
        //         } else {
        //             Err(ProverError::Internal("Invalid args for Gt".to_string()))
        //         }
        //     } else {
        //         Err(ProverError::Internal(
        //             "Invalid arg count for Gt".to_string(),
        //         ))
        //     }
        // }
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
        Predicate::Custom(_) => Err(ProverError::NotImplemented(
            "Building concrete Custom statements".to_string(),
        )),
        Predicate::BatchSelf(_) => Err(ProverError::Internal(
            "Cannot directly build BatchSelf statement".to_string(),
        )),
        _ => Err(ProverError::Internal(format!(
            "Unhandled predicate type in build_concrete_statement: {:?}",
            pred
        ))),
    }
}

/// Recursively traverses proof steps to find all base facts needed
impl ProofChain {
    fn collect_scope(
        &self,
        final_scope: &mut HashSet<(PodId, Statement)>,
        all_chains: &HashMap<Statement, ProofChain>,
        base_facts: &HashSet<(PodId, Statement)>,
    ) {
        for step in &self.0 {
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
                if let Some((pod_id, base_stmt)) =
                    base_facts.iter().find(|(_, stmt)| stmt == &step.inputs[0])
                {
                    final_scope.insert((*pod_id, base_stmt.clone()));
                } else {
                    println!("Warning: Could not find origin PodId for base fact in scope collection: {:?}", step.inputs[0]);
                }
            } else {
                for input_stmt in &step.inputs {
                    if let Some((pod_id, base_stmt)) =
                        base_facts.iter().find(|(_, stmt)| stmt == input_stmt)
                    {
                        final_scope.insert((*pod_id, base_stmt.clone()));
                    } else if let Some(input_chain) = all_chains.get(input_stmt) {
                        input_chain.collect_scope(final_scope, all_chains, base_facts);
                    } else {
                        println!("Warning: Could not find proof chain or base fact for input statement during scope collection: {:?}", input_stmt);
                    }
                }
            }
        }
    }
}
