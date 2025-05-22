use std::collections::{HashMap, HashSet};

use log::{debug, error, info, trace, warn};

use crate::{
    middleware::{
        self, AnchoredKey, Key, NativeOperation, NativePredicate, OperationType, Params, PodId,
        Predicate, Statement, StatementArg, ToFields, Value, Wildcard, WildcardValue,
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
pub mod types; // Make types public within the solver module

//pub mod tests;

use initialization::initialize_solver_state;
use proof::try_prove_statement;
use pruning::{get_wildcards_from_tmpl_arg, prune_domains_after_proof, prune_initial_domains};
use types::{
    Domain, ExpectedType, GlobalContext, MemoizationKey, MemoizedProofOutcome, ResolveScope,
    WildcardInterpretation,
};

use crate::prover::error::DeferralReason; // Corrected import path
use crate::prover::types::ConcreteValue;

/// Represents the state of the constraint solver during search and proof generation.
/// Contains domains for wildcards, structural constraints, and proof chains.
#[derive(Clone)]
pub struct SolverState {
    /// Configuration parameters for the solver
    // pub params: Params, // Removed as per plan
    /// Maps wildcards to their possible values and inferred types
    pub domains: HashMap<Wildcard, (Domain, ExpectedType)>,
    /// Constraints derived from request templates
    // pub constraints: Vec<Constraint>, // Removed as per plan
    /// Maps proven statements to their proof chains
    pub proof_chains: HashMap<Statement, ProofChain>,
    /// Base facts required to support the final proof chains
    pub scope: HashSet<(PodId, Statement)>,
    /// Cache for memoizing proof outcomes to avoid re-computation.
    pub memoization_cache: HashMap<MemoizationKey, MemoizedProofOutcome>,
    /// Tracks active custom predicate calls to detect cycles.
    pub active_custom_calls: HashSet<MemoizationKey>,
    /// Locally discovered potential constants, e.g. ValueOf(?SELF_HOLDER["key"], val) from custom predicate bodies
    pub local_potential_constant_info: Vec<(Wildcard, Key, Value)>,
}

impl SolverState {
    /// Creates a new empty solver state
    pub fn new() -> Self {
        // params argument kept for now, but unused, to minimize call-site changes initially
        Self {
            // params, // Removed
            domains: HashMap::new(),
            // constraints: Vec::new(), // Removed
            proof_chains: HashMap::new(),
            scope: HashSet::new(),
            memoization_cache: HashMap::new(),
            active_custom_calls: HashSet::new(),
            local_potential_constant_info: Vec::new(),
        }
    }

    pub(super) fn clone_state_for_search(&self) -> Self {
        Self {
            // params: self.params.clone(), // Removed
            domains: self.domains.clone(),
            // constraints: self.constraints.clone(), // Removed
            proof_chains: self.proof_chains.clone(),
            scope: self.scope.clone(),
            memoization_cache: self.memoization_cache.clone(),
            active_custom_calls: self.active_custom_calls.clone(),
            local_potential_constant_info: self.local_potential_constant_info.clone(),
        }
    }
}

impl Default for SolverState {
    fn default() -> Self {
        Self::new()
    }
}

// Helper to get all wildcards from a StatementTmpl (used for initial ResolveScope)
fn get_all_wildcards_from_tmpl(tmpl: &middleware::StatementTmpl) -> HashSet<Wildcard> {
    let mut wildcards = HashSet::new();
    for arg in &tmpl.args {
        match arg {
            middleware::StatementTmplArg::Key(w, kw_opt) => {
                wildcards.insert(w.clone());
                if let middleware::KeyOrWildcard::Wildcard(ref kw) = kw_opt {
                    wildcards.insert(kw.clone());
                }
            }
            middleware::StatementTmplArg::WildcardLiteral(w) => {
                wildcards.insert(w.clone());
            }
            _ => {}
        }
    }
    wildcards
}

/// Helper function to infer types and populate initial domains for global wildcards in request templates.
/// This is called once in `solve` before the main resolution process begins.
fn infer_and_populate_request_wildcard_domains(
    state: &mut SolverState,
    top_level_resolve_scope: &ResolveScope<'_>, // To get templates and interpretation map
    global_context: &GlobalContext<'_>,
) -> Result<(), ProverError> {
    for tmpl in top_level_resolve_scope.templates_to_resolve {
        // Case 1: Custom Predicate
        if let Predicate::Custom(custom_ref) = &tmpl.pred {
            let (custom_pred_def, batch_arc_opt) = global_context
                .custom_definitions
                .get(&Predicate::Custom(custom_ref.clone()).to_fields(global_context.params))
                .map(|(def, batch)| (def.clone(), Some(batch.clone()))) // Clone to avoid lifetime issues if any; def is CustomPredicate, batch is Arc
                .ok_or_else(|| {
                    ProverError::Internal(format!(
                        "Custom def not found for Custom tmpl in initial population: {:?}",
                        custom_ref
                    ))
                })?;

            for (arg_idx, arg_tmpl_val) in tmpl.args.iter().enumerate() {
                if arg_idx >= custom_pred_def.args_len {
                    // This arg in the template is not mapping to a formal public parameter of the custom predicate.
                    // This could be an error or a feature allowing extra literals, but for type inference of global WCs, we only care about those mapped to formal params.
                    continue;
                }

                let wc_in_template_arg = match arg_tmpl_val {
                    middleware::StatementTmplArg::WildcardLiteral(wc) => wc,
                    // If it's not a WildcardLiteral, it can't be a global wildcard being passed as an argument.
                    _ => continue,
                };

                if let Some(WildcardInterpretation::Global(global_wc)) = top_level_resolve_scope
                    .wildcard_interpretation_map
                    .get(wc_in_template_arg)
                {
                    let mut visited_type_inference = HashSet::new(); // Fresh for each top-level public arg type inference

                    let inferred_type = initialization::infer_type_for_custom_pred_public_arg(
                        &custom_pred_def, // Pass by reference
                        arg_idx,
                        global_context,
                        batch_arc_opt.as_ref(), // Option<&Arc<CustomPredicateBatch>>
                        &mut visited_type_inference,
                    )?;

                    debug!("Initial population: For global WC {:?} (from template arg {:?}, mapping to public arg #{} of {}), inferred type: {:?}", global_wc, wc_in_template_arg, arg_idx, custom_pred_def.name, inferred_type);

                    initialization::update_solver_wildcard_type(
                        state,
                        global_wc, // The actual global wildcard
                        inferred_type,
                        false, // It's a global wildcard, not a new private local
                        Some(global_context.indexes),
                    )?;
                } else {
                    // This means wc_in_template_arg was not found in the map, or it wasn't a Global interpretation.
                    // For top-level requests, all wildcards passed to custom predicates should be Global.
                    warn!("Initial population: Wildcard {:?} in custom predicate template arg not found as Global in interpretation map.", wc_in_template_arg);
                }
            }
        }
        // Case 2: Native Predicates
        else if let Predicate::Native(_) = &tmpl.pred {
            for arg_tmpl_val in &tmpl.args {
                match arg_tmpl_val {
                    middleware::StatementTmplArg::Key(wc_pod_template, key_or_wc_template) => {
                        if let Some(WildcardInterpretation::Global(global_wc_pod)) =
                            top_level_resolve_scope
                                .wildcard_interpretation_map
                                .get(wc_pod_template)
                        {
                            initialization::update_solver_wildcard_type(
                                state,
                                global_wc_pod,
                                ExpectedType::Pod,
                                false,
                                Some(global_context.indexes),
                            )?;
                        }
                        if let middleware::KeyOrWildcard::Wildcard(wc_key_template) =
                            key_or_wc_template
                        {
                            if let Some(WildcardInterpretation::Global(global_wc_key)) =
                                top_level_resolve_scope
                                    .wildcard_interpretation_map
                                    .get(wc_key_template)
                            {
                                initialization::update_solver_wildcard_type(
                                    state,
                                    global_wc_key,
                                    ExpectedType::Key,
                                    false,
                                    Some(global_context.indexes),
                                )?;
                            }
                        }
                    }
                    middleware::StatementTmplArg::WildcardLiteral(wc_val_template) => {
                        if let Some(WildcardInterpretation::Global(global_wc_val)) =
                            top_level_resolve_scope
                                .wildcard_interpretation_map
                                .get(wc_val_template)
                        {
                            initialization::update_solver_wildcard_type(
                                state,
                                global_wc_val,
                                ExpectedType::Val,
                                false,
                                Some(global_context.indexes),
                            )?;
                        }
                    }
                    _ => {} // Literals or None args don't involve global wildcards here
                }
            }
        }
    }
    Ok(())
}

fn resolve_templates(
    global_context: &GlobalContext<'_>,
    resolve_scope: &mut ResolveScope<'_>, // Made mutable to populate constraints
    mut solver_state: SolverState,
) -> Result<SolverState, ProverError> {
    let mut deferred_private_wildcards: Vec<Wildcard> = Vec::new(); // Initialize here
                                                                    // i. Scoped Constraint Generation:
    resolve_scope.constraints.clear(); // Clear for the current scope resolution
    debug!(
        "resolve_templates (depth {}): Entered for templates: {:?}",
        resolve_scope.current_depth,
        resolve_scope
            .templates_to_resolve
            .iter()
            .map(|t| t.pred.clone())
            .collect::<Vec<_>>()
    );

    // Call the new (currently stubbed) constraint generation function.
    // `current_batch_arc` needs to be determined based on whether this is a custom predicate call.
    // For the top-level call, it would be None. This will be refined when try_prove_statement calls this.
    let current_batch_arc_for_body: Option<
        std::sync::Arc<crate::middleware::CustomPredicateBatch>,
    > = if let Some(parent_key) = &resolve_scope.parent_custom_call_key {
        match parent_key {
            MemoizationKey::Custom {
                predicate_ref_id, ..
            } => global_context
                .custom_definitions
                .get(predicate_ref_id)
                .map(|(_, batch_arc_from_def)| batch_arc_from_def.clone()),
            MemoizationKey::Native(_) => None,
        }
    } else {
        None
    };

    let mut visited_parse_keys = HashSet::new(); // Should be initialized appropriately for the scope

    initialization::generate_constraints_for_resolve_scope(
        resolve_scope,
        global_context,
        &mut solver_state,
        current_batch_arc_for_body, // Pass the determined batch arc
        &mut visited_parse_keys,
    )?;

    // ii. Iterative Proving & Pruning Loop (adapted from IterativeSolver::run)
    const MAX_ITERATIONS: usize = 20;
    // Loop control: renamed from changed_in_iteration to progress_this_main_iter
    let mut progress_this_main_iter = true;
    let mut iteration = 0;

    // Need equality_pairs and inequality_pairs for this scope.
    // These should be derived from the actual `resolve_scope.constraints` once populated.
    // For now, deriving from templates_to_resolve is a temporary measure.
    let (equality_pairs, inequality_pairs) =
        extract_implied_pairs(resolve_scope.templates_to_resolve);
    debug!(
        "resolve_templates (depth {}): Equality pairs: {:?}, Inequality pairs: {:?}",
        resolve_scope.current_depth, equality_pairs, inequality_pairs
    );

    // Main iterative loop
    while progress_this_main_iter && iteration < MAX_ITERATIONS {
        // Reset progress flag for the current main iteration.
        // It will be set to true if any actual change (initial pruning, new proof added, dynamic pruning) occurs.
        progress_this_main_iter = false;
        iteration += 1;
        debug!(
            "resolve_templates iteration {} (depth {})",
            iteration, resolve_scope.current_depth
        );

        let initial_pruning_changed = prune_initial_domains(
            &mut solver_state,
            global_context.indexes,
            &equality_pairs,
            &inequality_pairs,
            &resolve_scope.constraints, // Use scoped constraints
        )?;
        debug!(
            "resolve_templates iter {}: prune_initial_domains changed: {}",
            iteration, initial_pruning_changed
        );

        if initial_pruning_changed {
            debug!("  - Initial pruning changed domains");
            progress_this_main_iter = true; // Dynamic pruning also signifies progress
        }

        // Renamed from new_proofs_found_this_iter. Tracks if any *genuinely new* proof was added in this main iteration.
        let mut any_new_proof_added_this_main_iter = false;
        let mut unsatisfiable_request_found = false;

        for tmpl in resolve_scope.templates_to_resolve {
            if unsatisfiable_request_found {
                break;
            }

            match try_generate_concrete_candidate_and_bindings(
                tmpl,
                &solver_state,
                resolve_scope,
                global_context,
            ) {
                Ok(Some((target_statement, bindings))) => {
                    // Check if this statement is already proven and stored.
                    if solver_state.proof_chains.contains_key(&target_statement) {
                        trace!(
                            "  - Statement {:?} already in proof_chains, skipping re-proof attempt.",
                            target_statement
                        );
                        continue; // Skip to the next template if already processed.
                    }

                    debug!(
                        "  - Attempting to prove candidate (from template {:?}): {:?}",
                        tmpl.pred, target_statement
                    );
                    match try_prove_statement(
                        &mut solver_state,
                        &target_statement,
                        global_context,
                        resolve_scope.current_depth,
                    ) {
                        Ok(chain) => {
                            // Try to insert the proof.
                            // new_proof_added_this_main_iter is set true only if this insert was new.
                            if solver_state
                                .proof_chains
                                .insert(target_statement.clone(), chain.clone())
                                .is_none()
                            {
                                debug!(
                                    "  -> Proof found and ADDED for template {:?} (concrete: {:?}) -> CHAIN_LEN: {}",
                                    tmpl.pred, target_statement, chain.0.len()
                                );
                                any_new_proof_added_this_main_iter = true; // A genuinely new proof was added

                                let dynamic_pruning_changed = prune_domains_after_proof(
                                    &mut solver_state,
                                    tmpl,
                                    &target_statement,
                                    &bindings,
                                )?;

                                if dynamic_pruning_changed {
                                    debug!(
                                        "    - Dynamic pruning after proof for {:?} changed domains: {}",
                                        target_statement, dynamic_pruning_changed
                                    );
                                    progress_this_main_iter = true; // Dynamic pruning also signifies progress
                                }
                            } else {
                                // This case means try_prove_statement succeeded, but the statement was already in proof_chains upon insert.
                                // This could happen if contains_key check above failed (e.g., Hash/Eq issue) or complex race.
                                trace!(
                                    "  -> Proof found for {:?} (concrete: {:?}) but already existed in proof_chains upon insert. CHAIN_LEN: {}",
                                    tmpl.pred, target_statement, chain.0.len()
                                );
                            }
                        }
                        Err(ProverError::Unsatisfiable(msg)) => {
                            debug!(
                                "  -> Unsatisfiable for template {:?} (concrete: {:?}): {}. This path fails.",
                                tmpl.pred,
                                target_statement,
                                msg
                            );
                            unsatisfiable_request_found = true;
                            break;
                        }
                        Err(ProverError::ProofDeferred(reason)) => {
                            // Changed from msg to reason
                            // This is deferral from *generating* the concrete statement.
                            let mut handled_as_private_deferral = false;
                            if resolve_scope.parent_custom_call_key.is_some() {
                                if let DeferralReason::AmbiguousPrivateWildcard {
                                    wildcard_name,
                                    domain_size: _,
                                } = &reason
                                {
                                    let mut found_wc_to_defer: Option<Wildcard> = None;
                                    for interpretation in
                                        resolve_scope.wildcard_interpretation_map.values()
                                    {
                                        if let WildcardInterpretation::PrivateLocal(actual_wc) =
                                            interpretation
                                        {
                                            if &actual_wc.name == wildcard_name {
                                                // Verify this actual_wc is indeed non-singleton in the current state's domains
                                                if let Some((domain, _)) =
                                                    solver_state.domains.get(actual_wc)
                                                {
                                                    if domain.len() != 1 {
                                                        found_wc_to_defer = Some(actual_wc.clone());
                                                        break;
                                                    }
                                                }
                                            }
                                        }
                                    }

                                    if let Some(wc_to_defer) = found_wc_to_defer {
                                        debug!(
                                            "  -> ProofDeferred (structured) for private local WC '{}'. Adding to deferred list and continuing iteration.",
                                            wc_to_defer.name
                                        );
                                        if !deferred_private_wildcards.contains(&wc_to_defer) {
                                            deferred_private_wildcards.push(wc_to_defer);
                                        }
                                        handled_as_private_deferral = true;
                                    }
                                }
                            }

                            if !handled_as_private_deferral {
                                // If not handled as a specific private deferral that we will attempt to search with the new logic.
                                // This is the existing logic for when a ProofDeferred might be resolvable by the current scope's *own* search targets.
                                if resolve_scope.parent_custom_call_key.is_some()
                                    && resolve_scope.search_targets.as_ref().is_some_and(|st| {
                                        !st.is_empty()
                                            && st.iter().any(|search_wc| {
                                                solver_state
                                                    .domains
                                                    .get(search_wc)
                                                    .is_none_or(|(d, _)| d.len() != 1)
                                            })
                                    })
                                {
                                    debug!(
                                        "  -> ProofDeferred (from try_generate_concrete_candidate) for template {:?} (depth {}) in custom pred body: {}. Recording for potential scoped search by THIS custom pred's resolve_templates call.",
                                        tmpl.pred, resolve_scope.current_depth, reason // Use reason here
                                    );
                                } else {
                                    debug!(
                                        "  -> ProofDeferred (from try_generate_concrete_candidate) for template {:?} (depth {}): {}. Propagating directly.",
                                        tmpl.pred, resolve_scope.current_depth, reason // Use reason here
                                    );
                                    return Err(ProverError::ProofDeferred(reason));
                                    // Propagate the original reason
                                }
                            }
                        }
                        Err(ProverError::MaxDepthExceeded(msg)) => {
                            warn!(
                                "  -> MaxDepthExceeded for template {:?} (concrete: {:?}): {}. Path fails.",
                                tmpl.pred,
                                target_statement,
                                msg
                            );
                            return Err(ProverError::MaxDepthExceeded(msg)); // Propagate
                        }
                        Err(e) => {
                            error!(
                                "  - Error proving candidate {:?}: {:?}",
                                target_statement, e
                            );
                            return Err(e);
                        }
                    }
                }
                Ok(None) => {} // Template not yet concrete
                Err(e) => return Err(e),
            }
        }
        if unsatisfiable_request_found {
            // If a template was found to be unsatisfiable, this whole resolve_templates call for this path fails.
            return Err(ProverError::Unsatisfiable(
                "An unsatisfiable template was encountered during resolve_templates iteration"
                    .to_string(),
            ));
        }

        // If any new proof was added during the for-loop, that counts as progress for the main iteration.
        if any_new_proof_added_this_main_iter {
            progress_this_main_iter = true;
        }

        debug!(
            "  - Iteration {} results: any_new_proof_added_this_main_iter: {}, progress_this_main_iter_at_end_of_iter: {}",
            iteration, any_new_proof_added_this_main_iter, progress_this_main_iter
        );
    }

    if iteration >= MAX_ITERATIONS && progress_this_main_iter {
        warn!(
            "resolve_templates (depth {}) reached maximum iterations ({}) but was still making progress. Potential infinite loop or slow convergence.",
            resolve_scope.current_depth, MAX_ITERATIONS
        );
        // Depending on strictness, this might still be an error or a truncated success.
        // For now, let it be an error if max iterations are hit.
        return Err(ProverError::Other(
            "resolve_templates reached maximum iterations while still making progress.".to_string(),
        ));
    } else if iteration >= MAX_ITERATIONS {
        warn!(
            "resolve_templates (depth {}) reached maximum iterations ({}).",
            resolve_scope.current_depth, MAX_ITERATIONS
        );
        return Err(ProverError::Other(
            "resolve_templates reached maximum iterations in iterative phase.".to_string(),
        ));
    }

    // Determine if search is needed *before* logging it.
    let needs_search = if let Some(search_targets) = &resolve_scope.search_targets {
        search_targets.iter().any(|wc| {
            solver_state
                .domains
                .get(wc)
                .is_some_and(|(d, _)| d.len() > 1)
        })
    } else {
        // If no specific search_targets, search if *any* domain is non-singleton.
        // This branch is for the top-level call.
        solver_state.domains.values().any(|(d, _)| d.len() > 1)
    };

    debug!(
        "resolve_templates (depth {}): Iterative phase finished after {} iterations. Needs search: {}",
        resolve_scope.current_depth, iteration, needs_search
    );

    // iii. Scoped Search (if necessary):

    // First, handle deferred private wildcards specific to this custom predicate body's resolution
    if !deferred_private_wildcards.is_empty() && resolve_scope.parent_custom_call_key.is_some() {
        let wc_to_search = deferred_private_wildcards[0].clone(); // Simple strategy: pick the first one
        debug!(
            "resolve_templates (depth {}): Attempting private search for deferred private wildcard: '{}' (domain size: {}). Deferred list: {:?}",
            resolve_scope.current_depth,
            wc_to_search.name,
            solver_state.domains.get(&wc_to_search).map_or(0, |(d,_)| d.len()),
            deferred_private_wildcards.iter().map(|wc| wc.name.clone()).collect::<Vec<_>>(),
        );

        let (domain_values_to_try, _) = solver_state
            .domains
            .get(&wc_to_search)
            .cloned() // Clone the (Domain, ExpectedType) tuple
            .ok_or_else(|| {
                ProverError::Internal(format!(
                    "Private search: Deferred private wildcard '{}' not found in domains.",
                    wc_to_search.name
                ))
            })?;

        if domain_values_to_try.is_empty() || domain_values_to_try.len() == 1 {
            // This shouldn't happen if it caused a deferral due to ambiguity.
            warn!(
                "Private search: Deferred wildcard '{}' has domain size {} during search setup. Inconsistency?",
                wc_to_search.name, domain_values_to_try.len()
            );
            // Fall through to the needs_search logic, or return the original deferral if no other option.
            // For safety, let's propagate a generic deferral here as the state is unexpected.
            return Err(ProverError::ProofDeferred(DeferralReason::General(format!(
                "Deferred private wildcard '{}' had unexpected domain size {} during private search.",
                wc_to_search.name, domain_values_to_try.len()
            ))));
        }

        let mut first_private_deferral_error: Option<ProverError> = None;
        let (equality_pairs_for_prune, inequality_pairs_for_prune) =
            extract_implied_pairs(resolve_scope.templates_to_resolve);

        for value_to_try in domain_values_to_try {
            debug!(
                "Private search (depth {}): Trying value: {:?} for private wildcard '{}'",
                resolve_scope.current_depth, value_to_try, wc_to_search.name
            );
            let mut hypothetical_state = solver_state.clone_state_for_search();
            let (domain_in_hypothetical, _) =
                hypothetical_state.domains.get_mut(&wc_to_search).unwrap();
            *domain_in_hypothetical = HashSet::from([value_to_try.clone()]);

            match prune_initial_domains(
                &mut hypothetical_state,
                global_context.indexes,
                &equality_pairs_for_prune,
                &inequality_pairs_for_prune,
                &resolve_scope.constraints, // Constraints from the current resolve_scope (parent custom pred body)
            ) {
                Ok(_pruning_changed) => {
                    let mut next_resolve_scope = ResolveScope {
                        templates_to_resolve: resolve_scope.templates_to_resolve,
                        constraints: Vec::new(), // Will be regenerated by the recursive call
                        search_targets: resolve_scope.search_targets.clone(), // Preserve parent's search targets if any, though this search is for private WCs
                        wildcard_interpretation_map: resolve_scope
                            .wildcard_interpretation_map
                            .clone(),
                        public_arg_bindings: resolve_scope.public_arg_bindings, // Pass reference to public args of parent custom pred
                        current_depth: resolve_scope.current_depth, // Depth does not increase for this internal search of the same body
                        parent_custom_call_key: resolve_scope.parent_custom_call_key.clone(),
                    };

                    match resolve_templates(
                        global_context,
                        &mut next_resolve_scope,
                        hypothetical_state,
                    ) {
                        Ok(solved_branch_state) => {
                            debug!(
                                "Private search (depth {}): Recursive resolve_templates Succeeded for value {:?} of '{}'.",
                                resolve_scope.current_depth, value_to_try, wc_to_search.name
                            );
                            return Ok(solved_branch_state); // This private search path found a solution for the custom predicate body
                        }
                        Err(ProverError::Unsatisfiable(msg)) => {
                            debug!(
                                "Private search (depth {}): Recursive resolve_templates for value {:?} of '{}' was Unsatisfiable: {}. Backtracking private search...",
                                resolve_scope.current_depth, value_to_try, wc_to_search.name, msg
                            );
                            // Continue to next value_to_try for wc_to_search
                        }
                        Err(ProverError::ProofDeferred(reason)) => {
                            debug!(
                                "Private search (depth {}): Recursive resolve_templates for value {:?} of '{}' Deferred: {}. Recording and backtracking private search...",
                                resolve_scope.current_depth, value_to_try, wc_to_search.name, reason
                            );
                            if first_private_deferral_error.is_none() {
                                first_private_deferral_error =
                                    Some(ProverError::ProofDeferred(reason));
                            }
                            // Continue to next value_to_try for wc_to_search
                        }
                        Err(e) => {
                            // Other more serious error from the recursive call
                            error!(
                                "Private search (depth {}): Recursive resolve_templates for value {:?} of '{}' returned error: {:?}. Propagating.",
                                resolve_scope.current_depth, value_to_try, wc_to_search.name, e
                            );
                            return Err(e);
                        }
                    }
                }
                Err(ProverError::Unsatisfiable(msg)) => {
                    debug!(
                        "Private search (depth {}): Pruning failed for value {:?} of '{}': {}. Backtracking private search...",
                        resolve_scope.current_depth, value_to_try, wc_to_search.name, msg
                    );
                    // Continue to next value_to_try for wc_to_search
                }
                Err(e) => {
                    // Other more serious error from pruning
                    error!(
                        "Private search (depth {}): Pruning for value {:?} of '{}' returned error: {:?}. Propagating.",
                        resolve_scope.current_depth, value_to_try, wc_to_search.name, e
                    );
                    return Err(e);
                }
            }
        }

        // If loop finishes, no value for wc_to_search worked.
        if let Some(deferral_err) = first_private_deferral_error {
            debug!(
                "Private search (depth {}): All branches for '{}' were unsatisfiable or deferred. Propagating recorded deferral: {:?}",
                resolve_scope.current_depth, wc_to_search.name, deferral_err
            );
            return Err(deferral_err);
        }

        debug!(
            "Private search (depth {}): All values tried for private wildcard '{}', none led to a solution for the custom predicate body. Returning Unsatisfiable.",
            resolve_scope.current_depth, wc_to_search.name
        );
        return Err(ProverError::Unsatisfiable(format!(
            "Private search failed for depth {}: No consistent value found for private wildcard '{}' within its custom predicate body after trying all options.",
            resolve_scope.current_depth, wc_to_search.name
        )));
    }

    if needs_search {
        // MODIFIED: Check needs_search directly, which considers if search_targets exist and are non-singleton
        // Check depth condition for scoped search
        debug!(
            "resolve_templates (depth {}): Needs search for {:?}. Initiating scoped search.",
            resolve_scope.current_depth, resolve_scope.search_targets
        );

        // --- Begin integrated search logic (adapted from perform_search) ---
        let var_to_assign_wc = resolve_scope
            .search_targets
            .as_ref()
            .and_then(|targets| {
                targets.iter().find(|wc| {
                    solver_state
                        .domains
                        .get(*wc)
                        .is_some_and(|(d, _)| d.len() > 1)
                })
            })
            .or_else(|| {
                solver_state
                    .domains
                    .iter()
                    .find(|(_, (d, _))| d.len() > 1)
                    .map(|(wc, _)| wc)
            });

        let (var_to_assign, (current_domain_for_var, _)) = match var_to_assign_wc {
            Some(wc) => solver_state
                .domains
                .get(wc)
                .map(|d_et| (wc.clone(), d_et.clone())),
            None => {
                // This case should ideally be caught by `needs_search` being false.
                // If needs_search is true but we can't find a variable, it's an internal issue or all vars are singletons (which base case should handle).
                // For safety, if all domains are singletons (should have been caught by base case of search, or needs_search should be false)
                // we attempt to verify the current state. This is a bit redundant with the main solve loop's final verification
                // but acts as a safeguard if called recursively.
                let mut all_singletons = true;
                for tmpl_to_verify in resolve_scope.templates_to_resolve {
                    match try_generate_concrete_candidate_and_bindings(
                        tmpl_to_verify,
                        &solver_state,
                        resolve_scope,
                        global_context,
                    ) {
                        Ok(Some((target_stmt, _))) => {
                            if try_prove_statement(
                                &mut solver_state, // Note: This mutates solver_state, might need clone for verification only path
                                &target_stmt,
                                global_context,
                                resolve_scope.current_depth, // Use current depth for this verification proof attempt
                            )
                            .is_err()
                            {
                                all_singletons = false; // If any proof fails, it's not a valid solution for this path.
                                break;
                            }
                        }
                        _ => {
                            all_singletons = false;
                            break;
                        } // Cannot generate concrete or error.
                    }
                }
                if all_singletons {
                    return Ok(solver_state); // Current state is a solution for this branch.
                }
                // If not all singletons or verification failed, but no var_to_assign was found, that's an issue.
                return Err(ProverError::Internal(
                    "Scoped search needed but no variable to assign, or verification failed."
                        .to_string(),
                ));
            }
        }
        .ok_or_else(|| {
            ProverError::Internal(
                "Scoped search: Failed to get variable domain even after selecting variable."
                    .to_string(),
            )
        })?;

        let domain_values_to_try_global_search = current_domain_for_var.clone();
        debug!(
            "Scoped search (depth {}): Selected variable: {}, trying {} values: {:?}",
            resolve_scope.current_depth,
            var_to_assign.name,
            domain_values_to_try_global_search.len(),
            domain_values_to_try_global_search
        );

        let mut first_deferral_error_global_search: Option<ProverError> = None;

        for value_to_try_global_search in domain_values_to_try_global_search {
            debug!(
                "Scoped search (depth {}): Trying value: {:?} for variable {}",
                resolve_scope.current_depth, value_to_try_global_search, var_to_assign.name
            );
            let mut hypothetical_state_global_search = solver_state.clone_state_for_search();
            let (domain_in_hypothetical_global, _) = hypothetical_state_global_search
                .domains
                .get_mut(&var_to_assign)
                .unwrap();
            *domain_in_hypothetical_global = HashSet::from([value_to_try_global_search.clone()]);

            // Constraints specific to this hypothesis might need re-evaluation or careful handling.
            // For now, use the existing resolve_scope constraints and let prune_initial_domains work.
            let (equality_pairs_for_global_prune, inequality_pairs_for_global_prune) =
                extract_implied_pairs(resolve_scope.templates_to_resolve);

            match prune_initial_domains(
                &mut hypothetical_state_global_search,
                global_context.indexes,
                &equality_pairs_for_global_prune,
                &inequality_pairs_for_global_prune,
                &resolve_scope.constraints, // Constraints from the current resolve_scope
            ) {
                Ok(_pruning_changed) => {
                    debug!(
                        "Scoped search (depth {}): Pruning for value {:?} succeeded. Recursive call to resolve_templates.",
                        resolve_scope.current_depth, value_to_try_global_search
                    );
                    // Recursively call resolve_templates for this hypothesis.
                    // Create a new ResolveScope for the recursive call - for now, clone and increment depth.
                    let mut next_resolve_scope_global_search = ResolveScope {
                        templates_to_resolve: resolve_scope.templates_to_resolve,
                        constraints: Vec::new(), // Will be regenerated by the recursive call
                        search_targets: resolve_scope.search_targets.clone(),
                        wildcard_interpretation_map: resolve_scope
                            .wildcard_interpretation_map
                            .clone(),
                        public_arg_bindings: resolve_scope.public_arg_bindings,
                        current_depth: resolve_scope.current_depth + 1, // Increment depth for this search path
                        parent_custom_call_key: resolve_scope.parent_custom_call_key.clone(),
                    };

                    match resolve_templates(
                        global_context,
                        &mut next_resolve_scope_global_search,
                        hypothetical_state_global_search,
                    ) {
                        Ok(solved_branch_state_global) => {
                            debug!("Scoped search (depth {}): Recursive call to resolve_templates succeeded for value {:?}.", resolve_scope.current_depth, value_to_try_global_search);
                            return Ok(solved_branch_state_global); // This branch found a solution
                        }
                        Err(ProverError::Unsatisfiable(msg)) => {
                            debug!(
                                "Scoped search (depth {}): Recursive call for value {:?} was unsatisfiable ({}). Backtracking...",
                                resolve_scope.current_depth, value_to_try_global_search, msg
                            );
                            // Continue to next value in domain_values_to_try_global_search
                        }
                        Err(ProverError::ProofDeferred(reason_global_search)) => {
                            debug!(
                                "Scoped search (depth {}): Recursive call for value {:?} deferred ({}). Recording and backtracking...",
                                resolve_scope.current_depth, value_to_try_global_search, reason_global_search
                            );
                            if first_deferral_error_global_search.is_none() {
                                first_deferral_error_global_search =
                                    Some(ProverError::ProofDeferred(reason_global_search));
                            }
                            // Continue to next value, but keep track of deferral
                        }
                        Err(e) => {
                            debug!(
                                "Scoped search (depth {}): Recursive call returned error: {:?}. Propagating.",
                                resolve_scope.current_depth, e
                            );
                            return Err(e); // Propagate other errors
                        }
                    }
                }
                Err(ProverError::Unsatisfiable(msg)) => {
                    debug!(
                        "Scoped search (depth {}): Pruning failed for value {:?} ({}). Backtracking...",
                        resolve_scope.current_depth, value_to_try_global_search, msg
                    );
                    // Continue to next value
                }
                Err(e) => {
                    debug!(
                        "Scoped search (depth {}): Pruning returned error: {:?}. Propagating.",
                        resolve_scope.current_depth, e
                    );
                    return Err(e); // Propagate other errors
                }
            }
        }
        // If loop finishes, no value worked.
        if let Some(deferral_err_global) = first_deferral_error_global_search {
            debug!("Scoped search (depth {}): All branches unsatisfiable or deferred. Propagating deferral.", resolve_scope.current_depth);
            return Err(deferral_err_global);
        }
        debug!("Scoped search (depth {}): All values tried for variable {}, none led to a solution. Backtracking from this level.", resolve_scope.current_depth, var_to_assign.name);
        return Err(ProverError::Unsatisfiable(format!(
            "Scoped search failed for depth {}: No consistent value found for variable '{}' within its current scope and search targets.",
            resolve_scope.current_depth, var_to_assign.name
        )));
        // --- End integrated search logic ---
    }
    debug!(
        "resolve_templates (depth {}): Returning Ok.",
        resolve_scope.current_depth
    );

    Ok(solver_state)
}

/// Solves a set of request templates by finding a consistent assignment of values to wildcards
/// and generating proofs for the resulting statements.
pub fn solve(
    request_templates: &[middleware::StatementTmpl],
    initial_facts: &[(PodId, Statement)],
    params: &Params,
    custom_definitions: &super::types::CustomDefinitions,
) -> Result<super::types::ProofSolution, super::error::ProverError> {
    info!(
        "Solver: Starting solve for {} request templates with {} initial facts.",
        request_templates.len(),
        initial_facts.len()
    );
    // Call initialize_solver_state first (it no longer needs ProverIndexes)
    let (mut state, potential_constant_info, self_facts) =
        initialize_solver_state(request_templates, params, custom_definitions)?;
    info!(
        "Solver: Initialization complete. Initial domains: {:?}. Potential constants: {}, Self facts: {}",
        state.domains.keys().map(|k| k.name.clone()).collect::<Vec<_>>(),
        potential_constant_info.len(),
        self_facts.len()
    );

    // Combine initial_facts with self_facts generated during initialization
    let mut combined_facts = initial_facts.to_vec();
    combined_facts.extend(self_facts);

    debug!("Combined facts count: {}", combined_facts.len());

    // 2. Build ProverIndexes
    let solver_indexes = ProverIndexes::build(params.clone(), &combined_facts);
    info!(
        "Solver: ProverIndexes built. value_map size: {}, key_to_id size: {}",
        solver_indexes.value_map.len(),
        solver_indexes.key_to_id.len()
    );

    // 3. Create GlobalContext
    let global_context = GlobalContext {
        indexes: &solver_indexes,
        custom_definitions,
        params,
        potential_constant_info: &potential_constant_info, // Use from init
    };

    // NOTE: The old domain population loop that was here has been removed.
    // Type inference and initial domain population for request wildcards will now occur
    // robustly inside the first call to generate_constraints_for_resolve_scope
    // triggered by resolve_templates, using the real global_context.indexes.
    // solver_state.domains at this point still has wildcards with Unknown type and empty domains from the simplified init.

    // 4. Create top-level ResolveScope for the request templates
    let mut top_level_wildcard_interpretation_map = HashMap::new();
    let mut all_wcs_in_request = HashSet::new();
    for tmpl in request_templates {
        all_wcs_in_request.extend(get_all_wildcards_from_tmpl(tmpl));
    }
    for wc in all_wcs_in_request {
        top_level_wildcard_interpretation_map
            .insert(wc.clone(), WildcardInterpretation::Global(wc));
    }

    let mut top_level_resolve_scope = ResolveScope {
        templates_to_resolve: request_templates,
        constraints: Vec::new(),
        search_targets: None,
        wildcard_interpretation_map: top_level_wildcard_interpretation_map,
        public_arg_bindings: None,
        current_depth: 0,
        parent_custom_call_key: None,
    };

    // NEW: Infer types and populate initial domains for request wildcards directly into `state`.
    if let Err(e) = infer_and_populate_request_wildcard_domains(
        &mut state,
        &top_level_resolve_scope,
        &global_context,
    ) {
        error!(
            "Solver: Error during initial domain population for request wildcards: {:?}",
            e
        );
        return Err(e);
    }
    debug!(
        "Solver: State after initial domain population for request WCs. Domains: {:?}",
        state
            .domains
            .iter()
            .map(|(wc, (d, t))| (&wc.name, d.len(), t))
            .collect::<Vec<_>>()
    );
    // ADDED LOG: Specifically check CONST's domain and type here
    if let Some(const_wc_for_log) = state.domains.keys().find(|k| k.name == "CONST") {
        if let Some((domain, wc_type)) = state.domains.get(const_wc_for_log) {
            debug!(
                "solve() before resolve_templates: CONST wildcard '{}': domain_size = {}, type = {:?}",
                const_wc_for_log.name, domain.len(), wc_type
            );
            if domain.len() == 1 {
                debug!(
                    "solve() before resolve_templates: CONST domain value: {:?}",
                    domain.iter().next().unwrap()
                );
            }
        } else {
            // Should not happen if found in keys
            debug!("solve() before resolve_templates: CONST wildcard somehow not found in get after being found in keys.");
        }
    } else {
        debug!("solve() before resolve_templates: CONST wildcard not found in domains.");
    }

    info!("Solver: Setup complete. Starting resolve_templates (depth 0).");
    match resolve_templates(
        &global_context,
        &mut top_level_resolve_scope,
        state.clone_state_for_search(),
    ) {
        Ok(resolved_state) => {
            state = resolved_state;
        }
        Err(ProverError::ProofDeferred(msg)) => {
            // If resolve_templates defers at the top level without initiating search (because depth was 0),
            // it implies that iterative proving alone wasn't enough and a search is likely needed.
            // We will proceed to the search block below if domains are still ambiguous.
            debug!("Top-level resolve_templates deferred: {}. Proceeding to check if search is needed.", msg);
        }
        Err(e) => return Err(e),
    }
    info!("Solver: Initial resolve_templates (depth 0) complete.");

    // Top-level search logic if domains are still ambiguous after initial resolve_templates call (depth 0)
    if state.domains.values().any(|(domain, _)| domain.len() > 1) {
        info!(
            "Solver: Top-level domains still ambiguous after initial resolve_templates. Initiating top-level search."
        );
        // Define equality_pairs and inequality_pairs for the top-level search,
        // based on the original request templates held in top_level_resolve_scope.templates_to_resolve.
        // These original templates are what the search is trying to satisfy.
        let (equality_pairs, inequality_pairs) =
            extract_implied_pairs(top_level_resolve_scope.templates_to_resolve);

        let mut search_state = state; // Start search with the state from resolve_templates

        // --- Begin top-level search logic (adapted from perform_search / resolve_templates internal search) ---
        let var_to_assign_wc = top_level_resolve_scope
            .search_targets // Use top-level scope's search_targets if any
            .as_ref()
            .and_then(|targets| {
                targets.iter().find(|wc| {
                    search_state
                        .domains
                        .get(*wc)
                        .is_some_and(|(d, _)| d.len() > 1)
                })
            })
            .or_else(|| {
                search_state
                    .domains
                    .iter()
                    .find(|(_, (d, _))| d.len() > 1)
                    .map(|(wc, _)| wc)
            });

        if let Some(var_wc_ref) = var_to_assign_wc {
            let var_to_assign = var_wc_ref.clone();
            let (current_domain_for_var, _) = search_state
                .domains
                .get(&var_to_assign)
                .expect("Var must exist")
                .clone();
            let domain_values_to_try = current_domain_for_var;

            debug!(
                "Top-level search: Selected variable: {}, trying {} values: {:?}",
                var_to_assign.name,
                domain_values_to_try.len(),
                domain_values_to_try
            );
            let mut solution_found_in_search = false;
            let mut first_deferral_error_top_level: Option<ProverError> = None;

            for value_to_try in domain_values_to_try {
                debug!(
                    "Top-level search: Trying value: {:?} for variable {}",
                    value_to_try, var_to_assign.name
                );
                let mut hypothetical_state_for_search = search_state.clone_state_for_search();
                let (domain_in_hypothetical, _) = hypothetical_state_for_search
                    .domains
                    .get_mut(&var_to_assign)
                    .unwrap();
                *domain_in_hypothetical = HashSet::from([value_to_try.clone()]);

                match prune_initial_domains(
                    &mut hypothetical_state_for_search,
                    global_context.indexes,
                    &equality_pairs,                      // Top-level equality pairs
                    &inequality_pairs,                    // Top-level inequality pairs
                    &top_level_resolve_scope.constraints, // Constraints from the top-level scope
                ) {
                    Ok(_) => {
                        debug!(
                            "Top-level search: Pruning for value {:?} succeeded. Recursive call to resolve_templates (depth 1).",
                             value_to_try
                        );
                        let mut next_resolve_scope_for_search = ResolveScope {
                            templates_to_resolve: top_level_resolve_scope.templates_to_resolve,
                            constraints: Vec::new(), // Will be regenerated
                            search_targets: top_level_resolve_scope.search_targets.clone(),
                            wildcard_interpretation_map: top_level_resolve_scope
                                .wildcard_interpretation_map
                                .clone(),
                            public_arg_bindings: None, // Top level has no public args from a parent call
                            current_depth: 1, // profundidad incrementada para la llamada recursiva
                            parent_custom_call_key: None,
                        };

                        match resolve_templates(
                            &global_context,
                            &mut next_resolve_scope_for_search,
                            hypothetical_state_for_search,
                        ) {
                            Ok(solved_branch_state) => {
                                debug!("Top-level search: Recursive call to resolve_templates succeeded for value {:?}.", value_to_try);
                                search_state = solved_branch_state; // Update state with the solution from this branch
                                solution_found_in_search = true;
                                break; // Found a solution
                            }
                            Err(ProverError::Unsatisfiable(msg)) => {
                                debug!(
                                    "Top-level search: Recursive call for value {:?} was unsatisfiable ({}). Backtracking...",
                                    value_to_try, msg
                                );
                            }
                            Err(ProverError::ProofDeferred(msg)) => {
                                debug!(
                                    "Top-level search: Recursive call for value {:?} deferred ({}). Recording...",
                                    value_to_try, msg
                                );
                                if first_deferral_error_top_level.is_none() {
                                    first_deferral_error_top_level =
                                        Some(ProverError::ProofDeferred(msg));
                                }
                            }
                            Err(e) => return Err(e), // Propagate other errors
                        }
                    }
                    Err(ProverError::Unsatisfiable(msg)) => {
                        debug!(
                            "Top-level search: Pruning failed for value {:?} ({}). Backtracking...",
                            value_to_try, msg
                        );
                    }
                    Err(e) => return Err(e), // Propagate other errors
                }
                if solution_found_in_search {
                    break;
                }
            }

            if !solution_found_in_search {
                if let Some(deferral_err) = first_deferral_error_top_level {
                    debug!("Top-level search: All branches unsatisfiable or deferred. Propagating deferral.");
                    return Err(deferral_err);
                }
                info!(
                    "Top-level search: All values tried for variable {}, none led to a solution.",
                    var_to_assign.name
                );
                return Err(ProverError::Unsatisfiable(format!(
                    "Top-level search failed: No consistent value found for variable '{}' after trying all options.",
                    var_to_assign.name
                )));
            }
        } else {
            // No variable to assign, but domains are still ambiguous. This is an inconsistency or means the initial check was flawed.
            // This state implies `state.domains.values().any(|(domain, _)| domain.len() > 1)` is true,
            // but `var_to_assign_wc` was None.
            return Err(ProverError::Unsatisfiable(
                "Top-level search: Domains are ambiguous but no specific variable found for assignment.".to_string(),
            ));
        }
        state = search_state; // Update main state with the result of the search
                              // --- End top-level search logic ---
    }

    // Ensure all wildcards from the original request_templates are properly resolved to singletons.
    // This check is crucial before declaring the solve process successful.
    for tmpl in request_templates {
        for wc_in_tmpl in get_all_wildcards_from_tmpl(tmpl) {
            match state.domains.get(&wc_in_tmpl) {
                Some((domain, wc_type)) => {
                    if domain.is_empty() {
                        error!(
                            "Solver: Wildcard {:?} (type: {:?}) from request templates has an EMPTY domain after solve. Current state domains: {:?}",
                            wc_in_tmpl, wc_type, state.domains.keys().map(|k| k.name.clone()).collect::<Vec<_>>()
                        );
                        return Err(ProverError::Unsatisfiable(format!(
                            "Wildcard '{}' from request templates has an empty domain after solve.",
                            wc_in_tmpl.name
                        )));
                    }
                    if domain.len() != 1 {
                        error!(
                            "Solver: Wildcard {:?} (type: {:?}) from request templates has non-singleton domain size {} ({:?}) after solve. Current state domains: {:?}",
                            wc_in_tmpl, wc_type, domain.len(), domain, state.domains.keys().map(|k| k.name.clone()).collect::<Vec<_>>()
                        );
                        return Err(ProverError::Unsatisfiable(format!(
                            "Wildcard '{}' from request templates resolved to a non-singleton domain (size {}) after solve.",
                            wc_in_tmpl.name, domain.len()
                        )));
                    }
                }
                None => {
                    // This case should ideally be prevented by initialization ensuring all request wildcards are in domains.
                    error!(
                        "Solver: Wildcard {:?} from request templates NOT FOUND in final domains after solve. Current state domains: {:?}",
                        wc_in_tmpl, state.domains.keys().map(|k| k.name.clone()).collect::<Vec<_>>()
                    );
                    return Err(ProverError::Internal(format!(
                        "Wildcard '{}' from request templates not found in final domains after solve.",
                        wc_in_tmpl.name
                    )));
                }
            }
        }
    }

    // Check for unresolved types before creating final_bindings
    for (wc, (domain, wc_type)) in &state.domains {
        // Consider only wildcards that were part of the original request templates or active in the proof process.
        // A simple check: if a domain is non-empty or it was part of the request, it was "used".
        // A more precise check might involve tracking all "active" wildcards.
        let is_request_wildcard = request_templates
            .iter()
            .any(|tmpl| get_all_wildcards_from_tmpl(tmpl).contains(wc));

        if *wc_type == ExpectedType::Unknown && (is_request_wildcard || !domain.is_empty()) {
            // Check if this Unknown wildcard was a private local that just didn't get used in a way to infer type
            // If it's a global request wildcard, it's definitely an error.
            // If it's a private local but its domain is not empty, it implies it was involved somehow but type not set.
            error!(
                    "Solver: Wildcard '{}' has an unresolved type 'Unknown' after solve. Domain size: {}.",
                    wc.name, domain.len()
                );
            return Err(ProverError::InconsistentWildcard(format!(
                "Wildcard '{}' has an unresolved type 'Unknown' after solve.",
                wc.name
            )));
        }
    }

    let final_bindings: HashMap<Wildcard, ConcreteValue> = state
        .domains
        .iter()
        .filter_map(|(wc, (domain, _))| {
            if domain.len() == 1 {
                Some((wc.clone(), domain.iter().next().unwrap().clone()))
            } else {
                warn!(
                    "Wildcard {:?} still has non-singleton domain ({:?}) after solve/search.",
                    wc, domain
                );
                None
            }
        })
        .collect();

    // Determine minimal scope based on proof chains
    let mut final_scope = HashSet::new();
    for tmpl in request_templates.iter() {
        let temp_state_for_generation = SolverState {
            // params: state.params.clone(), // Removed
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
            // constraints: vec![], // Removed
            proof_chains: HashMap::new(),
            scope: HashSet::new(),
            memoization_cache: HashMap::new(),
            active_custom_calls: HashSet::new(),
            local_potential_constant_info: Vec::new(),
        };

        if let Ok(Some((target_stmt, _))) = try_generate_concrete_candidate_and_bindings(
            tmpl,
            &temp_state_for_generation,
            &top_level_resolve_scope,
            &global_context,
        ) {
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

    info!(
        "Solver: Solve successful. Final bindings: {:?}, Scope size: {}, Proof chains: {}",
        final_bindings
            .keys()
            .map(|k| k.name.clone())
            .collect::<Vec<_>>(),
        final_scope.len(),
        state.proof_chains.len()
    );
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
    resolve_scope: &ResolveScope<'_>,
    global_context: &GlobalContext<'_>,
) -> Result<Option<CandidateAndBindings>, ProverError> {
    let mut bindings = HashMap::new();

    // Check if all wildcards are singletons and collect bindings
    for arg_tmpl in &tmpl.args {
        match collect_singleton_bindings(arg_tmpl, state, resolve_scope, &mut bindings) {
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
                match construct_concrete_arg(arg_tmpl, &bindings, state, resolve_scope) {
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
                    middleware::StatementTmplArg::WildcardLiteral(wc_template_at_call_site) => {
                        let interpretation = resolve_scope.wildcard_interpretation_map.get(wc_template_at_call_site)
                            .ok_or_else(|| ProverError::Internal(format!(
                                "Custom: Wildcard '{}' from custom template arg not found in interpretation map.", wc_template_at_call_site.name
                            )))?;

                        let wc_value = match interpretation {
                            WildcardInterpretation::PublicArg(idx_of_callers_public_arg) => {
                                resolve_scope.public_arg_bindings
                                    .and_then(|bindings_map| bindings_map.get(idx_of_callers_public_arg))
                                    .cloned()
                                    .ok_or_else(|| ProverError::Internal(format!(
                                        "Custom: Public argument binding for index {} (WC '{}') not found in current scope.",
                                        idx_of_callers_public_arg, wc_template_at_call_site.name
                                    )))?
                            }
                            WildcardInterpretation::PrivateLocal(resolved_wc) | WildcardInterpretation::Global(resolved_wc) => {
                                // wc_template_at_call_site is a local/global WC in the current resolve_scope.
                                // Its concrete value should be in `bindings` map, keyed by `wc_template_at_call_site`.
                                let bound_concrete_value = bindings.get(wc_template_at_call_site).ok_or_else(|| {
                                    ProverError::Internal(format!(
                                        "Custom: Binding for wildcard '{}' (resolved to {:?}) not found in collected bindings. Bindings map keys: {:?}",
                                        wc_template_at_call_site.name, resolved_wc, bindings.keys()
                                    ))
                                })?;
                                // Convert ConcreteValue to WildcardValue
                                match bound_concrete_value {
                                    ConcreteValue::Pod(id) => WildcardValue::PodId(*id),
                                    ConcreteValue::Key(k_name) => WildcardValue::Key(middleware::Key::new(k_name.clone())),
                                    ConcreteValue::Val(v) => {
                                        return Err(ProverError::Internal(format!(
                                            "Custom: Attempted to pass ConcreteValue::Val ({:?}) as WildcardValue for WC '{}' (resolved to {:?}) in Custom statement construction",
                                            v, wc_template_at_call_site.name, resolved_wc
                                        )));
                                    }
                                }
                            }
                        };
                        custom_args.push(wc_value);
                    }
                    middleware::StatementTmplArg::Literal(value) => match value.typed() {
                        crate::middleware::TypedValue::String(s) => {
                            custom_args.push(WildcardValue::Key(middleware::Key::new(s.clone())));
                        }
                        _ => {
                            return Err(ProverError::Internal(format!(
                                    "Custom: Invalid literal argument type {:?} for Custom. Expected String for Key.",
                                    value.typed()
                                )));
                        }
                    },
                    _ => {
                        return Err(ProverError::Internal(format!(
                            "Custom: Invalid argument type {:?} found in template for Custom call",
                            arg_tmpl
                        )));
                    }
                }
            }
            Statement::Custom(custom_ref.clone(), custom_args)
        }
        Predicate::BatchSelf(batch_idx) => {
            // 1. Get the batch of the *current* custom predicate whose body is being processed.
            let parent_batch_arc = if let Some(MemoizationKey::Custom {
                predicate_ref_id, ..
            }) = &resolve_scope.parent_custom_call_key
            {
                global_context.custom_definitions.get(predicate_ref_id)
                    .map(|(_, batch_arc_from_def)| batch_arc_from_def.clone())
                    .ok_or_else(|| ProverError::Internal(format!(
                        "BatchSelf: Parent custom predicate's batch not found for ref_id: {:?} during candidate generation.", predicate_ref_id
                    )))?
            } else {
                return Err(ProverError::Internal(
                    "BatchSelf: Not called from within a custom predicate context (missing parent_custom_call_key) during candidate generation.".to_string()
                ));
            };

            // 2. Create the CustomPredicateRef for the BatchSelf target.
            let target_custom_ref = middleware::CustomPredicateRef {
                batch: parent_batch_arc,
                index: *batch_idx,
            };

            // 3. Construct arguments (mirroring Predicate::Custom logic)
            let mut custom_args = Vec::with_capacity(tmpl.args.len());
            for arg_tmpl_val in &tmpl.args {
                match arg_tmpl_val {
                    middleware::StatementTmplArg::WildcardLiteral(
                        wc_template_in_batchself_call,
                    ) => {
                        // These wc_template_in_batchself_call are wildcards defined in the parent custom predicate's body.
                        // Their interpretation comes from the resolve_scope of the parent's body.
                        let interpretation = resolve_scope.wildcard_interpretation_map.get(wc_template_in_batchself_call)
                            .ok_or_else(|| ProverError::Internal(format!(
                                "BatchSelf: Wildcard '{}' from BatchSelf arg not found in interpretation map.", wc_template_in_batchself_call.name
                            )))?;

                        let wc_value = match interpretation {
                            WildcardInterpretation::PublicArg(idx_of_parent_arg) => {
                                // This wc_template_in_batchself_call is an alias for a public argument of the parent custom predicate.
                                resolve_scope.public_arg_bindings
                                    .and_then(|bindings_map| bindings_map.get(idx_of_parent_arg))
                                    .cloned()
                                    .ok_or_else(|| ProverError::Internal(format!(
                                        "BatchSelf: Public argument binding for parent's arg index {} (WC '{}') not found.",
                                        idx_of_parent_arg, wc_template_in_batchself_call.name
                                    )))?
                            }
                            WildcardInterpretation::PrivateLocal(resolved_wc)
                            | WildcardInterpretation::Global(resolved_wc) => {
                                // This wc_template_in_batchself_call is a private local wildcard (or a global one passed through).
                                // Its concrete value should be in `bindings` map, keyed by `wc_template_in_batchself_call`.
                                let bound_concrete_value = bindings.get(wc_template_in_batchself_call).ok_or_else(|| {
                                    ProverError::Internal(format!(
                                        "BatchSelf: Binding for wildcard '{}' (resolved to {:?}) not found in collected bindings. Bindings map keys: {:?}",
                                        wc_template_in_batchself_call.name, resolved_wc, bindings.keys()
                                    ))
                                })?;
                                // Convert ConcreteValue to WildcardValue
                                match bound_concrete_value {
                                    ConcreteValue::Pod(id) => WildcardValue::PodId(*id),
                                    ConcreteValue::Key(k_name) => {
                                        WildcardValue::Key(middleware::Key::new(k_name.clone()))
                                    }
                                    ConcreteValue::Val(v) => {
                                        return Err(ProverError::Internal(format!(
                                            "BatchSelf: Attempted to pass ConcreteValue::Val ({:?}) as WildcardValue for WC '{}' (resolved to {:?}) in BatchSelf statement construction",
                                            v, wc_template_in_batchself_call.name, resolved_wc
                                        )));
                                    }
                                }
                            }
                        };
                        custom_args.push(wc_value);
                    }
                    middleware::StatementTmplArg::Literal(value) => match value.typed() {
                        crate::middleware::TypedValue::String(s) => {
                            custom_args.push(WildcardValue::Key(middleware::Key::new(s.clone())));
                        }
                        _ => {
                            return Err(ProverError::Internal(format!(
                                    "BatchSelf: Invalid literal argument type {:?} for BatchSelf. Expected String for Key.",
                                    value.typed()
                                )));
                        }
                    },
                    _ => {
                        return Err(ProverError::Internal(format!(
                            "BatchSelf: Invalid argument type {:?} found in template for BatchSelf call",
                            arg_tmpl_val
                        )));
                    }
                }
            }
            Statement::Custom(target_custom_ref, custom_args)
        }
    };

    Ok(Some((concrete_statement, bindings)))
}

/// Checks if a wildcard's domain is a singleton and adds it to bindings if so.
/// This function now uses resolve_scope to interpret the wildcard.
pub(super) fn check_and_bind_singleton(
    wildcard_in_template: &Wildcard,
    state: &SolverState,
    resolve_scope: &ResolveScope<'_>,
    bindings: &mut HashMap<Wildcard, ConcreteValue>,
) -> Result<bool, ProverError> {
    let interpretation = resolve_scope.wildcard_interpretation_map.get(wildcard_in_template)
        .ok_or_else(|| ProverError::Internal(format!(
            "Wildcard '{}' from template not found in interpretation map during check_and_bind.", wildcard_in_template.name
        )))?;

    match interpretation {
        WildcardInterpretation::PublicArg(idx) => {
            if let Some(public_bindings_map) = resolve_scope.public_arg_bindings {
                if let Some(wc_val) = public_bindings_map.get(idx) {
                    let concrete_val = match wc_val {
                        WildcardValue::PodId(id) => ConcreteValue::Pod(*id),
                        WildcardValue::Key(k) => ConcreteValue::Key(k.name().to_string()),
                    };
                    bindings
                        .entry(wildcard_in_template.clone())
                        .or_insert(concrete_val);
                    Ok(true)
                } else {
                    Err(ProverError::Internal(format!(
                        "Public argument binding for index {} (WC '{}') not found.",
                        idx, wildcard_in_template.name
                    )))
                }
            } else {
                Err(ProverError::Internal(format!(
                    "Public bindings expected for WC '{}' but not found in scope.",
                    wildcard_in_template.name
                )))
            }
        }
        WildcardInterpretation::PrivateLocal(actual_wc) => {
            if let Some((domain, _)) = state.domains.get(actual_wc) {
                if domain.len() == 1 {
                    let concrete_value = domain.iter().next().unwrap().clone();
                    bindings.insert(wildcard_in_template.clone(), concrete_value);
                    Ok(true)
                } else {
                    // Not singleton
                    if resolve_scope.parent_custom_call_key.is_some() {
                        debug!(
                            "Deferring: PrivateLocal wildcard '{}' (template: '{}') in custom predicate scope is not singleton (domain size: {}).",
                            actual_wc.name, wildcard_in_template.name, domain.len()
                        );
                        Err(ProverError::ProofDeferred(
                            DeferralReason::AmbiguousPrivateWildcard {
                                wildcard_name: actual_wc.name.clone(),
                                domain_size: domain.len(),
                            },
                        ))
                    } else {
                        Ok(false) // Not in custom predicate scope, normal non-singleton case
                    }
                }
            } else {
                Err(ProverError::Internal(format!(
                    "Wildcard '{}' (original: '{}') from template not found in solver state domains.",
                    actual_wc.name, wildcard_in_template.name
                )))
            }
        }
        WildcardInterpretation::Global(actual_wc) => {
            if let Some((domain, _)) = state.domains.get(actual_wc) {
                if domain.len() == 1 {
                    let concrete_value = domain.iter().next().unwrap().clone();
                    bindings.insert(wildcard_in_template.clone(), concrete_value);
                    Ok(true)
                } else {
                    // Not singleton
                    if resolve_scope
                        .search_targets
                        .as_ref()
                        .is_some_and(|st| st.contains(actual_wc))
                    {
                        debug!(
                            "Deferring: Global wildcard '{}' (template: '{}') is a search target and not singleton (domain size: {}).",
                            actual_wc.name, wildcard_in_template.name, domain.len()
                        );
                        Err(ProverError::ProofDeferred(
                            DeferralReason::AmbiguousSearchTarget {
                                wildcard_name: actual_wc.name.clone(),
                                domain_size: domain.len(),
                            },
                        ))
                    } else if resolve_scope.parent_custom_call_key.is_some() {
                        // Global wildcard used inside a custom predicate body, not yet a direct search target of this *specific* call,
                        // but its ambiguity prevents the custom predicate body from becoming concrete.
                        debug!(
                            "Deferring: Global wildcard '{}' (template: '{}') used in custom predicate scope is not singleton (domain size: {}).",
                            actual_wc.name, wildcard_in_template.name, domain.len()
                        );
                        // We use AmbiguousPrivateWildcard here because the context is a custom predicate body trying to resolve.
                        // The solver might later make this global WC a search_target for the *custom predicate's own scoped search* if it has one.
                        Err(ProverError::ProofDeferred(
                            DeferralReason::AmbiguousPrivateWildcard {
                                wildcard_name: actual_wc.name.clone(), // It's a global WC, but its ambiguity blocks a private context.
                                domain_size: domain.len(),
                            },
                        ))
                    } else {
                        Ok(false) // Top-level global wildcard, normal non-singleton case for outer search
                    }
                }
            } else {
                Err(ProverError::Internal(format!(
                    "Wildcard '{}' (original: '{}') from template not found in solver state domains.",
                    actual_wc.name, wildcard_in_template.name
                )))
            }
        }
    }
}

/// Checks if all wildcards in a template argument are singletons and collects their bindings.
/// Adapts to use resolve_scope for wildcard interpretation.
pub(super) fn collect_singleton_bindings(
    arg_tmpl: &middleware::StatementTmplArg,
    state: &SolverState,
    resolve_scope: &ResolveScope<'_>,
    bindings: &mut HashMap<Wildcard, ConcreteValue>,
) -> Result<bool, ProverError> {
    match arg_tmpl {
        middleware::StatementTmplArg::Key(wc_pod_template, key_or_wc_template) => {
            if !check_and_bind_singleton(wc_pod_template, state, resolve_scope, bindings)? {
                return Ok(false);
            }
            if let middleware::KeyOrWildcard::Wildcard(wc_key_template) = key_or_wc_template {
                if !check_and_bind_singleton(wc_key_template, state, resolve_scope, bindings)? {
                    return Ok(false);
                }
            }
        }
        middleware::StatementTmplArg::WildcardLiteral(wc_val_template) => {
            if !check_and_bind_singleton(wc_val_template, state, resolve_scope, bindings)? {
                return Ok(false);
            }
        }
        middleware::StatementTmplArg::Literal(_) | middleware::StatementTmplArg::None => {}
    }
    Ok(true)
}

/// Constructs a concrete StatementArg from a template argument using bindings.
/// Adapts to use resolve_scope for interpreting wildcards.
pub(super) fn construct_concrete_arg(
    arg_tmpl: &middleware::StatementTmplArg,
    bindings: &HashMap<Wildcard, ConcreteValue>,
    state: &SolverState,
    resolve_scope: &ResolveScope<'_>,
) -> Result<Option<StatementArg>, ProverError> {
    match arg_tmpl {
        middleware::StatementTmplArg::Key(wc_pod_template, key_or_wc_template) => {
            let pod_id = match bindings.get(wc_pod_template) {
                Some(ConcreteValue::Pod(id)) => *id,
                _ => {
                    let mut temp_bindings = HashMap::new();
                    if check_and_bind_singleton(
                        wc_pod_template,
                        state,
                        resolve_scope,
                        &mut temp_bindings,
                    )? {
                        if let Some(ConcreteValue::Pod(id)) = temp_bindings.get(wc_pod_template) {
                            *id
                        } else {
                            return Err(ProverError::Internal(format!(
                                "Re-checked Pod WC '{}' is not Pod type after binding.",
                                wc_pod_template.name
                            )));
                        }
                    } else {
                        return Err(ProverError::Internal(format!(
                            "Pod WC '{}' not found in bindings and not singleton for concrete arg construction.", wc_pod_template.name
                        )));
                    }
                }
            };

            let key = match key_or_wc_template {
                middleware::KeyOrWildcard::Key(k) => k.clone(),
                middleware::KeyOrWildcard::Wildcard(wc_key_template) => {
                    match bindings.get(wc_key_template) {
                        Some(ConcreteValue::Key(k_name)) => middleware::Key::new(k_name.clone()),
                        _ => {
                            let mut temp_bindings = HashMap::new();
                            if check_and_bind_singleton(
                                wc_key_template,
                                state,
                                resolve_scope,
                                &mut temp_bindings,
                            )? {
                                if let Some(ConcreteValue::Key(k_name)) =
                                    temp_bindings.get(wc_key_template)
                                {
                                    middleware::Key::new(k_name.clone())
                                } else {
                                    return Err(ProverError::Internal(format!(
                                        "Re-checked Key WC '{}' is not Key type after binding.",
                                        wc_key_template.name
                                    )));
                                }
                            } else {
                                return Err(ProverError::Internal(format!(
                                    "Key WC '{}' not found in bindings and not singleton for concrete arg construction.", wc_key_template.name
                                )));
                            }
                        }
                    }
                }
            };
            Ok(Some(StatementArg::Key(AnchoredKey::new(pod_id, key))))
        }
        middleware::StatementTmplArg::WildcardLiteral(wc_val_template) => {
            match bindings.get(wc_val_template) {
                Some(ConcreteValue::Val(v)) => Ok(Some(StatementArg::Literal(v.clone()))),
                _ => {
                    let mut temp_bindings = HashMap::new();
                    if check_and_bind_singleton(
                        wc_val_template,
                        state,
                        resolve_scope,
                        &mut temp_bindings,
                    )? {
                        if let Some(ConcreteValue::Val(v)) = temp_bindings.get(wc_val_template) {
                            Ok(Some(StatementArg::Literal(v.clone())))
                        } else {
                            Err(ProverError::Internal(format!(
                                "Re-checked Value WC '{}' is not Value type after binding.",
                                wc_val_template.name
                            )))
                        }
                    } else {
                        Err(ProverError::Internal(format!(
                            "Value WC '{}' not found in bindings and not singleton for concrete arg construction.", wc_val_template.name
                        )))
                    }
                }
            }
        }
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

            // Check if the output of this step is a base fact that's already in final_scope.
            // This avoids redundant processing of base facts that are inputs to multiple proof steps.
            let output_is_already_scoped_base_fact = is_base_copy
                && base_facts.iter().any(|(pid, stmt)| {
                    stmt == &step.output && final_scope.contains(&(*pid, stmt.clone()))
                });

            if output_is_already_scoped_base_fact {
                continue;
            }

            if is_base_copy {
                // If it's a CopyStatement, its input is the base fact.
                // Ensure this base fact is added to the scope.
                if let Some(input_to_copy) = step.inputs.get(0) {
                    if let Some((pod_id, base_stmt)) =
                        base_facts.iter().find(|(_, stmt)| stmt == input_to_copy)
                    {
                        final_scope.insert((*pod_id, base_stmt.clone()));
                    } else {
                        warn!(
                            "Could not find origin PodId for base fact input of CopyStatement in scope collection: {:?}",
                            input_to_copy
                        );
                    }
                } else {
                    warn!("CopyStatement step found with no inputs: {:?}", step.output);
                }
            } else {
                // For other operations, recursively collect scope for their input statements.
                for input_stmt in &step.inputs {
                    if let Some((pod_id, base_stmt)) =
                        base_facts.iter().find(|(_, stmt)| stmt == input_stmt)
                    {
                        // If an input is a base fact, add it to the scope.
                        final_scope.insert((*pod_id, base_stmt.clone()));
                    } else if let Some(input_chain) = all_chains.get(input_stmt) {
                        // If an input is derived, recurse on its proof chain.
                        input_chain.collect_scope(final_scope, all_chains, base_facts);
                    } else {
                        // This indicates an input to a proof step that is neither a base fact
                        // nor has its own proof chain in `all_chains`. This suggests an inconsistency.
                        warn!("Could not find proof chain or base fact for input statement during scope collection: {:?}", input_stmt);
                    }
                }
            }
        }
    }
}
