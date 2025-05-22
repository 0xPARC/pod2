use std::{collections::HashSet, sync::Arc};

use log::{debug, error, info, trace, warn};

use super::{
    types::{Domain, ExpectedType, GlobalContext, ResolveScope, WildcardInterpretation},
    SolverState,
};
use crate::{
    middleware::{
        AnchoredKey, CustomPredicateBatch, Key, KeyOrWildcard, NativePredicate, Params, PodId,
        Predicate, Statement, StatementTmpl, StatementTmplArg, ToFields, Value, Wildcard, F,
    },
    prover::{
        error::ProverError,
        indexing::ProverIndexes,
        types::{ConcreteValue, CustomDefinitions},
    },
};

// Key for the visited set in parse_template_and_generate_constraints
type VisitedPredicateParseKey = (*const CustomPredicateBatch, usize);

// Placeholder for the type of the visited set for recursive type inference
type VisitedTypeInferenceKey = (String, usize); // (CustomPredicateName, PublicArgIndex)

// --- Stubbed out old helper functions ---
// fn update_wildcard_type(...) - This will be removed
// fn get_wildcards_from_definition_stmts(...) - This will be removed
// fn infer_argument_type(...) - This will be removed
// fn parse_template_and_generate_constraints(...) - This will be removed
// --- End of stubbed old helper functions ---

type PotentialConstantInfo = (Wildcard, Key, Value);

// New function for scoped constraint generation
pub(super) fn generate_constraints_for_resolve_scope(
    resolve_scope: &mut ResolveScope<'_>,
    global_context: &GlobalContext<'_>,
    solver_state: &mut SolverState,
    current_batch_arc_opt: Option<Arc<CustomPredicateBatch>>,
    visited_parse_keys: &mut HashSet<VisitedPredicateParseKey>,
) -> Result<(), ProverError> {
    debug!(
        "generate_constraints_for_resolve_scope (depth {}): Entered. Templates to resolve: {}, WC Interp Map Size: {}, Parent call key: {:?}, current_batch_arc_opt: {:?}" ,
        resolve_scope.current_depth,
        resolve_scope.templates_to_resolve.len(),
        resolve_scope.wildcard_interpretation_map.len(),
        resolve_scope.parent_custom_call_key,
        current_batch_arc_opt.as_ref().map(|arc| &arc.name)
    );

    let local_constraints = Vec::new(); // Collect constraints locally first

    for (tmpl_idx, tmpl) in resolve_scope.templates_to_resolve.iter().enumerate() {
        trace!(
            "generate_constraints_for_resolve_scope (depth {}): Processing template #{}: {:?}",
            resolve_scope.current_depth,
            tmpl_idx,
            tmpl.pred // Log only predicate for brevity
        );

        // --- Type inference based on native predicate signatures ---
        if let Predicate::Native(native_pred) = &tmpl.pred {
            match native_pred {
                NativePredicate::ValueOf => {
                    if tmpl.args.len() == 2 {
                        // Arg0: Key(wc_pod, wc_key) or Key(pod_id, wc_key) or Key(wc_pod, key_id)
                        if let StatementTmplArg::Key(pod_wc_template, key_or_wc) = &tmpl.args[0] {
                            update_wildcard_type_from_usage(
                                solver_state,
                                pod_wc_template,
                                ExpectedType::Pod,
                                resolve_scope,
                                global_context.indexes,
                            )?;
                            if let KeyOrWildcard::Wildcard(key_wc_template) = key_or_wc {
                                update_wildcard_type_from_usage(
                                    solver_state,
                                    key_wc_template,
                                    ExpectedType::Key,
                                    resolve_scope,
                                    global_context.indexes,
                                )?;
                            }
                        }
                        // Arg1: WildcardLiteral(wc_val) or Literal(val)
                        if let StatementTmplArg::WildcardLiteral(val_wc_template) = &tmpl.args[1] {
                            update_wildcard_type_from_usage(
                                solver_state,
                                val_wc_template,
                                ExpectedType::Val,
                                resolve_scope,
                                global_context.indexes,
                            )?;
                        }
                    }
                }
                NativePredicate::Equal
                | NativePredicate::NotEqual
                | NativePredicate::Lt
                | NativePredicate::LtEq => {
                    // For comparisons, if one arg implies a type, the other should match.
                    // And types are typically Val for Lt/LtEq, or can be Key/Pod for Equal/NotEqual.
                    // This logic can be complex; for now, ensure they are at least in domains.
                    // More specific type agreement (e.g. both Val) will be handled by pruning/unification.
                    if tmpl.args.len() == 2 {
                        for arg_idx_comp in 0..2 {
                            if let StatementTmplArg::Key(pod_wc_template, key_or_wc) =
                                &tmpl.args[arg_idx_comp]
                            {
                                update_wildcard_type_from_usage(
                                    solver_state,
                                    pod_wc_template,
                                    ExpectedType::Pod,
                                    resolve_scope,
                                    global_context.indexes,
                                )?;
                                if let KeyOrWildcard::Wildcard(key_wc_template) = key_or_wc {
                                    update_wildcard_type_from_usage(
                                        solver_state,
                                        key_wc_template,
                                        ExpectedType::Key,
                                        resolve_scope,
                                        global_context.indexes,
                                    )?;
                                }
                            } else if let StatementTmplArg::WildcardLiteral(wc_template) =
                                &tmpl.args[arg_idx_comp]
                            {
                                // If it's a direct wildcard literal in a comparison, it's likely a Val.
                                // Or it could be a PodId/Key if the other side is an AnchoredKey (handled above).
                                // If both are WildcardLiterals, they are likely Vals.
                                // For now, ensure it's in domains. If it needs to be Val, other logic should confirm.
                                ensure_wildcard_in_domains(
                                    solver_state,
                                    wc_template,
                                    resolve_scope,
                                    global_context.indexes,
                                )?;
                            }
                        }
                    }
                }
                NativePredicate::SumOf | NativePredicate::ProductOf | NativePredicate::MaxOf => {
                    if tmpl.args.len() == 3 {
                        for arg_idx_arith in 0..3 {
                            if let StatementTmplArg::Key(pod_wc_template, key_or_wc) =
                                &tmpl.args[arg_idx_arith]
                            {
                                update_wildcard_type_from_usage(
                                    solver_state,
                                    pod_wc_template,
                                    ExpectedType::Pod,
                                    resolve_scope,
                                    global_context.indexes,
                                )?;
                                if let KeyOrWildcard::Wildcard(key_wc_template) = key_or_wc {
                                    update_wildcard_type_from_usage(
                                        solver_state,
                                        key_wc_template,
                                        ExpectedType::Key,
                                        resolve_scope,
                                        global_context.indexes,
                                    )?;
                                    // Values at these keys are implicitly Val (numeric)
                                }
                            }
                        }
                    }
                }
                NativePredicate::Contains => {
                    if tmpl.args.len() == 3 {
                        // Arg0: Container (likely Pod type for its key)
                        if let StatementTmplArg::Key(pod_wc_template, _) = &tmpl.args[0] {
                            update_wildcard_type_from_usage(
                                solver_state,
                                pod_wc_template,
                                ExpectedType::Pod,
                                resolve_scope,
                                global_context.indexes,
                            )?;
                        }
                        // Arg1: Key being checked (likely Key type for its key part)
                        if let StatementTmplArg::Key(_, key_or_wc) = &tmpl.args[1] {
                            if let KeyOrWildcard::Wildcard(key_wc_template) = key_or_wc {
                                update_wildcard_type_from_usage(
                                    solver_state,
                                    key_wc_template,
                                    ExpectedType::Key,
                                    resolve_scope,
                                    global_context.indexes,
                                )?;
                            }
                        }
                        // Arg2: Value associated with the key (likely Pod type for its key part, value itself is Val)
                        if let StatementTmplArg::Key(pod_wc_template, _) = &tmpl.args[2] {
                            update_wildcard_type_from_usage(
                                solver_state,
                                pod_wc_template,
                                ExpectedType::Pod,
                                resolve_scope,
                                global_context.indexes,
                            )?;
                        }
                    }
                }
                NativePredicate::NotContains => {
                    if tmpl.args.len() == 2 {
                        // Arg0: Container
                        if let StatementTmplArg::Key(pod_wc_template, _) = &tmpl.args[0] {
                            update_wildcard_type_from_usage(
                                solver_state,
                                pod_wc_template,
                                ExpectedType::Pod,
                                resolve_scope,
                                global_context.indexes,
                            )?;
                        }
                        // Arg1: Key being checked
                        if let StatementTmplArg::Key(_, key_or_wc) = &tmpl.args[1] {
                            if let KeyOrWildcard::Wildcard(key_wc_template) = key_or_wc {
                                update_wildcard_type_from_usage(
                                    solver_state,
                                    key_wc_template,
                                    ExpectedType::Key,
                                    resolve_scope,
                                    global_context.indexes,
                                )?;
                            }
                        }
                    }
                }
                NativePredicate::HashOf => {
                    if tmpl.args.len() == 3 {
                        // All args are AnchoredKeys, implying Pods and Keys for their wildcards.
                        // The values themselves are of type Val.
                        for arg_idx_hash in 0..3 {
                            if let StatementTmplArg::Key(pod_wc_template, key_or_wc) =
                                &tmpl.args[arg_idx_hash]
                            {
                                update_wildcard_type_from_usage(
                                    solver_state,
                                    pod_wc_template,
                                    ExpectedType::Pod,
                                    resolve_scope,
                                    global_context.indexes,
                                )?;
                                if let KeyOrWildcard::Wildcard(key_wc_template) = key_or_wc {
                                    update_wildcard_type_from_usage(
                                        solver_state,
                                        key_wc_template,
                                        ExpectedType::Key,
                                        resolve_scope,
                                        global_context.indexes,
                                    )?;
                                }
                            }
                        }
                    }
                }
                // Add other native predicates as needed
                _ => {}
            }
        }
        // --- End type inference based on native predicate signatures ---

        // MODIFIED loop for argument processing:
        // This loop iterates over the arguments of the *current tmpl*
        for (arg_pos_idx, arg_tmpl_in_call) in tmpl.args.iter().enumerate() {
            match arg_tmpl_in_call {
                StatementTmplArg::Key(pod_wc_in_key, key_or_wc_in_key) => {
                    update_wildcard_type_from_usage(
                        solver_state,
                        pod_wc_in_key,
                        ExpectedType::Pod,
                        resolve_scope,
                        global_context.indexes,
                    )?;
                    if let KeyOrWildcard::Wildcard(key_wc) = key_or_wc_in_key {
                        update_wildcard_type_from_usage(
                            solver_state,
                            key_wc,
                            ExpectedType::Key,
                            resolve_scope,
                            global_context.indexes,
                        )?;
                    }
                }
                StatementTmplArg::WildcardLiteral(wc_literal_arg) => {
                    let mut type_to_update_with = ExpectedType::Unknown; // Default

                    match tmpl.pred {
                        // Check the predicate of the current template tmpl
                        Predicate::BatchSelf(called_pred_idx_in_current_batch) => {
                            let current_batch_arc = current_batch_arc_opt.as_ref().ok_or_else(|| {
                                error!(target: "pod2::prover::solver::initialization", "generate_constraints (depth {}): BatchSelf call to index {} but no current_batch_arc_opt context. WC: '{}'", resolve_scope.current_depth, called_pred_idx_in_current_batch, wc_literal_arg.name);
                                ProverError::Internal(format!("BatchSelf call (idx {}) without current_batch_arc context", called_pred_idx_in_current_batch))
                            })?;

                            if called_pred_idx_in_current_batch < current_batch_arc.predicates.len()
                            {
                                let called_custom_pred_def =
                                    &current_batch_arc.predicates[called_pred_idx_in_current_batch];
                                if arg_pos_idx < called_custom_pred_def.args_len {
                                    let inferred_type = infer_type_for_custom_pred_public_arg(
                                        called_custom_pred_def,
                                        arg_pos_idx,
                                        global_context,
                                        Some(current_batch_arc), // Callee's batch context (same as current)
                                        &mut HashSet::new(), // Fresh visited set for this inference
                                    )?;
                                    if inferred_type != ExpectedType::Unknown {
                                        type_to_update_with = inferred_type;
                                    }
                                    debug!(target: "pod2::prover::solver::initialization", "generate_constraints (depth {}): For BatchSelf call to '{}' (idx {}), arg #{} ('{}'), type from callee sig: {:?}, using: {:?}", resolve_scope.current_depth, called_custom_pred_def.name, called_pred_idx_in_current_batch, arg_pos_idx, wc_literal_arg.name, inferred_type, type_to_update_with);
                                }
                            } else {
                                warn!(target: "pod2::prover::solver::initialization", "generate_constraints (depth {}): BatchSelf call - index {} out of bounds for batch '{}' (len {}). WC: '{}'", resolve_scope.current_depth, called_pred_idx_in_current_batch, current_batch_arc.name, current_batch_arc.predicates.len(), wc_literal_arg.name);
                            }
                        }
                        Predicate::Native(NativePredicate::ValueOf) => {
                            if arg_pos_idx == 1 {
                                // Value arg of ValueOf must be Val
                                type_to_update_with = ExpectedType::Val;
                            }
                        }
                        _ => {}
                    }

                    update_wildcard_type_from_usage(
                        solver_state,
                        wc_literal_arg,
                        type_to_update_with, // Use determined type, or Unknown
                        resolve_scope,
                        global_context.indexes,
                    )?;
                }
                _ => {} // Other StatementTmplArg types (Literal, SelfRef)
            }
        }
    } // End of main loop over resolve_scope.templates_to_resolve

    resolve_scope.constraints = local_constraints; // Ensure this is still here if it was moved from original spot
    debug!(
        "generate_constraints_for_resolve_scope (depth {}): Exiting. Total constraints generated for this scope: {}",
        resolve_scope.current_depth,
        resolve_scope.constraints.len()
    );
    Ok(())
}

pub fn update_solver_wildcard_type(
    solver_state: &mut SolverState,
    wildcard: &Wildcard,
    new_type: ExpectedType,
    is_new_private_local: bool,
    indexes_opt: Option<&ProverIndexes>,
) -> Result<bool, ProverError> {
    let mut changed = false;
    trace!(
        "update_solver_wildcard_type: wc: {}, new_type: {:?}, is_new_private_local: {}",
        wildcard.name,
        new_type,
        is_new_private_local
    );

    let (domain, current_type_in_map_mut_ref) = solver_state
        .domains
        .entry(wildcard.clone())
        .or_insert_with(|| {
            debug!(
                "update_solver_wildcard_type: Inserting new wildcard {} into domains (was not present). New type: {:?}, is_new_private_local: {}",
                wildcard.name, new_type, is_new_private_local
            );
            (Domain::new(), ExpectedType::Unknown)
        });

    let old_type = *current_type_in_map_mut_ref;
    if old_type == ExpectedType::Unknown && new_type != ExpectedType::Unknown {
        *current_type_in_map_mut_ref = new_type;
    } else if new_type != ExpectedType::Unknown && new_type != old_type {
        // This case might indicate a type conflict, but for now, we'll allow promoting
        // from a less specific (e.g. Val from ValueOf) to a more specific (e.g. Pod from Key usage)
        // or if there's a genuine conflict (e.g. trying to set Pod then Key), an error should be raised.
        // For now, let's assume new_type is "more correct" or "more specific".
        // A proper type lattice / conflict resolution might be needed if this becomes problematic.
        warn!(target: "pod2::prover::solver::initialization", "Wildcard {} type changing from {:?} to {:?}. This might be a refinement or a conflict.", wildcard.name, old_type, new_type);
        *current_type_in_map_mut_ref = new_type;
    }

    let changed_to_known_type =
        old_type == ExpectedType::Unknown && *current_type_in_map_mut_ref != ExpectedType::Unknown;
    let original_type_was_unknown = old_type == ExpectedType::Unknown; // Re-evaluate based on the type *before* this update.

    if wildcard.name.as_str() == "intermed_ori" {
        debug!(target: "pod2::prover::solver::initialization", "intermed_ori update: new_type={:?}, old_type={:?}, changed_to_known_type={}, is_new_private_local={}, original_type_was_unknown={}", new_type, old_type, changed_to_known_type, is_new_private_local, original_type_was_unknown);
    }

    // Populate domain if type is now known and it was previously unknown or is a new private local wildcard
    if *current_type_in_map_mut_ref != ExpectedType::Unknown {
        // Check current type of domain_info
        if changed_to_known_type && (is_new_private_local || original_type_was_unknown) {
            if let Some(indexes) = indexes_opt {
                let mut new_domain_values = Domain::new();
                match *current_type_in_map_mut_ref {
                    ExpectedType::Pod => {
                        let mut pod_ids_from_indexes = HashSet::new();
                        for ak in indexes.id_to_key.iter() {
                            if ak.pod_id != crate::middleware::SELF {
                                pod_ids_from_indexes.insert(ak.pod_id);
                            }
                        }
                        debug!(
                            "update_solver_wildcard_type: Found {} unique PodIDs in ProverIndexes for {}: {:?}",
                            pod_ids_from_indexes.len(),
                            wildcard.name,
                            pod_ids_from_indexes.iter().take(5).collect::<Vec<_>>()
                        );
                        if !pod_ids_from_indexes.is_empty() {
                            for pod_id in pod_ids_from_indexes {
                                new_domain_values.insert(ConcreteValue::Pod(pod_id));
                            }
                        }
                    }
                    ExpectedType::Key => {
                        let mut keys_from_indexes = HashSet::new();
                        for ak in indexes.id_to_key.iter() {
                            keys_from_indexes.insert(ak.key.name().to_string());
                        }
                        debug!(
                            "update_solver_wildcard_type: Found {} unique Keys in ProverIndexes for {}: {:?}",
                            keys_from_indexes.len(),
                            wildcard.name,
                            keys_from_indexes.iter().take(5).collect::<Vec<_>>()
                        );
                        if !keys_from_indexes.is_empty() {
                            for key_name in keys_from_indexes {
                                new_domain_values.insert(ConcreteValue::Key(key_name));
                            }
                        }
                    }
                    ExpectedType::Val => {
                        debug!(
                            "update_solver_wildcard_type: Val type for {} - initial domain population from general indexes not implemented.",
                            wildcard.name
                        );
                    }
                    ExpectedType::Unknown => {}
                }

                if !new_domain_values.is_empty() {
                    debug!(
                        "update_solver_wildcard_type: Setting domain for {} (size {}) with values: {:?}",
                        wildcard.name,
                        new_domain_values.len(),
                        new_domain_values.iter().take(5).collect::<Vec<_>>()
                    );
                    domain.extend(new_domain_values);
                    changed = true;
                } else {
                    debug!(
                        "update_solver_wildcard_type: No initial domain values found from ProverIndexes for {} (type: {:?}). Domain remains empty.",
                        wildcard.name, current_type_in_map_mut_ref
                    );
                }
            } else if is_new_private_local || original_type_was_unknown {
                debug!(
                    "update_solver_wildcard_type: ProverIndexes not available for initial domain population of {}.",
                    wildcard.name
                );
            }
        }
    }

    trace!("update_solver_wildcard_type: Exiting for {}. Changed: {}. Final domain size: {}. Final type: {:?}", wildcard.name, changed, domain.len(), current_type_in_map_mut_ref);
    Ok(changed)
}

type InitializationResult = (
    SolverState,
    Vec<PotentialConstantInfo>,
    Vec<(PodId, Statement)>,
);

// Helper to get all wildcards from a StatementTmpl (can be moved or kept local)
fn get_all_wildcards_from_tmpl_init(tmpl: &StatementTmpl) -> HashSet<Wildcard> {
    let mut wildcards = HashSet::new();
    for arg in &tmpl.args {
        match arg {
            StatementTmplArg::Key(w, kw_opt) => {
                wildcards.insert(w.clone());
                if let KeyOrWildcard::Wildcard(ref kw) = kw_opt {
                    wildcards.insert(kw.clone());
                }
            }
            StatementTmplArg::WildcardLiteral(w) => {
                wildcards.insert(w.clone());
            }
            _ => {}
        }
    }
    wildcards
}

// Helper to scan for SELF_HOLDER ValueOf statements
fn extract_self_facts_and_constants_recursive(
    statements: &[StatementTmpl],
    params: &Params,
    custom_definitions: &CustomDefinitions,
    potential_constant_info: &mut Vec<PotentialConstantInfo>,
    self_facts: &mut Vec<(PodId, Statement)>,
    visited_custom_defs: &mut HashSet<Vec<F>>,
    is_top_level: bool,
) {
    for tmpl in statements {
        // Check for ValueOf(?SELF_HOLDER["key"], literal_value)
        if let Predicate::Native(NativePredicate::ValueOf) = &tmpl.pred {
            if tmpl.args.len() == 2 {
                if let (
                    StatementTmplArg::Key(wc_holder, KeyOrWildcard::Key(actual_key)),
                    StatementTmplArg::Literal(val),
                ) = (&tmpl.args[0], &tmpl.args[1])
                {
                    // Add to potential_constant_info regardless of naming convention or level
                    potential_constant_info.push((
                        wc_holder.clone(),
                        actual_key.clone(),
                        val.clone(),
                    ));

                    // Only add to global self_facts if at the top level
                    if is_top_level {
                        let self_fact_statement = Statement::ValueOf(
                            AnchoredKey::new(crate::middleware::SELF, actual_key.clone()),
                            val.clone(),
                        );
                        if !self_facts.iter().any(|(_, sf)| sf == &self_fact_statement) {
                            self_facts.push((crate::middleware::SELF, self_fact_statement));
                        }
                    }
                }
            }
        }
        // Recurse into custom predicates defined in these statements
        if let Predicate::Custom(custom_ref) = &tmpl.pred {
            let pred_key = Predicate::Custom(custom_ref.clone()).to_fields(params);
            if !visited_custom_defs.contains(&pred_key) {
                if let Some((custom_pred_def, _)) = custom_definitions.get(&pred_key) {
                    visited_custom_defs.insert(pred_key);
                    extract_self_facts_and_constants_recursive(
                        &custom_pred_def.statements,
                        params,
                        custom_definitions,
                        potential_constant_info,
                        self_facts,
                        visited_custom_defs,
                        false, // Recursive call is not top-level
                    );
                }
            }
        }
    }
}

pub(super) fn initialize_solver_state(
    request_templates: &[StatementTmpl],
    params: &Params,
    custom_definitions: &CustomDefinitions,
) -> Result<InitializationResult, ProverError> {
    info!("Solver Initialization: Starting initialize_solver_state (simplified).");
    let mut solver_state = SolverState::new();
    let mut potential_constant_info = Vec::new();
    let mut self_facts = Vec::new();
    let mut visited_custom_defs = HashSet::new();

    // 1. Populate solver_state.domains with all top-level wildcards from request_templates
    for tmpl in request_templates {
        for wc in get_all_wildcards_from_tmpl_init(tmpl) {
            solver_state.domains.entry(wc.clone()).or_insert_with(|| {
                (HashSet::new(), ExpectedType::Unknown) // Start as Unknown, empty domain
            });
        }
    }

    // 2. Extract self_facts and potential_constant_info from request_templates and custom definitions
    extract_self_facts_and_constants_recursive(
        request_templates,
        params,
        custom_definitions,
        &mut potential_constant_info,
        &mut self_facts,
        &mut visited_custom_defs,
        true, // Initial call is top-level
    );
    // Also scan all custom definitions directly in case SELF_HOLDERs are only in there
    for (_key, (custom_pred_def, _batch)) in custom_definitions.iter() {
        // Use the same visited set to avoid redundant processing if custom defs call each other
        // or if request templates call a custom def that's also iterated here.
        extract_self_facts_and_constants_recursive(
            &custom_pred_def.statements,
            params,
            custom_definitions,
            &mut potential_constant_info,
            &mut self_facts,
            &mut visited_custom_defs,
            false, // Recursive call is not top-level
        );
    }

    // NOTE: The complex type inference and constraint generation via
    // generate_constraints_for_resolve_scope is NO LONGER CALLED HERE.
    // It will be called by resolve_templates in the main solve() function,
    // after domains are populated with real ProverIndexes.

    // This loop ensures that any SELF_HOLDER wildcards (and top-level CONST) have their domain
    // correctly set to their unique PodId and type set to Pod.
    for (wc_from_info, _key, _value) in &potential_constant_info {
        if wc_from_info.name == "CONST" || wc_from_info.name.starts_with("SELF_HOLDER_") {
            if let Some(holder_pod_id) = self_facts.iter().find_map(|(pod_id, _)| {
                if *pod_id == crate::middleware::SELF {
                    Some(*pod_id)
                } else {
                    None
                }
            }) {
                if let Some((domain_ref, type_ref)) = solver_state.domains.get_mut(wc_from_info) {
                    if *type_ref == ExpectedType::Unknown || *type_ref == ExpectedType::Pod {
                        debug!(
                            "initialize_solver_state: Updating wc: {}, current type: {:?}, to specific PodId: {:?}, new type: Pod",
                            wc_from_info.name, *type_ref, holder_pod_id
                        );
                        domain_ref.clear();
                        domain_ref.insert(ConcreteValue::Pod(holder_pod_id));
                        *type_ref = ExpectedType::Pod;
                    } else {
                        error!(
                            "initialize_solver_state: SELF holder {} has an unexpected pre-existing type {:?} during final domain init",
                            wc_from_info.name, *type_ref
                        );
                    }
                } else {
                    error!("initialize_solver_state: Wildcard {} from potential_constant_info not found in state.domains for final update.", wc_from_info.name);
                }
            }
        }
    }

    // Log the state of CONST wildcard specifically before returning
    if let Some(const_wc_key) = potential_constant_info.iter().find_map(|(wc, _, _)| {
        if wc.name == "CONST" {
            Some(wc.clone())
        } else {
            None
        }
    }) {
        if let Some((domain, wc_type)) = solver_state.domains.get(&const_wc_key) {
            debug!(
                "initialize_solver_state: Final state for CONST wildcard '{}': domain_size = {}, type = {:?}",
                const_wc_key.name, domain.len(), wc_type
            );
            if domain.len() == 1 {
                debug!(
                    "initialize_solver_state: CONST domain value: {:?}",
                    domain.iter().next().unwrap()
                );
            }
        } else {
            debug!("initialize_solver_state: CONST wildcard '{}' (from potential_constant_info) not found in state.domains at the end.", const_wc_key.name);
        }
    } else {
        debug!("initialize_solver_state: CONST wildcard not found in potential_constant_info at the end.");
    }

    debug!(
        "Solver Initialization (simplified): Complete. Initial WC count: {}, Potential constants: {}, Self facts: {}",
        solver_state.domains.len(),
        potential_constant_info.len(),
        self_facts.len()
    );

    Ok((solver_state, potential_constant_info, self_facts))
}

pub fn infer_type_for_custom_pred_public_arg(
    custom_pred_def: &crate::middleware::CustomPredicate,
    public_arg_idx: usize, // The index of the public argument we are finding the type for
    global_context: &GlobalContext<'_>,
    current_batch_arc_opt: Option<&Arc<crate::middleware::CustomPredicateBatch>>, // Qualified path
    visited_for_type_inference: &mut HashSet<VisitedTypeInferenceKey>,
) -> Result<ExpectedType, ProverError> {
    let visit_key = (custom_pred_def.name.clone(), public_arg_idx);
    if visited_for_type_inference.contains(&visit_key) {
        debug!(
            "TypeInference: Cycle detected or already visited for custom predicate '{}' arg index {}. Returning Unknown to break cycle.",
            custom_pred_def.name, public_arg_idx
        );
        return Ok(ExpectedType::Unknown); // Avoid infinite recursion
    }
    visited_for_type_inference.insert(visit_key.clone());

    debug!(
        "TypeInference: Inferring type for public arg #{} of custom predicate '{}'",
        public_arg_idx, custom_pred_def.name
    );

    // Find the wildcard that represents this public argument in the custom_pred_def's context.
    // Public arguments are typically indexed 0 to args_len - 1.
    // We need to find a Wildcard { index: public_arg_idx, name: some_name } used in its body.
    // Or, more directly, iterate through statements and see how the placeholder for this public_arg_idx is used.
    // Let's assume public wildcards in the body are named like "pub_arg_0", "pub_arg_1" etc. OR match by index.
    // The custom_pred_def.statements use Wildcard instances. We need to identify which one corresponds to `public_arg_idx`.
    // A simple way: any Wildcard { index: public_arg_idx, .. } found in the body IS the public arg.

    let mut inferred_types: Vec<ExpectedType> = Vec::new();

    for stmt_tmpl in &custom_pred_def.statements {
        for arg_in_body_tmpl in &stmt_tmpl.args {
            match arg_in_body_tmpl {
                StatementTmplArg::Key(wc, k_or_wc) => {
                    if wc.index == public_arg_idx {
                        debug!("  TypeInference ('{}' pub_arg #{}): Used as pod_wildcard in Key(_, _) -> Pod", custom_pred_def.name, public_arg_idx);
                        inferred_types.push(ExpectedType::Pod);
                    }
                    if let KeyOrWildcard::Wildcard(ref key_wc) = k_or_wc {
                        if key_wc.index == public_arg_idx {
                            debug!("  TypeInference ('{}' pub_arg #{}): Used as key_wildcard in Key(_, Wildcard(_)) -> Key", custom_pred_def.name, public_arg_idx);
                            inferred_types.push(ExpectedType::Key);
                        }
                    }
                }
                StatementTmplArg::WildcardLiteral(wc) => {
                    if wc.index == public_arg_idx {
                        // This wildcard (wc) IS our public_arg_idx. Now see how it's used in stmt_tmpl.pred
                        match &stmt_tmpl.pred {
                            Predicate::Native(native_pred) => {
                                // TODO: Determine type based on native_pred and arg position of 'wc'
                                // For now, assume Val if used as WildcardLiteral with native. This is a simplification.
                                debug!("  TypeInference ('{}' pub_arg #{}): Used as WildcardLiteral with Native predicate {:?}. Assuming Val (simplification).", custom_pred_def.name, public_arg_idx, native_pred);
                                inferred_types.push(ExpectedType::Val);
                            }
                            Predicate::Custom(_target_custom_ref) => {
                                // This case means a public arg of 'custom_pred_def' is passed as a WildcardLiteral arg
                                // to another custom predicate call inside 'custom_pred_def'.
                                // This shouldn't happen with current structure; custom calls take WildcardLiterals from *their* args.
                                // If wc (public_arg_idx of outer) *is* the WildcardLiteral arg here, it implies direct pass-through.
                                // This needs careful thought. For now, this path implies an issue or complex mapping.
                                warn!("  TypeInference ('{}' pub_arg #{}): Used as WildcardLiteral arg to another Custom predicate. This path is complex and not fully handled, defaulting to Unknown.", custom_pred_def.name, public_arg_idx);
                                inferred_types.push(ExpectedType::Unknown);
                            }
                            Predicate::BatchSelf(target_batch_idx) => {
                                if let Some(batch_arc) = current_batch_arc_opt {
                                    if let Some(target_pred_in_batch_def) =
                                        batch_arc.predicates.get(*target_batch_idx)
                                    {
                                        // `wc` (which is public_arg_idx of current custom_pred_def) is being passed to target_pred_in_batch_def.
                                        // Find which public argument of target_pred_in_batch_def this `wc` corresponds to.
                                        let mut arg_pos_in_batchself_call = None;
                                        for (i, batch_call_arg) in stmt_tmpl.args.iter().enumerate()
                                        {
                                            if let StatementTmplArg::WildcardLiteral(ref inner_wc) =
                                                batch_call_arg
                                            {
                                                if inner_wc.index == public_arg_idx {
                                                    // inner_wc is our wc
                                                    arg_pos_in_batchself_call = Some(i);
                                                    break;
                                                }
                                            }
                                        }

                                        if let Some(target_public_arg_idx) =
                                            arg_pos_in_batchself_call
                                        {
                                            if target_public_arg_idx
                                                < target_pred_in_batch_def.args_len
                                            {
                                                debug!("  TypeInference ('{}' pub_arg #{}): Recursively inferring from BatchSelf call to '{}', target arg #{}", custom_pred_def.name, public_arg_idx, target_pred_in_batch_def.name, target_public_arg_idx);
                                                match infer_type_for_custom_pred_public_arg(
                                                    target_pred_in_batch_def,
                                                    target_public_arg_idx,
                                                    global_context,
                                                    current_batch_arc_opt, // Pass through current batch context
                                                    visited_for_type_inference,
                                                ) {
                                                    Ok(recursive_type) => {
                                                        inferred_types.push(recursive_type)
                                                    }
                                                    Err(e) => {
                                                        error!("Error during recursive type inference: {:?}", e);
                                                        inferred_types.push(ExpectedType::Unknown);
                                                    }
                                                }
                                            } else {
                                                warn!("  TypeInference ('{}' pub_arg #{}): Arg index {} out of bounds for BatchSelf target '{}' with {} args.", custom_pred_def.name, public_arg_idx, target_public_arg_idx, target_pred_in_batch_def.name, target_pred_in_batch_def.args_len);
                                                inferred_types.push(ExpectedType::Unknown);
                                            }
                                        } else {
                                            warn!("  TypeInference ('{}' pub_arg #{}): Could not map to an arg in BatchSelf call.", custom_pred_def.name, public_arg_idx);
                                            inferred_types.push(ExpectedType::Unknown);
                                        }
                                    } else {
                                        warn!("  TypeInference ('{}' pub_arg #{}): BatchSelf target_idx {} out of bounds for current batch '{}'.", custom_pred_def.name, public_arg_idx, target_batch_idx, batch_arc.name);
                                        inferred_types.push(ExpectedType::Unknown);
                                    }
                                } else {
                                    warn!("  TypeInference ('{}' pub_arg #{}): BatchSelf used but no current_batch_arc_opt provided.", custom_pred_def.name, public_arg_idx);
                                    inferred_types.push(ExpectedType::Unknown);
                                }
                            }
                        }
                    }
                }
                _ => {} // Other StatementTmplArg types (Literal, None) don't involve the public wildcard directly for its type.
            }
        }
    }

    visited_for_type_inference.remove(&visit_key);

    // Resolve multiple inferred types.
    // Prioritize Pod > Key > Val. If conflicting (e.g. Pod and Val), then Unknown or error.
    let mut final_type = ExpectedType::Unknown;
    let mut has_pod = false;
    let mut has_key = false;
    let mut has_val = false;

    for t in inferred_types.iter() {
        match t {
            ExpectedType::Pod => has_pod = true,
            ExpectedType::Key => has_key = true,
            ExpectedType::Val => has_val = true,
            ExpectedType::Unknown => {} // Ignore
        }
    }

    if has_pod {
        final_type = ExpectedType::Pod;
    } else if has_key {
        final_type = ExpectedType::Key;
    } else if has_val {
        final_type = ExpectedType::Val;
    }

    // Conflict detection (simple version)
    if (has_pod && (has_key || has_val)) || (has_key && has_val) {
        warn!(
            "TypeInference: Conflicting types inferred for custom predicate '{}' public arg #{}. Pod: {}, Key: {}, Val: {}. Defaulting to Unknown.",
            custom_pred_def.name, public_arg_idx, has_pod, has_key, has_val
        );
        return Ok(ExpectedType::Unknown); // Conflicting types
    }

    // If loop completes and type is still Unknown, it means the public arg was not used in a way that defines its type.
    if final_type == ExpectedType::Unknown {
        // If inferred_types is empty, it means no part of the function body
        // provided any type information for this public argument. This is "unused".
        if inferred_types.is_empty() {
            warn!(
                "Public argument #{} of custom predicate \'{}\' is unused in its body and its type cannot be inferred.",
                public_arg_idx, custom_pred_def.name
            );
            return Err(ProverError::InconsistentWildcard(format!(
                "Public argument #{} of custom predicate \'{}\' is unused. All declared arguments must be used and their types inferable.",
                public_arg_idx, custom_pred_def.name
            )));
        } else {
            // The argument was used, but its type resolved to Unknown (e.g., due to cycles or conflicts).
            // Allow Unknown to propagate. The solver might handle this, or later checks will flag it if problematic.
            warn!(
                "Public argument #{} of custom predicate \'{}\' resolved to Unknown type after considering usages (e.g., due to recursion or conflict). Proceeding with Unknown.",
                public_arg_idx, custom_pred_def.name
            );
            // Return Ok(ExpectedType::Unknown) instead of an error here.
            // The original strict error was:
            // return Err(ProverError::InconsistentWildcard(format!(
            //     "Public argument #{} of custom predicate \'{}\' is unused or its type cannot be inferred. All declared arguments must be used.\",
            //     public_arg_idx, custom_pred_def.name
            // )));
            // By returning Ok(ExpectedType::Unknown), we are saying its type is "Unknown" for now.
        }
    }

    debug!(
        "  TypeInference ('{}' pub_arg #{}): Final inferred type: {:?}",
        custom_pred_def.name, public_arg_idx, final_type
    );
    Ok(final_type)
}

// Helper function to avoid code duplication in generate_constraints_for_resolve_scope
fn update_wildcard_type_from_usage(
    solver_state: &mut SolverState,
    wc_in_template: &Wildcard,
    inferred_type: ExpectedType,
    resolve_scope: &ResolveScope<'_>,
    indexes: &ProverIndexes,
) -> Result<(), ProverError> {
    let interpretation = resolve_scope
        .wildcard_interpretation_map
        .get(wc_in_template)
        .ok_or_else(|| {
            ProverError::Internal(format!(
                "WC {} from template arg not in interpretation map during type_from_usage",
                wc_in_template.name
            ))
        })?;

    match interpretation {
        WildcardInterpretation::PrivateLocal(actual_private_wc) => {
            update_solver_wildcard_type(
                solver_state,
                actual_private_wc,
                inferred_type,
                !solver_state.domains.contains_key(actual_private_wc), // is_new if not in domains
                Some(indexes),
            )?;
        }
        WildcardInterpretation::Global(actual_global_wc) => {
            update_solver_wildcard_type(
                solver_state,
                actual_global_wc,
                inferred_type,
                !solver_state.domains.contains_key(actual_global_wc), // is_new if not in domains
                Some(indexes),
            )?;
        }
        WildcardInterpretation::PublicArg(_) => {
            // Type of public arg is determined by its usage inside or by the caller.
            // If usage here implies a type, it serves as a check or refinement.
            // The actual WildcardValue for PublicArg is handled by caller's binding.
            // For now, we don't enforce type check on PublicArg here,
            // assuming `infer_type_for_custom_pred_public_arg` and caller handle it.
        }
    }
    Ok(())
}

// Helper to ensure a wildcard (usually for WildcardLiteral) is in domains, defaulting to Unknown.
fn ensure_wildcard_in_domains(
    solver_state: &mut SolverState,
    wc_in_template: &Wildcard,
    resolve_scope: &ResolveScope<'_>,
    indexes: &ProverIndexes,
) -> Result<(), ProverError> {
    let interpretation = resolve_scope
        .wildcard_interpretation_map
        .get(wc_in_template)
        .ok_or_else(|| {
            ProverError::Internal(format!(
                "WC {} from template WildcardLiteral not in interpretation map",
                wc_in_template.name
            ))
        })?;
    match interpretation {
        WildcardInterpretation::PrivateLocal(actual_private_wc) => {
            if !solver_state.domains.contains_key(actual_private_wc) {
                update_solver_wildcard_type(
                    solver_state,
                    actual_private_wc,
                    ExpectedType::Unknown, // Default for WildcardLiterals if type not yet clear
                    true,
                    Some(indexes),
                )?;
            }
        }
        WildcardInterpretation::Global(actual_global_wc) => {
            if !solver_state.domains.contains_key(actual_global_wc) {
                update_solver_wildcard_type(
                    solver_state,
                    actual_global_wc,
                    ExpectedType::Unknown,
                    true,
                    Some(indexes),
                )?;
            }
        }
        _ => {} // PublicArgs are handled by caller.
    }
    Ok(())
}
