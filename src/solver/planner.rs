//! The query planner is responsible for taking a user's proof request and
//! transforming it into an efficient query plan that can be executed by the
//! engine.
//!
//! This involves:
//! 1.  **SIPS Selection:** Choosing an optimal evaluation order for literals in a rule.
//! 2.  **Magic Set Transformation:** Rewriting the rules to be goal-directed.
//!
//! The output of the planner is a set of "magic" and "guarded" rules ready for
//! bottom-up evaluation.

use std::{
    collections::{HashSet, VecDeque},
    hash::Hash,
};

use crate::{
    middleware::{
        CustomPredicate, CustomPredicateBatch, CustomPredicateRef, Params, Predicate,
        StatementTmpl, StatementTmplArg, Wildcard,
    },
    solver::{
        error::SolverError,
        ir::{self, Rule},
    },
};

/// The bound/free status of a single argument in a predicate.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum Binding {
    Bound,
    Free,
}

/// An adornment represents the pattern of bound/free arguments for a predicate.
pub type Adornment = Vec<Binding>;

/// A set of rules that have been optimized by the planner.
#[derive(Debug)]
pub struct QueryPlan {
    /// Rules for deriving "magic" sets.
    pub magic_rules: Vec<Rule>,
    /// The original rules, guarded by magic predicates.
    pub guarded_rules: Vec<Rule>,
}

pub struct Planner;

impl Planner {
    pub fn new() -> Self {
        Self {}
    }

    /// Computes the adornment for a literal given a set of bound variables.
    fn get_adornment(&self, literal: &ir::Atom, bound_vars: &HashSet<Wildcard>) -> Adornment {
        literal
            .terms
            .iter()
            .map(|term| match term {
                StatementTmplArg::Literal(_) => Binding::Bound,
                StatementTmplArg::Wildcard(w) => {
                    if bound_vars.contains(w) {
                        Binding::Bound
                    } else {
                        Binding::Free
                    }
                }
                StatementTmplArg::AnchoredKey(w, _) => {
                    if bound_vars.contains(w) {
                        Binding::Bound
                    } else {
                        Binding::Free
                    }
                }
                StatementTmplArg::None => Binding::Free, // Should be caught later
            })
            .collect()
    }

    /// Reorders the literals in a rule body based on a "most-bound-first" SIPS.
    fn reorder_body_for_sips(
        &self,
        body: &[ir::Atom],
        initial_bound: &HashSet<Wildcard>,
    ) -> Vec<ir::Atom> {
        let mut reordered_body = Vec::new();
        let mut remaining_literals: Vec<ir::Atom> = body.to_vec();
        let mut currently_bound = initial_bound.clone();

        // Two-phase selection: first exhaust all non-native literals, then the native ones.
        let mut picking_native_phase = false;

        while !remaining_literals.is_empty() {
            // Helper: skip natives in the first phase
            let best_literal_index = remaining_literals
                .iter()
                .enumerate()
                .filter(|(_, lit)| {
                    if picking_native_phase {
                        true // take everything in second phase
                    } else {
                        !matches!(
                            lit.predicate,
                            ir::PredicateIdentifier::Normal(Predicate::Native(_))
                        )
                    }
                })
                .max_by_key(|(_, literal)| {
                    self.get_adornment(literal, &currently_bound)
                        .iter()
                        .filter(|&&b| b == Binding::Bound)
                        .count()
                })
                .map(|(i, _)| i);

            if best_literal_index.is_none() {
                // No candidate found in this phase → switch to native phase.
                if !picking_native_phase {
                    picking_native_phase = true;
                    continue;
                }
            }

            let Some(index) = best_literal_index else {
                // Should not happen, but break to avoid infinite loop.
                break;
            };

            let best_literal = remaining_literals.remove(index);

            // Only wildcards that are *already bound* in this literal become available
            // to later literals.  Otherwise we would mistakenly count variables in
            // still-free positions as bound and distort the heuristic.
            let adornment = self.get_adornment(&best_literal, &currently_bound);
            for (term, bind) in best_literal.terms.iter().zip(adornment.iter()) {
                if *bind == Binding::Bound {
                    if let Ok(wcs) = collect_wildcards(std::slice::from_ref(term)) {
                        currently_bound.extend(wcs);
                    }
                }
            }

            reordered_body.push(best_literal);
        }
        reordered_body
    }

    /// Performs the Magic Set transformation on a set of Datalog rules.
    fn magic_set_transform(
        &self,
        program: &[ir::Rule],
        request: &[StatementTmpl],
    ) -> Result<QueryPlan, SolverError> {
        let mut magic_rules = Vec::new();
        let mut guarded_rules = Vec::new();
        let mut seen_guarded_rules = HashSet::new();

        let mut adorned_predicates = HashSet::new();
        let mut worklist: VecDeque<(String, Adornment)> = VecDeque::new();

        // 1. Seed the worklist and create seed rules from the initial request.
        for tmpl in request {
            if let Predicate::Custom(cpr) = &tmpl.pred {
                let request_literal = ir::Atom {
                    predicate: ir::PredicateIdentifier::Normal(Predicate::Custom(cpr.clone())),
                    terms: tmpl.args.clone(),
                    order: usize::MAX,
                };

                let adornment = self.get_adornment(&request_literal, &HashSet::new());
                let pred_name = &cpr.predicate().name;

                if adorned_predicates.insert((pred_name.clone(), adornment.clone())) {
                    worklist.push_back((pred_name.clone(), adornment.clone()));
                }

                // Create the magic seed rule.
                let magic_pred_id = self.create_magic_predicate_id(pred_name, &adornment);
                let magic_head_terms = request_literal
                    .terms
                    .iter()
                    .zip(adornment.iter())
                    .filter(|(_, &b)| b == Binding::Bound)
                    .map(|(t, _)| t.clone())
                    .collect();

                magic_rules.push(ir::Rule {
                    head: ir::Atom {
                        predicate: magic_pred_id,
                        terms: magic_head_terms,
                        order: usize::MAX,
                    },
                    body: vec![], // No flattened literals
                });
            }
        }

        // 2. Process the worklist to generate all necessary magic and guarded rules.
        while let Some((pred_name, adornment)) = worklist.pop_front() {
            // Find all rules in the program that define the predicate.
            let relevant_rules: Vec<_> = program
                .iter()
                .filter(|rule| match &rule.head.predicate {
                    ir::PredicateIdentifier::Normal(Predicate::Custom(cpr)) => {
                        cpr.predicate().name == pred_name
                    }
                    _ => false,
                })
                .collect();

            for rule in relevant_rules {
                // Create and add the guarded rule if we haven't seen it for this adornment.
                let guarded_rule = self.create_guarded_rule(rule, &adornment)?;
                let rule_signature = format!("{:?}", guarded_rule);
                if seen_guarded_rules.insert(rule_signature) {
                    guarded_rules.push(guarded_rule);
                }

                // Determine the initial set of bound variables from the head's adornment.
                let mut bound_in_body = HashSet::new();
                for (term, binding) in rule.head.terms.iter().zip(adornment.iter()) {
                    if *binding == Binding::Bound {
                        if let Ok(wildcards) = collect_wildcards(std::slice::from_ref(term)) {
                            bound_in_body.extend(wildcards);
                        }
                    }
                }

                // Reorder body literals based on the SIPS.
                let reordered_body = self.reorder_body_for_sips(&rule.body, &bound_in_body);

                // Create magic propagation rules for custom predicates in the body.
                let mut accumulated_guards =
                    vec![self.create_magic_guard(&pred_name, &adornment, &rule.head.terms)?];
                let mut accumulated_bindings = bound_in_body.clone();

                for literal in &reordered_body {
                    // If this literal is a fully-bound native predicate, its constraint
                    // should already apply to **this** propagation step.  Push it into
                    // the guards *before* emitting any magic rule so its bindings are
                    // taken into account.
                    let adornment_now = self.get_adornment(literal, &accumulated_bindings);
                    let is_fully_bound_native =
                        matches!(
                            &literal.predicate,
                            ir::PredicateIdentifier::Normal(Predicate::Native(_))
                        ) && adornment_now.iter().all(|b| *b == Binding::Bound);

                    if is_fully_bound_native {
                        accumulated_guards.push(literal.clone());
                    }

                    let literal_cpr = match &literal.predicate {
                        ir::PredicateIdentifier::Normal(Predicate::Custom(cpr)) => {
                            Some(cpr.clone())
                        }
                        _ => None,
                    };

                    if let Some(cpr) = literal_cpr {
                        let body_literal_adornment =
                            self.get_adornment(literal, &accumulated_bindings);
                        let body_pred_name = &cpr.predicate().name;

                        if adorned_predicates
                            .insert((body_pred_name.clone(), body_literal_adornment.clone()))
                        {
                            worklist.push_back((
                                body_pred_name.clone(),
                                body_literal_adornment.clone(),
                            ));
                        }

                        // Create the magic propagation rule.
                        let magic_head_id =
                            self.create_magic_predicate_id(body_pred_name, &body_literal_adornment);
                        let magic_head_terms = literal
                            .terms
                            .iter()
                            .zip(body_literal_adornment.iter())
                            .filter(|(_, &b)| b == Binding::Bound)
                            .map(|(t, _)| t.clone())
                            .collect();

                        magic_rules.push(ir::Rule {
                            head: ir::Atom {
                                predicate: magic_head_id,
                                terms: magic_head_terms,
                                order: usize::MAX,
                            },
                            body: accumulated_guards.clone(),
                        });
                    }

                    // Add the current literal to the set of guards for the *next* magic rule
                    // unless we already added it above.
                    if !is_fully_bound_native {
                        accumulated_guards.push(literal.clone());
                    }

                    // Update bindings for the next literal in the chain.
                    if let Ok(newly_bound) = collect_wildcards(&literal.terms) {
                        accumulated_bindings.extend(newly_bound);
                    }
                }
            }
        }

        Ok(QueryPlan {
            magic_rules,
            guarded_rules,
        })
    }

    /// Creates the magic predicate identifier for a given predicate name and adornment.
    fn create_magic_predicate_id(
        &self,
        pred_name: &str,
        adornment: &Adornment,
    ) -> ir::PredicateIdentifier {
        let bound_indices = adornment
            .iter()
            .enumerate()
            .filter(|(_, &b)| b == Binding::Bound)
            .map(|(i, _)| i)
            .collect();

        ir::PredicateIdentifier::Magic {
            name: pred_name.to_string(),
            bound_indices,
        }
    }

    /// Creates a guarded version of a rule by adding a magic literal to its body.
    fn create_guarded_rule(
        &self,
        rule: &ir::Rule,
        head_adornment: &Adornment,
    ) -> Result<ir::Rule, SolverError> {
        let mut guarded_rule = rule.clone();
        let pred_name = match &rule.head.predicate {
            ir::PredicateIdentifier::Normal(Predicate::Custom(cpr)) => &cpr.predicate().name,
            _ => return Ok(rule.clone()), // Only guard custom predicates
        };

        let magic_pred_id = self.create_magic_predicate_id(pred_name, head_adornment);

        // The terms of the magic literal are the *bound* terms from the head.
        let magic_terms: Vec<StatementTmplArg> = rule
            .head
            .terms
            .iter()
            .zip(head_adornment.iter())
            .filter(|(_, &b)| b == Binding::Bound)
            .map(|(t, _)| t.clone())
            .collect();

        let magic_literal = ir::Atom {
            predicate: magic_pred_id,
            terms: magic_terms,
            order: usize::MAX,
        };

        // Compute which wildcards are already bound at the start of the body
        let mut initially_bound: HashSet<Wildcard> = HashSet::new();
        for (term, binding) in rule.head.terms.iter().zip(head_adornment.iter()) {
            if *binding == Binding::Bound {
                if let Ok(wcs) = collect_wildcards(std::slice::from_ref(term)) {
                    initially_bound.extend(wcs);
                }
            }
        }

        let reordered = self.reorder_body_for_sips(&rule.body, &initially_bound);

        // Final guarded body: magic guard first, then the reordered literals.
        let mut new_body = Vec::with_capacity(1 + reordered.len());
        new_body.push(magic_literal);
        new_body.extend(reordered);

        guarded_rule.body = new_body;
        Ok(guarded_rule)
    }

    fn create_magic_guard(
        &self,
        pred_name: &str,
        adornment: &Adornment,
        head_terms: &[StatementTmplArg],
    ) -> Result<ir::Atom, SolverError> {
        let magic_pred_id = self.create_magic_predicate_id(pred_name, adornment);
        let magic_terms: Vec<StatementTmplArg> = head_terms
            .iter()
            .zip(adornment.iter())
            .filter(|(_, &b)| b == Binding::Bound)
            .map(|(t, _)| t.clone())
            .collect();
        Ok(ir::Atom {
            predicate: magic_pred_id,
            terms: magic_terms,
            order: usize::MAX,
        })
    }

    pub fn create_plan(&self, request: &[StatementTmpl]) -> Result<QueryPlan, SolverError> {
        let mut all_rules = self.collect_and_flatten_rules(request)?;
        let mut final_request = request.to_vec();

        // If the request contains any native predicates, or is empty but has custom rules defined,
        // we synthesize a single top-level goal predicate to drive the evaluation.
        // This unifies the handling of all query types.
        if !request.is_empty() {
            // Synthesize an implicit rule for the entire request block.
            // e.g., REQUEST(A, B) becomes `_request_goal(wildcards) :- A, B.`
            let synthetic_pred_name = "_request_goal".to_string();

            let mut synthetic_rule_body = Vec::new();
            for tmpl in request {
                synthetic_rule_body.push(ir::Atom {
                    predicate: ir::PredicateIdentifier::Normal(tmpl.pred.clone()),
                    terms: tmpl.args.clone(),
                    order: usize::MAX,
                });
            }

            // The head of the synthetic rule contains all wildcards from the request.
            let bound_variables = request
                .iter()
                .map(|tmpl| collect_wildcards(&tmpl.args))
                .collect::<Result<Vec<_>, _>>()?
                .into_iter()
                .flatten()
                .collect::<HashSet<_>>();

            let mut head_wildcards: Vec<_> = bound_variables.into_iter().collect();
            head_wildcards.sort_by_key(|w| w.index); // Canonical order
            let wildcard_names: Vec<_> = head_wildcards.iter().map(|w| w.name.clone()).collect();

            // Create a synthetic CustomPredicateRef to represent our implicit goal.
            let synth_pred_def = CustomPredicate {
                name: synthetic_pred_name.clone(),
                conjunction: true,
                statements: request.to_vec(),
                args_len: head_wildcards.len(),
                wildcard_names: wildcard_names.clone(),
            };
            let params = Params::default();
            let synth_batch = CustomPredicateBatch::new(
                &params,
                "SyntheticRequestBatch".to_string(),
                vec![synth_pred_def],
            );
            let synthetic_cpr = CustomPredicateRef::new(synth_batch, 0);

            let synthetic_rule_head = ir::Atom {
                predicate: ir::PredicateIdentifier::Normal(Predicate::Custom(
                    synthetic_cpr.clone(),
                )),
                terms: head_wildcards
                    .into_iter()
                    .map(StatementTmplArg::Wildcard)
                    .collect(),
                order: usize::MAX,
            };

            all_rules.push(ir::Rule {
                head: synthetic_rule_head,
                body: synthetic_rule_body,
            });

            // Replace the original request with a new request for our synthetic goal.
            let synthetic_request_args = wildcard_names
                .iter()
                .enumerate()
                .map(|(i, name)| StatementTmplArg::Wildcard(Wildcard::new(name.clone(), i)))
                .collect();

            final_request = vec![StatementTmpl {
                pred: Predicate::Custom(synthetic_cpr),
                args: synthetic_request_args,
            }];
        }

        self.magic_set_transform(&all_rules, &final_request)
    }

    /// Same as `create_plan` but skips the Magic-Set transformation.
    /// Useful in tests to isolate bugs in the optimiser from bugs in the
    /// semi-naive engine, materialiser, proof reconstructor, etc.
    pub fn create_plan_naive(&self, request: &[StatementTmpl]) -> Result<QueryPlan, SolverError> {
        // 1. Collect & flatten all custom-predicate rules
        let mut all_rules = self.collect_and_flatten_rules(request)?;

        // 2. Synthesise the `_request_goal` rule exactly like `create_plan` does, but we don't
        // need to preserve an adjusted `request` value afterwards.
        if !request.is_empty() {
            // --- identical to the block in `create_plan` ------------------
            let synthetic_pred_name = "_request_goal".to_string();

            let synthetic_rule_body: Vec<_> = request
                .iter()
                .map(|tmpl| ir::Atom {
                    predicate: ir::PredicateIdentifier::Normal(tmpl.pred.clone()),
                    terms: tmpl.args.clone(),
                    order: usize::MAX,
                })
                .collect();

            // gather distinct wildcards from the user request
            let bound_wcs: HashSet<_> = request
                .iter()
                .map(|tmpl| collect_wildcards(&tmpl.args))
                .collect::<Result<Vec<_>, _>>()?
                .into_iter()
                .flatten()
                .collect();

            // canonical ordering for the synthetic head
            let mut head_wildcards: Vec<_> = bound_wcs.into_iter().collect();
            head_wildcards.sort_by_key(|w| w.index);

            let wildcard_names: Vec<_> = head_wildcards.iter().map(|w| w.name.clone()).collect();

            // build a one-off CustomPredicateRef for the goal
            let synth_pred_def = CustomPredicate {
                name: synthetic_pred_name.clone(),
                conjunction: true,
                statements: request.to_vec(),
                args_len: head_wildcards.len(),
                wildcard_names: wildcard_names.clone(),
            };
            let params = Params::default();
            let synth_batch = CustomPredicateBatch::new(
                &params,
                "SyntheticRequestBatch".to_string(),
                vec![synth_pred_def],
            );
            let synthetic_cpr = CustomPredicateRef::new(synth_batch, 0);

            let synthetic_rule_head = ir::Atom {
                predicate: ir::PredicateIdentifier::Normal(Predicate::Custom(
                    synthetic_cpr.clone(),
                )),
                terms: head_wildcards
                    .iter()
                    .cloned()
                    .map(StatementTmplArg::Wildcard)
                    .collect(),
                order: usize::MAX,
            };

            all_rules.push(ir::Rule {
                head: synthetic_rule_head,
                body: synthetic_rule_body,
            });
            // --- end identical block --------------------------------------
        }

        // 3. Return a plan with *no* magic rules
        Ok(QueryPlan {
            magic_rules: vec![],
            guarded_rules: all_rules,
        })
    }

    /// Takes a proof request and transitively collects all custom predicate
    /// definitions, flattening them into the Datalog IR format.
    fn collect_and_flatten_rules(
        &self,
        request: &[StatementTmpl],
    ) -> Result<Vec<ir::Rule>, SolverError> {
        let mut all_rules = Vec::new();
        let mut worklist: VecDeque<CustomPredicateRef> = VecDeque::new();
        let mut visited: HashSet<usize> = HashSet::new();

        // Seed the worklist with custom predicates from the initial request.
        for tmpl in request {
            if let Predicate::Custom(cpr) = &tmpl.pred {
                if visited.insert(cpr.index) {
                    worklist.push_back(cpr.clone());
                }
            }
        }

        while let Some(cpr) = worklist.pop_front() {
            let pred_def = cpr.predicate();
            let head_args: Vec<StatementTmplArg> = pred_def
                .wildcard_names
                .iter()
                .take(pred_def.args_len)
                .enumerate()
                .map(|(i, name)| StatementTmplArg::Wildcard(Wildcard::new(name.clone(), i)))
                .collect();

            if pred_def.conjunction {
                // AND case: one rule with all statements in the body.
                let rule = self.translate_to_ir_rule(
                    &cpr,
                    &head_args,
                    &pred_def.statements,
                    &mut worklist,
                    &mut visited,
                )?;
                all_rules.push(rule);
            } else {
                // OR case: one rule for each statement in the body.
                for (i, tmpl) in pred_def.statements.iter().enumerate() {
                    let mut rule = self.translate_to_ir_rule(
                        &cpr,
                        &head_args,
                        std::slice::from_ref(tmpl),
                        &mut worklist,
                        &mut visited,
                    )?;
                    // Record which OR-branch this rule originates from so that proof
                    // reconstruction can restore the author-written order.
                    rule.head.order = i;
                    all_rules.push(rule);
                }
            }
        }

        Ok(all_rules)
    }

    /// Helper to translate a single custom predicate definition into a Datalog IR rule.
    fn translate_to_ir_rule(
        &self,
        cpr: &CustomPredicateRef,
        head_args: &[StatementTmplArg],
        body_tmpls: &[StatementTmpl],
        worklist: &mut VecDeque<CustomPredicateRef>,
        visited: &mut HashSet<usize>,
    ) -> Result<ir::Rule, SolverError> {
        // Translate the head of the rule.
        let head_literal = ir::Atom {
            predicate: ir::PredicateIdentifier::Normal(Predicate::Custom(cpr.clone())),
            terms: head_args.to_vec(),
            order: usize::MAX,
        };

        // Translate the body of the rule.
        let mut body_literals = Vec::new();
        for (i, tmpl) in body_tmpls.iter().enumerate() {
            match &tmpl.pred {
                // Resolve self-references inside the same batch immediately.
                Predicate::BatchSelf(idx) => {
                    let resolved_cpr = CustomPredicateRef::new(cpr.batch.clone(), *idx);

                    body_literals.push(ir::Atom {
                        predicate: ir::PredicateIdentifier::Normal(Predicate::Custom(
                            resolved_cpr.clone(),
                        )),
                        terms: tmpl.args.clone(),
                        order: i,
                    });

                    // Schedule the referenced predicate for traversal if not yet seen.
                    if visited.insert(*idx) {
                        worklist.push_back(resolved_cpr);
                    }
                }
                _ => {
                    // Leave other predicates unchanged.
                    body_literals.push(ir::Atom {
                        predicate: ir::PredicateIdentifier::Normal(tmpl.pred.clone()),
                        terms: tmpl.args.clone(),
                        order: i,
                    });
                }
            }
        }

        Ok(ir::Rule {
            head: head_literal,
            body: body_literals,
        })
    }
}

impl Default for Planner {
    fn default() -> Self {
        Self::new()
    }
}

fn collect_wildcards(args: &[StatementTmplArg]) -> Result<HashSet<Wildcard>, SolverError> {
    let mut wildcards = HashSet::new();
    for arg in args {
        match arg {
            StatementTmplArg::Wildcard(w) => {
                wildcards.insert(w.clone());
            }
            StatementTmplArg::AnchoredKey(pod_wc, _) => {
                wildcards.insert(pod_wc.clone());
            }
            StatementTmplArg::Literal(_) => {}
            StatementTmplArg::None => {
                return Err(SolverError::Internal(
                    "None argument not supported in custom predicates".to_string(),
                ));
            }
        }
    }
    Ok(wildcards)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{
        lang::{self, parse},
        middleware::{NativePredicate, Params, Predicate},
        solver::ir,
    };

    #[test]
    fn test_simple_magic_set_transform() -> Result<(), lang::LangError> {
        let podlog = r#"
            is_equal(A, B) = AND(
                Equal(?A["key"], ?B["key"])
            )

            REQUEST(
                is_equal(?Pod1, ?Pod2)
            )
        "#;

        let params = Params::default();
        let processed = parse(podlog, &params, &[])?;
        let request = processed.request_templates;

        let planner = Planner::new();
        let plan = planner.create_plan(&request).unwrap();

        assert_eq!(plan.magic_rules.len(), 2);
        assert_eq!(plan.guarded_rules.len(), 2);

        println!("plan: {:#?}", plan);

        // Check magic rule (seed)
        let magic_rule = &plan.magic_rules[0];
        assert!(
            magic_rule.body.is_empty(),
            "Magic seed rule should have an empty body"
        );
        match &magic_rule.head.predicate {
            ir::PredicateIdentifier::Magic {
                name,
                bound_indices,
            } => {
                assert_eq!(name, "_request_goal");
                assert!(
                    bound_indices.is_empty(),
                    "Adornment should be 'ff', so no bound indices"
                );
            }
            _ => panic!("Expected a magic predicate in the head of the magic rule"),
        }
        assert!(
            magic_rule.head.terms.is_empty(),
            "Magic 'ff' head should have no terms"
        );

        // Check guarded rule
        let guarded_rule = &plan.guarded_rules[1];
        assert_eq!(guarded_rule.body.len(), 2, "Expected magic_guard + Equal");

        // Check head of guarded rule
        match &guarded_rule.head.predicate {
            ir::PredicateIdentifier::Normal(Predicate::Custom(cpr)) => {
                assert_eq!(cpr.predicate().name, "is_equal");
            }
            _ => panic!("Expected normal custom predicate in head of guarded rule"),
        }

        // Check body of guarded rule
        match &guarded_rule.body[0].predicate {
            ir::PredicateIdentifier::Magic {
                name,
                bound_indices,
            } => {
                assert_eq!(name, "is_equal");
                assert!(bound_indices.is_empty());
            }
            _ => panic!("Expected magic guard as first literal in body"),
        }

        match &guarded_rule.body[1].predicate {
            ir::PredicateIdentifier::Normal(Predicate::Native(NativePredicate::Equal)) => (),
            _ => panic!("Expected Equal predicate as the second literal in the body"),
        }

        Ok(())
    }

    #[test]
    fn test_magic_set_with_bound_variable() -> Result<(), lang::LangError> {
        let podlog = r#"
            is_friend(A, B) = AND(
                Equal(?A["id"], ?B["id"])
            )

            REQUEST(
                is_friend("alice_pod", ?AnyFriend)
            )
        "#;

        let params = Params::default();
        let processed = parse(podlog, &params, &[])?;
        let request = processed.request_templates;

        let planner = Planner::new();
        let plan = planner.create_plan(&request).unwrap();

        assert_eq!(plan.magic_rules.len(), 2);
        assert_eq!(plan.guarded_rules.len(), 2);

        // Find the magic seed rule for the request goal
        let magic_seed_rule = plan
            .magic_rules
            .iter()
            .find(|r| r.body.is_empty())
            .expect("Could not find magic seed rule");

        match &magic_seed_rule.head.predicate {
            ir::PredicateIdentifier::Magic {
                name,
                bound_indices,
            } => {
                assert_eq!(name, "_request_goal");
                assert!(bound_indices.is_empty()); // Adornment for the synthetic goal is 'f'
            }
            _ => panic!("Expected magic predicate"),
        }

        assert!(magic_seed_rule.head.terms.is_empty()); // No bound terms are passed to the synthetic goal

        // Check guarded rule for `is_friend`
        let guarded_rule = plan
            .guarded_rules
            .iter()
            .find(|r| match &r.head.predicate {
                ir::PredicateIdentifier::Normal(Predicate::Custom(cpr)) => {
                    cpr.predicate().name == "is_friend"
                }
                _ => false,
            })
            .expect("Could not find guarded rule for is_friend");

        // Body: magic_guard, Equal
        assert_eq!(guarded_rule.body.len(), 2);

        // check the magic guard
        let magic_guard = &guarded_rule.body[0];
        match &magic_guard.predicate {
            ir::PredicateIdentifier::Magic {
                name,
                bound_indices,
            } => {
                assert_eq!(name, "is_friend");
                assert_eq!(bound_indices, &vec![0]); // bf
            }
            _ => panic!("Expected magic guard"),
        }
        assert_eq!(magic_guard.terms.len(), 1);
        match &magic_guard.terms[0] {
            // The term in the guard refers to the variable in the rule's head.
            StatementTmplArg::Wildcard(w) => assert_eq!(w.name, "A"),
            _ => panic!("Expected wildcard term in magic guard"),
        }

        Ok(())
    }

    #[test]
    fn test_recursive_predicate() -> Result<(), lang::LangError> {
        let podlog = r#"
            edge(X, Y) = AND( Equal(?X["val"], ?Y["val"]) )

            path(X, Y) = OR(
                edge(?X, ?Y)
                path_rec(?X, ?Y)
            )
            
            path_rec(X, Y, private: Z) = AND(
                path(?X, ?Z)
                edge(?Z, ?Y)
            )

            REQUEST(
                path("start_node", ?End)
            )
        "#;

        let params = Params::default();
        let processed = parse(podlog, &params, &[])?;
        let request = processed.request_templates;

        let planner = Planner::new();
        let plan = planner.create_plan(&request).unwrap();

        // Expected outcome analysis:
        // - 1 seed rule for _request_goal(?End) -> magic__request_goal_f().
        // - Propagation from _request_goal to path -> magic_path_bf("start_node") :- magic__request_goal_f().
        // - Propagation from path to edge: magic_edge_bf(X) :- magic_path_bf(X).
        // - Propagation from path to path_rec: magic_path_bf(X) :- magic_path_rec_bf(X).
        // - Propagation from path_rec to path (recursive): magic_path_bf(X) :- magic_path_rec_bf(X).
        // - Propagation from path_rec to edge: magic_edge_bf(Z) :- magic_path_rec_bf(X), path(X,Z).
        // Total: 6 magic rules.

        // - Guarded rules are created for each predicate with a magic adornment.
        // - _request_goal -> 1 rule
        // - (path, bf) -> 2 rules (from OR).
        // - (edge, bf) -> 1 rule.
        // - (path_rec, bf) -> 1 rule.
        // Total: 5 guarded rules.

        assert_eq!(
            plan.magic_rules.len(),
            6,
            "Incorrect number of magic rules generated"
        );
        assert_eq!(
            plan.guarded_rules.len(),
            5,
            "Incorrect number of guarded rules generated"
        );

        // Check for the seed rule.
        let has_seed_rule = plan.magic_rules.iter().any(|r| {
            if let ir::PredicateIdentifier::Magic {
                name,
                bound_indices,
            } = &r.head.predicate
            {
                r.body.is_empty()
                    && name == "_request_goal"
                    && bound_indices.is_empty()
                    && r.head.terms.is_empty()
            } else {
                false
            }
        });
        assert!(
            has_seed_rule,
            "Magic seed rule for _request_goal() was not generated"
        );

        // Check for recursive propagation
        let has_recursive_propagation = plan.magic_rules.iter().any(|r| {
            if let ir::PredicateIdentifier::Magic { name, .. } = &r.head.predicate {
                name == "path" && !r.body.is_empty()
            } else {
                false
            }
        });
        assert!(
            has_recursive_propagation,
            "Magic propagation rule for recursive 'path' call was not generated"
        );

        Ok(())
    }
}
