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

mod translator;

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
    fn get_adornment(&self, literal: &ir::Literal, bound_vars: &HashSet<Wildcard>) -> Adornment {
        literal
            .terms
            .iter()
            .map(|term| match term {
                ir::Term::Constant(_) => Binding::Bound,
                ir::Term::Variable(w) => {
                    if bound_vars.contains(w) {
                        Binding::Bound
                    } else {
                        Binding::Free
                    }
                }
            })
            .collect()
    }

    /// Reorders the literals in a rule body based on a "most-bound-first" SIPS.
    fn reorder_body_for_sips(
        &self,
        body: &[ir::Literal],
        initial_bound: &HashSet<Wildcard>,
    ) -> Vec<ir::Literal> {
        let mut reordered_body = Vec::new();
        let mut remaining_literals: Vec<ir::Literal> = body.to_vec();
        let mut currently_bound = initial_bound.clone();

        while !remaining_literals.is_empty() {
            let best_literal_index = remaining_literals
                .iter()
                .enumerate()
                .max_by_key(|(_, literal)| {
                    self.get_adornment(literal, &currently_bound)
                        .iter()
                        .filter(|&&b| b == Binding::Bound)
                        .count()
                })
                .map(|(i, _)| i);

            if let Some(index) = best_literal_index {
                let best_literal = remaining_literals.remove(index);

                let adornment = self.get_adornment(&best_literal, &currently_bound);
                for (i, term) in best_literal.terms.iter().enumerate() {
                    if let ir::Term::Variable(w) = term {
                        if adornment[i] == Binding::Free {
                            currently_bound.insert(w.clone());
                        }
                    }
                }

                reordered_body.push(best_literal);
            } else {
                reordered_body.extend(remaining_literals.into_iter());
                break;
            }
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
                let mut ctx = translator::TranslationContext::new();
                let request_terms = tmpl
                    .args
                    .iter()
                    .map(|arg| ctx.translate_arg_to_term(arg))
                    .collect::<Result<Vec<_>, _>>()?;

                let request_literal = ir::Literal {
                    predicate: ir::PredicateIdentifier::Normal(Predicate::Custom(cpr.clone())),
                    terms: request_terms,
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
                let magic_seed_body = ctx.flattened_literals;

                magic_rules.push(ir::Rule {
                    head: ir::Literal {
                        predicate: magic_pred_id,
                        terms: magic_head_terms,
                    },
                    body: magic_seed_body,
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
                        if let ir::Term::Variable(w) = term {
                            bound_in_body.insert(w.clone());
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
                    let literal_cpr = match &literal.predicate {
                        ir::PredicateIdentifier::Normal(Predicate::Custom(cpr)) => {
                            Some(cpr.clone())
                        }
                        ir::PredicateIdentifier::Normal(Predicate::BatchSelf(idx)) => {
                            let head_cpr = match &rule.head.predicate {
                                ir::PredicateIdentifier::Normal(Predicate::Custom(cpr)) => cpr,
                                _ => continue,
                            };
                            Some(CustomPredicateRef::new(head_cpr.batch.clone(), *idx))
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
                            head: ir::Literal {
                                predicate: magic_head_id,
                                terms: magic_head_terms,
                            },
                            body: accumulated_guards.clone(),
                        });
                    }

                    // Add the current literal to the set of guards for the next magic rule.
                    // If it's a BatchSelf, resolve it now into a full Custom predicate.
                    let guard_to_add = match &literal.predicate {
                        ir::PredicateIdentifier::Normal(Predicate::BatchSelf(idx)) => {
                            let head_cpr = match &rule.head.predicate {
                                ir::PredicateIdentifier::Normal(Predicate::Custom(cpr)) => cpr,
                                _ => {
                                    // This should be unreachable if the program is well-formed.
                                    return Err(SolverError::Internal(
                                        "Cannot resolve BatchSelf in rule with non-custom head"
                                            .to_string(),
                                    ));
                                }
                            };
                            let resolved_cpr =
                                CustomPredicateRef::new(head_cpr.batch.clone(), *idx);
                            let mut resolved_literal = literal.clone();
                            resolved_literal.predicate =
                                ir::PredicateIdentifier::Normal(Predicate::Custom(resolved_cpr));
                            resolved_literal
                        }
                        _ => literal.clone(),
                    };
                    accumulated_guards.push(guard_to_add);

                    // Update bindings for the next literal in the chain.
                    for term in &literal.terms {
                        if let ir::Term::Variable(w) = term {
                            accumulated_bindings.insert(w.clone());
                        }
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
        let magic_terms: Vec<ir::Term> = rule
            .head
            .terms
            .iter()
            .zip(head_adornment.iter())
            .filter(|(_, &b)| b == Binding::Bound)
            .map(|(t, _)| t.clone())
            .collect();

        let magic_literal = ir::Literal {
            predicate: magic_pred_id,
            terms: magic_terms,
        };

        guarded_rule.body.insert(0, magic_literal);
        Ok(guarded_rule)
    }

    fn create_magic_guard(
        &self,
        pred_name: &str,
        adornment: &Adornment,
        head_terms: &[ir::Term],
    ) -> Result<ir::Literal, SolverError> {
        let magic_pred_id = self.create_magic_predicate_id(pred_name, adornment);
        let magic_terms: Vec<ir::Term> = head_terms
            .iter()
            .zip(adornment.iter())
            .filter(|(_, &b)| b == Binding::Bound)
            .map(|(t, _)| t.clone())
            .collect();
        Ok(ir::Literal {
            predicate: magic_pred_id,
            terms: magic_terms,
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

            let mut ctx = translator::TranslationContext::new();
            let mut synthetic_rule_body = Vec::new();
            for tmpl in request {
                let terms = tmpl
                    .args
                    .iter()
                    .map(|arg| ctx.translate_arg_to_term(arg))
                    .collect::<Result<Vec<_>, _>>()?;
                synthetic_rule_body.push(ir::Literal {
                    predicate: ir::PredicateIdentifier::Normal(tmpl.pred.clone()),
                    terms,
                });
            }
            let mut full_synthetic_body = ctx.flattened_literals;
            full_synthetic_body.extend(synthetic_rule_body);

            // The head of the synthetic rule contains all wildcards from the request.
            let mut head_wildcards: Vec<_> = ctx.bound_variables.into_iter().collect();
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

            let synthetic_rule_head = ir::Literal {
                predicate: ir::PredicateIdentifier::Normal(Predicate::Custom(
                    synthetic_cpr.clone(),
                )),
                terms: head_wildcards.into_iter().map(ir::Term::Variable).collect(),
            };

            all_rules.push(ir::Rule {
                head: synthetic_rule_head,
                body: full_synthetic_body,
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
                for tmpl in &pred_def.statements {
                    let rule = self.translate_to_ir_rule(
                        &cpr,
                        &head_args,
                        std::slice::from_ref(tmpl),
                        &mut worklist,
                        &mut visited,
                    )?;
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
        let mut ctx = translator::TranslationContext::new();

        // Translate the head of the rule.
        let head_terms = head_args
            .iter()
            .map(|arg| ctx.translate_arg_to_term(arg))
            .collect::<Result<Vec<_>, _>>()?;
        let head_literal = ir::Literal {
            predicate: ir::PredicateIdentifier::Normal(Predicate::Custom(cpr.clone())),
            terms: head_terms,
        };

        // Translate the body of the rule.
        let mut body_literals = Vec::new();
        for tmpl in body_tmpls {
            let terms = tmpl
                .args
                .iter()
                .map(|arg| ctx.translate_arg_to_term(arg))
                .collect::<Result<Vec<_>, _>>()?;
            body_literals.push(ir::Literal {
                predicate: ir::PredicateIdentifier::Normal(tmpl.pred.clone()),
                terms,
            });

            // If this body literal is a custom predicate, add it to the worklist for traversal.
            if let Predicate::BatchSelf(idx) = &tmpl.pred {
                if visited.insert(*idx) {
                    worklist.push_back(CustomPredicateRef::new(cpr.batch.clone(), *idx));
                }
            }
        }

        // Prepend any flattened literals (from GetValue) to the body.
        let mut final_body = ctx.flattened_literals;
        final_body.extend(body_literals);

        Ok(ir::Rule {
            head: head_literal,
            body: final_body,
        })
    }
}

impl Default for Planner {
    fn default() -> Self {
        Self::new()
    }
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
        assert_eq!(
            guarded_rule.body.len(),
            4,
            "Expected magic_guard + 2*GetValue + Equal"
        );

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

        assert_eq!(
            guarded_rule.body[1].predicate,
            ir::PredicateIdentifier::GetValue
        );
        assert_eq!(
            guarded_rule.body[2].predicate,
            ir::PredicateIdentifier::GetValue
        );

        match &guarded_rule.body[3].predicate {
            ir::PredicateIdentifier::Normal(Predicate::Native(NativePredicate::Equal)) => (),
            _ => panic!("Expected Equal predicate as the final literal in the body"),
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

        // Body: magic_guard, GetValue(A), GetValue(B), Equal
        assert_eq!(guarded_rule.body.len(), 4);

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
            ir::Term::Variable(w) => assert_eq!(w.name, "A"),
            _ => panic!("Expected variable term in magic guard"),
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
        // - Propagation from path to path_rec: magic_path_rec_bf(X) :- magic_path_bf(X).
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
