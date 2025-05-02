pub mod error;
pub mod indexing;
pub mod pod_building;
pub mod solver;
// Keep test_utils public for external integration/library tests if needed
pub mod test_utils;
pub mod translation;
pub mod types;

pub use error::ProverError;

#[cfg(test)]
mod tests {
    use std::{collections::HashMap, sync::Arc};

    use super::*;
    use crate::{
        middleware::{
            self, AnchoredKey, CustomPredicate, CustomPredicateBatch, CustomPredicateRef, Key,
            KeyOrWildcard, NativePredicate, Predicate, Statement, StatementTmpl, StatementTmplArg,
            ToFields, Value, Wildcard, WildcardValue,
        },
        prover::{pod_building, solver, test_utils::*, types::CustomDefinitions},
    };

    #[test]
    fn test_prover_end_to_end_simple_gt() -> Result<(), Box<dyn std::error::Error>> {
        let params = middleware::Params::default();

        // 1. Create mock input SignedPods containing initial key-value data.
        let pod_a =
            create_test_signed_pod(&params, &[("foo", Value::from(10))], "signer_a").unwrap();
        let pod_b =
            create_test_signed_pod(&params, &[("bar", Value::from(20))], "signer_b").unwrap();

        // 2. Define the request template: we want to prove Gt(?y["bar"], ?x["foo"])
        let wc_x = Wildcard::new("x".to_string(), 0); // Wildcard representing pod A's context
        let wc_y = Wildcard::new("y".to_string(), 1); // Wildcard representing pod B's context
        let key_foo = Key::new("foo".to_string());
        let key_bar = Key::new("bar".to_string());

        let request_templates = vec![StatementTmpl {
            pred: middleware::Predicate::Native(NativePredicate::Gt),
            args: vec![
                StatementTmplArg::Key(wc_y.clone(), KeyOrWildcard::Key(key_bar.clone())), // ?y["bar"]
                StatementTmplArg::Key(wc_x.clone(), KeyOrWildcard::Key(key_foo.clone())), // ?x["foo"]
            ],
        }];

        // 3. Prepare inputs for the constraint solver.
        // Index the initial facts (public statements) from the input pods.
        let initial_facts = vec![
            (pod_a.id(), pod_a.get_statement("foo").unwrap()),
            (pod_b.id(), pod_b.get_statement("bar").unwrap()),
        ];
        let indexes = indexing::ProverIndexes::build(params.clone(), &initial_facts);
        let custom_definitions = CustomDefinitions::default();

        // 4. Call the solver to find a consistent assignment and proof steps.
        let solve_result = solver::solve(&request_templates, &indexes, &custom_definitions);
        assert!(
            solve_result.is_ok(),
            "Solver failed: {:?}",
            solve_result.err()
        );
        let solution = solve_result.unwrap();

        // 5. Prepare inputs for the pod building stage.
        let original_signed_pods = HashMap::from([
            (pod_a.id(), Arc::new(pod_a.clone())),
            (pod_b.id(), Arc::new(pod_b.clone())),
        ]);
        let original_main_pods = HashMap::new();

        // 6. Call the pod building process to construct the final MainPod based on the solution.
        let build_result = pod_building::build_main_pod_from_solution(
            &solution,
            &original_signed_pods,
            &original_main_pods,
            &params,
            &request_templates,
        );
        assert!(
            build_result.is_ok(),
            "Pod building failed: {:?}",
            build_result.err()
        );
        let main_pod = build_result.unwrap();

        // 7. Verify the integrity and correctness of the generated MainPod.
        let verification_result = main_pod.pod.verify();
        assert!(
            verification_result.is_ok(),
            "MainPod verification failed: {:?}",
            verification_result.err()
        );

        // 8. Check that the generated MainPod contains the expected public statements.
        //    In this case, the target Gt statement should be public.
        let expected_public_statement = Statement::Gt(
            AnchoredKey::new(pod_b.id(), key_bar),
            AnchoredKey::new(pod_a.id(), key_foo),
        );
        assert_eq!(
            main_pod.public_statements.len(),
            2,
            "Expected exactly two public statements (Gt and ValueOf for _type)"
        );
        assert!(
            main_pod
                .public_statements
                .contains(&expected_public_statement),
            "Expected Gt statement missing from public statements"
        );

        println!("End-to-end test successful!");
        println!("Generated MainPod: {}", main_pod);

        Ok(())
    }

    #[test]
    fn test_prover_nested_custom_predicates() -> Result<(), Box<dyn std::error::Error>> {
        let params = middleware::Params::default();

        // --- Define Custom Predicates ---

        // InnerP (Index 0): Checks relationships previously held by pods a, b, c, d
        // Public Args: ?p1 (holding val_a, key_c), ?p2 (holding val_b), ?p3 (holding key_d)
        let wc_p1_inner = wc("p1_inner", 0);
        let wc_p2_inner = wc("p2_inner", 1);
        let wc_p3_inner = wc("p3_inner", 2);
        let key_val_a = key("val_a"); // Renamed from "val" (originally pod_a)
        let key_val_b = key("val_b"); // Renamed from "val" (originally pod_b)
        let key_key_c = key("key_c"); // Renamed from "key" (originally pod_c)
        let key_key_d = key("key_d"); // Renamed from "key" (originally pod_d)

        let inner_tmpl_gt = StatementTmpl {
            pred: Predicate::Native(NativePredicate::Gt),
            args: vec![
                StatementTmplArg::Key(wc_p1_inner.clone(), KeyOrWildcard::Key(key_val_a.clone())), // ?p1["val_a"]
                StatementTmplArg::Key(wc_p2_inner.clone(), KeyOrWildcard::Key(key_val_b.clone())), // ?p2["val_b"]
            ],
        };
        let inner_tmpl_eq = StatementTmpl {
            pred: Predicate::Native(NativePredicate::Equal),
            args: vec![
                StatementTmplArg::Key(wc_p1_inner.clone(), KeyOrWildcard::Key(key_key_c.clone())), // ?p1["key_c"]
                StatementTmplArg::Key(wc_p3_inner.clone(), KeyOrWildcard::Key(key_key_d.clone())), // ?p3["key_d"]
            ],
        };
        let inner_pred_def = CustomPredicate {
            name: "InnerP_Combined".to_string(),
            args_len: 3, // p1, p2, p3
            statements: vec![inner_tmpl_gt, inner_tmpl_eq],
            conjunction: true,
        };

        // OuterP (Index 1): Combines InnerP call with Lt check previously held by m, n
        // Public Args: ?pod1 (used for InnerP's p1), ?pod2 (used for InnerP's p2 & Lt's val_m), ?pod3 (used for InnerP's p3 & Lt's val_n)
        let wc_pod1_outer = wc("pod1_outer", 0);
        let wc_pod2_outer = wc("pod2_outer", 1);
        let wc_pod3_outer = wc("pod3_outer", 2);
        let key_val_m = key("val_m"); // Renamed from "val" (originally pod_m)
        let key_val_n = key("val_n"); // Renamed from "val" (originally pod_n)

        let outer_tmpl_inner = StatementTmpl {
            pred: Predicate::BatchSelf(0), // Calls InnerP_Combined at index 0
            args: vec![
                StatementTmplArg::WildcardLiteral(wc_pod1_outer.clone()), // InnerP.?p1 <- OuterP.?pod1
                StatementTmplArg::WildcardLiteral(wc_pod2_outer.clone()), // InnerP.?p2 <- OuterP.?pod2
                StatementTmplArg::WildcardLiteral(wc_pod3_outer.clone()), // InnerP.?p3 <- OuterP.?pod3
            ],
        };
        let outer_tmpl_lt = StatementTmpl {
            pred: Predicate::Native(NativePredicate::Lt),
            args: vec![
                StatementTmplArg::Key(wc_pod2_outer.clone(), KeyOrWildcard::Key(key_val_m.clone())), // ?pod2["val_m"]
                StatementTmplArg::Key(wc_pod3_outer.clone(), KeyOrWildcard::Key(key_val_n.clone())), // ?pod3["val_n"]
            ],
        };
        let outer_pred_def = CustomPredicate {
            name: "OuterP_Combined".to_string(),
            args_len: 3, // pod1, pod2, pod3
            statements: vec![outer_tmpl_inner, outer_tmpl_lt],
            conjunction: true,
        };

        // --- Create Batch and Refs ---
        let custom_batch = Arc::new(CustomPredicateBatch {
            name: "NestedBatchCombined".to_string(),
            predicates: vec![inner_pred_def.clone(), outer_pred_def.clone()], // Inner=0, Outer=1
        });
        let inner_pred_ref = CustomPredicateRef {
            batch: custom_batch.clone(),
            index: 0,
        };
        let outer_pred_ref = CustomPredicateRef {
            batch: custom_batch.clone(),
            index: 1,
        };

        // --- Create 3 Input Pods ---
        let pod_1 = create_test_signed_pod(
            // Was pod_a (val=100) and pod_c (key="same")
            &params,
            &[("val_a", val(100)), ("key_c", Value::from("same"))],
            "signer_1",
        )?;
        let pod_2 = create_test_signed_pod(
            // Was pod_b (val=50) and pod_m (val=10)
            &params,
            &[("val_b", val(50)), ("val_m", val(10))],
            "signer_2",
        )?;
        let pod_3 = create_test_signed_pod(
            // Was pod_d (key="same") and pod_n (val=20)
            &params,
            &[("key_d", Value::from("same")), ("val_n", val(20))],
            "signer_3",
        )?;

        // --- Prepare Solver Inputs ---
        let initial_facts = vec![
            // From pod_1
            (
                pod_1.id(),
                pod_1
                    .get_statement("val_a")
                    .ok_or("Missing val_a for pod_1")?
                    .clone(),
            ),
            (
                pod_1.id(),
                pod_1
                    .get_statement("key_c")
                    .ok_or("Missing key_c for pod_1")?
                    .clone(),
            ),
            // From pod_2
            (
                pod_2.id(),
                pod_2
                    .get_statement("val_b")
                    .ok_or("Missing val_b for pod_2")?
                    .clone(),
            ),
            (
                pod_2.id(),
                pod_2
                    .get_statement("val_m")
                    .ok_or("Missing val_m for pod_2")?
                    .clone(),
            ),
            // From pod_3
            (
                pod_3.id(),
                pod_3
                    .get_statement("key_d")
                    .ok_or("Missing key_d for pod_3")?
                    .clone(),
            ),
            (
                pod_3.id(),
                pod_3
                    .get_statement("val_n")
                    .ok_or("Missing val_n for pod_3")?
                    .clone(),
            ),
        ];
        let indexes = indexing::ProverIndexes::build(params.clone(), &initial_facts);

        // Build custom_definitions map
        let mut custom_definitions = CustomDefinitions::new();
        let inner_pred_variant = Predicate::Custom(inner_pred_ref.clone());
        let outer_pred_variant = Predicate::Custom(outer_pred_ref.clone());
        custom_definitions.insert(
            inner_pred_variant.to_fields(&params),
            (inner_pred_def, custom_batch.clone()),
        );
        custom_definitions.insert(
            outer_pred_variant.to_fields(&params),
            (outer_pred_def, custom_batch.clone()),
        );

        // --- Define Request Template targeting OuterP ---
        // Define wildcards for the request
        let wc_req_p1 = wc("req_p1", 10);
        let wc_req_p2 = wc("req_p2", 11);
        let wc_req_p3 = wc("req_p3", 12);

        // The request template uses wildcards for the public arguments
        let request_templates = vec![StatementTmpl {
            pred: Predicate::Custom(outer_pred_ref.clone()),
            args: vec![
                StatementTmplArg::WildcardLiteral(wc_req_p1.clone()), // ?req_p1
                StatementTmplArg::WildcardLiteral(wc_req_p2.clone()), // ?req_p2
                StatementTmplArg::WildcardLiteral(wc_req_p3.clone()), // ?req_p3
            ],
        }];

        // --- Solve ---
        // The solver needs to bind wc_req_p1=pod_1, wc_req_p2=pod_2, wc_req_p3=pod_3
        let solve_result = solver::solve(&request_templates, &indexes, &custom_definitions);
        assert!(
            solve_result.is_ok(),
            "Solver failed for nested predicates: {:?}",
            solve_result.err()
        );
        let solution = solve_result.unwrap();

        // --- Build Pod ---
        let original_signed_pods = HashMap::from([
            (pod_1.id(), Arc::new(pod_1.clone())),
            (pod_2.id(), Arc::new(pod_2.clone())),
            (pod_3.id(), Arc::new(pod_3.clone())),
        ]);
        let original_main_pods = HashMap::new();

        // Adjust params if needed (though default should be okay with 3 pods)
        // let build_params = middleware::Params { max_input_signed_pods: 4, ..Default::default() };

        let build_result = pod_building::build_main_pod_from_solution(
            &solution,
            &original_signed_pods,
            &original_main_pods,
            &params,            // Use original params or adjusted build_params
            &request_templates, // <-- Pass the request templates
        );
        assert!(
            build_result.is_ok(),
            "Pod building failed for nested predicates: {:?}",
            build_result.err()
        );
        let main_pod = build_result.unwrap();

        // --- Verify ---
        let verification_result = main_pod.pod.verify();
        assert!(
            verification_result.is_ok(),
            "MainPod verification failed for nested predicates: {:?}",
            verification_result.err()
        );

        // Check that the OuterP custom statement is public
        let expected_public_statement = Statement::Custom(
            outer_pred_ref.clone(),
            vec![
                WildcardValue::PodId(pod_1.id()), // Bound to req_p1
                WildcardValue::PodId(pod_2.id()), // Bound to req_p2
                WildcardValue::PodId(pod_3.id()), // Bound to req_p3
            ],
        );
        assert!(
            main_pod
                .public_statements
                .contains(&expected_public_statement),
            "Expected OuterP statement missing from public statements. Found: {:?}",
            main_pod.public_statements
        );

        // Check that the intermediate InnerP custom statement is NOT necessarily public
        let intermediate_inner_statement = Statement::Custom(
            inner_pred_ref.clone(),
            vec![
                WildcardValue::PodId(pod_1.id()), // Bound via OuterP.?pod1 -> InnerP.?p1
                WildcardValue::PodId(pod_2.id()), // Bound via OuterP.?pod2 -> InnerP.?p2
                WildcardValue::PodId(pod_3.id()), // Bound via OuterP.?pod3 -> InnerP.?p3
            ],
        );
        // Note: Exact check might be too strict depending on builder internals.
        // Check if it's present at all, and maybe assert it's NOT public if that's guaranteed.
        let found_inner_in_solution = solution
            .proof_chains
            .values()
            .flat_map(|chain| &chain.0) // Iterate through all ProofSteps in all chains
            .any(|step| step.output == intermediate_inner_statement);

        assert!(
            found_inner_in_solution,
            "Intermediate InnerP statement should exist as an output in solution.proof_chains"
        );
        assert!(
            !main_pod
                .public_statements
                .contains(&intermediate_inner_statement),
            "Intermediate InnerP statement should NOT be public"
        );

        println!("Nested custom predicate test successful!");
        Ok(())
    }
}
