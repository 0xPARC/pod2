pub mod error;
pub mod indexing;
pub mod pod_building;
pub mod solver;
pub mod test_utils;
pub mod translation;
pub mod types;
pub mod visualization;

pub use error::ProverError;

#[cfg(test)]
mod tests {
    use std::{
        collections::{HashMap, HashSet},
        sync::Arc,
    };

    use crate::{
        backends::plonky2::mock::signedpod::MockSigner,
        examples::zu_kyc_sign_pod_builders,
        middleware::{
            self, AnchoredKey, CustomPredicate, CustomPredicateBatch, CustomPredicateRef, Key,
            KeyOrWildcard, NativePredicate, PodId, Predicate, Statement, StatementTmpl,
            StatementTmplArg, ToFields, Value, Wildcard, WildcardValue,
        },
        prover::{
            pod_building,
            solver::{self, types::ExpectedType, SolverState},
            test_utils::*,
            types::{ConcreteValue, CustomDefinitions},
            visualization::generate_graphviz_dot,
        },
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
        let custom_definitions = CustomDefinitions::default();

        // 4. Call the solver to find a consistent assignment and proof steps.
        let solve_result = solver::solve(
            &request_templates,
            &initial_facts,
            &params,
            &custom_definitions,
        );
        assert!(
            solve_result.is_ok(),
            "Solver failed: {:?}",
            solve_result.err()
        );
        let solution = solve_result.unwrap();

        // 5. Prepare inputs for the pod building stage.
        let original_signed_pods =
            HashMap::from([(pod_a.id(), pod_a.clone()), (pod_b.id(), pod_b.clone())]);
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
        let solve_result = solver::solve(
            &request_templates,
            &initial_facts,
            &params,
            &custom_definitions,
        );
        assert!(
            solve_result.is_ok(),
            "Solver failed for nested predicates: {:?}",
            solve_result.err()
        );
        let solution = solve_result.unwrap();

        // --- Build Pod ---
        let original_signed_pods = HashMap::from([
            (pod_1.id(), pod_1.clone()),
            (pod_2.id(), pod_2.clone()),
            (pod_3.id(), pod_3.clone()),
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

    // Helper function to adjust statements with SELF pod IDs
    fn adjust_statement_for_self(stmt: &Statement, final_pod_id: PodId) -> Statement {
        match stmt {
            Statement::ValueOf(ak, val) => Statement::ValueOf(
                if ak.pod_id == middleware::SELF {
                    AnchoredKey::new(final_pod_id, ak.key.clone())
                } else {
                    ak.clone()
                },
                val.clone(),
            ),
            Statement::Equal(ak1, ak2) => Statement::Equal(
                if ak1.pod_id == middleware::SELF {
                    AnchoredKey::new(final_pod_id, ak1.key.clone())
                } else {
                    ak1.clone()
                },
                if ak2.pod_id == middleware::SELF {
                    AnchoredKey::new(final_pod_id, ak2.key.clone())
                } else {
                    ak2.clone()
                },
            ),
            Statement::NotEqual(ak1, ak2) => Statement::NotEqual(
                if ak1.pod_id == middleware::SELF {
                    AnchoredKey::new(final_pod_id, ak1.key.clone())
                } else {
                    ak1.clone()
                },
                if ak2.pod_id == middleware::SELF {
                    AnchoredKey::new(final_pod_id, ak2.key.clone())
                } else {
                    ak2.clone()
                },
            ),
            Statement::Gt(ak1, ak2) => Statement::Gt(
                if ak1.pod_id == middleware::SELF {
                    AnchoredKey::new(final_pod_id, ak1.key.clone())
                } else {
                    ak1.clone()
                },
                if ak2.pod_id == middleware::SELF {
                    AnchoredKey::new(final_pod_id, ak2.key.clone())
                } else {
                    ak2.clone()
                },
            ),
            Statement::Lt(ak1, ak2) => Statement::Lt(
                if ak1.pod_id == middleware::SELF {
                    AnchoredKey::new(final_pod_id, ak1.key.clone())
                } else {
                    ak1.clone()
                },
                if ak2.pod_id == middleware::SELF {
                    AnchoredKey::new(final_pod_id, ak2.key.clone())
                } else {
                    ak2.clone()
                },
            ),
            Statement::SumOf(ak1, ak2, ak3) => Statement::SumOf(
                if ak1.pod_id == middleware::SELF {
                    AnchoredKey::new(final_pod_id, ak1.key.clone())
                } else {
                    ak1.clone()
                },
                if ak2.pod_id == middleware::SELF {
                    AnchoredKey::new(final_pod_id, ak2.key.clone())
                } else {
                    ak2.clone()
                },
                if ak3.pod_id == middleware::SELF {
                    AnchoredKey::new(final_pod_id, ak3.key.clone())
                } else {
                    ak3.clone()
                },
            ),
            Statement::ProductOf(ak1, ak2, ak3) => Statement::ProductOf(
                if ak1.pod_id == middleware::SELF {
                    AnchoredKey::new(final_pod_id, ak1.key.clone())
                } else {
                    ak1.clone()
                },
                if ak2.pod_id == middleware::SELF {
                    AnchoredKey::new(final_pod_id, ak2.key.clone())
                } else {
                    ak2.clone()
                },
                if ak3.pod_id == middleware::SELF {
                    AnchoredKey::new(final_pod_id, ak3.key.clone())
                } else {
                    ak3.clone()
                },
            ),
            Statement::MaxOf(ak1, ak2, ak3) => Statement::MaxOf(
                if ak1.pod_id == middleware::SELF {
                    AnchoredKey::new(final_pod_id, ak1.key.clone())
                } else {
                    ak1.clone()
                },
                if ak2.pod_id == middleware::SELF {
                    AnchoredKey::new(final_pod_id, ak2.key.clone())
                } else {
                    ak2.clone()
                },
                if ak3.pod_id == middleware::SELF {
                    AnchoredKey::new(final_pod_id, ak3.key.clone())
                } else {
                    ak3.clone()
                },
            ),
            Statement::Contains(ak1, ak2, ak3) => Statement::Contains(
                if ak1.pod_id == middleware::SELF {
                    AnchoredKey::new(final_pod_id, ak1.key.clone())
                } else {
                    ak1.clone()
                },
                if ak2.pod_id == middleware::SELF {
                    AnchoredKey::new(final_pod_id, ak2.key.clone())
                } else {
                    ak2.clone()
                },
                if ak3.pod_id == middleware::SELF {
                    AnchoredKey::new(final_pod_id, ak3.key.clone())
                } else {
                    ak3.clone()
                },
            ),
            Statement::NotContains(ak1, ak2) => Statement::NotContains(
                if ak1.pod_id == middleware::SELF {
                    AnchoredKey::new(final_pod_id, ak1.key.clone())
                } else {
                    ak1.clone()
                },
                if ak2.pod_id == middleware::SELF {
                    AnchoredKey::new(final_pod_id, ak2.key.clone())
                } else {
                    ak2.clone()
                },
            ),
            // Add other statement variants if they use AnchoredKeys...
            // Custom statements need careful handling if their args can contain SELF
            Statement::Custom(pred_ref, args) => {
                // This assumes WildcardValue doesn't directly contain SELF PodId
                // If it could, this adjustment logic needs extension.
                Statement::Custom(pred_ref.clone(), args.clone())
            }
            Statement::None => Statement::None,
        }
    }

    #[test]
    fn test_prover_zukyc() -> Result<(), Box<dyn std::error::Error>> {
        let params = middleware::Params::default();

        // 1. Create mock input SignedPods
        let mut gov_signer = MockSigner { pk: "gov".into() };
        let mut pay_signer = MockSigner { pk: "pay".into() };
        let mut sanction_signer = MockSigner {
            pk: "sanction".into(),
        };

        let (gov_builder, pay_builder, sanction_builder) = zu_kyc_sign_pod_builders(&params);

        let gov_id_pod = gov_builder.sign(&mut gov_signer)?;
        let pay_stub_pod = pay_builder.sign(&mut pay_signer)?;
        let sanction_list_pod = sanction_builder.sign(&mut sanction_signer)?;

        // 2. Define constants needed in templates
        let now_minus_18y_val = Value::from(1169909388_i64);
        let now_minus_1y_val = Value::from(1706367566_i64);

        // 3. Define wildcards and keys for the request
        let wc_gov = wc("gov", 0);
        let wc_pay = wc("pay", 1);
        let wc_sanctions = wc("sanctions", 2);
        let wc_const = wc("const", 3);
        let wc_holder_18y = wc("SELF_HOLDER_18Y", 4);
        let wc_holder_1y = wc("SELF_HOLDER_1Y", 5);

        let id_num_key = key("idNumber");
        let dob_key = key("dateOfBirth");
        let ssn_key = key("socialSecurityNumber");
        let start_date_key = key("startDate");
        let sanction_list_key = key("sanctionList");
        // Add keys for constants
        let const_18y_key = key("const_18y");
        let const_1y_key = key("const_1y");

        // 4. Define the request templates using wildcards for constants
        let request_templates = vec![
            StatementTmpl {
                pred: Predicate::Native(NativePredicate::NotContains),
                args: vec![
                    StatementTmplArg::Key(
                        wc_sanctions.clone(),
                        KeyOrWildcard::Key(sanction_list_key.clone()),
                    ), // ?sanctions["sanctionList"]
                    StatementTmplArg::Key(wc_gov.clone(), KeyOrWildcard::Key(id_num_key.clone())), // ?gov["idNumber"]
                ],
            },
            StatementTmpl {
                pred: Predicate::Native(NativePredicate::Lt),
                args: vec![
                    StatementTmplArg::Key(wc_gov.clone(), KeyOrWildcard::Key(dob_key.clone())), // ?gov["dateOfBirth"]
                    StatementTmplArg::Key(
                        wc_const.clone(),
                        KeyOrWildcard::Key(const_18y_key.clone()),
                    ),
                ],
            },
            StatementTmpl {
                pred: Predicate::Native(NativePredicate::Equal), // Use Eq based on example
                args: vec![
                    StatementTmplArg::Key(
                        wc_pay.clone(),
                        KeyOrWildcard::Key(start_date_key.clone()),
                    ), // ?pay["startDate"]
                    StatementTmplArg::Key(
                        wc_const.clone(),
                        KeyOrWildcard::Key(const_1y_key.clone()),
                    ),
                ],
            },
            StatementTmpl {
                pred: Predicate::Native(NativePredicate::Equal),
                args: vec![
                    StatementTmplArg::Key(wc_gov.clone(), KeyOrWildcard::Key(ssn_key.clone())), // ?gov["socialSecurityNumber"]
                    StatementTmplArg::Key(wc_pay.clone(), KeyOrWildcard::Key(ssn_key.clone())), // ?pay["socialSecurityNumber"]
                ],
            },
            StatementTmpl {
                pred: Predicate::Native(NativePredicate::ValueOf),
                args: vec![
                    StatementTmplArg::Key(
                        wc_holder_18y.clone(),
                        KeyOrWildcard::Key(const_18y_key.clone()),
                    ),
                    StatementTmplArg::Literal(now_minus_18y_val.clone()),
                ],
            },
            StatementTmpl {
                pred: Predicate::Native(NativePredicate::ValueOf),
                args: vec![
                    StatementTmplArg::Key(
                        wc_holder_1y.clone(), // Use the distinct holder wildcard
                        KeyOrWildcard::Key(const_1y_key.clone()),
                    ),
                    StatementTmplArg::Literal(now_minus_1y_val.clone()),
                ],
            },
        ];

        // 5. Prepare inputs for the constraint solver.
        // Only include facts from the real signed pods.
        let initial_facts: Vec<(PodId, Statement)> = gov_id_pod
            .pod
            .pub_statements()
            .into_iter()
            .map(|stmt| (gov_id_pod.id(), stmt))
            .chain(
                pay_stub_pod
                    .pod
                    .pub_statements()
                    .into_iter()
                    .map(|stmt| (pay_stub_pod.id(), stmt)),
            )
            .chain(
                sanction_list_pod
                    .pod
                    .pub_statements()
                    .into_iter()
                    .map(|stmt| (sanction_list_pod.id(), stmt)),
            )
            .collect();

        let custom_definitions = CustomDefinitions::default();

        // 6. Call the solver.
        // Pass initial_facts and params directly
        let solve_result = solver::solve(
            &request_templates,
            &initial_facts, // Use the list including SELF facts
            &params,
            &custom_definitions,
        );
        assert!(
            solve_result.is_ok(),
            "Solver failed for ZuKYC: {:?}",
            solve_result.err()
        );
        let solution = solve_result.unwrap();

        // Check bindings (optional but helpful)
        assert_eq!(
            solution.bindings.get(&wc_gov),
            Some(&ConcreteValue::Pod(gov_id_pod.id()))
        );
        assert_eq!(
            solution.bindings.get(&wc_pay),
            Some(&ConcreteValue::Pod(pay_stub_pod.id()))
        );
        assert_eq!(
            solution.bindings.get(&wc_sanctions),
            Some(&ConcreteValue::Pod(sanction_list_pod.id()))
        );
        // Check constant bindings
        // assert_eq!(
        //     solution.bindings.get(&wc_18y),
        //     Some(&ConcreteValue::Val(now_minus_18y_val.clone()))
        // );
        // assert_eq!(
        //     solution.bindings.get(&wc_1y),
        //     Some(&ConcreteValue::Val(now_minus_1y_val.clone()))
        // );

        // 7. Prepare inputs for pod building.
        let original_signed_pods = HashMap::from([
            (gov_id_pod.id(), gov_id_pod.clone()),
            (pay_stub_pod.id(), pay_stub_pod.clone()),
            (sanction_list_pod.id(), sanction_list_pod.clone()),
        ]);
        let original_main_pods = HashMap::new(); // No input main pods

        // 8. Call pod building.
        let build_result = pod_building::build_main_pod_from_solution(
            &solution,
            &original_signed_pods,
            &original_main_pods,
            &params,
            &request_templates,
        );
        assert!(
            build_result.is_ok(),
            "Pod building failed for ZuKYC: {:?}",
            build_result.err()
        );
        let main_pod = build_result.unwrap();

        // 9. Verify the generated MainPod.
        let verification_result = main_pod.pod.verify();
        assert!(
            verification_result.is_ok(),
            "MainPod verification failed for ZuKYC: {:?}",
            verification_result.err()
        );

        // 10. Check that the generated MainPod contains the expected public statements.
        // Re-generate the target statements using the solution bindings.
        // Need to manually create the SELF statements for generation check
        let mut final_domains = solution
            .bindings
            .iter()
            .map(|(wc, cv)| {
                (
                    // Determine ExpectedType based on ConcreteValue variant
                    wc.clone(),
                    (
                        HashSet::from([cv.clone()]),
                        match cv {
                            ConcreteValue::Pod(_) => ExpectedType::Pod,
                            ConcreteValue::Key(_) => ExpectedType::Key,
                            ConcreteValue::Val(_) => ExpectedType::Val,
                        },
                    ),
                )
            })
            .collect::<HashMap<_, _>>();

        // Add SELF pod wildcard mapping for generation
        // These map the dummy SELF holder wildcards to the actual SELF PodId
        final_domains.insert(
            Wildcard::new("SELF_HOLDER_18Y".to_string(), 100),
            (
                HashSet::from([ConcreteValue::Pod(middleware::SELF)]),
                ExpectedType::Pod,
            ),
        );
        final_domains.insert(
            Wildcard::new("SELF_HOLDER_1Y".to_string(), 101),
            (
                HashSet::from([ConcreteValue::Pod(middleware::SELF)]),
                ExpectedType::Pod,
            ),
        );

        let final_state_for_generation = SolverState {
            params: params.clone(),
            domains: final_domains,
            constraints: Vec::new(),
            proof_chains: HashMap::new(),
            scope: HashSet::new(),
        };

        let mut expected_public_statements = HashSet::new();
        for tmpl in &request_templates {
            // Use original templates for verification check
            // Use check_templates here <-- No, use original templates
            match crate::prover::solver::try_generate_concrete_candidate_and_bindings(
            tmpl,
            &final_state_for_generation,
        ) {
            Ok(Some((target_stmt, _))) => {
                expected_public_statements.insert(target_stmt);
            }
            Ok(None) => panic!("Failed to generate concrete statement (None) from template {:?} during verification check", tmpl),
            Err(e) => panic!("Failed to generate concrete statement (Err {:?}) from template {:?} during verification check", e, tmpl),
        }
        }

        // --- Adjust expected statements for SELF --- START ---
        let main_pod_id = main_pod.id();
        let adjusted_expected_public_statements: HashSet<_> = expected_public_statements
            .iter()
            .map(|stmt| adjust_statement_for_self(stmt, main_pod_id))
            .collect();
        // --- Adjust expected statements for SELF --- END ---

        // Add the implicit _type statement
        assert_eq!(
            main_pod.public_statements.len(),
            adjusted_expected_public_statements.len() + 1, // to account for the _type statement
            "Mismatch in number of public statements.\nExpected (adjusted): {:#?}\n   Found: {:#?}",
            adjusted_expected_public_statements, // Use adjusted set
            main_pod.public_statements
        );

        for stmt in &adjusted_expected_public_statements {
            // Use the adjusted set
            // Exclude the ValueOf statements for constants from the final public check
            // (This exclusion might be removable now, depending on how strictly we want to check)
            if let Statement::ValueOf(ak, _) = stmt {
                if ak.pod_id == main_pod_id // Check against the actual pod ID
                    && (ak.key == const_18y_key || ak.key == const_1y_key)
                {
                    continue;
                }
            }
            assert!(
                main_pod.public_statements.contains(stmt),
                "Expected public statement missing: {:?}",
                stmt
            );
        }

        println!("ZuKYC end-to-end test successful!");
        println!("Generated MainPod: {}", main_pod);

        println!("Solution:\n{}", generate_graphviz_dot(&solution));

        Ok(())
    }
}
