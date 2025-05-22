/// The prover module handles proof generation and verification for pod statements.
/// It includes components for solving constraints, building pods, and managing proof chains.
pub mod error;
pub mod indexing;
pub mod pod_building;
pub mod runtime;
pub mod solver;
pub mod test_utils;
pub mod translation;
pub mod types;
pub mod visualization;

use std::{collections::HashMap, sync::Arc};

pub use error::ProverError;
use types::CustomDefinitions;

use crate::middleware::{
    CustomPredicate, CustomPredicateBatch, CustomPredicateRef, Params, Pod, PodId, Predicate,
    Statement, ToFields, F,
};

pub fn facts_from_pods(pods: &[&Box<dyn Pod>]) -> Vec<(PodId, Statement)> {
    pods.iter()
        .flat_map(|pod| {
            let statements = pod.pub_statements();
            statements
                .iter()
                .map(|stmt| (pod.id(), stmt.clone()))
                .collect::<Vec<(PodId, Statement)>>()
        })
        .collect()
}

pub fn custom_definitions_from_batches(
    batches: &[Arc<CustomPredicateBatch>],
    params: &Params,
) -> CustomDefinitions {
    HashMap::from_iter(batches.iter().flat_map(|batch| {
        batch
            .predicates
            .iter()
            .enumerate()
            .map(|(index, pred)| {
                let key = Predicate::Custom(CustomPredicateRef {
                    batch: batch.clone(),
                    index,
                })
                .to_fields(params);
                (key, (pred.clone(), batch.clone()))
            })
            .collect::<Vec<(Vec<F>, (CustomPredicate, Arc<CustomPredicateBatch>))>>()
    }))
}
#[cfg(test)]
mod tests {
    use std::{
        collections::{HashMap, HashSet},
        sync::Arc,
    };

    use hex::ToHex;

    use crate::{
        backends::plonky2::mock::signedpod::MockSigner,
        examples::{eth_friend_signed_pod_builder, zu_kyc_sign_pod_builders},
        lang::{self, parse},
        middleware::{
            self, AnchoredKey, CustomPredicate, CustomPredicateBatch, CustomPredicateRef, Key,
            KeyOrWildcard, NativePredicate, PodId, Predicate, Statement, StatementTmpl,
            StatementTmplArg, ToFields, Value, Wildcard, WildcardValue, KEY_SIGNER,
        },
        prover::{
            custom_definitions_from_batches, facts_from_pods, pod_building,
            solver::{
                self, try_generate_concrete_candidate_and_bindings,
                types::{ExpectedType, GlobalContext},
                SolverState,
            },
            test_utils::*,
            types::{ConcreteValue, CustomDefinitions},
            visualization::{generate_graphviz_dot, generate_mermaid_markdown},
        },
    };

    /// Tests a simple end-to-end proof involving a less-than comparison between two pods.
    /// Creates two pods with numeric values and proves that one value is less than the other.
    #[test]
    fn test_prover_end_to_end_simple_lt() -> Result<(), Box<dyn std::error::Error>> {
        let _ = env_logger::try_init(); // Initialize logger
        let params = middleware::Params::default();

        // Create input SignedPods with test data
        let pod_a = create_test_signed_pod(&params, &[("foo", Value::from(20))], "signer_a")?;
        let pod_b = create_test_signed_pod(&params, &[("bar", Value::from(10))], "signer_b")?;

        // Define request template: Lt(?y["bar"], ?x["foo"])
        let wc_x = Wildcard::new("x".to_string(), 0);
        let wc_y = Wildcard::new("y".to_string(), 1);
        let key_foo = Key::new("foo".to_string());
        let key_bar = Key::new("bar".to_string());

        let request_templates = vec![StatementTmpl {
            pred: middleware::Predicate::Native(NativePredicate::Lt),
            args: vec![
                StatementTmplArg::Key(wc_y.clone(), KeyOrWildcard::Key(key_bar.clone())),
                StatementTmplArg::Key(wc_x.clone(), KeyOrWildcard::Key(key_foo.clone())),
            ],
        }];

        // Prepare solver inputs from pod statements
        let initial_facts = vec![
            (pod_a.id(), pod_a.get_statement("foo").unwrap()),
            (pod_b.id(), pod_b.get_statement("bar").unwrap()),
        ];
        let custom_definitions = CustomDefinitions::default();

        // Find consistent assignment and generate proof
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

        // Build final MainPod from solution
        let original_signed_pods = HashMap::from([(pod_a.id(), &pod_a), (pod_b.id(), &pod_b)]);
        let original_main_pods = HashMap::new();

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

        // Verify MainPod integrity
        let verification_result = main_pod.pod.verify();
        assert!(
            verification_result.is_ok(),
            "MainPod verification failed: {:?}",
            verification_result.err()
        );

        // Verify expected public statements
        let expected_public_statement = Statement::Lt(
            AnchoredKey::new(pod_b.id(), key_bar),
            AnchoredKey::new(pod_a.id(), key_foo),
        );
        assert_eq!(
            main_pod.public_statements.len(),
            2,
            "Expected exactly two public statements (Lt and ValueOf for _type)"
        );
        assert!(
            main_pod
                .public_statements
                .contains(&expected_public_statement),
            "Expected Lt statement missing from public statements"
        );

        println!("End-to-end test successful!");
        println!("Generated MainPod: {}", main_pod);

        Ok(())
    }

    /// Tests nested custom predicates with complex relationships between multiple pods.
    /// Demonstrates how to define and use custom predicates that combine multiple native predicates
    /// and reference other custom predicates.
    #[test]
    fn test_prover_nested_custom_predicates() -> Result<(), Box<dyn std::error::Error>> {
        let _ = env_logger::try_init(); // Initialize logger
        let params = middleware::Params::default();

        // Define InnerP predicate: checks relationships between pods a, b, c, d
        // - Lt(?p1["val_b"], ?p2["val_a"])
        // - Equal(?p1["key_c"], ?p3["key_d"])
        let wc_p1_inner = wc("p1_inner", 0);
        let wc_p2_inner = wc("p2_inner", 1);
        let wc_p3_inner = wc("p3_inner", 2);
        let key_val_a = key("val_a");
        let key_val_b = key("val_b");
        let key_key_c = key("key_c");
        let key_key_d = key("key_d");

        let inner_tmpl_lt = StatementTmpl {
            pred: Predicate::Native(NativePredicate::Lt),
            args: vec![
                StatementTmplArg::Key(wc_p2_inner.clone(), KeyOrWildcard::Key(key_val_b.clone())),
                StatementTmplArg::Key(wc_p1_inner.clone(), KeyOrWildcard::Key(key_val_a.clone())),
            ],
        };
        let inner_tmpl_eq = StatementTmpl {
            pred: Predicate::Native(NativePredicate::Equal),
            args: vec![
                StatementTmplArg::Key(wc_p1_inner.clone(), KeyOrWildcard::Key(key_key_c.clone())),
                StatementTmplArg::Key(wc_p3_inner.clone(), KeyOrWildcard::Key(key_key_d.clone())),
            ],
        };
        let inner_pred_def = CustomPredicate {
            name: "InnerP_Combined".to_string(),
            args_len: 3,
            statements: vec![inner_tmpl_lt, inner_tmpl_eq],
            conjunction: true,
        };

        // Define OuterP predicate: combines InnerP with additional Lt check
        // - InnerP(?pod1, ?pod2, ?pod3)
        // - Lt(?pod2["val_m"], ?pod3["val_n"])
        let wc_pod1_outer = wc("pod1_outer", 0);
        let wc_pod2_outer = wc("pod2_outer", 1);
        let wc_pod3_outer = wc("pod3_outer", 2);
        let key_val_m = key("val_m");
        let key_val_n = key("val_n");

        let outer_tmpl_inner = StatementTmpl {
            pred: Predicate::BatchSelf(0),
            args: vec![
                StatementTmplArg::WildcardLiteral(wc_pod1_outer.clone()),
                StatementTmplArg::WildcardLiteral(wc_pod2_outer.clone()),
                StatementTmplArg::WildcardLiteral(wc_pod3_outer.clone()),
            ],
        };
        let outer_tmpl_lt = StatementTmpl {
            pred: Predicate::Native(NativePredicate::Lt),
            args: vec![
                StatementTmplArg::Key(wc_pod2_outer.clone(), KeyOrWildcard::Key(key_val_m.clone())),
                StatementTmplArg::Key(wc_pod3_outer.clone(), KeyOrWildcard::Key(key_val_n.clone())),
            ],
        };
        let outer_pred_def = CustomPredicate {
            name: "OuterP_Combined".to_string(),
            args_len: 3,
            statements: vec![outer_tmpl_inner, outer_tmpl_lt],
            conjunction: true,
        };

        // Create predicate batch and references
        // InnerP is at index 0, OuterP at index 1
        let custom_batch = Arc::new(CustomPredicateBatch {
            name: "NestedBatchCombined".to_string(),
            predicates: vec![inner_pred_def.clone(), outer_pred_def.clone()],
        });
        let inner_pred_ref = CustomPredicateRef {
            batch: custom_batch.clone(),
            index: 0,
        };
        let outer_pred_ref = CustomPredicateRef {
            batch: custom_batch.clone(),
            index: 1,
        };

        // Create test pods with required data:
        // pod_1: val_a=100, key_c="same"
        // pod_2: val_b=50, val_m=10
        // pod_3: key_d="same", val_n=20
        let pod_1 = create_test_signed_pod(
            &params,
            &[("val_a", val(100)), ("key_c", Value::from("same"))],
            "signer_1",
        )?;
        let pod_2 = create_test_signed_pod(
            &params,
            &[("val_b", val(50)), ("val_m", val(10))],
            "signer_2",
        )?;
        let pod_3 = create_test_signed_pod(
            &params,
            &[("key_d", Value::from("same")), ("val_n", val(20))],
            "signer_3",
        )?;

        // Extract initial facts from pods
        let initial_facts = vec![
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

        // Register custom predicates
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

        // Define request template using OuterP
        let wc_req_p1 = wc("req_p1", 10);
        let wc_req_p2 = wc("req_p2", 11);
        let wc_req_p3 = wc("req_p3", 12);

        let request_templates = vec![StatementTmpl {
            pred: Predicate::Custom(outer_pred_ref.clone()),
            args: vec![
                StatementTmplArg::WildcardLiteral(wc_req_p1.clone()),
                StatementTmplArg::WildcardLiteral(wc_req_p2.clone()),
                StatementTmplArg::WildcardLiteral(wc_req_p3.clone()),
            ],
        }];

        // Find solution and generate proof
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

        // Build MainPod from solution
        let original_signed_pods = HashMap::from([
            (pod_1.id(), &pod_1),
            (pod_2.id(), &pod_2),
            (pod_3.id(), &pod_3),
        ]);
        let original_main_pods = HashMap::new();

        let build_result = pod_building::build_main_pod_from_solution(
            &solution,
            &original_signed_pods,
            &original_main_pods,
            &params,
            &request_templates,
        );
        assert!(
            build_result.is_ok(),
            "Pod building failed for nested predicates: {:?}",
            build_result.err()
        );
        let main_pod = build_result.unwrap();

        // Verify MainPod integrity
        let verification_result = main_pod.pod.verify();
        assert!(
            verification_result.is_ok(),
            "MainPod verification failed for nested predicates: {:?}",
            verification_result.err()
        );

        // Verify that OuterP statement is public
        let expected_public_statement = Statement::Custom(
            outer_pred_ref.clone(),
            vec![
                WildcardValue::PodId(pod_1.id()),
                WildcardValue::PodId(pod_2.id()),
                WildcardValue::PodId(pod_3.id()),
            ],
        );
        assert!(
            main_pod
                .public_statements
                .contains(&expected_public_statement),
            "Expected OuterP statement missing from public statements. Found: {:?}",
            main_pod.public_statements
        );

        // Verify that InnerP statement exists in proof chain but is not public
        let intermediate_inner_statement = Statement::Custom(
            inner_pred_ref.clone(),
            vec![
                WildcardValue::PodId(pod_1.id()),
                WildcardValue::PodId(pod_2.id()),
                WildcardValue::PodId(pod_3.id()),
            ],
        );

        let found_inner_in_solution = solution
            .proof_chains
            .values()
            .flat_map(|chain| &chain.0)
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
            // Statement::Gt(ak1, ak2) => Statement::Gt(
            //     if ak1.pod_id == middleware::SELF {
            //         AnchoredKey::new(final_pod_id, ak1.key.clone())
            //     } else {
            //         ak1.clone()
            //     },
            //     if ak2.pod_id == middleware::SELF {
            //         AnchoredKey::new(final_pod_id, ak2.key.clone())
            //     } else {
            //         ak2.clone()
            //     },
            // ),
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
            Statement::LtEq(ak1, ak2) => Statement::LtEq(
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
            Statement::HashOf(ak1, ak2, ak3) => Statement::HashOf(
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
    /// Tests the ZuKYC example with manually constructed request templates.
    /// Demonstrates a real-world use case involving multiple pods and complex relationships
    /// between their values.
    ///
    /// The test verifies:
    /// 1. A person's ID is not in a sanctions list
    /// 2. The person is at least 18 years old (based on date of birth)
    /// 3. The employment started within the last year
    /// 4. The social security numbers match between government and employer records
    #[test]
    fn test_prover_zukyc() -> Result<(), Box<dyn std::error::Error>> {
        let params = middleware::Params::default();

        // Create mock signers for each authority
        let mut gov_signer = MockSigner { pk: "gov".into() };
        let mut pay_signer = MockSigner { pk: "pay".into() };
        let mut sanction_signer = MockSigner {
            pk: "sanction".into(),
        };

        // Create pods with required data using predefined builders
        let (gov_builder, pay_builder, sanction_builder) = zu_kyc_sign_pod_builders(&params);
        let gov_id_pod = gov_builder.sign(&mut gov_signer)?;
        let pay_stub_pod = pay_builder.sign(&mut pay_signer)?;
        let sanction_list_pod = sanction_builder.sign(&mut sanction_signer)?;

        // Define constants for age verification
        let now_minus_18y_val = Value::from(1169909388_i64); // Current time - 18 years
        let now_minus_1y_val = Value::from(1706367566_i64); // Current time - 1 year

        // Define wildcards for each pod and constant holder
        let wc_gov = wc("gov", 0);
        let wc_pay = wc("pay", 1);
        let wc_sanctions = wc("sanctions", 2);
        let wc_const = wc("const", 3);
        let wc_holder_18y = wc("SELF_HOLDER_18Y", 4);
        let wc_holder_1y = wc("SELF_HOLDER_1Y", 5);

        // Define keys used in the verification
        let id_num_key = key("idNumber");
        let dob_key = key("dateOfBirth");
        let ssn_key = key("socialSecurityNumber");
        let start_date_key = key("startDate");
        let sanction_list_key = key("sanctionList");
        let const_18y_key = key("const_18y");
        let const_1y_key = key("const_1y");

        // Define request templates for each verification step
        let request_templates = vec![
            // Check ID not in sanctions list
            StatementTmpl {
                pred: Predicate::Native(NativePredicate::NotContains),
                args: vec![
                    StatementTmplArg::Key(
                        wc_sanctions.clone(),
                        KeyOrWildcard::Key(sanction_list_key.clone()),
                    ),
                    StatementTmplArg::Key(wc_gov.clone(), KeyOrWildcard::Key(id_num_key.clone())),
                ],
            },
            // Verify age >= 18 years
            StatementTmpl {
                pred: Predicate::Native(NativePredicate::Lt),
                args: vec![
                    StatementTmplArg::Key(wc_gov.clone(), KeyOrWildcard::Key(dob_key.clone())),
                    StatementTmplArg::Key(
                        wc_const.clone(),
                        KeyOrWildcard::Key(const_18y_key.clone()),
                    ),
                ],
            },
            // Verify employment started within last year
            StatementTmpl {
                pred: Predicate::Native(NativePredicate::Equal),
                args: vec![
                    StatementTmplArg::Key(
                        wc_pay.clone(),
                        KeyOrWildcard::Key(start_date_key.clone()),
                    ),
                    StatementTmplArg::Key(
                        wc_const.clone(),
                        KeyOrWildcard::Key(const_1y_key.clone()),
                    ),
                ],
            },
            // Verify SSN matches between records
            StatementTmpl {
                pred: Predicate::Native(NativePredicate::Equal),
                args: vec![
                    StatementTmplArg::Key(wc_gov.clone(), KeyOrWildcard::Key(ssn_key.clone())),
                    StatementTmplArg::Key(wc_pay.clone(), KeyOrWildcard::Key(ssn_key.clone())),
                ],
            },
            // Define constant for 18-year check
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
            // Define constant for 1-year check
            StatementTmpl {
                pred: Predicate::Native(NativePredicate::ValueOf),
                args: vec![
                    StatementTmplArg::Key(
                        wc_holder_1y.clone(),
                        KeyOrWildcard::Key(const_1y_key.clone()),
                    ),
                    StatementTmplArg::Literal(now_minus_1y_val.clone()),
                ],
            },
        ];

        // Extract initial facts from all pods
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

        // Find solution and generate proof
        let solve_result = solver::solve(
            &request_templates,
            &initial_facts,
            &params,
            &custom_definitions,
        );
        assert!(
            solve_result.is_ok(),
            "Solver failed for ZuKYC: {:?}",
            solve_result.err()
        );
        let solution = solve_result.unwrap();

        // Build MainPod from solution
        let original_signed_pods = HashMap::from([
            (gov_id_pod.id(), &gov_id_pod),
            (pay_stub_pod.id(), &pay_stub_pod),
            (sanction_list_pod.id(), &sanction_list_pod),
        ]);
        let original_main_pods = HashMap::new();

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

        // Verify MainPod integrity
        let verification_result = main_pod.pod.verify();
        assert!(
            verification_result.is_ok(),
            "MainPod verification failed for ZuKYC: {:?}",
            verification_result.err()
        );

        // Prepare expected statements for verification
        let mut final_domains = solution
            .bindings
            .iter()
            .map(|(wc, cv)| {
                (
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

        // Add SELF pod mappings for constant holders
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

        // Generate expected statements from templates
        let final_state_for_generation = SolverState {
            domains: final_domains,
            proof_chains: HashMap::new(),
            scope: HashSet::new(),
            memoization_cache: HashMap::new(),
            active_custom_calls: HashSet::new(),
            local_potential_constant_info: Vec::new(),
        };

        // Create a dummy ResolveScope for the call to try_generate_concrete_candidate_and_bindings
        let dummy_resolve_scope_for_zukyc = crate::prover::solver::types::ResolveScope {
            templates_to_resolve: &[],
            constraints: Vec::new(),
            search_targets: None,
            wildcard_interpretation_map: HashMap::new(),
            public_arg_bindings: None,
            current_depth: 0,
            parent_custom_call_key: None,
        };

        // Construct GlobalContext for the test call
        let solver_indexes_for_test =
            crate::prover::indexing::ProverIndexes::build(params.clone(), &initial_facts);
        let potential_constants_for_test: Vec<(Wildcard, Key, Value)> = Vec::new();
        let global_context_for_test = GlobalContext {
            indexes: &solver_indexes_for_test,
            custom_definitions: &custom_definitions,
            params: &params,
            potential_constant_info: &potential_constants_for_test,
        };

        let mut expected_public_statements = HashSet::new();
        for tmpl in &request_templates {
            match try_generate_concrete_candidate_and_bindings(tmpl, &final_state_for_generation, &dummy_resolve_scope_for_zukyc, &global_context_for_test) {
                Ok(Some((target_stmt, _))) => {
                    expected_public_statements.insert(target_stmt);
                }
                Ok(None) => panic!("Failed to generate concrete statement (None) from template {:?} during verification check", tmpl),
                Err(e) => panic!("Failed to generate concrete statement (Err {:?}) from template {:?} during verification check", e, tmpl),
            }
        }

        // Adjust statements to use actual pod ID instead of SELF
        let main_pod_id = main_pod.id();
        let adjusted_expected_public_statements: HashSet<_> = expected_public_statements
            .iter()
            .map(|stmt| adjust_statement_for_self(stmt, main_pod_id))
            .collect();

        // Verify all expected statements are present
        assert_eq!(
            main_pod.public_statements.len(),
            adjusted_expected_public_statements.len() + 1,
            "Mismatch in number of public statements.\nExpected (adjusted): {:#?}\n   Found: {:#?}",
            adjusted_expected_public_statements,
            main_pod.public_statements
        );

        for stmt in &adjusted_expected_public_statements {
            // Skip constant value statements in final check
            if let Statement::ValueOf(ak, _) = stmt {
                if ak.pod_id == main_pod_id {
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

    /// Tests the ZuKYC example with request templates parsed from podlog.
    /// Similar to test_prover_zukyc but uses the podlog parser to create templates,
    /// demonstrating the integration with the parsing system.
    #[test]
    fn test_prover_zukyc_from_podlog() -> Result<(), Box<dyn std::error::Error>> {
        let params = middleware::Params::default();

        // Create mock input SignedPods
        let mut gov_signer = MockSigner { pk: "gov".into() };
        let mut pay_signer = MockSigner { pk: "pay".into() };
        let mut sanction_signer = MockSigner {
            pk: "sanction".into(),
        };

        let (gov_builder, pay_builder, sanction_builder) = zu_kyc_sign_pod_builders(&params);

        let gov_id_pod = gov_builder.sign(&mut gov_signer)?;
        let pay_stub_pod = pay_builder.sign(&mut pay_signer)?;
        let sanction_list_pod = sanction_builder.sign(&mut sanction_signer)?;

        let input = r#"
        REQUEST(
            NotContains(?sanctions["sanctionList"], ?gov["idNumber"])
            Lt(?gov["dateOfBirth"], ?SELF_HOLDER_18Y["const_18y"])
            Equal(?pay["startDate"], ?SELF_HOLDER_1Y["const_1y"])
            Equal(?gov["socialSecurityNumber"], ?pay["socialSecurityNumber"])
            ValueOf(?SELF_HOLDER_18Y["const_18y"], 1169909388)
            ValueOf(?SELF_HOLDER_1Y["const_1y"], 1706367566)
        )
    "#;

        let processed = parse(input, &params).unwrap();
        let request_templates = processed.request_templates;

        // Prepare inputs for the constraint solver.
        // Only include facts from the real signed pods.
        let initial_facts: Vec<(PodId, Statement)> =
            facts_from_pods(&[&gov_id_pod.pod, &pay_stub_pod.pod, &sanction_list_pod.pod]);

        let custom_definitions = CustomDefinitions::default();

        // Call the solver.
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

        // Build MainPod from solution
        let original_signed_pods = HashMap::from([
            (gov_id_pod.id(), &gov_id_pod),
            (pay_stub_pod.id(), &pay_stub_pod),
            (sanction_list_pod.id(), &sanction_list_pod),
        ]);
        let original_main_pods = HashMap::new(); // No input main pods

        // Call pod building.
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

        // Verify the generated MainPod.
        let verification_result = main_pod.pod.verify();
        assert!(
            verification_result.is_ok(),
            "MainPod verification failed for ZuKYC: {:?}",
            verification_result.err()
        );
        /*
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
                    domains: final_domains,
                    proof_chains: HashMap::new(),
                    scope: HashSet::new(),
                    memoization_cache: HashMap::new(),
                    active_custom_calls: HashSet::new(),
                    local_potential_constant_info: Vec::new(),
                };

                // Create a dummy ResolveScope for the call to try_generate_concrete_candidate_and_bindings
                let dummy_resolve_scope_for_zukyc_podlog = crate::prover::solver::types::ResolveScope {
                    templates_to_resolve: &[], // Not strictly needed for this generation check
                    constraints: Vec::new(),
                    search_targets: None,
                    wildcard_interpretation_map: HashMap::new(), // Assuming global interpretation for this test helper
                    public_arg_bindings: None,
                    current_depth: 0,
                    parent_custom_call_key: None,
                };

                // Construct GlobalContext for the test call
                let solver_indexes_for_test_podlog =
                    crate::prover::indexing::ProverIndexes::build(params.clone(), &initial_facts);
                let potential_constants_for_test_podlog: Vec<(Wildcard, Key, Value)> = Vec::new();
                let global_context_for_test_podlog = GlobalContext {
                    indexes: &solver_indexes_for_test_podlog,
                    custom_definitions: &custom_definitions,
                    params: &params,
                    potential_constant_info: &potential_constants_for_test_podlog,
                };

                let mut expected_public_statements = HashSet::new();
                for tmpl in &request_templates {
                    // Use original templates for verification check
                    match try_generate_concrete_candidate_and_bindings(
                    tmpl,
                    &final_state_for_generation,
                    &dummy_resolve_scope_for_zukyc_podlog,
                    &global_context_for_test_podlog, // Pass global_context_for_test_podlog
                ) {
                    Ok(Some((target_stmt, _))) => {
                        expected_public_statements.insert(target_stmt);
                    }
                    Ok(None) => panic!("Failed to generate concrete statement (None) from template {:?} during verification check", tmpl),
                    Err(e) => panic!("Failed to generate concrete statement (Err {:?}) from template {:?} during verification check", e, tmpl),
                }
                }

                // Adjust expected statements for SELF
                let main_pod_id = main_pod.id();
                let adjusted_expected_public_statements: HashSet<_> = expected_public_statements
                    .iter()
                    .map(|stmt| adjust_statement_for_self(stmt, main_pod_id))
                    .collect();

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
                        if ak.pod_id == main_pod_id
                        // Check against the actual pod ID
                        //       && (ak.key == const_18y_key || ak.key == const_1y_key)
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

                let sol = solver::solve(
                    &request_templates,
                    &facts_from_pods(&[&main_pod.pod]),
                    &params,
                    &custom_definitions,
                );

                assert!(
                    sol.is_ok(),
                    "Pod building failed for ZuKYC: {:?}",
                    sol.err()
                );
        */
        println!("ZuKYC end-to-end test successful!");
        println!("Generated MainPod: {}", main_pod);

        println!("Solution:\n{}", generate_mermaid_markdown(&solution));

        Ok(())
    }

    #[test]
    fn test_prover_custom() -> Result<(), Box<dyn std::error::Error>> {
        env_logger::init();
        let params = middleware::Params {
            max_input_signed_pods: 3,
            max_input_main_pods: 3,
            max_statements: 31,
            max_signed_pod_values: 8,
            max_public_statements: 10,
            max_statement_args: 6,
            max_operation_args: 5,
            max_custom_predicate_arity: 5,
            max_custom_batch_size: 5,
            max_custom_predicate_wildcards: 12,
            ..Default::default()
        };

        let mut alice = MockSigner { pk: "Alice".into() };
        let bob = MockSigner { pk: "Bob".into() };
        let mut charlie = MockSigner {
            pk: "Charlie".into(),
        };

        let input = format!(
            r#"
            eth_friend(src_ori, src_key, dst_ori, dst_key, private: attestation_pod) = AND(
                // ValueOf(?attestation_pod["__type__"], "MockSigned")
                Equal(?attestation_pod["_signer"], ?src_ori[?src_key])
                Equal(?attestation_pod["attestation"], ?dst_ori[?dst_key])
            )

            eth_dos_distance_base(src_ori, src_key, dst_ori, dst_key, distance_ori, distance_key) = AND(
                Equal(?src_ori[?src_key], ?dst_ori[?dst_key])
                ValueOf(?distance_ori[?distance_key], 0)
            )

            eth_dos_distance_ind(src_ori, src_key, dst_ori, dst_key, distance_ori, distance_key,
              private: one_ori, one_key, shorter_distance_ori, shorter_distance_key, intermed_ori, intermed_key) = AND(
                eth_friend(?intermed_ori, ?intermed_key, ?dst_ori, ?dst_key)
                ValueOf(?one_ori[?one_key], 1)
                eth_dos_distance(?src_ori, ?src_key, ?intermed_ori, ?intermed_key, ?shorter_distance_ori, ?shorter_distance_key)
                SumOf(?distance_ori[?distance_key], ?shorter_distance_ori[?shorter_distance_key], ?one_ori[?one_key])
            )

            eth_dos_distance(src_ori, src_key, dst_ori, dst_key, distance_ori, distance_key) = OR(
                eth_dos_distance_base(?src_ori, ?src_key, ?dst_ori, ?dst_key, ?distance_ori, ?distance_key)
             //   eth_dos_distance_ind(?src_ori, ?src_key, ?dst_ori, ?dst_key, ?distance_ori, ?distance_key)
            )

            REQUEST(
                ValueOf(?CONST["alice"], 0x{})
                ValueOf(?CONST["bob"], 0x{})
                ValueOf(?CONST["charlie"], 0x{})
                ValueOf(?CONST["zero"], 0)
                ValueOf(?CONST["one"], 1)
            //    ValueOf(?CONST["two"], 2)
            //    eth_friend(?CONST, "alice", ?CONST, "charlie")
            //    eth_friend(?CONST, "charlie", ?CONST, "bob")
                eth_dos_distance(?CONST, "alice", ?CONST, "charlie", ?CONST, ?distance_key)
            )
        "#,
            alice.pubkey().encode_hex::<String>(),
            bob.pubkey().encode_hex::<String>(),
            charlie.pubkey().encode_hex::<String>(),
        );

        let processed = lang::parse(&input, &params)?;

        // assert_eq!(
        //     processed.request_templates.len(),
        //     3,
        //     "Expected 3 request templates"
        // );
        // assert_eq!(
        //     processed.custom_batch.predicates.len(),
        //     4,
        //     "Expected 4 custom predicates"
        // );

        // let mut alice = MockSigner { pk: "Alice".into() };
        // let bob = MockSigner { pk: "Bob".into() };
        // let mut charlie = MockSigner {
        //     pk: "Charlie".into(),
        // };

        // Alice attests that she is ETH friends with Charlie and Charlie
        // attests that he is ETH friends with Bob.
        let alice_attestation =
            eth_friend_signed_pod_builder(&params, charlie.pubkey().into()).sign(&mut alice)?;
        let charlie_attestation =
            eth_friend_signed_pod_builder(&params, bob.pubkey().into()).sign(&mut charlie)?;

        let alice_attestation_signer = alice_attestation.get(KEY_SIGNER);
        let charlie_attestation_signer = charlie_attestation.get(KEY_SIGNER);

        println!(
            "alice_attestation_signer: {}",
            alice_attestation_signer.unwrap().typed()
        );
        println!(
            "charlie_attestation_signer: {}",
            charlie_attestation_signer.unwrap().typed()
        );

        println!(
            "alice pubkey hex: {}",
            alice.pubkey() //.encode_hex::<String>()
        );
        println!(
            "charlie pubkey hex: {}",
            charlie.pubkey() //.encode_hex::<String>()
        );
        println!(
            "bob pubkey hex: {}",
            bob.pubkey() //.encode_hex::<String>());
        );

        let initial_facts = facts_from_pods(&[&alice_attestation.pod, &charlie_attestation.pod]);
        let custom_definitions =
            custom_definitions_from_batches(&[processed.custom_batch], &params);

        let _solve_result = solver::solve(
            &processed.request_templates,
            &initial_facts,
            &params,
            &custom_definitions,
        )?;
        Ok(())
    }

    /* // Start comment for test_prover_ethdos_from_podlog
    // #[test]
    // fn test_prover_ethdos_from_podlog() -> Result<(), Box<dyn std::error::Error>> {
    //     let params = middleware::Params {
    //         max_input_signed_pods: 3,
    //         max_input_main_pods: 3,
    //         max_statements: 31,
    //         max_signed_pod_values: 8,
    //         max_public_statements: 10,
    //         max_statement_args: 6,
    //         max_operation_args: 5,
    //         max_custom_predicate_arity: 5,
    //         max_custom_batch_size: 5,
    //         max_custom_predicate_wildcards: 12,
    //         ..Default::default()
    //     };
    //     // ... (rest of the function body)
    //     Ok(())
    // }
     */ // End comment for test_prover_ethdos_from_podlog

    /* // Start comment for test_prover_custom
    #[test]
    fn test_prover_custom() -> Result<(), Box<dyn std::error::Error>> {
        let params = middleware::Params {
            max_input_signed_pods: 3,
            max_input_main_pods: 3,
            max_statements: 31,
            max_signed_pod_values: 8,
            max_public_statements: 10,
            max_statement_args: 6,
            max_operation_args: 5,
            max_custom_predicate_arity: 5,
            max_custom_batch_size: 5,
            max_custom_predicate_wildcards: 12,
            ..Default::default()
        };
        // ... (rest of the function body)
        Ok(())
    }
    */ // End comment for test_prover_custom
}
