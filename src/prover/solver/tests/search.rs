use super::*;

#[cfg(test)]
mod search_tests {
    use super::*;
    use crate::prover::solver::solve;

    #[test]
    fn test_solve_requires_search() {
        // Scenario where initial pruning isn't enough
        let w_pod_a = wc("A", 0);
        let w_pod_b = wc("B", 0);
        let p1 = pod(1);
        let p2 = pod(2);
        let k_foo = key("foo");

        // Facts: p1["foo"] = 10, p2["foo"] = 10
        let facts = vec![
            (p1, Statement::ValueOf(ak(1, "foo"), val(10))),
            (p2, Statement::ValueOf(ak(2, "foo"), val(10))),
        ];
        let _params = middleware::Params::default();
        let custom_definitions = CustomDefinitions::default();

        // Request: Equal(?A["foo"], ?B["foo"])
        // After initial pruning, ?A and ?B could still be {p1, p2}.
        // Needs search or more advanced propagation.
        let request = vec![StatementTmpl {
            pred: Predicate::Native(NativePredicate::Equal),
            args: vec![
                StatementTmplArg::Key(w_pod_a.clone(), KeyOrWildcard::Key(k_foo.clone())),
                StatementTmplArg::Key(w_pod_b.clone(), KeyOrWildcard::Key(k_foo.clone())),
            ],
        }];

        let result = solve(&request, &facts, &_params, &custom_definitions);

        // Current expectation is that search finds a solution (A=p1, B=p1 or A=p2, B=p2)
        // Let's verify it finds *a* solution, not error out.
        assert!(
            result.is_ok(),
            "Expected search to find a solution for Equal, got {:?}",
            result.err()
        );

        if let Ok(solution) = result {
            // Check bindings are consistent
            assert!(solution.bindings.contains_key(&w_pod_a));
            assert!(solution.bindings.contains_key(&w_pod_b));
            assert_eq!(
                solution.bindings[&w_pod_a], solution.bindings[&w_pod_b],
                "Bindings for ?A and ?B must be equal"
            );
            let bound_pod = solution.bindings[&w_pod_a].clone();
            assert!(
                bound_pod == cv_pod(1) || bound_pod == cv_pod(2),
                "Binding should be p1 or p2"
            );

            // Check proof for the Equal statement
            let bound_ak = match bound_pod {
                ConcreteValue::Pod(pid) => {
                    if pid == p1 {
                        ak(1, "foo")
                    } else {
                        ak(2, "foo")
                    }
                }
                _ => panic!("Unexpected binding type"),
            };
            let target_eq = Statement::Equal(bound_ak.clone(), bound_ak.clone()); // Since A=B
            assert!(
                solution.proof_chains.contains_key(&target_eq),
                "Proof chain for Equal missing"
            );
        }
    }

    #[test]
    fn test_solve_simple_gt_proves_and_reaches_extraction() {
        // Goal: Prove Gt(C["quux"], A["foo"]) from ValueOf statements.
        // Expected: Solver finds the Gt statement via GtFromEntries,
        // loop terminates, and hits unimplemented Solution Extraction.

        let pod_a = pod(1);
        let pod_c = pod(3);
        let key_foo = key("foo");
        let key_quux = key("quux");
        let val_10 = val(10);
        let val_20 = val(20);
        let wc_z = wc("Z", 0); // For C["quux"]
        let wc_a = wc("A", 0); // For A["foo"]

        // Facts: A["foo"] = 10, C["quux"] = 20
        let facts = vec![
            (pod_a, Statement::ValueOf(ak(1, "foo"), val_10.clone())),
            (pod_c, Statement::ValueOf(ak(3, "quux"), val_20.clone())),
        ];
        let _params = middleware::Params::default();
        let custom_definitions = CustomDefinitions::default();

        // Request Template: Gt(?Z["quux"], ?A["foo"])
        let request_templates = vec![StatementTmpl {
            pred: Predicate::Native(NativePredicate::Gt),
            args: vec![
                StatementTmplArg::Key(wc_z.clone(), KeyOrWildcard::Key(key_quux)), // ?Z["quux"]
                StatementTmplArg::Key(wc_a.clone(), KeyOrWildcard::Key(key_foo)),  // ?A["foo"]
            ],
        }];

        // Run the solver
        let result = solve(&request_templates, &facts, &_params, &custom_definitions);

        // --- Assertions ---
        // Assert: Expect the solver to succeed now
        assert!(
            result.is_ok(),
            "Expected solver to succeed, but got Err: {:?}",
            result.err()
        );

        // Basic checks on the solution
        if let Ok(solution) = result {
            // Check bindings
            assert!(
                solution.bindings.contains_key(&wc_z),
                "Binding for ?Z missing"
            );
            assert_eq!(solution.bindings[&wc_z], cv_pod(3));
            assert!(
                solution.bindings.contains_key(&wc_a),
                "Binding for ?A missing"
            );
            assert_eq!(solution.bindings[&wc_a], cv_pod(1));

            // Check scope contains the necessary ValueOf statements
            let target_gt = Statement::Gt(ak(3, "quux"), ak(1, "foo"));
            let expected_scope_items: HashSet<(PodId, Statement)> = [
                (pod_c, Statement::ValueOf(ak(3, "quux"), val_20.clone())),
                (pod_a, Statement::ValueOf(ak(1, "foo"), val_10.clone())),
            ]
            .iter()
            .cloned()
            .collect();
            let actual_scope_items: HashSet<(PodId, Statement)> =
                solution.scope.iter().cloned().collect();
            assert!(
                actual_scope_items.is_superset(&expected_scope_items),
                "Scope missing required ValueOf statements"
            );

            // Check proof chain exists for the Gt statement
            assert!(
                solution.proof_chains.contains_key(&target_gt),
                "Proof chain for Gt statement missing"
            );
            let chain = &solution.proof_chains[&target_gt];
            assert_eq!(chain.0.len(), 1, "Expected single step proof chain");
            assert_eq!(
                chain.0[0].operation,
                OperationType::Native(NativeOperation::GtFromEntries)
            );
            assert_eq!(chain.0[0].output, target_gt);
        }
    }

    #[test]
    fn test_solve_unsatisfiable_gt() {
        // Goal: Request Gt(A["foo"], B["bar"]) where values are 10 and 20.
        // Expected: Solver generates candidate Gt(A["foo"], B["bar"]).
        // try_prove_statement fails this candidate via GtFromEntries (10 !> 20).
        // CURRENTLY: The solve loop ignores this failure and proceeds to extraction.
        // DESIRED: The solve loop should recognize the definitive failure and return Unsatisfiable.

        let pod_a = pod(1);
        let pod_b = pod(2);
        let key_foo = key("foo");
        let key_bar = key("bar");
        let val_10 = val(10);
        let val_20 = val(20);
        let wc_x = wc("X", 0); // For A["foo"]
        let wc_y = wc("Y", 0); // For B["bar"]

        // Facts: A["foo"] = 10, B["bar"] = 20
        let facts = vec![
            (pod_a, Statement::ValueOf(ak(1, "foo"), val_10)),
            (pod_b, Statement::ValueOf(ak(2, "bar"), val_20)),
        ];
        let _params = middleware::Params::default();
        let custom_definitions = CustomDefinitions::default();

        // Request Template: Gt(?X["foo"], ?Y["bar"])
        let request_templates = vec![StatementTmpl {
            pred: Predicate::Native(NativePredicate::Gt),
            args: vec![
                StatementTmplArg::Key(wc_x.clone(), KeyOrWildcard::Key(key_foo)), // ?X["foo"]
                StatementTmplArg::Key(wc_y.clone(), KeyOrWildcard::Key(key_bar)), // ?Y["bar"]
            ],
        }];

        // Run the solver
        let result = solve(&request_templates, &facts, &_params, &custom_definitions);

        // Assert: Expect the solver to return Unsatisfiable because Gt(10, 20) fails.
        assert!(
            result.is_err(),
            "Expected solver to return an Unsatisfiable error"
        );
        match result.err().unwrap() {
            ProverError::Unsatisfiable(msg) => {
                // Check that the error message indicates the failure of the specific Gt candidate
                assert!(
                    msg.contains("Failed to prove required candidate statement derived from request templates: Gt("),
                    "Error message missing expected prefix/statement, got: {}",
                    msg
                );
                // Check for the inner reason from try_prove_statement
                assert!(
                    msg.contains("Reason: Could not find or derive proof for: Gt("),
                    "Error message missing inner failure reason, got: {}",
                    msg
                );
            }
            e => panic!("Expected Unsatisfiable error, got {:?}", e),
        }
    }

    // --- START: Tests for Solver with Search ---

    #[test]
    fn test_solve_search_finds_solution() {
        // Scenario: Prove Gt(?A["val"], ?B["val"])
        // Facts: p1["val"] = 20, p2["val"] = 10
        // Initial domains: ?A = {p1, p2}, ?B = {p1, p2}
        // Propagation alone isn't enough.
        // Search must find the specific assignment A=p1, B=p2 for the Gt to be provable.

        let p1 = pod(1);
        let p2 = pod(2);
        let wc_a = wc("A", 0);
        let wc_b = wc("B", 0);
        let val_key = key("val");

        // Facts required for the Gt proof
        let facts = vec![
            (p1, Statement::ValueOf(ak(1, "val"), val(20))),
            (p2, Statement::ValueOf(ak(2, "val"), val(10))),
        ];
        let _params = middleware::Params::default();
        let custom_definitions = CustomDefinitions::default();

        // Request Template: Gt(?A["val"], ?B["val"])
        let request_templates = vec![StatementTmpl {
            pred: Predicate::Native(NativePredicate::Gt),
            args: vec![
                StatementTmplArg::Key(wc_a.clone(), KeyOrWildcard::Key(val_key.clone())), // ?A["val"]
                StatementTmplArg::Key(wc_b.clone(), KeyOrWildcard::Key(val_key.clone())), // ?B["val"]
            ],
        }];

        // Run the solver
        let result = solve(&request_templates, &facts, &_params, &custom_definitions);
        assert!(
            result.is_ok(),
            "Solver failed for Gt search. Err: {:?}",
            result.err()
        );
        let solution = result.unwrap();

        // Check bindings are the correct ones
        assert!(solution.bindings.contains_key(&wc_a));
        assert!(solution.bindings.contains_key(&wc_b));
        assert_eq!(solution.bindings[&wc_a], cv_pod(1), "Expected ?A=p1");
        assert_eq!(solution.bindings[&wc_b], cv_pod(2), "Expected ?B=p2");

        // Check scope contains the necessary ValueOfs for the final Gt proof
        let target_gt_stmt = Statement::Gt(ak(1, "val"), ak(2, "val"));
        let expected_scope_items: HashSet<(PodId, Statement)> = [
            (p1, Statement::ValueOf(ak(1, "val"), val(20))),
            (p2, Statement::ValueOf(ak(2, "val"), val(10))),
        ]
        .iter()
        .cloned()
        .collect();
        let actual_scope_items: HashSet<(PodId, Statement)> =
            solution.scope.iter().cloned().collect();
        assert!(
            actual_scope_items.is_superset(&expected_scope_items),
            "Scope missing required ValueOf statements for Gt proof"
        );

        // Check proof chain for the final Gt statement
        assert!(
            solution.proof_chains.contains_key(&target_gt_stmt),
            "Proof chain for target Gt statement missing"
        );
        let chain = &solution.proof_chains[&target_gt_stmt];
        assert_eq!(
            chain.0.len(),
            1,
            "Expected single step GtFromEntries proof chain"
        );
        assert_eq!(
            chain.0[0].operation,
            OperationType::Native(NativeOperation::GtFromEntries)
        );
    }

    #[test]
    fn test_solve_search_is_unsatisfiable() {
        // Scenario: Prove Eq(?A["k"], ?B["k"]) AND NEq(?A, ?B)
        // Facts: p1["k"]=10, p2["k"]=10.
        // Initial domains: ?A={p1,p2}, ?B={p1,p2}.
        // Search is needed for NEq. Eq requires A=B (either p1 or p2).
        // The constraints are contradictory.

        let p1 = pod(1);
        let p2 = pod(2);
        let wc_a = wc("A", 0);
        let wc_b = wc("B", 0);
        let k = key("k");
        let id_key = key("_pod_id_val"); // Key for auxiliary facts

        let facts = vec![
            (p1, Statement::ValueOf(ak(1, "k"), val(10))),
            (p2, Statement::ValueOf(ak(2, "k"), val(10))),
            // Add auxiliary facts to represent Pod IDs as values
            (p1, Statement::ValueOf(ak(1, "_pod_id_val"), val(1))),
            (p2, Statement::ValueOf(ak(2, "_pod_id_val"), val(2))),
        ];
        let _params = middleware::Params::default();
        let custom_definitions = CustomDefinitions::default();

        let request_templates = vec![
            // Constraint 1: Eq(?A["k"], ?B["k"])
            StatementTmpl {
                pred: Predicate::Native(NativePredicate::Equal),
                args: vec![
                    StatementTmplArg::Key(wc_a.clone(), KeyOrWildcard::Key(k.clone())),
                    StatementTmplArg::Key(wc_b.clone(), KeyOrWildcard::Key(k.clone())),
                ],
            },
            // Constraint 2: NotEqual(?A["_pod_id_val"], ?B["_pod_id_val"])
            // Correctly compares values associated with the Pod IDs.
            StatementTmpl {
                pred: Predicate::Native(NativePredicate::NotEqual),
                args: vec![
                    StatementTmplArg::Key(wc_a.clone(), KeyOrWildcard::Key(id_key.clone())),
                    StatementTmplArg::Key(wc_b.clone(), KeyOrWildcard::Key(id_key.clone())),
                ],
            },
        ];

        // Run the solver
        let result = solve(&request_templates, &facts, &_params, &custom_definitions);

        // Expect Unsatisfiable because the constraints conflict
        assert!(
            result.is_err(),
            "Solver should fail with Unsatisfiable. Got: Ok(...)"
        );
        match result.err().unwrap() {
            ProverError::Unsatisfiable(msg) => {
                // Check that the error message indicates the failure.
                // The exact message can vary depending on whether the failure
                // is caught during initial propagation, search propagation, or final check.
                assert!(
                     msg.contains("Failed to prove required candidate statement derived from request templates: NotEqual") ||
                     msg.contains("Search failed") || // Accept general search failure
                     msg.contains("emptied domain"),
                    "Expected Unsatisfiable from search/propagation/final check, got: {}",
                    msg
                );
            }
            e => panic!("Expected Unsatisfiable error, got {:?}", e),
        }
    }

    // --- END: Tests for Solver with Search ---
}
