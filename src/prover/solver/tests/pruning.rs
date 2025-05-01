use super::*; // Import helpers from mod.rs
use crate::prover::solver::{
    pruning::{
        prune_by_literal_key, prune_by_literal_origin, prune_by_literal_value, prune_by_type,
        prune_domains_after_proof, prune_initial_domains,
    },
    types::Constraint,
};

#[cfg(test)]
mod pruning_tests {
    use super::*; // Make helpers available inside the module

    #[test]
    fn test_prune_by_type() {
        /* ... */
        let w_pod = wc("A", 0);
        let w_key = wc("X", 0);
        let w_val = wc("V", 0);
        let w_unknown = wc("U", 0);

        let p1 = cv_pod(1);
        let k1 = cv_key("foo");
        let v1 = cv_val(10);

        let mut state = solver_state_with_domains(vec![
            (
                w_pod.clone(),
                HashSet::from([p1.clone(), k1.clone(), v1.clone()]),
                ExpectedType::Pod,
            ),
            (
                w_key.clone(),
                HashSet::from([p1.clone(), k1.clone(), v1.clone()]),
                ExpectedType::Key,
            ),
            (
                w_val.clone(),
                HashSet::from([p1.clone(), k1.clone(), v1.clone()]),
                ExpectedType::Val,
            ),
            (
                w_unknown.clone(),
                HashSet::from([p1.clone(), k1.clone(), v1.clone()]),
                ExpectedType::Unknown,
            ),
        ]);

        let result = prune_by_type(&mut state);
        assert!(result.is_ok());
        assert!(result.unwrap(), "Domains should have changed");

        assert_eq!(state.domains[&w_pod].0, HashSet::from([p1.clone()]));
        assert_eq!(state.domains[&w_key].0, HashSet::from([k1.clone()]));
        assert_eq!(state.domains[&w_val].0, HashSet::from([v1.clone()]));
        assert_eq!(
            state.domains[&w_unknown].0,
            HashSet::from([p1.clone(), k1.clone(), v1.clone()])
        ); // Unknown type doesn't prune
    }

    #[test]
    fn test_prune_by_literal_value() {
        /* ... */
        let w_val = wc("V", 0);
        let v1 = cv_val(10);
        let v2 = cv_val(20);
        let k1 = cv_key("foo"); // Incompatible type

        let mut state = solver_state_with_domains(vec![(
            w_val.clone(),
            HashSet::from([v1.clone(), v2.clone(), k1.clone()]),
            ExpectedType::Val,
        )]);
        let constraints = vec![Constraint::LiteralValue {
            wildcard: w_val.clone(),
            literal_value: val(10), // Expecting value 10
        }];
        let indexes = dummy_prover_indexes(); // Not used by this function

        // Run type pruning first to remove k1
        assert!(prune_by_type(&mut state).unwrap());
        assert_eq!(
            state.domains[&w_val].0,
            HashSet::from([v1.clone(), v2.clone()])
        );

        // Now run literal value pruning
        let result = prune_by_literal_value(&mut state, &indexes, &constraints);
        assert!(result.is_ok());
        assert!(result.unwrap(), "Domain should have changed");

        assert_eq!(state.domains[&w_val].0, HashSet::from([v1.clone()]));
    }

    #[test]
    fn test_prune_by_literal_key() {
        /* ... */
        let w_pod = wc("A", 0);
        let p1 = pod(1);
        let p2 = pod(2);
        let k_foo = key("foo");

        // Setup indexes: p1 has "foo", p2 has "foo" and "bar", p3 has nothing
        let facts = vec![
            (p1, Statement::ValueOf(ak(1, "foo"), val(10))),
            (p2, Statement::ValueOf(ak(2, "foo"), val(20))),
            (p2, Statement::ValueOf(ak(2, "bar"), val(30))),
        ];
        let indexes = setup_indexes_with_facts(facts);

        let mut state = solver_state_with_domains(vec![(
            w_pod.clone(),
            HashSet::from([cv_pod(1), cv_pod(2), cv_pod(3), cv_key("baz")]),
            ExpectedType::Pod,
        )]);
        let constraints = vec![Constraint::LiteralKey {
            pod_wildcard: w_pod.clone(),
            literal_key: k_foo.name().to_string(), // Constrain to key "foo"
        }];

        // Run type pruning first
        assert!(prune_by_type(&mut state).unwrap());
        assert_eq!(
            state.domains[&w_pod].0,
            HashSet::from([cv_pod(1), cv_pod(2), cv_pod(3)])
        );

        // Now run literal key pruning
        let result = prune_by_literal_key(&mut state, &indexes, &constraints);
        assert!(result.is_ok());
        assert!(result.unwrap(), "Domain should have changed");

        // Only Pods 1 and 2 have key "foo"
        assert_eq!(
            state.domains[&w_pod].0,
            HashSet::from([cv_pod(1), cv_pod(2)])
        );
    }

    #[test]
    fn test_prune_by_literal_origin() {
        /* ... */
        let w_key = wc("X", 0);
        let p1 = pod(1);
        let p2 = pod(2);

        // Setup indexes: p1 has "foo" and "bar", p2 has "baz"
        let facts = vec![
            (p1, Statement::ValueOf(ak(1, "foo"), val(10))),
            (p1, Statement::ValueOf(ak(1, "bar"), val(20))),
            (p2, Statement::ValueOf(ak(2, "baz"), val(30))),
        ];
        let indexes = setup_indexes_with_facts(facts);

        let mut state = solver_state_with_domains(vec![(
            w_key.clone(),
            HashSet::from([cv_key("foo"), cv_key("bar"), cv_key("baz"), cv_pod(3)]),
            ExpectedType::Key,
        )]);
        let constraints = vec![Constraint::LiteralOrigin {
            key_wildcard: w_key.clone(),
            literal_pod_id: p1, // Constrain to keys originating from p1
        }];

        // Run type pruning first
        assert!(prune_by_type(&mut state).unwrap());
        assert_eq!(
            state.domains[&w_key].0,
            HashSet::from([cv_key("foo"), cv_key("bar"), cv_key("baz")])
        );

        // Now run literal origin pruning
        let result = prune_by_literal_origin(&mut state, &indexes, &constraints);
        assert!(result.is_ok());
        assert!(result.unwrap(), "Domain should have changed");

        // Only keys "foo" and "bar" originate from p1
        assert_eq!(
            state.domains[&w_key].0,
            HashSet::from([cv_key("foo"), cv_key("bar")])
        );
    }

    #[test]
    fn test_prune_initial_domains_loop() {
        /* ... */
        // Simulate a scenario where multiple pruning steps interact
        let w_pod = wc("A", 0);
        let w_key = wc("X", 0);
        let p1 = pod(1);
        let k_foo = key("foo");

        // Setup indexes: p1 has "foo", p2 does not
        let facts = vec![(p1, Statement::ValueOf(ak(1, "foo"), val(10)))];
        let indexes = setup_indexes_with_facts(facts);

        // Initial state: w_pod can be p1 or p2, w_key can be "foo" or "bar"
        let mut state = solver_state_with_domains(vec![
            (
                w_pod.clone(),
                HashSet::from([cv_pod(1), cv_pod(2)]),
                ExpectedType::Pod,
            ),
            (
                w_key.clone(),
                HashSet::from([cv_key("foo"), cv_key("bar")]),
                ExpectedType::Key,
            ),
        ]);

        // Constraints:
        // 1. Pod ?A must have key "foo" (LiteralKey)
        // 2. Key ?X must originate from Pod p1 (LiteralOrigin)
        state.constraints = vec![
            Constraint::LiteralKey {
                pod_wildcard: w_pod.clone(),
                literal_key: k_foo.name().to_string(),
            },
            Constraint::LiteralOrigin {
                key_wildcard: w_key.clone(),
                literal_pod_id: p1,
            },
        ];

        let result = prune_initial_domains(&mut state, &indexes, &[], &[]);
        assert!(result.is_ok());

        // Expected outcome after propagation:
        // - LiteralKey removes p2 from w_pod's domain (only p1 has "foo")
        // - LiteralOrigin removes "bar" from w_key's domain (p1 doesn't have "bar")
        assert_eq!(state.domains[&w_pod].0, HashSet::from([cv_pod(1)]));
        assert_eq!(state.domains[&w_key].0, HashSet::from([cv_key("foo")]));
    }

    // Test prune_arithmetic helper (implicitly via prune_domains_after_proof)
    #[test]
    fn test_prune_domains_after_proof_sum_of() {
        let wc_s = wc("S", 0);
        let wc_a = wc("A", 0);
        let wc_b = wc("B", 0);
        let v10 = cv_val(10);
        let v20 = cv_val(20);
        let v30 = cv_val(30);
        let v40 = cv_val(40);

        // Case 1: Prune Result (A=10, B=20 => S must be 30)
        let mut state1 = solver_state_with_domains(vec![
            (
                wc_s.clone(),
                HashSet::from([v30.clone(), v40.clone()]),
                ExpectedType::Val,
            ),
            (
                wc_a.clone(),
                HashSet::from([v10.clone()]),
                ExpectedType::Val,
            ),
            (
                wc_b.clone(),
                HashSet::from([v20.clone()]),
                ExpectedType::Val,
            ),
        ]);
        let template1 = StatementTmpl {
            pred: Predicate::Native(NativePredicate::SumOf),
            args: vec![
                StatementTmplArg::WildcardLiteral(wc_s.clone()),
                StatementTmplArg::WildcardLiteral(wc_a.clone()),
                StatementTmplArg::WildcardLiteral(wc_b.clone()),
            ],
        };
        let proven_stmt1 = Statement::SumOf(ak(0, "s"), ak(0, "a"), ak(0, "b")); // Dummy AKs
        let bindings1 = HashMap::from([
            (wc_s.clone(), v30.clone()), // Doesn't matter for pruning S
            (wc_a.clone(), v10.clone()),
            (wc_b.clone(), v20.clone()),
        ]);
        let changed1 = prune_domains_after_proof(
            &mut state1,
            &template1,
            &proven_stmt1,
            &bindings1,
            &dummy_prover_indexes(),
        )
        .unwrap();
        assert!(changed1, "Case 1: Domain S should change");
        assert_eq!(state1.domains[&wc_s].0, HashSet::from([v30.clone()]));

        // Case 2: Prune Operand B (S=30, A=10 => B must be 20)
        let mut state2 = solver_state_with_domains(vec![
            (
                wc_s.clone(),
                HashSet::from([v30.clone()]),
                ExpectedType::Val,
            ),
            (
                wc_a.clone(),
                HashSet::from([v10.clone()]),
                ExpectedType::Val,
            ),
            (
                wc_b.clone(),
                HashSet::from([v20.clone(), v40.clone()]),
                ExpectedType::Val,
            ),
        ]);
        // Template and proven_stmt are the same
        let bindings2 = HashMap::from([
            (wc_s.clone(), v30.clone()),
            (wc_a.clone(), v10.clone()),
            (wc_b.clone(), v20.clone()), // Doesn't matter for pruning B
        ]);
        let changed2 = prune_domains_after_proof(
            &mut state2,
            &template1,
            &proven_stmt1,
            &bindings2,
            &dummy_prover_indexes(),
        )
        .unwrap();
        assert!(changed2, "Case 2: Domain B should change");
        assert_eq!(state2.domains[&wc_b].0, HashSet::from([v20.clone()]));

        // Case 3: Prune Operand A (S=30, B=20 => A must be 10)
        let mut state3 = solver_state_with_domains(vec![
            (
                wc_s.clone(),
                HashSet::from([v30.clone()]),
                ExpectedType::Val,
            ),
            (
                wc_a.clone(),
                HashSet::from([v10.clone(), v40.clone()]),
                ExpectedType::Val,
            ),
            (
                wc_b.clone(),
                HashSet::from([v20.clone()]),
                ExpectedType::Val,
            ),
        ]);
        let bindings3 = HashMap::from([
            (wc_s.clone(), v30.clone()),
            (wc_a.clone(), v10.clone()), // Doesn't matter for pruning A
            (wc_b.clone(), v20.clone()),
        ]);
        let changed3 = prune_domains_after_proof(
            &mut state3,
            &template1,
            &proven_stmt1,
            &bindings3,
            &dummy_prover_indexes(),
        )
        .unwrap();
        assert!(changed3, "Case 3: Domain A should change");
        assert_eq!(state3.domains[&wc_a].0, HashSet::from([v10.clone()]));

        // Case 4: Pruning operand for ProductOf/MaxOf is skipped (currently)
        let template_max = StatementTmpl {
            pred: Predicate::Native(NativePredicate::MaxOf),
            args: vec![
                StatementTmplArg::WildcardLiteral(wc_s.clone()),
                StatementTmplArg::WildcardLiteral(wc_a.clone()),
                StatementTmplArg::WildcardLiteral(wc_b.clone()),
            ],
        };
        let proven_stmt_max = Statement::MaxOf(ak(0, "s"), ak(0, "a"), ak(0, "b"));
        let mut state4 = solver_state_with_domains(vec![
            (
                wc_s.clone(),
                HashSet::from([v20.clone()]),
                ExpectedType::Val,
            ), // Max = 20
            (
                wc_a.clone(),
                HashSet::from([v10.clone(), v20.clone()]),
                ExpectedType::Val,
            ), // A could be 10 or 20
            (
                wc_b.clone(),
                HashSet::from([v10.clone()]),
                ExpectedType::Val,
            ), // B = 10
        ]);
        let bindings4 = HashMap::from([
            (wc_s.clone(), v20.clone()),
            (wc_a.clone(), v20.clone()), // Assume A binds to 20
            (wc_b.clone(), v10.clone()),
        ]);
        let changed4 = prune_domains_after_proof(
            &mut state4,
            &template_max,
            &proven_stmt_max,
            &bindings4,
            &dummy_prover_indexes(),
        )
        .unwrap();
        assert!(
            !changed4,
            "Case 4: Domain A should not change for MaxOf (operand pruning)"
        );
        assert_eq!(
            state4.domains[&wc_a].0,
            HashSet::from([v10.clone(), v20.clone()])
        );
    }

    #[test]
    fn test_prune_domains_after_proof_gt_lt_values() {
        let wc_a = wc("A", 0);
        let wc_b = wc("B", 0);
        let v5 = cv_val(5);
        let v10 = cv_val(10);
        let v15 = cv_val(15);
        let v20 = cv_val(20);

        // Case 1: Gt(A, B) -> Prune A and B
        let mut state1 = solver_state_with_domains(vec![
            (
                wc_a.clone(),
                HashSet::from([v10.clone(), v20.clone()]),
                ExpectedType::Val,
            ),
            (
                wc_b.clone(),
                HashSet::from([v5.clone(), v15.clone()]),
                ExpectedType::Val,
            ),
        ]);
        let template_gt = StatementTmpl {
            pred: Predicate::Native(NativePredicate::Gt),
            args: vec![
                StatementTmplArg::WildcardLiteral(wc_a.clone()),
                StatementTmplArg::WildcardLiteral(wc_b.clone()),
            ],
        };
        let proven_stmt_gt = Statement::Gt(ak(0, "a"), ak(0, "b")); // Dummy AKs
                                                                    // Bindings don't matter for value pruning part
        let bindings = HashMap::new();
        let changed1 = prune_domains_after_proof(
            &mut state1,
            &template_gt,
            &proven_stmt_gt,
            &bindings,
            &dummy_prover_indexes(),
        )
        .unwrap();
        assert!(changed1, "Case 1: Domains should change for Gt");
        assert_eq!(
            state1.domains[&wc_a].0,
            HashSet::from([v20.clone()]),
            "A should be pruned to > max(B)=15"
        );
        assert_eq!(
            state1.domains[&wc_b].0,
            HashSet::from([v5.clone()]),
            "B should be pruned to < min(A)=10"
        );

        // Case 2: Lt(A, B) -> Prune A and B
        let mut state2 = solver_state_with_domains(vec![
            (
                wc_a.clone(),
                HashSet::from([v5.clone(), v15.clone()]),
                ExpectedType::Val,
            ),
            (
                wc_b.clone(),
                HashSet::from([v10.clone(), v20.clone()]),
                ExpectedType::Val,
            ),
        ]);
        let template_lt = StatementTmpl {
            pred: Predicate::Native(NativePredicate::Lt),
            args: vec![
                StatementTmplArg::WildcardLiteral(wc_a.clone()),
                StatementTmplArg::WildcardLiteral(wc_b.clone()),
            ],
        };
        let proven_stmt_lt = Statement::Lt(ak(0, "a"), ak(0, "b")); // Dummy AKs
        let changed2 = prune_domains_after_proof(
            &mut state2,
            &template_lt,
            &proven_stmt_lt,
            &bindings,
            &dummy_prover_indexes(),
        )
        .unwrap();
        assert!(changed2, "Case 2: Domains should change for Lt");
        assert_eq!(
            state2.domains[&wc_a].0,
            HashSet::from([v5.clone()]),
            "A should be pruned to < min(B)=10"
        );
        assert_eq!(
            state2.domains[&wc_b].0,
            HashSet::from([v20.clone()]),
            "B should be pruned to > max(A)=15"
        );

        // Case 3: Gt(A, B) -> Pruning makes domain empty
        let mut state3 = solver_state_with_domains(vec![
            (
                wc_a.clone(),
                HashSet::from([v10.clone()]),
                ExpectedType::Val,
            ), // max=10
            (
                wc_b.clone(),
                HashSet::from([v15.clone()]),
                ExpectedType::Val,
            ), // min=15
        ]);
        let result3 = prune_domains_after_proof(
            &mut state3,
            &template_gt,
            &proven_stmt_gt,
            &bindings,
            &dummy_prover_indexes(),
        );
        assert!(result3.is_err(), "Case 3: Pruning should cause error");
        match result3.err().unwrap() {
            ProverError::Unsatisfiable(msg) => {
                assert!(msg.contains("Gt/Lt values") && msg.contains("emptied domain"))
            }
            _ => panic!("Expected Unsatisfiable error"),
        }
    }

    // --- START: Dynamic Pruning Tests for Contains/NotContains ---

    #[test]
    fn test_prune_domains_after_proof_contains_bound_container() {
        let wc_c = wc("C", 0); // Container
        let wc_k = wc("K", 0); // Key
        let wc_v = wc("V", 0); // Value

        let container1 = dict_val(vec![("a", 10), ("b", 20)]);
        let cv_container1 = ConcreteValue::Val(container1.clone());

        // Create ConcreteValues for keys correctly as Val(String)
        let cv_key_a_val = ConcreteValue::Val(Value::from("a"));
        let cv_key_c_val = ConcreteValue::Val(Value::from("c"));

        let val_10 = cv_val(10);
        let val_30 = cv_val(30); // Non-existent value

        let mut state = solver_state_with_domains(vec![
            (
                wc_c.clone(),
                HashSet::from([cv_container1.clone()]),
                ExpectedType::Val,
            ),
            (
                wc_k.clone(),
                HashSet::from([cv_key_a_val.clone(), cv_key_c_val.clone()]), // Use correct Val representation
                ExpectedType::Val,
            ),
            (
                wc_v.clone(),
                HashSet::from([val_10.clone(), val_30.clone()]),
                ExpectedType::Val,
            ),
        ]);

        let template = StatementTmpl {
            pred: Predicate::Native(NativePredicate::Contains),
            args: vec![
                StatementTmplArg::WildcardLiteral(wc_c.clone()),
                StatementTmplArg::WildcardLiteral(wc_k.clone()),
                StatementTmplArg::WildcardLiteral(wc_v.clone()),
            ],
        };
        let proven_stmt = Statement::Contains(ak(0, "c"), ak(0, "k"), ak(0, "v")); // Dummy AKs
        let bindings = HashMap::from([(wc_c.clone(), cv_container1.clone())]); // Container is bound

        let changed = prune_domains_after_proof(
            &mut state,
            &template,
            &proven_stmt,
            &bindings,
            &dummy_prover_indexes(),
        )
        .unwrap();

        assert!(changed, "Domains should have changed");
        // Key domain should be pruned to only existing keys ("a")
        // Need to create the ConcreteValue for the key 'a' correctly (as Val(String))
        let cv_key_a_val = ConcreteValue::Val(Value::from("a"));
        assert_eq!(
            state.domains[&wc_k].0,
            HashSet::from([cv_key_a_val.clone()])
        );
        // Value domain should be pruned to only existing values (10)
        assert_eq!(state.domains[&wc_v].0, HashSet::from([val_10.clone()]));
    }

    #[test]
    fn test_prune_domains_after_proof_contains_bound_key() {
        let wc_c = wc("C", 0); // Container
        let wc_k = wc("K", 0); // Key
        let wc_v = wc("V", 0); // Value

        let container1 = dict_val(vec![("a", 10), ("b", 20)]);
        let container2 = dict_val(vec![("a", 15), ("c", 25)]);
        let container3 = dict_val(vec![("b", 50)]); // Does not contain key "a"

        let cv_container1 = ConcreteValue::Val(container1.clone());
        let cv_container2 = ConcreteValue::Val(container2.clone());
        let cv_container3 = ConcreteValue::Val(container3.clone());

        let key_a_val = Value::from("a"); // The actual key value "a"
        let cv_key_a = ConcreteValue::Val(key_a_val.clone());

        let val_10 = cv_val(10);
        let val_15 = cv_val(15);
        let val_20 = cv_val(20);

        let mut state = solver_state_with_domains(vec![
            (
                wc_c.clone(),
                HashSet::from([
                    cv_container1.clone(),
                    cv_container2.clone(),
                    cv_container3.clone(),
                ]),
                ExpectedType::Val,
            ),
            (
                wc_k.clone(),
                HashSet::from([cv_key_a.clone()]),
                ExpectedType::Val,
            ),
            (
                wc_v.clone(),
                HashSet::from([val_10.clone(), val_15.clone(), val_20.clone()]),
                ExpectedType::Val,
            ),
        ]);

        let template = StatementTmpl {
            pred: Predicate::Native(NativePredicate::Contains),
            args: vec![
                StatementTmplArg::WildcardLiteral(wc_c.clone()),
                StatementTmplArg::WildcardLiteral(wc_k.clone()),
                StatementTmplArg::WildcardLiteral(wc_v.clone()),
            ],
        };
        let proven_stmt = Statement::Contains(ak(0, "c"), ak(0, "k"), ak(0, "v")); // Dummy AKs
        let bindings = HashMap::from([(wc_k.clone(), cv_key_a.clone())]); // Key is bound to "a"

        let changed = prune_domains_after_proof(
            &mut state,
            &template,
            &proven_stmt,
            &bindings,
            &dummy_prover_indexes(),
        )
        .unwrap();

        assert!(changed, "Domains should have changed");
        // Container domain pruned to those containing key "a"
        assert_eq!(
            state.domains[&wc_c].0,
            HashSet::from([cv_container1.clone(), cv_container2.clone()])
        );
        // Value domain pruned to values associated with key "a" in possible containers (10, 15)
        assert_eq!(
            state.domains[&wc_v].0,
            HashSet::from([val_10.clone(), val_15.clone()])
        );
    }

    #[test]
    fn test_prune_domains_after_proof_contains_bound_value() {
        let wc_c = wc("C", 0); // Container
        let wc_k = wc("K", 0); // Key
        let wc_v = wc("V", 0); // Value

        let container1 = dict_val(vec![("a", 10), ("b", 20)]); // Contains 10
        let container2 = set_val(vec![15, 25]); // Does not contain 10
        let container3 = array_val(vec![5, 10, 15]); // Contains 10

        let cv_container1 = ConcreteValue::Val(container1.clone());
        let cv_container2 = ConcreteValue::Val(container2.clone());
        let cv_container3 = ConcreteValue::Val(container3.clone());

        let key_a_val = Value::from("a");
        let key_b_val = Value::from("b");
        let cv_key_a = ConcreteValue::Val(key_a_val.clone());
        let cv_key_b = ConcreteValue::Val(key_b_val.clone());

        let val_10 = Value::from(10);
        let cv_val_10 = ConcreteValue::Val(val_10.clone());

        let mut state = solver_state_with_domains(vec![
            (
                wc_c.clone(),
                HashSet::from([
                    cv_container1.clone(),
                    cv_container2.clone(),
                    cv_container3.clone(),
                ]),
                ExpectedType::Val,
            ),
            (
                wc_k.clone(),
                HashSet::from([cv_key_a.clone(), cv_key_b.clone()]), // Allow potential keys
                ExpectedType::Val,
            ),
            (
                wc_v.clone(),
                HashSet::from([cv_val_10.clone()]),
                ExpectedType::Val,
            ),
        ]);

        let template = StatementTmpl {
            pred: Predicate::Native(NativePredicate::Contains),
            args: vec![
                StatementTmplArg::WildcardLiteral(wc_c.clone()),
                StatementTmplArg::WildcardLiteral(wc_k.clone()), // Key can be anything here for Set/Array
                StatementTmplArg::WildcardLiteral(wc_v.clone()),
            ],
        };
        let proven_stmt = Statement::Contains(ak(0, "c"), ak(0, "k"), ak(0, "v")); // Dummy AKs
        let bindings = HashMap::from([(wc_v.clone(), cv_val_10.clone())]); // Value is bound to 10

        let changed = prune_domains_after_proof(
            &mut state,
            &template,
            &proven_stmt,
            &bindings,
            &dummy_prover_indexes(),
        )
        .unwrap();

        assert!(changed, "Domains should have changed");
        // Container domain pruned to those containing value 10 (dict1 and array3)
        assert_eq!(
            state.domains[&wc_c].0,
            HashSet::from([cv_container1.clone(), cv_container3.clone()])
        );
        // Key domain should be pruned: only key "a" maps to value 10 in the possible containers.
        // Array/Set contains don't use keys in the same way for this pruning, so only dict1 matters here.
        // The implementation collects keys/indices mapping to the value. Here, key 'a' from dict1 maps to 10.
        assert_eq!(state.domains[&wc_k].0, HashSet::from([cv_key_a.clone()]));
    }

    #[test]
    fn test_prune_domains_after_proof_notcontains_bound_container() {
        let wc_c = wc("C", 0); // Container
        let wc_k = wc("K", 0); // Key

        let container1 = dict_val(vec![("a", 10), ("b", 20)]);
        let cv_container1 = ConcreteValue::Val(container1.clone());

        let key_a_val = Value::from("a"); // Existing key
        let key_c_val = Value::from("c"); // Non-existent key
        let cv_key_a = ConcreteValue::Val(key_a_val.clone());
        let cv_key_c = ConcreteValue::Val(key_c_val.clone());

        let mut state = solver_state_with_domains(vec![
            (
                wc_c.clone(),
                HashSet::from([cv_container1.clone()]),
                ExpectedType::Val,
            ),
            (
                wc_k.clone(),
                HashSet::from([cv_key_a.clone(), cv_key_c.clone()]), // Use correct Val representation
                ExpectedType::Val,
            ),
        ]);

        let template = StatementTmpl {
            pred: Predicate::Native(NativePredicate::NotContains),
            args: vec![
                StatementTmplArg::WildcardLiteral(wc_c.clone()),
                StatementTmplArg::WildcardLiteral(wc_k.clone()),
            ],
        };
        let proven_stmt = Statement::NotContains(ak(0, "c"), ak(0, "k")); // Dummy AKs
        let bindings = HashMap::from([(wc_c.clone(), cv_container1.clone())]); // Container is bound

        let changed = prune_domains_after_proof(
            &mut state,
            &template,
            &proven_stmt,
            &bindings,
            &dummy_prover_indexes(),
        )
        .unwrap();

        assert!(changed, "Domains should have changed");
        // Key domain should be pruned to only non-existing keys ("c")
        assert_eq!(state.domains[&wc_k].0, HashSet::from([cv_key_c.clone()]));
    }

    #[test]
    fn test_prune_domains_after_proof_notcontains_bound_key() {
        let wc_c = wc("C", 0); // Container
        let wc_k = wc("K", 0); // Key

        let container1 = dict_val(vec![("a", 10), ("b", 20)]); // Contains "a"
        let container2 = set_val(vec![15, 25]); // Does not contain "a" (as key)
        let container3 = dict_val(vec![("b", 50)]); // Does not contain key "a"

        let cv_container1 = ConcreteValue::Val(container1.clone());
        let cv_container2 = ConcreteValue::Val(container2.clone());
        let cv_container3 = ConcreteValue::Val(container3.clone());

        let key_a_val = Value::from("a"); // The actual key value "a"
        let cv_key_a = ConcreteValue::Val(key_a_val.clone());

        let mut state = solver_state_with_domains(vec![
            (
                wc_c.clone(),
                HashSet::from([
                    cv_container1.clone(),
                    cv_container2.clone(),
                    cv_container3.clone(),
                ]),
                ExpectedType::Val,
            ),
            (
                wc_k.clone(),
                HashSet::from([cv_key_a.clone()]),
                ExpectedType::Val, // Key type for Dict
            ),
        ]);

        let template = StatementTmpl {
            pred: Predicate::Native(NativePredicate::NotContains),
            args: vec![
                StatementTmplArg::WildcardLiteral(wc_c.clone()),
                StatementTmplArg::WildcardLiteral(wc_k.clone()),
            ],
        };
        let proven_stmt = Statement::NotContains(ak(0, "c"), ak(0, "k")); // Dummy AKs
        let bindings = HashMap::from([(wc_k.clone(), cv_key_a.clone())]); // Key is bound to "a"

        let changed = prune_domains_after_proof(
            &mut state,
            &template,
            &proven_stmt,
            &bindings,
            &dummy_prover_indexes(),
        )
        .unwrap();

        assert!(changed, "Domains should have changed");
        // Container domain pruned to those *not* containing key "a" (set2 and dict3)
        assert_eq!(
            state.domains[&wc_c].0,
            HashSet::from([cv_container2.clone(), cv_container3.clone()])
        );
    }

    #[test]
    fn test_prune_domains_after_proof_contains_error_empty_domain() {
        let wc_c = wc("C", 0);
        let wc_k = wc("K", 0);
        let wc_v = wc("V", 0);

        let container1 = dict_val(vec![("a", 10)]);
        let cv_container1 = ConcreteValue::Val(container1.clone());

        let key_c_val = Value::from("c"); // Non-existent key
        let cv_key_c = ConcreteValue::Val(key_c_val.clone());
        let val_30 = cv_val(30);

        // Key domain only contains a non-existent key
        let mut state = solver_state_with_domains(vec![
            (
                wc_c.clone(),
                HashSet::from([cv_container1.clone()]),
                ExpectedType::Val,
            ),
            (
                wc_k.clone(),
                HashSet::from([cv_key_c.clone()]), // Use correct Val representation
                ExpectedType::Val,
            ),
            (
                wc_v.clone(),
                HashSet::from([val_30.clone()]),
                ExpectedType::Val,
            ),
        ]);

        let template = StatementTmpl {
            pred: Predicate::Native(NativePredicate::Contains),
            args: vec![
                StatementTmplArg::WildcardLiteral(wc_c.clone()),
                StatementTmplArg::WildcardLiteral(wc_k.clone()),
                StatementTmplArg::WildcardLiteral(wc_v.clone()),
            ],
        };
        let proven_stmt = Statement::Contains(ak(0, "c"), ak(0, "k"), ak(0, "v"));
        let bindings = HashMap::from([(wc_c.clone(), cv_container1.clone())]); // Container is bound

        // Pruning Key domain based on bound container should fail
        let result = prune_domains_after_proof(
            &mut state,
            &template,
            &proven_stmt,
            &bindings,
            &dummy_prover_indexes(),
        );

        assert!(result.is_err());
        match result.err().unwrap() {
            ProverError::Unsatisfiable(msg) => {
                assert!(msg.contains("Dynamic pruning (Contains/NotContains Key) emptied domain"));
            }
            e => panic!("Expected Unsatisfiable, got {:?}", e),
        }
    }
}
