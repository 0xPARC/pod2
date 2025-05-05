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

    /// Verifies that domains are correctly pruned based on expected type constraints.
    #[test]
    fn test_prune_by_type() {
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

        // Each domain should only contain values of its expected type
        assert_eq!(state.domains[&w_pod].0, HashSet::from([p1.clone()]));
        assert_eq!(state.domains[&w_key].0, HashSet::from([k1.clone()]));
        assert_eq!(state.domains[&w_val].0, HashSet::from([v1.clone()]));
        // Unknown type preserves all values
        assert_eq!(
            state.domains[&w_unknown].0,
            HashSet::from([p1.clone(), k1.clone(), v1.clone()])
        );
    }

    /// Verifies that domains are correctly pruned based on literal value constraints.
    #[test]
    fn test_prune_by_literal_value() {
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
            literal_value: val(10),
        }];
        let indexes = dummy_prover_indexes();

        // First remove incompatible types
        assert!(prune_by_type(&mut state).unwrap());
        assert_eq!(
            state.domains[&w_val].0,
            HashSet::from([v1.clone(), v2.clone()])
        );

        // Then prune by literal value
        let result = prune_by_literal_value(&mut state, &indexes, &constraints);
        assert!(result.is_ok());
        assert!(result.unwrap(), "Domain should have changed");

        // Only the matching value should remain
        assert_eq!(state.domains[&w_val].0, HashSet::from([v1.clone()]));
    }

    /// Verifies that domains are correctly pruned based on literal key constraints.
    #[test]
    fn test_prune_by_literal_key() {
        let w_pod = wc("A", 0);
        let p1 = pod(1);
        let p2 = pod(2);
        let k_foo = key("foo");

        // Setup test facts: p1 and p2 have "foo", p2 also has "bar"
        let facts = vec![
            (p1, Statement::ValueOf(ak(1, "foo"), val(10))),
            (p2, Statement::ValueOf(ak(2, "foo"), val(20))),
            (p2, Statement::ValueOf(ak(2, "bar"), val(30))),
        ];
        let (indexes, _params) = setup_indexes_with_facts(&facts);

        let mut state = solver_state_with_domains(vec![(
            w_pod.clone(),
            HashSet::from([cv_pod(1), cv_pod(2), cv_pod(3), cv_key("baz")]),
            ExpectedType::Pod,
        )]);
        let constraints = vec![Constraint::LiteralKey {
            pod_wildcard: w_pod.clone(),
            literal_key: k_foo.name().to_string(),
        }];

        // First remove incompatible types
        assert!(prune_by_type(&mut state).unwrap());
        assert_eq!(
            state.domains[&w_pod].0,
            HashSet::from([cv_pod(1), cv_pod(2), cv_pod(3)])
        );

        // Then prune by literal key
        let result = prune_by_literal_key(&mut state, &indexes, &constraints);
        assert!(result.is_ok());
        assert!(result.unwrap(), "Domain should have changed");

        // Only pods containing key "foo" should remain
        assert_eq!(
            state.domains[&w_pod].0,
            HashSet::from([cv_pod(1), cv_pod(2)])
        );
    }

    /// Verifies that domains are correctly pruned based on literal origin constraints.
    #[test]
    fn test_prune_by_literal_origin() {
        let w_key = wc("X", 0);
        let p1 = pod(1);
        let p2 = pod(2);

        // Setup test facts: p1 has "foo" and "bar", p2 has "baz"
        let facts = vec![
            (p1, Statement::ValueOf(ak(1, "foo"), val(10))),
            (p1, Statement::ValueOf(ak(1, "bar"), val(20))),
            (p2, Statement::ValueOf(ak(2, "baz"), val(30))),
        ];
        let (indexes, _params) = setup_indexes_with_facts(&facts);

        let mut state = solver_state_with_domains(vec![(
            w_key.clone(),
            HashSet::from([cv_key("foo"), cv_key("bar"), cv_key("baz"), cv_pod(3)]),
            ExpectedType::Key,
        )]);
        let constraints = vec![Constraint::LiteralOrigin {
            key_wildcard: w_key.clone(),
            literal_pod_id: p1,
        }];

        // First remove incompatible types
        assert!(prune_by_type(&mut state).unwrap());
        assert_eq!(
            state.domains[&w_key].0,
            HashSet::from([cv_key("foo"), cv_key("bar"), cv_key("baz")])
        );

        // Then prune by literal origin
        let result = prune_by_literal_origin(&mut state, &indexes, &constraints);
        assert!(result.is_ok());
        assert!(result.unwrap(), "Domain should have changed");

        // Only keys from pod p1 should remain
        assert_eq!(
            state.domains[&w_key].0,
            HashSet::from([cv_key("foo"), cv_key("bar")])
        );
    }

    /// Verifies that multiple pruning steps interact correctly when constraints are interdependent.
    #[test]
    fn test_prune_initial_domains_loop() {
        let w_pod = wc("A", 0);
        let w_key = wc("X", 0);
        let p1 = pod(1);
        let k_foo = key("foo");

        // Setup test facts: only p1 has key "foo"
        let facts = vec![(p1, Statement::ValueOf(ak(1, "foo"), val(10)))];
        let (indexes, _params) = setup_indexes_with_facts(&facts);

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

        // Constraints that interact:
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

        // After propagation:
        // - w_pod domain reduced to p1 (only pod with "foo")
        // - w_key domain reduced to "foo" (only key in p1)
        assert_eq!(state.domains[&w_pod].0, HashSet::from([cv_pod(1)]));
        assert_eq!(state.domains[&w_key].0, HashSet::from([cv_key("foo")]));
    }

    /// Verifies domain pruning for SumOf statements with various binding combinations.
    #[test]
    fn test_prune_domains_after_proof_sum_of() {
        let wc_s = wc("S", 0);
        let wc_a = wc("A", 0);
        let wc_b = wc("B", 0);
        let v10 = cv_val(10);
        let v20 = cv_val(20);
        let v30 = cv_val(30);
        let v40 = cv_val(40);

        // Case 1: When operands are bound, result domain is pruned to their sum
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
        let proven_stmt1 = Statement::SumOf(ak(0, "s"), ak(0, "a"), ak(0, "b"));
        let bindings1 = HashMap::from([
            (wc_s.clone(), v30.clone()),
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
        assert!(changed1, "Case 1: Domain S should be pruned to sum");
        assert_eq!(state1.domains[&wc_s].0, HashSet::from([v30.clone()]));

        // Case 2: When result and first operand are bound, second operand is pruned
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
        let bindings2 = HashMap::from([
            (wc_s.clone(), v30.clone()),
            (wc_a.clone(), v10.clone()),
            (wc_b.clone(), v20.clone()),
        ]);
        let changed2 = prune_domains_after_proof(
            &mut state2,
            &template1,
            &proven_stmt1,
            &bindings2,
            &dummy_prover_indexes(),
        )
        .unwrap();
        assert!(changed2, "Case 2: Domain B should be pruned");
        assert_eq!(state2.domains[&wc_b].0, HashSet::from([v20.clone()]));

        // Case 3: When result and second operand are bound, first operand is pruned
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
            (wc_a.clone(), v10.clone()),
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
        assert!(changed3, "Case 3: Domain A should be pruned");
        assert_eq!(state3.domains[&wc_a].0, HashSet::from([v10.clone()]));

        // Case 4: MaxOf/ProductOf operand pruning is not implemented
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
            ),
            (
                wc_a.clone(),
                HashSet::from([v10.clone(), v20.clone()]),
                ExpectedType::Val,
            ),
            (
                wc_b.clone(),
                HashSet::from([v10.clone()]),
                ExpectedType::Val,
            ),
        ]);
        let bindings4 = HashMap::from([
            (wc_s.clone(), v20.clone()),
            (wc_a.clone(), v20.clone()),
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
        assert!(!changed4, "Case 4: MaxOf operand pruning not implemented");
        assert_eq!(
            state4.domains[&wc_a].0,
            HashSet::from([v10.clone(), v20.clone()])
        );
    }

    /// Verifies domain pruning for Gt/Lt statements based on value constraints.
    #[test]
    fn test_prune_domains_after_proof_gt_lt_values() {
        let wc_a = wc("A", 0);
        let wc_b = wc("B", 0);
        let v5 = cv_val(5);
        let v10 = cv_val(10);
        let v15 = cv_val(15);
        let v20 = cv_val(20);

        // Case 1: Gt(A, B) prunes both domains based on value constraints
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
        let proven_stmt_gt = Statement::Gt(ak(0, "a"), ak(0, "b"));
        let bindings = HashMap::new();
        let changed1 = prune_domains_after_proof(
            &mut state1,
            &template_gt,
            &proven_stmt_gt,
            &bindings,
            &dummy_prover_indexes(),
        )
        .unwrap();
        assert!(changed1, "Case 1: Domains should be pruned for Gt");
        assert_eq!(
            state1.domains[&wc_a].0,
            HashSet::from([v20.clone()]),
            "A must be greater than max(B)=15"
        );
        assert_eq!(
            state1.domains[&wc_b].0,
            HashSet::from([v5.clone()]),
            "B must be less than min(A)=10"
        );

        // Case 2: Lt(A, B) prunes both domains based on value constraints
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
        let proven_stmt_lt = Statement::Lt(ak(0, "a"), ak(0, "b"));
        let changed2 = prune_domains_after_proof(
            &mut state2,
            &template_lt,
            &proven_stmt_lt,
            &bindings,
            &dummy_prover_indexes(),
        )
        .unwrap();
        assert!(changed2, "Case 2: Domains should be pruned for Lt");
        assert_eq!(
            state2.domains[&wc_a].0,
            HashSet::from([v5.clone()]),
            "A must be less than min(B)=10"
        );
        assert_eq!(
            state2.domains[&wc_b].0,
            HashSet::from([v20.clone()]),
            "B must be greater than max(A)=15"
        );

        // Case 3: Gt(A, B) fails when value constraints cannot be satisfied
        let mut state3 = solver_state_with_domains(vec![
            (
                wc_a.clone(),
                HashSet::from([v10.clone()]),
                ExpectedType::Val,
            ),
            (
                wc_b.clone(),
                HashSet::from([v15.clone()]),
                ExpectedType::Val,
            ),
        ]);
        let result3 = prune_domains_after_proof(
            &mut state3,
            &template_gt,
            &proven_stmt_gt,
            &bindings,
            &dummy_prover_indexes(),
        );
        assert!(result3.is_err(), "Case 3: Should fail when A ≤ B");
        match result3.err().unwrap() {
            ProverError::Unsatisfiable(msg) => {
                assert!(msg.contains("Gt/Lt values") && msg.contains("emptied domain"))
            }
            _ => panic!("Expected Unsatisfiable error"),
        }
    }

    // --- START: Dynamic Pruning Tests for Contains/NotContains ---

    /// Verifies domain pruning for Contains statements when the container is bound.
    #[test]
    fn test_prune_domains_after_proof_contains_bound_container() {
        let wc_c = wc("C", 0); // Container
        let wc_k = wc("K", 0); // Key
        let wc_v = wc("V", 0); // Value

        let container1 = dict_val(vec![("a", 10), ("b", 20)]);
        let cv_container1 = ConcreteValue::Val(container1.clone());

        let cv_key_a_val = ConcreteValue::Val(Value::from("a"));
        let cv_key_c_val = ConcreteValue::Val(Value::from("c"));

        let val_10 = cv_val(10);
        let val_30 = cv_val(30);

        let mut state = solver_state_with_domains(vec![
            (
                wc_c.clone(),
                HashSet::from([cv_container1.clone()]),
                ExpectedType::Val,
            ),
            (
                wc_k.clone(),
                HashSet::from([cv_key_a_val.clone(), cv_key_c_val.clone()]),
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
        let proven_stmt = Statement::Contains(ak(0, "c"), ak(0, "k"), ak(0, "v"));
        let bindings = HashMap::from([(wc_c.clone(), cv_container1.clone())]);

        let changed = prune_domains_after_proof(
            &mut state,
            &template,
            &proven_stmt,
            &bindings,
            &dummy_prover_indexes(),
        )
        .unwrap();

        assert!(changed, "Domains should be pruned");
        assert_eq!(
            state.domains[&wc_k].0,
            HashSet::from([cv_key_a_val.clone()]),
            "Only key 'a' exists in container"
        );
        assert_eq!(
            state.domains[&wc_v].0,
            HashSet::from([val_10.clone()]),
            "Only value 10 exists in container"
        );
    }

    /// Verifies domain pruning for Contains statements when the key is bound.
    #[test]
    fn test_prune_domains_after_proof_contains_bound_key() {
        let wc_c = wc("C", 0);
        let wc_k = wc("K", 0);
        let wc_v = wc("V", 0);

        // Define containers with different key-value mappings
        let container1 = dict_val(vec![("a", 10), ("b", 20)]);
        let container2 = dict_val(vec![("a", 15), ("c", 25)]);
        let container3 = dict_val(vec![("b", 50)]);

        let cv_container1 = ConcreteValue::Val(container1.clone());
        let cv_container2 = ConcreteValue::Val(container2.clone());
        let cv_container3 = ConcreteValue::Val(container3.clone());

        let key_a_val = Value::from("a");
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
        let proven_stmt = Statement::Contains(ak(0, "c"), ak(0, "k"), ak(0, "v"));
        let bindings = HashMap::from([(wc_k.clone(), cv_key_a.clone())]);

        let changed = prune_domains_after_proof(
            &mut state,
            &template,
            &proven_stmt,
            &bindings,
            &dummy_prover_indexes(),
        )
        .unwrap();

        assert!(changed, "Domains should be pruned");
        assert_eq!(
            state.domains[&wc_c].0,
            HashSet::from([cv_container1.clone(), cv_container2.clone()]),
            "Only containers with key 'a' remain"
        );
        assert_eq!(
            state.domains[&wc_v].0,
            HashSet::from([val_10.clone(), val_15.clone()]),
            "Only values mapped to key 'a' remain"
        );
    }

    /// Verifies domain pruning for Contains statements when the value is bound.
    #[test]
    fn test_prune_domains_after_proof_contains_bound_value() {
        let wc_c = wc("C", 0);
        let wc_k = wc("K", 0);
        let wc_v = wc("V", 0);

        // Define containers with different value locations
        let container1 = dict_val(vec![("a", 10), ("b", 20)]);
        let container2 = set_val(vec![15, 25]);
        let container3 = array_val(vec![5, 10, 15]);

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
                HashSet::from([cv_key_a.clone(), cv_key_b.clone()]),
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
                StatementTmplArg::WildcardLiteral(wc_k.clone()),
                StatementTmplArg::WildcardLiteral(wc_v.clone()),
            ],
        };
        let proven_stmt = Statement::Contains(ak(0, "c"), ak(0, "k"), ak(0, "v"));
        let bindings = HashMap::from([(wc_v.clone(), cv_val_10.clone())]);

        let changed = prune_domains_after_proof(
            &mut state,
            &template,
            &proven_stmt,
            &bindings,
            &dummy_prover_indexes(),
        )
        .unwrap();

        assert!(changed, "Domains should be pruned");
        assert_eq!(
            state.domains[&wc_c].0,
            HashSet::from([cv_container1.clone(), cv_container3.clone()]),
            "Only containers containing value 10 remain"
        );
        assert_eq!(
            state.domains[&wc_k].0,
            HashSet::from([cv_key_a.clone()]),
            "Only keys mapping to value 10 remain"
        );
    }

    /// Verifies domain pruning for NotContains statements when the container is bound.
    #[test]
    fn test_prune_domains_after_proof_notcontains_bound_container() {
        let wc_c = wc("C", 0);
        let wc_k = wc("K", 0);

        let container1 = dict_val(vec![("a", 10), ("b", 20)]);
        let cv_container1 = ConcreteValue::Val(container1.clone());

        let key_a_val = Value::from("a");
        let key_c_val = Value::from("c");
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
                HashSet::from([cv_key_a.clone(), cv_key_c.clone()]),
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
        let proven_stmt = Statement::NotContains(ak(0, "c"), ak(0, "k"));
        let bindings = HashMap::from([(wc_c.clone(), cv_container1.clone())]);

        let changed = prune_domains_after_proof(
            &mut state,
            &template,
            &proven_stmt,
            &bindings,
            &dummy_prover_indexes(),
        )
        .unwrap();

        assert!(changed, "Domains should be pruned");
        assert_eq!(
            state.domains[&wc_k].0,
            HashSet::from([cv_key_c.clone()]),
            "Only non-existent keys remain"
        );
    }

    /// Verifies domain pruning for NotContains statements when the key is bound.
    #[test]
    fn test_prune_domains_after_proof_notcontains_bound_key() {
        let wc_c = wc("C", 0);
        let wc_k = wc("K", 0);

        // Define containers with different key presence
        let container1 = dict_val(vec![("a", 10), ("b", 20)]);
        let container2 = set_val(vec![15, 25]);
        let container3 = dict_val(vec![("b", 50)]);

        let cv_container1 = ConcreteValue::Val(container1.clone());
        let cv_container2 = ConcreteValue::Val(container2.clone());
        let cv_container3 = ConcreteValue::Val(container3.clone());

        let key_a_val = Value::from("a");
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
        let proven_stmt = Statement::NotContains(ak(0, "c"), ak(0, "k"));
        let bindings = HashMap::from([(wc_k.clone(), cv_key_a.clone())]);

        let changed = prune_domains_after_proof(
            &mut state,
            &template,
            &proven_stmt,
            &bindings,
            &dummy_prover_indexes(),
        )
        .unwrap();

        assert!(changed, "Domains should be pruned");
        assert_eq!(
            state.domains[&wc_c].0,
            HashSet::from([cv_container2.clone(), cv_container3.clone()]),
            "Only containers without key 'a' remain"
        );
    }

    /// Verifies that domain pruning fails appropriately when constraints cannot be satisfied.
    #[test]
    fn test_prune_domains_after_proof_contains_error_empty_domain() {
        let wc_c = wc("C", 0);
        let wc_k = wc("K", 0);
        let wc_v = wc("V", 0);

        let container1 = dict_val(vec![("a", 10)]);
        let cv_container1 = ConcreteValue::Val(container1.clone());

        let key_c_val = Value::from("c");
        let cv_key_c = ConcreteValue::Val(key_c_val.clone());
        let val_30 = cv_val(30);

        let mut state = solver_state_with_domains(vec![
            (
                wc_c.clone(),
                HashSet::from([cv_container1.clone()]),
                ExpectedType::Val,
            ),
            (
                wc_k.clone(),
                HashSet::from([cv_key_c.clone()]),
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
        let bindings = HashMap::from([(wc_c.clone(), cv_container1.clone())]);

        let result = prune_domains_after_proof(
            &mut state,
            &template,
            &proven_stmt,
            &bindings,
            &dummy_prover_indexes(),
        );

        assert!(result.is_err(), "Should fail when no valid values remain");
        match result.err().unwrap() {
            ProverError::Unsatisfiable(msg) => {
                assert!(msg.contains("Dynamic pruning (Contains/NotContains Key) emptied domain"));
            }
            _ => panic!("Expected Unsatisfiable error"),
        }
    }
}
