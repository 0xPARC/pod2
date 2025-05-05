use std::{
    collections::{HashMap, HashSet},
    sync::Arc,
};

use super::*;
use crate::{
    middleware::{
        statement::WildcardValue, CustomPredicate, CustomPredicateBatch, CustomPredicateRef,
        KeyOrWildcard, NativeOperation, NativePredicate, OperationType, Predicate, Statement,
        StatementTmpl, StatementTmplArg, Value, Wildcard,
    },
    prover::{
        solver::{proof::try_prove_statement, ExpectedType},
        types::{CustomDefinitions, ProofChain},
    },
};

/// Tests for the proof generation system's core operations:
/// - Statement copying from base facts
/// - Equality and inequality derivation
/// - Arithmetic operations (sum, product, max)
/// - Dictionary membership verification
/// - Custom predicate evaluation
/// - Transitive equality chains
#[cfg(test)]
mod proof_tests {
    use super::*;
    use crate::middleware::ToFields;

    /// Verifies the CopyStatement operation and proof caching behavior.
    #[test]
    fn test_try_prove_statement_copy_base_fact() {
        let pod_a = pod(1);
        let key_foo = key("foo");
        let val_10 = val(10);
        let base_fact_stmt =
            Statement::ValueOf(AnchoredKey::new(pod_a, key_foo.clone()), val_10.clone());
        let base_fact_prover: Statement = base_fact_stmt.clone();
        let (indexes, _) = setup_indexes_with_facts(&vec![(pod_a, base_fact_stmt.clone())]);
        let custom_definitions = CustomDefinitions::default();
        let mut state = solver_state_with_domains(vec![]);

        let result = try_prove_statement(
            &mut state,
            &base_fact_prover,
            &indexes,
            &custom_definitions,
            &[],
        );
        assert!(result.is_ok(), "Proof should succeed via CopyStatement");
        let proof_chain = result.unwrap();

        assert_eq!(proof_chain.0.len(), 1, "Should be a single step chain");
        let step = &proof_chain.0[0];
        assert_eq!(
            step.operation,
            OperationType::Native(NativeOperation::CopyStatement)
        );
        assert_eq!(step.inputs.len(), 1, "CopyStatement has one input");
        assert_eq!(
            step.inputs[0], base_fact_prover,
            "Input should be the base fact itself"
        );
        assert_eq!(step.output, base_fact_prover, "Output should be the target");

        assert!(
            state.proof_chains.contains_key(&base_fact_prover.clone()),
            "Proof chain should be stored in state"
        );
        assert_eq!(
            state.proof_chains[&base_fact_prover.clone()],
            proof_chain,
            "Stored proof chain should match returned one"
        );
        assert!(
            state.scope.contains(&(pod_a, base_fact_prover.clone())),
            "Base fact should be added to scope"
        );
        assert_eq!(
            state.scope.len(),
            1,
            "Scope should contain only the one base fact"
        );

        // Verify that reproving returns the cached proof
        let result_again = try_prove_statement(
            &mut state,
            &base_fact_prover,
            &indexes,
            &custom_definitions,
            &[],
        );
        assert!(result_again.is_ok(), "Second proof should succeed");
        assert_eq!(
            result_again.unwrap(),
            proof_chain,
            "Should return the cached proof chain"
        );
        assert_eq!(state.scope.len(), 1, "Scope size should not change");
    }

    /// Verifies error handling when attempting to prove a statement without required base facts.
    #[test]
    fn test_try_prove_statement_not_found() {
        let pod_a = pod(1);
        let key_foo = key("foo");
        let val_10 = val(10);
        let target_stmt =
            Statement::ValueOf(AnchoredKey::new(pod_a, key_foo.clone()), val_10.clone());
        let target_prover: Statement = target_stmt.clone();

        let (indexes, _) = setup_indexes_with_facts(&[]);
        let custom_definitions = CustomDefinitions::default();
        let mut state = solver_state_with_domains(vec![]);

        let result = try_prove_statement(
            &mut state,
            &target_prover,
            &indexes,
            &custom_definitions,
            &[],
        );

        assert!(result.is_err(), "Proof should fail");
        match result.err().unwrap() {
            ProverError::Unsatisfiable(msg) => {
                assert!(
                    msg.contains("Could not find or derive proof"),
                    "Error message mismatch"
                );
                assert!(
                    msg.contains(&format!("{:?}", target_prover)),
                    "Error message mismatch"
                );
            }
            e => panic!("Expected Unsatisfiable error, got {:?}", e),
        }

        assert!(state.proof_chains.is_empty());
        assert!(state.scope.is_empty());
    }

    /// Verifies that proof chains are cached and reused for repeated proof attempts.
    #[test]
    fn test_try_prove_statement_already_proven() {
        let pod_a = pod(1);
        let key_foo = key("foo");
        let val_10 = val(10);
        let target_stmt =
            Statement::ValueOf(AnchoredKey::new(pod_a, key_foo.clone()), val_10.clone());
        let target_prover: Statement = target_stmt.clone();

        let custom_definitions = CustomDefinitions::default();
        let mut state = solver_state_with_domains(vec![]);

        let dummy_chain = ProofChain(vec![]);
        state
            .proof_chains
            .insert(target_prover.clone(), dummy_chain.clone());

        let (indexes, _) = setup_indexes_with_facts(&[]);
        let result = try_prove_statement(
            &mut state,
            &target_prover,
            &indexes,
            &custom_definitions,
            &[],
        );

        assert!(
            result.is_ok(),
            "Proof should succeed by retrieving existing chain"
        );
        assert_eq!(
            result.unwrap(),
            dummy_chain,
            "Should return the pre-existing dummy chain"
        );

        assert_eq!(state.proof_chains.len(), 1);
        assert!(state.scope.is_empty());
    }

    /// Tests that equality between two values can be proven when they are equal.
    ///
    /// Verifies the EqualFromEntries operation using ValueOf statements.
    #[test]
    fn test_try_prove_statement_equal_from_entries_success() {
        let pod_a = pod(1);
        let pod_b = pod(2);
        let key_foo = key("foo");
        let key_bar = key("bar");
        let val_10 = val(10);

        let ak1 = AnchoredKey::new(pod_a, key_foo.clone());
        let ak2 = AnchoredKey::new(pod_b, key_bar.clone());

        let fact1 = Statement::ValueOf(ak1.clone(), val_10.clone());
        let fact2 = Statement::ValueOf(ak2.clone(), val_10.clone());
        let target_stmt = Statement::Equal(ak1.clone(), ak2.clone());

        let (indexes, _) =
            setup_indexes_with_facts(&vec![(pod_a, fact1.clone()), (pod_b, fact2.clone())]);
        let custom_definitions = CustomDefinitions::default();
        let mut state = solver_state_with_domains(vec![]);

        let result =
            try_prove_statement(&mut state, &target_stmt, &indexes, &custom_definitions, &[]);
        assert!(result.is_ok(), "Proof should succeed via EqualFromEntries");
        let proof_chain = result.unwrap();

        assert_eq!(proof_chain.0.len(), 1);
        let step = &proof_chain.0[0];
        assert_eq!(
            step.operation,
            OperationType::Native(NativeOperation::EqualFromEntries)
        );
        assert_eq!(step.inputs.len(), 2);
        assert!(step.inputs.contains(&fact1));
        assert!(step.inputs.contains(&fact2));
        assert_eq!(step.output, target_stmt);

        assert!(state.proof_chains.contains_key(&target_stmt));
        assert_eq!(state.scope.len(), 2);
        assert!(state.scope.contains(&(pod_a, fact1)));
        assert!(state.scope.contains(&(pod_b, fact2)));
    }

    /// Tests that equality cannot be proven when the values are different.
    ///
    /// This test verifies that the EqualFromEntries operation fails when attempting
    /// to prove equality between two values that are not equal.
    #[test]
    fn test_try_prove_statement_equal_from_entries_fail_different_values() {
        let pod_a = pod(1);
        let pod_b = pod(2);
        let key_foo = key("foo");
        let key_bar = key("bar");
        let val_10 = val(10);
        let val_20 = val(20);

        let ak1 = AnchoredKey::new(pod_a, key_foo.clone());
        let ak2 = AnchoredKey::new(pod_b, key_bar.clone());

        let fact1 = Statement::ValueOf(ak1.clone(), val_10.clone());
        let fact2 = Statement::ValueOf(ak2.clone(), val_20.clone()); // Different value
        let target_stmt = Statement::Equal(ak1.clone(), ak2.clone());

        let (indexes, _) =
            setup_indexes_with_facts(&vec![(pod_a, fact1.clone()), (pod_b, fact2.clone())]);
        let custom_definitions = CustomDefinitions::default();
        let mut state = solver_state_with_domains(vec![]);

        let result =
            try_prove_statement(&mut state, &target_stmt, &indexes, &custom_definitions, &[]);
        assert!(result.is_err(), "Proof should fail with different values");
        match result.err().unwrap() {
            ProverError::Unsatisfiable(msg) => {
                assert!(
                    msg.contains("Cannot prove Equal")
                        && msg.contains("transitively: not in same DSU set"),
                    "Expected DSU set error message, got: {}",
                    msg
                );
                assert!(msg.contains("AnchoredKey { pod_id: PodId(Hash("));
            }
            e => panic!("Expected Unsatisfiable(DSU set error), got {:?}", e),
        }
        assert!(state.proof_chains.is_empty());
        assert!(state.scope.is_empty());
    }

    /// Tests that equality cannot be proven when one of the values is missing.
    ///
    /// Verifies that EqualFromEntries fails when a required ValueOf statement is absent.
    #[test]
    fn test_try_prove_statement_equal_from_entries_fail_missing_value() {
        let pod_a = pod(1);
        let pod_b = pod(2);
        let key_foo = key("foo");
        let key_bar = key("bar");
        let val_10 = val(10);

        let ak1 = AnchoredKey::new(pod_a, key_foo.clone());
        let ak2 = AnchoredKey::new(pod_b, key_bar.clone());

        let fact1 = Statement::ValueOf(ak1.clone(), val_10.clone());
        // Missing fact2
        let target_stmt = Statement::Equal(ak1.clone(), ak2.clone());

        // Destructure the result and pass &indexes
        let (indexes, _) = setup_indexes_with_facts(&vec![(pod_a, fact1.clone())]);
        let custom_definitions = CustomDefinitions::default();
        let mut state = solver_state_with_domains(vec![]);

        // Pass &indexes
        let result =
            try_prove_statement(&mut state, &target_stmt, &indexes, &custom_definitions, &[]);
        // Should now fall through to the generic Unsatisfiable error because the transitive check
        // will see that ak2 is not indexed and skip that path.
        assert!(result.is_err());
        match result.err().unwrap() {
            ProverError::Unsatisfiable(msg) => {
                assert!(
                    msg.contains("Could not find or derive proof for: Equal"),
                    "Expected generic Unsatisfiable error, got: {}",
                    msg
                );
            }
            e => panic!("Expected Unsatisfiable(generic), got {:?}", e),
        }
    }

    #[test]
    fn test_try_prove_statement_ne_from_entries_success() {
        let pod_a = pod(1);
        let pod_b = pod(2);
        let key_foo = key("foo");
        let key_bar = key("bar");
        let val_10 = val(10);
        let val_20 = val(20);

        let ak1 = AnchoredKey::new(pod_a, key_foo.clone());
        let ak2 = AnchoredKey::new(pod_b, key_bar.clone());

        let fact1 = Statement::ValueOf(ak1.clone(), val_10.clone());
        let fact2 = Statement::ValueOf(ak2.clone(), val_20.clone()); // Different values
        let target_stmt = Statement::NotEqual(ak1.clone(), ak2.clone());

        // Destructure the result and pass &indexes
        let (indexes, _) =
            setup_indexes_with_facts(&vec![(pod_a, fact1.clone()), (pod_b, fact2.clone())]);
        let custom_definitions = CustomDefinitions::default();
        let mut state = solver_state_with_domains(vec![]);

        // Pass &indexes
        let result =
            try_prove_statement(&mut state, &target_stmt, &indexes, &custom_definitions, &[]);
        assert!(
            result.is_ok(),
            "Proof should succeed via NotEqualFromEntries"
        );
        let proof_chain = result.unwrap();

        assert_eq!(proof_chain.0.len(), 1);
        let step = &proof_chain.0[0];
        assert_eq!(
            step.operation,
            OperationType::Native(NativeOperation::NotEqualFromEntries)
        );
        assert_eq!(step.inputs.len(), 2);
        assert!(step.inputs.contains(&fact1));
        assert!(step.inputs.contains(&fact2));
        assert_eq!(step.output, target_stmt);

        assert!(state.proof_chains.contains_key(&target_stmt));
        assert_eq!(state.scope.len(), 2);
        assert!(state.scope.contains(&(pod_a, fact1)));
        assert!(state.scope.contains(&(pod_b, fact2)));
    }

    #[test]
    fn test_try_prove_statement_ne_from_entries_fail_same_values() {
        let pod_a = pod(1);
        let pod_b = pod(2);
        let key_foo = key("foo");
        let key_bar = key("bar");
        let val_10 = val(10);

        let ak1 = AnchoredKey::new(pod_a, key_foo.clone());
        let ak2 = AnchoredKey::new(pod_b, key_bar.clone());

        let fact1 = Statement::ValueOf(ak1.clone(), val_10.clone());
        let fact2 = Statement::ValueOf(ak2.clone(), val_10.clone()); // Same value
        let target_stmt = Statement::NotEqual(ak1.clone(), ak2.clone());

        // Destructure the result and pass &indexes
        let (indexes, _) =
            setup_indexes_with_facts(&vec![(pod_a, fact1.clone()), (pod_b, fact2.clone())]);
        let custom_definitions = CustomDefinitions::default();
        let mut state = solver_state_with_domains(vec![]);

        let result =
            try_prove_statement(&mut state, &target_stmt, &indexes, &custom_definitions, &[]);
        assert!(result.is_err());
        match result.err().unwrap() {
            ProverError::Unsatisfiable(msg) => {
                assert!(msg.contains("Could not find or derive proof"));
            }
            e => panic!("Expected Unsatisfiable, got {:?}", e),
        }
    }

    /// Tests that GtFromEntries operation succeeds with valid numeric values.
    #[test]
    fn test_try_prove_statement_gt_from_entries_success() {
        let pod_a = pod(1);
        let pod_b = pod(2);
        let key_gt = key("greater");
        let key_lt = key("less");
        let val_20 = val(20);
        let val_10 = val(10);

        let ak_gt = AnchoredKey::new(pod_a, key_gt.clone());
        let ak_lt = AnchoredKey::new(pod_b, key_lt.clone());

        let fact_gt = Statement::ValueOf(ak_gt.clone(), val_20.clone());
        let fact_lt = Statement::ValueOf(ak_lt.clone(), val_10.clone());
        let target_stmt = Statement::Gt(ak_gt.clone(), ak_lt.clone());

        let (indexes, _) =
            setup_indexes_with_facts(&vec![(pod_a, fact_gt.clone()), (pod_b, fact_lt.clone())]);
        let custom_definitions = CustomDefinitions::default();
        let mut state = solver_state_with_domains(vec![]);

        let result =
            try_prove_statement(&mut state, &target_stmt, &indexes, &custom_definitions, &[]);
        assert!(result.is_ok(), "Proof should succeed via GtFromEntries");
        let proof_chain = result.unwrap();

        assert_eq!(proof_chain.0.len(), 1);
        let step = &proof_chain.0[0];
        assert_eq!(
            step.operation,
            OperationType::Native(NativeOperation::GtFromEntries)
        );
        assert_eq!(step.inputs.len(), 2);
        assert!(step.inputs.contains(&fact_gt));
        assert!(step.inputs.contains(&fact_lt));
        assert_eq!(step.output, target_stmt);

        assert!(state.proof_chains.contains_key(&target_stmt));
        assert_eq!(state.scope.len(), 2);
        assert!(state.scope.contains(&(pod_a, fact_gt)));
        assert!(state.scope.contains(&(pod_b, fact_lt)));
    }

    /// Tests that GtFromEntries fails when the first value is less than the second.
    #[test]
    fn test_try_prove_statement_gt_from_entries_fail_not_greater() {
        let pod_a = pod(1);
        let pod_b = pod(2);
        let key_a = key("a");
        let key_b = key("b");
        let val_10 = val(10);
        let val_20 = val(20);

        let ak_a = AnchoredKey::new(pod_a, key_a.clone());
        let ak_b = AnchoredKey::new(pod_b, key_b.clone());

        let fact_a = Statement::ValueOf(ak_a.clone(), val_10.clone());
        let fact_b = Statement::ValueOf(ak_b.clone(), val_20.clone());
        let target_stmt = Statement::Gt(ak_a.clone(), ak_b.clone());

        let (indexes, _) =
            setup_indexes_with_facts(&vec![(pod_a, fact_a.clone()), (pod_b, fact_b.clone())]);
        let custom_definitions = CustomDefinitions::default();
        let mut state = solver_state_with_domains(vec![]);

        let result =
            try_prove_statement(&mut state, &target_stmt, &indexes, &custom_definitions, &[]);
        assert!(result.is_err());
        match result.err().unwrap() {
            ProverError::Unsatisfiable(msg) => {
                assert!(msg.contains("Could not find or derive proof"));
            }
            e => panic!("Expected Unsatisfiable error, got {:?}", e),
        }
    }

    /// Tests that GtFromEntries fails when comparing incompatible value types.
    #[test]
    fn test_try_prove_statement_gt_from_entries_fail_wrong_type() {
        let pod_a = pod(1);
        let pod_b = pod(2);
        let key_a = key("a");
        let key_b = key("b");
        let val_10 = val(10);
        let val_str = Value::from("hello");

        let ak_a = AnchoredKey::new(pod_a, key_a.clone());
        let ak_b = AnchoredKey::new(pod_b, key_b.clone());

        let fact_a = Statement::ValueOf(ak_a.clone(), val_10.clone());
        let fact_b = Statement::ValueOf(ak_b.clone(), val_str.clone());
        let target_stmt = Statement::Gt(ak_a.clone(), ak_b.clone());

        let (indexes, _) =
            setup_indexes_with_facts(&vec![(pod_a, fact_a.clone()), (pod_b, fact_b.clone())]);
        let custom_definitions = CustomDefinitions::default();
        let mut state = solver_state_with_domains(vec![]);

        let result =
            try_prove_statement(&mut state, &target_stmt, &indexes, &custom_definitions, &[]);
        assert!(result.is_err());
        match result.err().unwrap() {
            ProverError::Unsatisfiable(msg) => {
                assert!(msg.contains("Could not find or derive proof"));
            }
            e => panic!("Expected Unsatisfiable, got {:?}", e),
        }
    }

    /// Tests successful derivation of Lt statement from ValueOf statements.
    #[test]
    fn test_try_prove_statement_lt_from_entries_success() {
        let pod_a = pod(1);
        let pod_b = pod(2);
        let key_lt = key("less");
        let key_gt = key("greater");
        let val_10 = val(10);
        let val_20 = val(20);

        let ak_lt = AnchoredKey::new(pod_a, key_lt.clone());
        let ak_gt = AnchoredKey::new(pod_b, key_gt.clone());

        let fact_lt = Statement::ValueOf(ak_lt.clone(), val_10.clone());
        let fact_gt = Statement::ValueOf(ak_gt.clone(), val_20.clone());
        let target_stmt = Statement::Lt(ak_lt.clone(), ak_gt.clone());

        let (indexes, _) =
            setup_indexes_with_facts(&vec![(pod_a, fact_lt.clone()), (pod_b, fact_gt.clone())]);
        let custom_definitions = CustomDefinitions::default();
        let mut state = solver_state_with_domains(vec![]);

        let result =
            try_prove_statement(&mut state, &target_stmt, &indexes, &custom_definitions, &[]);
        assert!(result.is_ok(), "Proof should succeed via LtFromEntries");
        let proof_chain = result.unwrap();

        assert_eq!(proof_chain.0.len(), 1);
        let step = &proof_chain.0[0];
        assert_eq!(
            step.operation,
            OperationType::Native(NativeOperation::LtFromEntries)
        );
        assert_eq!(step.inputs.len(), 2);
        assert!(step.inputs.contains(&fact_lt));
        assert!(step.inputs.contains(&fact_gt));
        assert_eq!(step.output, target_stmt);

        assert!(state.proof_chains.contains_key(&target_stmt));
        assert_eq!(state.scope.len(), 2);
        assert!(state.scope.contains(&(pod_a, fact_lt)));
        assert!(state.scope.contains(&(pod_b, fact_gt)));
    }

    /// Tests that LtFromEntries fails when the first value is not less than the second.
    #[test]
    fn test_try_prove_statement_lt_from_entries_fail_not_less() {
        let pod_a = pod(1);
        let pod_b = pod(2);
        let key_a = key("a");
        let key_b = key("b");
        let val_20 = val(20);
        let val_10 = val(10);

        let ak_a = AnchoredKey::new(pod_a, key_a.clone());
        let ak_b = AnchoredKey::new(pod_b, key_b.clone());

        let fact_a = Statement::ValueOf(ak_a.clone(), val_20.clone());
        let fact_b = Statement::ValueOf(ak_b.clone(), val_10.clone());
        let target_stmt = Statement::Lt(ak_a.clone(), ak_b.clone());

        let (indexes, _) =
            setup_indexes_with_facts(&vec![(pod_a, fact_a.clone()), (pod_b, fact_b.clone())]);
        let custom_definitions = CustomDefinitions::default();
        let mut state = solver_state_with_domains(vec![]);

        let result =
            try_prove_statement(&mut state, &target_stmt, &indexes, &custom_definitions, &[]);
        assert!(result.is_err());
        match result.err().unwrap() {
            ProverError::Unsatisfiable(msg) => {
                assert!(msg.contains("Could not find or derive proof"));
            }
            e => panic!("Expected Unsatisfiable, got {:?}", e),
        }
    }

    /// Tests successful derivation of SumOf statement from three ValueOf statements.
    #[test]
    fn test_try_prove_statement_sumof_success() {
        let pod_a = pod(1);
        let pod_b = pod(2);
        let pod_c = pod(3);
        let key_sum = key("sum");
        let key_add1 = key("add1");
        let key_add2 = key("add2");
        let val_30 = val(30);
        let val_10 = val(10);
        let val_20 = val(20);

        let ak_sum = AnchoredKey::new(pod_a, key_sum.clone());
        let ak_add1 = AnchoredKey::new(pod_b, key_add1.clone());
        let ak_add2 = AnchoredKey::new(pod_c, key_add2.clone());

        let fact_sum = Statement::ValueOf(ak_sum.clone(), val_30.clone());
        let fact_add1 = Statement::ValueOf(ak_add1.clone(), val_10.clone());
        let fact_add2 = Statement::ValueOf(ak_add2.clone(), val_20.clone());
        let target_stmt = Statement::SumOf(ak_sum.clone(), ak_add1.clone(), ak_add2.clone());

        let (indexes, _) = setup_indexes_with_facts(&vec![
            (pod_a, fact_sum.clone()),
            (pod_b, fact_add1.clone()),
            (pod_c, fact_add2.clone()),
        ]);
        let custom_definitions = CustomDefinitions::default();
        let mut state = solver_state_with_domains(vec![]);

        let result =
            try_prove_statement(&mut state, &target_stmt, &indexes, &custom_definitions, &[]);
        assert!(result.is_ok(), "Proof should succeed via SumOf");
        let proof_chain = result.unwrap();

        assert_eq!(proof_chain.0.len(), 1);
        let step = &proof_chain.0[0];
        assert_eq!(
            step.operation,
            OperationType::Native(NativeOperation::SumOf)
        );
        assert_eq!(step.inputs.len(), 3);
        assert!(step.inputs.contains(&fact_sum));
        assert!(step.inputs.contains(&fact_add1));
        assert!(step.inputs.contains(&fact_add2));
        assert_eq!(step.output, target_stmt);

        assert!(state.proof_chains.contains_key(&target_stmt));
        assert_eq!(state.scope.len(), 3);
        assert!(state.scope.contains(&(pod_a, fact_sum)));
        assert!(state.scope.contains(&(pod_b, fact_add1)));
        assert!(state.scope.contains(&(pod_c, fact_add2)));
    }

    /// Tests that SumOf fails when the sum does not match the addends.
    #[test]
    fn test_try_prove_statement_sumof_fail_wrong_sum() {
        let pod_a = pod(1);
        let pod_b = pod(2);
        let pod_c = pod(3);
        let key_sum = key("sum");
        let key_add1 = key("add1");
        let key_add2 = key("add2");
        let val_35 = val(35);
        let val_10 = val(10);
        let val_20 = val(20);

        let ak_sum = AnchoredKey::new(pod_a, key_sum.clone());
        let ak_add1 = AnchoredKey::new(pod_b, key_add1.clone());
        let ak_add2 = AnchoredKey::new(pod_c, key_add2.clone());

        let fact_sum = Statement::ValueOf(ak_sum.clone(), val_35.clone());
        let fact_add1 = Statement::ValueOf(ak_add1.clone(), val_10.clone());
        let fact_add2 = Statement::ValueOf(ak_add2.clone(), val_20.clone());
        let target_stmt = Statement::SumOf(ak_sum.clone(), ak_add1.clone(), ak_add2.clone());

        let (indexes, _) = setup_indexes_with_facts(&vec![
            (pod_a, fact_sum.clone()),
            (pod_b, fact_add1.clone()),
            (pod_c, fact_add2.clone()),
        ]);
        let custom_definitions = CustomDefinitions::default();
        let mut state = solver_state_with_domains(vec![]);

        let result =
            try_prove_statement(&mut state, &target_stmt, &indexes, &custom_definitions, &[]);
        assert!(result.is_err());
        match result.err().unwrap() {
            ProverError::Unsatisfiable(msg) => {
                assert!(msg.contains("Could not find or derive proof"));
            }
            e => panic!("Expected Unsatisfiable, got {:?}", e),
        }
    }

    /// Tests that SumOf fails when comparing incompatible value types.
    #[test]
    fn test_try_prove_statement_sumof_fail_wrong_type() {
        let pod_a = pod(1);
        let pod_b = pod(2);
        let pod_c = pod(3);
        let key_sum = key("sum");
        let key_add1 = key("add1");
        let key_add2 = key("add2");
        let val_30 = val(30);
        let val_str = Value::from("ten");
        let val_20 = val(20);

        let ak_sum = AnchoredKey::new(pod_a, key_sum.clone());
        let ak_add1 = AnchoredKey::new(pod_b, key_add1.clone());
        let ak_add2 = AnchoredKey::new(pod_c, key_add2.clone());

        let fact_sum = Statement::ValueOf(ak_sum.clone(), val_30.clone());
        let fact_add1 = Statement::ValueOf(ak_add1.clone(), val_str.clone());
        let fact_add2 = Statement::ValueOf(ak_add2.clone(), val_20.clone());
        let target_stmt = Statement::SumOf(ak_sum.clone(), ak_add1.clone(), ak_add2.clone());

        let (indexes, _) = setup_indexes_with_facts(&vec![
            (pod_a, fact_sum.clone()),
            (pod_b, fact_add1.clone()),
            (pod_c, fact_add2.clone()),
        ]);
        let custom_definitions = CustomDefinitions::default();
        let mut state = solver_state_with_domains(vec![]);

        let result =
            try_prove_statement(&mut state, &target_stmt, &indexes, &custom_definitions, &[]);
        assert!(result.is_err(), "Should fail due to wrong type");
        match result.err().unwrap() {
            ProverError::Unsatisfiable(msg) => {
                assert!(msg.contains("Could not find or derive proof"));
            }
            e => panic!("Expected Unsatisfiable, got {:?}", e),
        }
    }

    /// Tests that SumOf fails when a required ValueOf statement is missing.
    #[test]
    fn test_try_prove_statement_sumof_fail_missing_value() {
        let pod_a = pod(1);
        let pod_b = pod(2);
        let pod_c = pod(3);
        let key_sum = key("sum");
        let key_add1 = key("add1");
        let key_add2 = key("add2");
        let val_30 = val(30);
        let val_10 = val(10);

        let ak_sum = AnchoredKey::new(pod_a, key_sum.clone());
        let ak_add1 = AnchoredKey::new(pod_b, key_add1.clone());
        let ak_add2 = AnchoredKey::new(pod_c, key_add2.clone());

        let fact_sum = Statement::ValueOf(ak_sum.clone(), val_30.clone());
        let fact_add1 = Statement::ValueOf(ak_add1.clone(), val_10.clone());
        let target_stmt = Statement::SumOf(ak_sum.clone(), ak_add1.clone(), ak_add2.clone());

        let (indexes, _) =
            setup_indexes_with_facts(&vec![(pod_a, fact_sum.clone()), (pod_b, fact_add1.clone())]);
        let custom_definitions = CustomDefinitions::default();
        let mut state = solver_state_with_domains(vec![]);

        let result =
            try_prove_statement(&mut state, &target_stmt, &indexes, &custom_definitions, &[]);
        assert!(result.is_err());
        match result.err().unwrap() {
            ProverError::Unsatisfiable(msg) => {
                assert!(msg.contains("Could not find or derive proof"));
            }
            e => panic!("Expected Unsatisfiable, got {:?}", e),
        }
    }

    // --- ProductOf Tests ---
    #[test]
    fn test_try_prove_statement_productof_success() {
        let pod_a = pod(1);
        let pod_b = pod(2);
        let pod_c = pod(3);
        let key_prod = key("prod");
        let key_fac1 = key("fac1");
        let key_fac2 = key("fac2");
        let val_30 = val(30);
        let val_3 = val(3);
        let val_10 = val(10);

        let ak_prod = AnchoredKey::new(pod_a, key_prod.clone());
        let ak_fac1 = AnchoredKey::new(pod_b, key_fac1.clone());
        let ak_fac2 = AnchoredKey::new(pod_c, key_fac2.clone());

        let fact_prod = Statement::ValueOf(ak_prod.clone(), val_30.clone());
        let fact_fac1 = Statement::ValueOf(ak_fac1.clone(), val_3.clone());
        let fact_fac2 = Statement::ValueOf(ak_fac2.clone(), val_10.clone());
        let target_stmt = Statement::ProductOf(ak_prod.clone(), ak_fac1.clone(), ak_fac2.clone());

        // Destructure the result and pass &indexes
        let (indexes, _) = setup_indexes_with_facts(&vec![
            (pod_a, fact_prod.clone()),
            (pod_b, fact_fac1.clone()),
            (pod_c, fact_fac2.clone()),
        ]);
        let custom_definitions = CustomDefinitions::default();
        let mut state = solver_state_with_domains(vec![]);

        // Pass &indexes
        let result =
            try_prove_statement(&mut state, &target_stmt, &indexes, &custom_definitions, &[]);
        assert!(result.is_ok(), "Proof should succeed via ProductOf");
        let proof_chain = result.unwrap();

        assert_eq!(proof_chain.0.len(), 1);
        let step = &proof_chain.0[0];
        assert_eq!(
            step.operation,
            OperationType::Native(NativeOperation::ProductOf)
        );
        assert_eq!(step.inputs.len(), 3);
        assert!(step.inputs.contains(&fact_prod));
        assert!(step.inputs.contains(&fact_fac1));
        assert!(step.inputs.contains(&fact_fac2));
        assert_eq!(step.output, target_stmt);

        assert!(state.proof_chains.contains_key(&target_stmt));
        assert_eq!(state.scope.len(), 3);
        assert!(state.scope.contains(&(pod_a, fact_prod)));
        assert!(state.scope.contains(&(pod_b, fact_fac1)));
        assert!(state.scope.contains(&(pod_c, fact_fac2)));
    }

    #[test]
    fn test_try_prove_statement_productof_fail_wrong_product() {
        let pod_a = pod(1);
        let pod_b = pod(2);
        let pod_c = pod(3);
        let key_prod = key("prod");
        let key_fac1 = key("fac1");
        let key_fac2 = key("fac2");
        let val_35 = val(35); // Incorrect product
        let val_3 = val(3);
        let val_10 = val(10);

        let ak_prod = AnchoredKey::new(pod_a, key_prod.clone());
        let ak_fac1 = AnchoredKey::new(pod_b, key_fac1.clone());
        let ak_fac2 = AnchoredKey::new(pod_c, key_fac2.clone());

        let fact_prod = Statement::ValueOf(ak_prod.clone(), val_35.clone());
        let fact_fac1 = Statement::ValueOf(ak_fac1.clone(), val_3.clone());
        let fact_fac2 = Statement::ValueOf(ak_fac2.clone(), val_10.clone());
        let target_stmt = Statement::ProductOf(ak_prod.clone(), ak_fac1.clone(), ak_fac2.clone());

        // Destructure the result and pass &indexes
        let (indexes, _) = setup_indexes_with_facts(&vec![
            (pod_a, fact_prod.clone()),
            (pod_b, fact_fac1.clone()),
            (pod_c, fact_fac2.clone()),
        ]);
        let custom_definitions = CustomDefinitions::default();
        let mut state = solver_state_with_domains(vec![]);

        // Pass &indexes
        let result =
            try_prove_statement(&mut state, &target_stmt, &indexes, &custom_definitions, &[]);
        assert!(result.is_err());
        match result.err().unwrap() {
            ProverError::Unsatisfiable(msg) => {
                assert!(msg.contains("Could not find or derive proof"));
            }
            e => panic!("Expected Unsatisfiable, got {:?}", e),
        }
    }

    // --- MaxOf Tests ---

    #[test]
    fn test_try_prove_statement_maxof_success() {
        let pod_a = pod(1);
        let pod_b = pod(2);
        let pod_c = pod(3);
        let key_max = key("max");
        let key_op1 = key("op1");
        let key_op2 = key("op2");
        let val_20 = val(20);
        let val_10 = val(10);
        let val_neg5 = val(-5);

        let ak_max = AnchoredKey::new(pod_a, key_max.clone());
        let ak_op1 = AnchoredKey::new(pod_b, key_op1.clone());
        let ak_op2 = AnchoredKey::new(pod_c, key_op2.clone());

        let fact_max = Statement::ValueOf(ak_max.clone(), val_20.clone()); // Max is 20
        let fact_op1 = Statement::ValueOf(ak_op1.clone(), val_20.clone());
        let fact_op2 = Statement::ValueOf(ak_op2.clone(), val_10.clone());
        let target_stmt = Statement::MaxOf(ak_max.clone(), ak_op1.clone(), ak_op2.clone());

        // Destructure the result and pass &indexes
        let (indexes, _) = setup_indexes_with_facts(&vec![
            (pod_a, fact_max.clone()),
            (pod_b, fact_op1.clone()),
            (pod_c, fact_op2.clone()),
        ]);
        let custom_definitions = CustomDefinitions::default();
        let mut state = solver_state_with_domains(vec![]);

        // Pass &indexes
        let result =
            try_prove_statement(&mut state, &target_stmt, &indexes, &custom_definitions, &[]);
        assert!(result.is_ok(), "Proof should succeed via MaxOf (case 1)");
        let proof_chain = result.unwrap();

        assert_eq!(proof_chain.0.len(), 1);
        let step = &proof_chain.0[0];
        assert_eq!(
            step.operation,
            OperationType::Native(NativeOperation::MaxOf)
        );
        assert_eq!(step.inputs.len(), 3);
        assert!(step.inputs.contains(&fact_max));
        assert!(step.inputs.contains(&fact_op1));
        assert!(step.inputs.contains(&fact_op2));
        assert_eq!(step.output, target_stmt);

        assert!(state.proof_chains.contains_key(&target_stmt));
        assert_eq!(state.scope.len(), 3);
        assert!(state.scope.contains(&(pod_a, fact_max)));
        assert!(state.scope.contains(&(pod_b, fact_op1)));
        assert!(state.scope.contains(&(pod_c, fact_op2)));

        // Case 2: op2 is max
        let fact_max2 = Statement::ValueOf(ak_max.clone(), val_10.clone()); // Max is 10
        let fact_op1_2 = Statement::ValueOf(ak_op1.clone(), val_neg5.clone());
        let fact_op2_2 = Statement::ValueOf(ak_op2.clone(), val_10.clone());
        let target_stmt2 = Statement::MaxOf(ak_max.clone(), ak_op1.clone(), ak_op2.clone());

        // Destructure the result and pass &indexes
        let (indexes2, _) = setup_indexes_with_facts(&vec![
            (pod_a, fact_max2.clone()),
            (pod_b, fact_op1_2.clone()),
            (pod_c, fact_op2_2.clone()),
        ]);
        let mut state2 = solver_state_with_domains(vec![]);
        // Pass &indexes2
        let result2 = try_prove_statement(
            &mut state2,
            &target_stmt2,
            &indexes2,
            &custom_definitions,
            &[],
        );
        assert!(result2.is_ok(), "Proof should succeed via MaxOf (case 2)");
    }

    #[test]
    fn test_try_prove_statement_maxof_fail_wrong_max() {
        let pod_a = pod(1);
        let pod_b = pod(2);
        let pod_c = pod(3);
        let key_max = key("max");
        let key_op1 = key("op1");
        let key_op2 = key("op2");
        let val_15 = val(15); // Incorrect max
        let val_20 = val(20);
        let val_10 = val(10);

        let ak_max = AnchoredKey::new(pod_a, key_max.clone());
        let ak_op1 = AnchoredKey::new(pod_b, key_op1.clone());
        let ak_op2 = AnchoredKey::new(pod_c, key_op2.clone());

        let fact_max = Statement::ValueOf(ak_max.clone(), val_15.clone());
        let fact_op1 = Statement::ValueOf(ak_op1.clone(), val_20.clone());
        let fact_op2 = Statement::ValueOf(ak_op2.clone(), val_10.clone());
        let target_stmt = Statement::MaxOf(ak_max.clone(), ak_op1.clone(), ak_op2.clone());

        // Destructure the result and pass &indexes
        let (indexes, _) = setup_indexes_with_facts(&vec![
            (pod_a, fact_max.clone()),
            (pod_b, fact_op1.clone()),
            (pod_c, fact_op2.clone()),
        ]);
        let custom_definitions = CustomDefinitions::default();
        let mut state = solver_state_with_domains(vec![]);

        // Pass &indexes
        let result =
            try_prove_statement(&mut state, &target_stmt, &indexes, &custom_definitions, &[]);
        assert!(result.is_err());
        match result.err().unwrap() {
            ProverError::Unsatisfiable(msg) => {
                assert!(msg.contains("Could not find or derive proof"));
            }
            e => panic!("Expected Unsatisfiable, got {:?}", e),
        }
    }

    // --- Contains/NotContains Tests (Dictionaries) ---

    /// Tests successful verification of a key-value pair in a dictionary.
    /// The test verifies that ContainsFromEntries correctly handles string values
    /// and dictionary key lookups.
    #[test]
    fn test_try_prove_statement_contains_dict_success() {
        let pod_a = pod(1);
        let pod_b = pod(2);
        let pod_c = pod(3);

        let key_dict = key("my_dict");
        let key_lookup = key("lookup_key");
        let key_expected_val = key("expected_value");

        let dict_val_str = Value::from("hello");
        let dict_key = key("world");

        let mut map = HashMap::new();
        map.insert(dict_key.clone(), dict_val_str.clone());
        let dict_container = Value::from(Dictionary::new(map).unwrap());

        let ak_dict = AnchoredKey::new(pod_a, key_dict);
        let ak_key = AnchoredKey::new(pod_b, key_lookup);
        let ak_val = AnchoredKey::new(pod_c, key_expected_val);

        let fact_dict = Statement::ValueOf(ak_dict.clone(), dict_container.clone());
        let fact_key = Statement::ValueOf(ak_key.clone(), Value::from(dict_key.name().to_string()));
        let fact_val = Statement::ValueOf(ak_val.clone(), dict_val_str.clone());
        let target_stmt = Statement::Contains(ak_dict.clone(), ak_key.clone(), ak_val.clone());

        let (indexes, _) = setup_indexes_with_facts(&vec![
            (pod_a, fact_dict.clone()),
            (pod_b, fact_key.clone()),
            (pod_c, fact_val.clone()),
        ]);
        let custom_definitions = CustomDefinitions::default();
        let mut state = solver_state_with_domains(vec![]);

        let result =
            try_prove_statement(&mut state, &target_stmt, &indexes, &custom_definitions, &[]);
        assert!(
            result.is_ok(),
            "Proof should succeed via ContainsFromEntries"
        );
        let proof_chain = result.unwrap();

        assert_eq!(proof_chain.0.len(), 1);
        let step = &proof_chain.0[0];
        assert_eq!(
            step.operation,
            OperationType::Native(NativeOperation::ContainsFromEntries)
        );
        assert_eq!(step.inputs.len(), 3); // ValueOf(dict), ValueOf(key), ValueOf(value)
        assert!(step.inputs.contains(&fact_dict));
        assert!(step.inputs.contains(&fact_key));
        assert!(step.inputs.contains(&fact_val));
        assert_eq!(step.output, target_stmt);

        assert!(state.proof_chains.contains_key(&target_stmt));
        assert_eq!(state.scope.len(), 3);
        assert!(state.scope.contains(&(pod_a, fact_dict)));
        assert!(state.scope.contains(&(pod_b, fact_key)));
        assert!(state.scope.contains(&(pod_c, fact_val)));
    }

    /// Tests that Contains fails when the key is not present in the dictionary.
    /// This verifies that ContainsFromEntries correctly handles non-existent keys.
    #[test]
    fn test_try_prove_statement_contains_dict_fail_key_not_found() {
        let pod_a = pod(1);
        let pod_b = pod(2);
        let pod_c = pod(3);

        let key_dict = key("my_dict");
        let key_lookup_missing = key("missing_key");
        let key_expected_val = key("expected_value");

        let dict_val_str = Value::from("hello");
        let dict_key = key("world");
        let missing_key = key("missing");

        let mut map = HashMap::new();
        map.insert(dict_key.clone(), dict_val_str.clone());
        let dict_container = Value::from(Dictionary::new(map).unwrap());

        let ak_dict = AnchoredKey::new(pod_a, key_dict);
        let ak_key_missing = AnchoredKey::new(pod_b, key_lookup_missing);
        let ak_val = AnchoredKey::new(pod_c, key_expected_val);

        let fact_dict = Statement::ValueOf(ak_dict.clone(), dict_container.clone());
        let fact_key_missing = Statement::ValueOf(
            ak_key_missing.clone(),
            Value::from(missing_key.name().to_string()),
        );
        let fact_val = Statement::ValueOf(ak_val.clone(), dict_val_str.clone());
        let target_stmt =
            Statement::Contains(ak_dict.clone(), ak_key_missing.clone(), ak_val.clone());

        let (indexes, _) = setup_indexes_with_facts(&vec![
            (pod_a, fact_dict.clone()),
            (pod_b, fact_key_missing.clone()),
            (pod_c, fact_val.clone()),
        ]);
        let custom_definitions = CustomDefinitions::default();
        let mut state = solver_state_with_domains(vec![]);

        let result =
            try_prove_statement(&mut state, &target_stmt, &indexes, &custom_definitions, &[]);
        assert!(result.is_err());
        match result.err().unwrap() {
            ProverError::Unsatisfiable(msg) => {
                assert!(msg.contains("Could not find or derive proof"));
            }
            e => panic!("Expected Unsatisfiable, got {:?}", e),
        }
    }

    /// Tests that Contains fails when the value doesn't match the dictionary entry.
    /// This verifies that ContainsFromEntries checks both key existence and value equality.
    #[test]
    fn test_try_prove_statement_contains_dict_fail_wrong_value() {
        let pod_a = pod(1);
        let pod_b = pod(2);
        let pod_c = pod(3);

        let key_dict = key("my_dict");
        let key_lookup = key("lookup_key");
        let key_wrong_val = key("wrong_value");

        let dict_val_str_actual = Value::from("actual_value");
        let dict_key = key("the_key");
        let dict_val_str_wrong = Value::from("wrong_value");

        let mut map = HashMap::new();
        map.insert(dict_key.clone(), dict_val_str_actual.clone());
        let dict_container = Value::from(Dictionary::new(map).unwrap());

        let ak_dict = AnchoredKey::new(pod_a, key_dict);
        let ak_key = AnchoredKey::new(pod_b, key_lookup);
        let ak_val_wrong = AnchoredKey::new(pod_c, key_wrong_val);

        let fact_dict = Statement::ValueOf(ak_dict.clone(), dict_container.clone());
        let fact_key = Statement::ValueOf(ak_key.clone(), Value::from(dict_key.name().to_string()));
        let fact_val_wrong = Statement::ValueOf(ak_val_wrong.clone(), dict_val_str_wrong.clone());
        let target_stmt =
            Statement::Contains(ak_dict.clone(), ak_key.clone(), ak_val_wrong.clone());

        let (indexes, _) = setup_indexes_with_facts(&vec![
            (pod_a, fact_dict.clone()),
            (pod_b, fact_key.clone()),
            (pod_c, fact_val_wrong.clone()),
        ]);
        let custom_definitions = CustomDefinitions::default();
        let mut state = solver_state_with_domains(vec![]);

        let result =
            try_prove_statement(&mut state, &target_stmt, &indexes, &custom_definitions, &[]);
        assert!(result.is_err());
        match result.err().unwrap() {
            ProverError::Unsatisfiable(msg) => {
                assert!(msg.contains("Could not find or derive proof"));
            }
            e => panic!("Expected Unsatisfiable, got {:?}", e),
        }
    }

    /// Tests that Contains fails when a required ValueOf statement is missing.
    /// This verifies that ContainsFromEntries requires all three input statements.
    #[test]
    fn test_try_prove_statement_contains_dict_fail_missing_input_value() {
        let pod_a = pod(1);
        let pod_b = pod(2);
        let pod_c = pod(3);

        let key_dict = key("my_dict");
        let key_lookup = key("lookup_key");
        let key_expected_val = key("expected_value");

        let dict_val_str = Value::from("hello");
        let dict_key = key("world");

        let mut map = HashMap::new();
        map.insert(dict_key.clone(), dict_val_str.clone());
        let dict_container = Value::from(Dictionary::new(map).unwrap());

        let ak_dict = AnchoredKey::new(pod_a, key_dict);
        let ak_key = AnchoredKey::new(pod_b, key_lookup);
        let ak_val = AnchoredKey::new(pod_c, key_expected_val);

        let fact_dict = Statement::ValueOf(ak_dict.clone(), dict_container.clone());
        let fact_key = Statement::ValueOf(ak_key.clone(), Value::from(dict_key.name().to_string()));
        let target_stmt = Statement::Contains(ak_dict.clone(), ak_key.clone(), ak_val.clone());

        let (indexes, _) =
            setup_indexes_with_facts(&vec![(pod_a, fact_dict.clone()), (pod_b, fact_key.clone())]);
        let custom_definitions = CustomDefinitions::default();
        let mut state = solver_state_with_domains(vec![]);

        let result =
            try_prove_statement(&mut state, &target_stmt, &indexes, &custom_definitions, &[]);
        assert!(result.is_err());
        match result.err().unwrap() {
            ProverError::Unsatisfiable(msg) => {
                assert!(msg.contains("Could not find or derive proof"));
            }
            e => panic!("Expected Unsatisfiable, got {:?}", e),
        }
    }

    /// Tests successful verification that a key is not present in a dictionary.
    /// This verifies that NotContainsFromEntries correctly handles non-existent keys.
    #[test]
    fn test_try_prove_statement_notcontains_dict_success() {
        let pod_a = pod(1);
        let pod_b = pod(2);

        let key_dict = key("my_dict");
        let key_lookup_missing = key("missing_key");

        let dict_val_str = Value::from("hello");
        let dict_key = key("world");
        let missing_key = key("missing");

        let mut map = HashMap::new();
        map.insert(dict_key.clone(), dict_val_str.clone());
        let dict_container = Value::from(Dictionary::new(map).unwrap());

        let ak_dict = AnchoredKey::new(pod_a, key_dict);
        let ak_key_missing = AnchoredKey::new(pod_b, key_lookup_missing);

        let fact_dict = Statement::ValueOf(ak_dict.clone(), dict_container.clone());
        let fact_key_missing = Statement::ValueOf(
            ak_key_missing.clone(),
            Value::from(missing_key.name().to_string()),
        );
        let target_stmt = Statement::NotContains(ak_dict.clone(), ak_key_missing.clone());

        let (indexes, _) = setup_indexes_with_facts(&vec![
            (pod_a, fact_dict.clone()),
            (pod_b, fact_key_missing.clone()),
        ]);
        let custom_definitions = CustomDefinitions::default();
        let mut state = solver_state_with_domains(vec![]);

        let result =
            try_prove_statement(&mut state, &target_stmt, &indexes, &custom_definitions, &[]);
        assert!(
            result.is_ok(),
            "Proof should succeed via NotContainsFromEntries"
        );
        let proof_chain = result.unwrap();

        assert_eq!(proof_chain.0.len(), 1);
        let step = &proof_chain.0[0];
        assert_eq!(
            step.operation,
            OperationType::Native(NativeOperation::NotContainsFromEntries)
        );
        assert_eq!(step.inputs.len(), 2);
        assert!(step.inputs.contains(&fact_dict));
        assert!(step.inputs.contains(&fact_key_missing));
        assert_eq!(step.output, target_stmt);

        assert!(state.proof_chains.contains_key(&target_stmt));
        assert_eq!(state.scope.len(), 2);
        assert!(state.scope.contains(&(pod_a, fact_dict)));
        assert!(state.scope.contains(&(pod_b, fact_key_missing)));
    }

    /// Tests that NotContains fails when the key exists in the dictionary.
    /// This verifies that NotContainsFromEntries correctly handles existing keys.
    #[test]
    fn test_try_prove_statement_notcontains_dict_fail_key_found() {
        let pod_a = pod(1);
        let pod_b = pod(2);

        let key_dict = key("my_dict");
        let key_lookup_exists = key("existing_key");

        let dict_val_str = Value::from("hello");
        let dict_key = key("world");

        let mut map = HashMap::new();
        map.insert(dict_key.clone(), dict_val_str.clone());
        let dict_container = Value::from(Dictionary::new(map).unwrap());

        let ak_dict = AnchoredKey::new(pod_a, key_dict);
        let ak_key_exists = AnchoredKey::new(pod_b, key_lookup_exists);

        let fact_dict = Statement::ValueOf(ak_dict.clone(), dict_container.clone());
        let fact_key_exists = Statement::ValueOf(
            ak_key_exists.clone(),
            Value::from(dict_key.name().to_string()),
        );
        let target_stmt = Statement::NotContains(ak_dict.clone(), ak_key_exists.clone());

        let (indexes, _) = setup_indexes_with_facts(&vec![
            (pod_a, fact_dict.clone()),
            (pod_b, fact_key_exists.clone()),
        ]);
        let custom_definitions = CustomDefinitions::default();
        let mut state = solver_state_with_domains(vec![]);

        let result =
            try_prove_statement(&mut state, &target_stmt, &indexes, &custom_definitions, &[]);
        assert!(
            result.is_err(),
            "Should fail because key exists in dictionary"
        );
        match result.err().unwrap() {
            ProverError::Unsatisfiable(msg) => {
                assert!(msg.contains("Could not find or derive proof"));
            }
            e => panic!("Expected Unsatisfiable, got {:?}", e),
        }
    }

    #[test]
    fn test_transitive_equality_proof() {
        // Inputs: Eq(A["foo"], B["bar"]), Eq(B["bar"], C["quux"])
        // Target: Eq(A["foo"], C["quux"])

        let pod_a = pod(1);
        let pod_b = pod(2);

        let ak_a_foo = ak(1, "foo");
        let ak_b_bar = ak(2, "bar");
        let ak_c_quux = ak(3, "quux");

        let initial_facts = vec![
            // Direct Equality statements are the required inputs
            (pod_a, Statement::Equal(ak_a_foo.clone(), ak_b_bar.clone())),
            (pod_b, Statement::Equal(ak_b_bar.clone(), ak_c_quux.clone())),
        ];

        // Destructure the result and pass &indexes
        let initial_facts_clone = initial_facts.clone(); // Clone `initial_facts` here if needed later
        let (indexes, _) = setup_indexes_with_facts(&initial_facts);
        let custom_definitions: CustomDefinitions = HashMap::new();

        // Request template for the target statement - Use wildcards
        let target_statement = Statement::Equal(ak_a_foo.clone(), ak_c_quux.clone());
        let mut state = solver_state_with_domains(vec![]); // We need state for try_prove

        // --- Call try_prove_statement directly --- (Solver logic is tested in search.rs)
        // Pass &indexes
        let result = try_prove_statement(
            &mut state,
            &target_statement,
            &indexes,
            &custom_definitions,
            &[],
        );

        // --- Assertions ---
        assert!(
            result.is_ok(),
            "try_prove_statement failed: {:?}",
            result.err()
        );
        let proof_chain = result.unwrap();

        // Check scope (should contain the two input Eq statements, added by CopyStatement)
        let expected_scope_items: HashSet<(PodId, Statement)> =
            initial_facts_clone.into_iter().collect();
        let actual_scope_items: HashSet<(PodId, Statement)> = state.scope.into_iter().collect();

        assert_eq!(
            actual_scope_items, expected_scope_items,
            "Scope mismatch. Expected {:?}, got {:?}",
            expected_scope_items, actual_scope_items
        );

        // Check proof chain for the target statement
        assert!(
            state.proof_chains.contains_key(&target_statement),
            "Proof chain for target statement {:?} not found",
            target_statement
        );
        assert_eq!(
            state.proof_chains.get(&target_statement),
            Some(&proof_chain)
        );

        assert!(
            !proof_chain.0.is_empty(),
            "Proof chain is unexpectedly empty"
        );

        // Find the final step (might not be the *last* step if CopyStatements were added after)
        let final_step = proof_chain
            .0
            .iter()
            .find(|step| step.output == target_statement)
            .expect("Final step producing target not found");

        assert_eq!(
            final_step.operation,
            OperationType::Native(NativeOperation::TransitiveEqualFromStatements)
        );
        assert_eq!(final_step.inputs.len(), 2);
        // Order of inputs for TransitiveEqual might vary depending on search path, check both:
        let input1 = Statement::Equal(ak_a_foo.clone(), ak_b_bar.clone());
        let input2 = Statement::Equal(ak_b_bar.clone(), ak_c_quux.clone());
        assert!(
            (final_step.inputs[0] == input1 && final_step.inputs[1] == input2)
                || (final_step.inputs[0] == input2 && final_step.inputs[1] == input1),
            "Inputs to final TransitiveEqual step are incorrect or in unexpected order"
        );

        // Check that the inputs to the final step also have proof chains (likely CopyStatement)
        for input_stmt in &final_step.inputs {
            assert!(
                state.proof_chains.contains_key(input_stmt),
                "Proof chain missing for input: {:?}",
                input_stmt
            );
            let input_chain = &state.proof_chains[input_stmt];
            assert_eq!(
                input_chain.0.len(),
                1,
                "Input proof chain should be single Copy step"
            );
            assert_eq!(
                input_chain.0[0].operation,
                OperationType::Native(NativeOperation::CopyStatement)
            );
        }
    }

    // --- START: New Tests for GtToNotEqual / LtToNotEqual ---

    #[test]
    fn test_try_prove_statement_neq_from_gt_base_fact() {
        let pod_a = pod(1);
        let pod_b = pod(2);
        let key_a = key("a");
        let key_b = key("b");

        let ak1 = AnchoredKey::new(pod_a, key_a.clone());
        let ak2 = AnchoredKey::new(pod_b, key_b.clone());

        // Input base fact: Gt(ak1, ak2)
        let input_gt_stmt = Statement::Gt(ak1.clone(), ak2.clone());
        // Target: NotEqual(ak1, ak2)
        let target_neq_stmt = Statement::NotEqual(ak1.clone(), ak2.clone());

        // Destructure the result and pass &indexes
        let (indexes, _) = setup_indexes_with_facts(&vec![(pod_a, input_gt_stmt.clone())]);
        let custom_definitions = CustomDefinitions::default();
        let mut state = solver_state_with_domains(vec![]);

        // Pass &indexes
        let result = try_prove_statement(
            &mut state,
            &target_neq_stmt,
            &indexes,
            &custom_definitions,
            &[],
        );
        assert!(result.is_ok(), "Proof should succeed via GtToNotEqual");
        let proof_chain = result.unwrap();

        // Expect 2 steps: CopyStatement for Gt, then GtToNotEqual
        assert_eq!(proof_chain.0.len(), 2);

        // Check step 1: CopyStatement for the Gt input
        let step1 = &proof_chain.0[0];
        assert_eq!(
            step1.operation,
            OperationType::Native(NativeOperation::CopyStatement)
        );
        assert_eq!(step1.output, input_gt_stmt);

        // Check step 2: GtToNotEqual
        let step2 = &proof_chain.0[1];
        assert_eq!(
            step2.operation,
            OperationType::Native(NativeOperation::GtToNotEqual)
        );
        assert_eq!(step2.inputs.len(), 1);
        assert_eq!(step2.inputs[0], input_gt_stmt); // Input is the Gt statement
        assert_eq!(step2.output, target_neq_stmt); // Output is the NotEqual statement

        assert!(state.proof_chains.contains_key(&target_neq_stmt));
        assert!(state.proof_chains.contains_key(&input_gt_stmt)); // Sub-proof should also be cached
        assert_eq!(state.scope.len(), 1);
        assert!(state.scope.contains(&(pod_a, input_gt_stmt))); // Scope contains original base fact
    }

    #[test]
    fn test_try_prove_statement_neq_from_lt_base_fact() {
        let pod_a = pod(1);
        let pod_b = pod(2);
        let key_a = key("a");
        let key_b = key("b");

        let ak1 = AnchoredKey::new(pod_a, key_a.clone());
        let ak2 = AnchoredKey::new(pod_b, key_b.clone());

        let input_lt_stmt = Statement::Lt(ak1.clone(), ak2.clone());
        let target_neq_stmt = Statement::NotEqual(ak1.clone(), ak2.clone());

        let (indexes, _) = setup_indexes_with_facts(&vec![(pod_a, input_lt_stmt.clone())]);
        let custom_definitions = CustomDefinitions::default();
        let mut state = solver_state_with_domains(vec![]);

        // Pass &indexes
        let result = try_prove_statement(
            &mut state,
            &target_neq_stmt,
            &indexes,
            &custom_definitions,
            &[],
        );
        assert!(result.is_ok(), "Proof should succeed via LtToNotEqual");
        let proof_chain = result.unwrap();

        // Expect 2 steps: CopyStatement for Lt, then LtToNotEqual
        assert_eq!(proof_chain.0.len(), 2);

        // Check step 1: CopyStatement for the Lt input
        let step1 = &proof_chain.0[0];
        assert_eq!(
            step1.operation,
            OperationType::Native(NativeOperation::CopyStatement)
        );
        assert_eq!(step1.output, input_lt_stmt);

        // Check step 2: LtToNotEqual
        let step2 = &proof_chain.0[1];
        assert_eq!(
            step2.operation,
            OperationType::Native(NativeOperation::LtToNotEqual)
        );
        assert_eq!(step2.inputs.len(), 1);
        assert_eq!(step2.inputs[0], input_lt_stmt); // Input is the Lt statement
        assert_eq!(step2.output, target_neq_stmt); // Output is the NotEqual statement

        assert!(state.proof_chains.contains_key(&target_neq_stmt));
        assert!(state.proof_chains.contains_key(&input_lt_stmt)); // Sub-proof should also be cached
        assert_eq!(state.scope.len(), 1);
        assert!(state.scope.contains(&(pod_a, input_lt_stmt))); // Scope contains original base fact
    }

    #[test]
    fn test_try_prove_statement_neq_fails_when_gt_lt_unprovable() {
        let pod_a = pod(1);
        let pod_b = pod(2);
        let key_a = key("a");
        let key_b = key("b");

        let ak1 = AnchoredKey::new(pod_a, key_a.clone());
        let ak2 = AnchoredKey::new(pod_b, key_b.clone());

        // Target: NotEqual(ak1, ak2)
        let target_neq_stmt = Statement::NotEqual(ak1.clone(), ak2.clone());

        // No facts provided, so Gt/Lt cannot be proven
        // Destructure the result and pass &indexes
        let (indexes, _) = setup_indexes_with_facts(&[]);
        let custom_definitions = CustomDefinitions::default();
        let mut state = solver_state_with_domains(vec![]);

        // Pass &indexes
        let result = try_prove_statement(
            &mut state,
            &target_neq_stmt,
            &indexes,
            &custom_definitions,
            &[],
        );
        assert!(result.is_err());
        match result.err().unwrap() {
            ProverError::Unsatisfiable(msg) => {
                assert!(msg.contains("Could not find or derive proof"));
                assert!(msg.contains(&format!("{:?}", target_neq_stmt)));
            }
            e => panic!("Expected Unsatisfiable, got {:?}", e),
        }
    }

    #[test]
    fn test_try_prove_statement_neq_from_entries_takes_precedence() {
        // Scenario: We have ValueOf facts that prove NEq AND a Gt base fact.
        // NEqFromEntries should be tried first and succeed.

        let pod_a = pod(1);
        let pod_b = pod(2);
        let key_a = key("a");
        let key_b = key("b");
        let val_20 = val(20);
        let val_10 = val(10);

        let ak1 = AnchoredKey::new(pod_a, key_a.clone());
        let ak2 = AnchoredKey::new(pod_b, key_b.clone());

        let fact_a = Statement::ValueOf(ak1.clone(), val_20.clone());
        let fact_b = Statement::ValueOf(ak2.clone(), val_10.clone());
        let input_gt_stmt = Statement::Gt(ak1.clone(), ak2.clone()); // Also true and a base fact
        let target_neq_stmt = Statement::NotEqual(ak1.clone(), ak2.clone());

        // Destructure the result and pass &indexes
        let facts_vec = vec![
            (pod_a, fact_a.clone()),
            (pod_b, fact_b.clone()),
            (pod_a, input_gt_stmt.clone()), // Add the Gt base fact
        ];
        let (indexes, _) = setup_indexes_with_facts(&facts_vec);
        let custom_definitions = CustomDefinitions::default();
        let mut state = solver_state_with_domains(vec![]);

        // Pass &indexes
        let result = try_prove_statement(
            &mut state,
            &target_neq_stmt,
            &indexes,
            &custom_definitions,
            &[],
        );
        assert!(result.is_ok(), "Proof should succeed");
        let proof_chain = result.unwrap();

        // Expect 1 step: NotEqualFromEntries (should be found before GtToNotEqual)
        assert_eq!(proof_chain.0.len(), 1);
        let step1 = &proof_chain.0[0];
        assert_eq!(
            step1.operation,
            OperationType::Native(NativeOperation::NotEqualFromEntries)
        );
        assert_eq!(step1.inputs.len(), 2);
        assert!(step1.inputs.contains(&fact_a));
        assert!(step1.inputs.contains(&fact_b));
        assert_eq!(step1.output, target_neq_stmt);

        assert!(state.proof_chains.contains_key(&target_neq_stmt));
        assert_eq!(state.scope.len(), 2);
        assert!(state.scope.contains(&(pod_a, fact_a)));
        assert!(state.scope.contains(&(pod_b, fact_b)));
        // Gt statement should NOT be in scope because it wasn't used for this proof path
        assert!(!state.scope.contains(&(pod_a, input_gt_stmt)));
    }

    // --- END: New Tests for GtToNotEqual / LtToNotEqual ---

    // --- START: Custom Predicate Tests ---

    /// Helper function to create a CustomPredicateRef from a batch and index.
    fn build_custom_ref(batch: Arc<CustomPredicateBatch>, index: usize) -> CustomPredicateRef {
        CustomPredicateRef { batch, index }
    }

    /// Tests successful evaluation of a custom predicate with AND logic.
    /// The predicate requires both a Gt and Equal statement to be satisfied.
    /// This verifies that:
    /// 1. Custom predicate definitions are correctly interpreted
    /// 2. Multiple statement templates are properly evaluated
    /// 3. AND logic correctly requires all conditions to be met
    #[test]
    fn test_try_prove_custom_and_success() {
        let pod_target = pod(1);
        let pod_const1 = pod(10);
        let pod_const2 = pod(11);

        let val_key = key("val");
        let key_key = key("key");
        let const_val_key = key("const_val");
        let const_key_key = key("const_key");

        let fact_target_val = Statement::ValueOf(ak(1, "val"), val(10));
        let fact_target_key = Statement::ValueOf(ak(1, "key"), Value::from("hello"));
        let fact_const_val = Statement::ValueOf(ak(10, "const_val"), val(5));
        let fact_const_key = Statement::ValueOf(ak(11, "const_key"), Value::from("hello"));

        let facts = vec![
            (pod_target, fact_target_val.clone()),
            (pod_target, fact_target_key.clone()),
            (pod_const1, fact_const_val.clone()),
            (pod_const2, fact_const_key.clone()),
        ];
        let (indexes, params) = setup_indexes_with_facts(&facts);

        let custom_pred_index = 0;
        let wc_a = wc("A", 0);

        // Define templates for Gt and Equal conditions
        let sub_tmpl_gt = StatementTmpl {
            pred: Predicate::Native(NativePredicate::Gt),
            args: vec![
                StatementTmplArg::Key(wc_a.clone(), KeyOrWildcard::Key(val_key.clone())),
                StatementTmplArg::Key(
                    Wildcard {
                        index: 100,
                        name: "P_CONST_VAL".to_string(),
                    },
                    KeyOrWildcard::Key(const_val_key.clone()),
                ),
            ],
        };
        let sub_tmpl_eq = StatementTmpl {
            pred: Predicate::Native(NativePredicate::Equal),
            args: vec![
                StatementTmplArg::Key(wc_a.clone(), KeyOrWildcard::Key(key_key.clone())),
                StatementTmplArg::Key(
                    Wildcard {
                        index: 101,
                        name: "P_CONST_KEY".to_string(),
                    },
                    KeyOrWildcard::Key(const_key_key.clone()),
                ),
            ],
        };

        let custom_pred_def = CustomPredicate {
            name: "TestAndPredicate".to_string(),
            args_len: 1,
            statements: vec![sub_tmpl_gt.clone(), sub_tmpl_eq.clone()],
            conjunction: true,
        };

        let custom_batch = Arc::new(CustomPredicateBatch {
            name: "TestAndBatch".to_string(),
            predicates: vec![custom_pred_def.clone()],
        });
        let custom_pred_ref = build_custom_ref(custom_batch.clone(), custom_pred_index);
        let custom_pred_variant = Predicate::Custom(custom_pred_ref.clone());

        let mut custom_definitions = CustomDefinitions::new();
        let key = custom_pred_variant.to_fields(&params);
        custom_definitions.insert(key, (custom_pred_def, custom_batch.clone()));

        let target_stmt = Statement::Custom(
            custom_pred_ref.clone(),
            vec![WildcardValue::PodId(pod_target)],
        );

        let mut state = solver_state_with_domains(vec![
            (
                Wildcard {
                    index: 100,
                    name: "P_CONST_VAL".to_string(),
                },
                HashSet::from([cv_pod(10)]),
                ExpectedType::Pod,
            ),
            (
                Wildcard {
                    index: 101,
                    name: "P_CONST_KEY".to_string(),
                },
                HashSet::from([cv_pod(11)]),
                ExpectedType::Pod,
            ),
        ]);

        let result =
            try_prove_statement(&mut state, &target_stmt, &indexes, &custom_definitions, &[]);

        assert!(result.is_ok(), "Proof failed: {:?}", result.err());
        let proof_chain = result.unwrap();

        let expected_sub_gt = Statement::Gt(ak(1, "val"), ak(10, "const_val"));
        let expected_sub_eq = Statement::Equal(ak(1, "key"), ak(11, "const_key"));

        assert!(!proof_chain.0.is_empty());
        let final_step = proof_chain.0.last().unwrap();
        assert_eq!(final_step.operation, OperationType::Custom(custom_pred_ref));
        assert_eq!(final_step.output, target_stmt);
        assert_eq!(final_step.inputs.len(), 2);
        assert!(final_step.inputs.contains(&expected_sub_gt));
        assert!(final_step.inputs.contains(&expected_sub_eq));

        assert!(state.proof_chains.contains_key(&expected_sub_gt));
        assert!(state.proof_chains.contains_key(&expected_sub_eq));

        assert!(state.scope.contains(&(pod_target, fact_target_val)));
        assert!(state.scope.contains(&(pod_target, fact_target_key)));
        assert!(state.scope.contains(&(pod_const1, fact_const_val)));
        assert!(state.scope.contains(&(pod_const2, fact_const_key)));
    }

    /// Tests successful evaluation of a custom predicate with OR logic.
    /// The predicate requires either a Gt or Equal statement to be satisfied.
    /// This verifies that:
    /// 1. OR logic correctly succeeds when any condition is met
    /// 2. Only the successful branch's statements are included in the proof
    /// 3. The proof chain contains only the necessary operations
    #[test]
    fn test_try_prove_custom_or_first_branch_success() {
        let pod_target = pod(1);
        let pod_const1 = pod(10);

        let val_key = key("val");
        let const_val_key = key("const_val");

        let fact_target_val = Statement::ValueOf(ak(1, "val"), val(10));
        let fact_const_val = Statement::ValueOf(ak(10, "const_val"), val(5));

        let facts = vec![
            (pod_target, fact_target_val.clone()),
            (pod_const1, fact_const_val.clone()),
            (
                pod_target,
                Statement::ValueOf(ak(1, "key"), Value::from("hello")),
            ),
            (
                pod(11),
                Statement::ValueOf(ak(11, "const_key"), Value::from("different")),
            ),
        ];
        let (indexes, params) = setup_indexes_with_facts(&facts);

        let custom_pred_index = 0;
        let wc_a = wc("A", 0);

        let sub_tmpl_gt = StatementTmpl {
            pred: Predicate::Native(NativePredicate::Gt),
            args: vec![
                StatementTmplArg::Key(wc_a.clone(), KeyOrWildcard::Key(val_key)),
                StatementTmplArg::Key(
                    Wildcard {
                        index: 100,
                        name: "P_CONST_VAL".to_string(),
                    },
                    KeyOrWildcard::Key(const_val_key),
                ),
            ],
        };
        let sub_tmpl_eq = StatementTmpl {
            pred: Predicate::Native(NativePredicate::Equal),
            args: vec![
                StatementTmplArg::Key(wc_a.clone(), KeyOrWildcard::Key(key("key"))),
                StatementTmplArg::Key(
                    Wildcard {
                        index: 101,
                        name: "P_CONST_KEY".to_string(),
                    },
                    KeyOrWildcard::Key(key("const_key")),
                ),
            ],
        };

        let custom_pred_def = CustomPredicate {
            name: "TestOrPredicate".to_string(),
            args_len: 1,
            statements: vec![sub_tmpl_gt.clone(), sub_tmpl_eq.clone()],
            conjunction: false,
        };

        let custom_batch = Arc::new(CustomPredicateBatch {
            name: "TestOrBatch".to_string(),
            predicates: vec![custom_pred_def.clone()],
        });
        let custom_pred_ref = build_custom_ref(custom_batch.clone(), custom_pred_index);
        let custom_pred_variant = Predicate::Custom(custom_pred_ref.clone());

        let custom_definitions = setup_custom_definitions_for_test(
            vec![(
                custom_pred_variant.clone(),
                custom_pred_def,
                custom_batch.clone(),
            )],
            &params,
        );

        let target_stmt = Statement::Custom(
            custom_pred_ref.clone(),
            vec![WildcardValue::PodId(pod_target)],
        );

        let mut state = solver_state_with_domains(vec![
            (
                Wildcard {
                    index: 100,
                    name: "P_CONST_VAL".to_string(),
                },
                HashSet::from([cv_pod(10)]),
                ExpectedType::Pod,
            ),
            (
                Wildcard {
                    index: 101,
                    name: "P_CONST_KEY".to_string(),
                },
                HashSet::from([cv_pod(11)]),
                ExpectedType::Pod,
            ),
        ]);

        let result =
            try_prove_statement(&mut state, &target_stmt, &indexes, &custom_definitions, &[]);

        assert!(result.is_ok(), "Proof failed for OR: {:?}", result.err());
        let proof_chain = result.unwrap();

        let expected_sub_gt = Statement::Gt(ak(1, "val"), ak(10, "const_val"));

        assert!(!proof_chain.0.is_empty());
        let final_step = proof_chain.0.last().unwrap();
        assert_eq!(final_step.operation, OperationType::Custom(custom_pred_ref));
        assert_eq!(final_step.output, target_stmt);
        assert_eq!(final_step.inputs.len(), 1);
        assert_eq!(final_step.inputs[0], expected_sub_gt);

        assert!(state.proof_chains.contains_key(&expected_sub_gt));
        let expected_sub_eq_fail = Statement::Equal(ak(1, "key"), ak(11, "const_key"));
        assert!(!state.proof_chains.contains_key(&expected_sub_eq_fail));

        assert!(state.scope.contains(&(pod_target, fact_target_val)));
        assert!(state.scope.contains(&(pod_const1, fact_const_val)));
        assert!(!state.scope.contains(&(
            pod_target,
            Statement::ValueOf(ak(1, "key"), Value::from("hello"))
        )));
    }

    /// Tests that a custom predicate with AND logic fails when a required sub-statement cannot be proven.
    /// This verifies that:
    /// 1. AND logic correctly fails when any condition fails
    /// 2. The error propagates from the failed sub-statement
    /// 3. No proof chains are generated for the target statement
    #[test]
    fn test_try_prove_custom_and_fail_sub_proof() {
        let pod_target = pod(1);
        let pod_const2 = pod(11);

        let val_key = key("val");
        let key_key = key("key");
        let const_val_key = key("const_val");
        let const_key_key = key("const_key");

        let fact_target_val = Statement::ValueOf(ak(1, "val"), val(10));
        let fact_target_key = Statement::ValueOf(ak(1, "key"), Value::from("hello"));
        let fact_const_key = Statement::ValueOf(ak(11, "const_key"), Value::from("hello"));

        let facts = vec![
            (pod_target, fact_target_val.clone()),
            (pod_target, fact_target_key.clone()),
            (pod_const2, fact_const_key.clone()),
        ];
        let (indexes, params) = setup_indexes_with_facts(&facts);

        let custom_pred_index = 0;
        let wc_a = wc("A", 0);

        let sub_tmpl_gt = StatementTmpl {
            pred: Predicate::Native(NativePredicate::Gt),
            args: vec![
                StatementTmplArg::Key(wc_a.clone(), KeyOrWildcard::Key(val_key.clone())),
                StatementTmplArg::Key(
                    Wildcard {
                        index: 100,
                        name: "P_CONST_VAL".to_string(),
                    },
                    KeyOrWildcard::Key(const_val_key.clone()),
                ),
            ],
        };
        let sub_tmpl_eq = StatementTmpl {
            pred: Predicate::Native(NativePredicate::Equal),
            args: vec![
                StatementTmplArg::Key(wc_a.clone(), KeyOrWildcard::Key(key_key.clone())),
                StatementTmplArg::Key(
                    Wildcard {
                        index: 101,
                        name: "P_CONST_KEY".to_string(),
                    },
                    KeyOrWildcard::Key(const_key_key.clone()),
                ),
            ],
        };

        let custom_pred_def = CustomPredicate {
            name: "TestAndPredicateFail".to_string(),
            args_len: 1,
            statements: vec![sub_tmpl_gt.clone(), sub_tmpl_eq.clone()],
            conjunction: true,
        };
        let custom_batch = Arc::new(CustomPredicateBatch {
            name: "TestAndFailBatch".to_string(),
            predicates: vec![custom_pred_def.clone()],
        });
        let custom_pred_ref = build_custom_ref(custom_batch.clone(), custom_pred_index);
        let custom_pred_variant = Predicate::Custom(custom_pred_ref.clone());

        let custom_definitions = setup_custom_definitions_for_test(
            vec![(
                custom_pred_variant.clone(),
                custom_pred_def,
                custom_batch.clone(),
            )],
            &params,
        );

        let target_stmt = Statement::Custom(
            custom_pred_ref.clone(),
            vec![WildcardValue::PodId(pod_target)],
        );

        let mut state = solver_state_with_domains(vec![
            (
                Wildcard {
                    index: 100,
                    name: "P_CONST_VAL".to_string(),
                },
                HashSet::from([cv_pod(10)]),
                ExpectedType::Pod,
            ),
            (
                Wildcard {
                    index: 101,
                    name: "P_CONST_KEY".to_string(),
                },
                HashSet::from([cv_pod(11)]),
                ExpectedType::Pod,
            ),
        ]);

        let result =
            try_prove_statement(&mut state, &target_stmt, &indexes, &custom_definitions, &[]);

        assert!(result.is_err());
        match result.err().unwrap() {
            ProverError::Unsatisfiable(msg) => {
                assert!(
                    msg.contains("Could not find or derive proof for: Gt("),
                    "Expected Unsatisfiable from Gt sub-proof failure, got: {}",
                    msg
                );
            }
            e => panic!("Expected Unsatisfiable error, got {:?}", e),
        }

        assert!(!state.proof_chains.contains_key(&target_stmt));
    }

    /// Tests that a custom predicate with OR logic fails when all branches fail.
    /// This verifies that:
    /// 1. OR logic correctly fails when all conditions fail
    /// 2. The error propagates from the failed branches
    /// 3. No proof chains are generated for the target statement
    #[test]
    fn test_try_prove_custom_or_fail_all_branches() {
        let pod_target = pod(1);
        let pod_const1 = pod(10);
        let pod_const2 = pod(11);

        let val_key = key("val");
        let key_key = key("key");
        let const_val_key = key("const_val");
        let const_key_key = key("const_key");

        // Base facts - Set up so BOTH branches fail
        // Gt(ak(1,"val"), ak(10,"const_val")) fails because 5 !> 10
        let fact_target_val = Statement::ValueOf(ak(1, "val"), val(5));
        let fact_const_val = Statement::ValueOf(ak(10, "const_val"), val(10));
        // Eq(ak(1,"key"), ak(11,"const_key")) fails because "hello" != "world"
        let fact_target_key = Statement::ValueOf(ak(1, "key"), Value::from("hello"));
        let fact_const_key = Statement::ValueOf(ak(11, "const_key"), Value::from("world"));

        let facts = vec![
            (pod_target, fact_target_val.clone()),
            (pod_const1, fact_const_val.clone()),
            (pod_target, fact_target_key.clone()),
            (pod_const2, fact_const_key.clone()),
        ];
        let (indexes, params) = setup_indexes_with_facts(&facts); // Clone facts here

        // --- Custom Predicate Definition (OR) ---
        let custom_pred_index = 0;
        let wc_a = wc("A", 0); // Public Arg 0: PodId

        let sub_tmpl_gt = StatementTmpl {
            // First branch (will fail)
            pred: Predicate::Native(NativePredicate::Gt),
            args: vec![
                StatementTmplArg::Key(wc_a.clone(), KeyOrWildcard::Key(val_key.clone())),
                StatementTmplArg::Key(
                    Wildcard {
                        index: 100,
                        name: "P_CONST_VAL".to_string(),
                    },
                    KeyOrWildcard::Key(const_val_key.clone()),
                ),
            ],
        };
        let sub_tmpl_eq = StatementTmpl {
            // Second branch (will fail)
            pred: Predicate::Native(NativePredicate::Equal),
            args: vec![
                StatementTmplArg::Key(wc_a.clone(), KeyOrWildcard::Key(key_key.clone())),
                StatementTmplArg::Key(
                    Wildcard {
                        index: 101,
                        name: "P_CONST_KEY".to_string(),
                    },
                    KeyOrWildcard::Key(const_key_key.clone()),
                ),
            ],
        };

        let custom_pred_def = CustomPredicate {
            name: "TestOrFailPredicate".to_string(),
            args_len: 1,
            statements: vec![sub_tmpl_gt.clone(), sub_tmpl_eq.clone()],
            conjunction: false, // OR
        };
        let custom_batch = Arc::new(CustomPredicateBatch {
            name: "TestOrFailBatch".to_string(),
            predicates: vec![custom_pred_def.clone()],
        });
        let custom_pred_ref = build_custom_ref(custom_batch.clone(), custom_pred_index);
        let custom_pred_variant = Predicate::Custom(custom_pred_ref.clone());

        // Use the new helper
        let custom_definitions = setup_custom_definitions_for_test(
            vec![(
                custom_pred_variant.clone(),
                custom_pred_def,
                custom_batch.clone(),
            )],
            &params,
        );
        // --- End Definition ---

        // Target Statement to prove
        let target_stmt = Statement::Custom(
            custom_pred_ref.clone(),
            vec![WildcardValue::PodId(pod_target)], // Provide concrete PodId for ?A
        );

        let mut state = solver_state_with_domains(vec![
            // Need domains for private wildcards in *both* branches
            (
                Wildcard {
                    index: 100,
                    name: "P_CONST_VAL".to_string(),
                },
                HashSet::from([cv_pod(10)]),
                ExpectedType::Pod,
            ),
            (
                Wildcard {
                    index: 101,
                    name: "P_CONST_KEY".to_string(),
                },
                HashSet::from([cv_pod(11)]),
                ExpectedType::Pod,
            ),
        ]);

        // Pass &indexes
        let result =
            try_prove_statement(&mut state, &target_stmt, &indexes, &custom_definitions, &[]);

        assert!(
            result.is_err(),
            "Proof should fail because both OR branches fail"
        );
        match result.err().unwrap() {
            ProverError::Unsatisfiable(msg) => {
                // The error should be the generic failure for the Custom statement,
                // as both internal branches failed.
                assert!(
                    msg.contains("Could not find or derive proof for: Custom("),
                    "Expected Unsatisfiable for Custom statement, got: {}",
                    msg
                );
                // Check that the specific target statement is mentioned
                assert!(
                    msg.contains(&format!("{:?}", target_stmt)),
                    "Error message should contain the target statement: {}",
                    msg
                );
            }
            e => panic!("Expected Unsatisfiable error, got {:?}", e),
        }
        // Check state - no proof chain for the target should be added
        assert!(!state.proof_chains.contains_key(&target_stmt));
    }

    /// Tests evaluation of nested custom predicates with wildcard aliasing.
    /// This test verifies that:
    /// 1. Nested predicates correctly share wildcards between outer and inner scopes
    /// 2. Multiple conditions across different nesting levels are properly evaluated
    /// 3. Proof chains correctly include all necessary intermediate steps
    #[test]
    fn test_try_prove_nested_custom_predicates() {
        let pod_a = pod(1);
        let pod_b = pod(2);
        let pod_c = pod(3);
        let pod_d = pod(4);
        let pod_m = pod(5);
        let pod_n = pod(6);

        let val_key = key("val");
        let key_key = key("key");

        let fact_a_val = Statement::ValueOf(ak(1, "val"), val(100));
        let fact_b_val = Statement::ValueOf(ak(2, "val"), val(50));
        let fact_c_key = Statement::ValueOf(ak(3, "key"), Value::from("same_key"));
        let fact_d_key = Statement::ValueOf(ak(4, "key"), Value::from("same_key"));
        let fact_m_val = Statement::ValueOf(ak(5, "val"), val(10));
        let fact_n_val = Statement::ValueOf(ak(6, "val"), val(20));

        let facts = vec![
            (pod_a, fact_a_val.clone()),
            (pod_b, fact_b_val.clone()),
            (pod_c, fact_c_key.clone()),
            (pod_d, fact_d_key.clone()),
            (pod_m, fact_m_val.clone()),
            (pod_n, fact_n_val.clone()),
        ];
        let (indexes, params) = setup_indexes_with_facts(&facts);

        // Define inner predicate that requires both Gt and Equal conditions
        let wc_x = wc("X", 0);
        let wc_y = wc("Y", 1);
        let wc_z = wc("Z", 2);
        let wc_w = wc("W", 3);

        let inner_tmpl_gt = StatementTmpl {
            pred: Predicate::Native(NativePredicate::Gt),
            args: vec![
                StatementTmplArg::Key(wc_x.clone(), KeyOrWildcard::Key(val_key.clone())),
                StatementTmplArg::Key(wc_y.clone(), KeyOrWildcard::Key(val_key.clone())),
            ],
        };
        let inner_tmpl_eq = StatementTmpl {
            pred: Predicate::Native(NativePredicate::Equal),
            args: vec![
                StatementTmplArg::Key(wc_z.clone(), KeyOrWildcard::Key(key_key.clone())),
                StatementTmplArg::Key(wc_w.clone(), KeyOrWildcard::Key(key_key.clone())),
            ],
        };
        let inner_pred_def = CustomPredicate {
            name: "InnerP".to_string(),
            args_len: 4,
            statements: vec![inner_tmpl_gt.clone(), inner_tmpl_eq.clone()],
            conjunction: true,
        };

        // Define outer predicate that combines inner predicate with Lt condition
        let wc_a = wc("A", 0);
        let wc_b = wc("B", 1);
        let wc_c = wc("C", 2);
        let wc_d = wc("D", 3);
        let wc_m = wc("M", 4);
        let wc_n = wc("N", 5);

        let outer_tmpl_inner = StatementTmpl {
            pred: Predicate::BatchSelf(0),
            args: vec![
                StatementTmplArg::WildcardLiteral(wc_a.clone()),
                StatementTmplArg::WildcardLiteral(wc_b.clone()),
                StatementTmplArg::WildcardLiteral(wc_c.clone()),
                StatementTmplArg::WildcardLiteral(wc_d.clone()),
            ],
        };
        let outer_tmpl_lt = StatementTmpl {
            pred: Predicate::Native(NativePredicate::Lt),
            args: vec![
                StatementTmplArg::Key(wc_m.clone(), KeyOrWildcard::Key(val_key.clone())),
                StatementTmplArg::Key(wc_n.clone(), KeyOrWildcard::Key(val_key.clone())),
            ],
        };
        let outer_pred_def = CustomPredicate {
            name: "OuterP".to_string(),
            args_len: 6,
            statements: vec![outer_tmpl_inner.clone(), outer_tmpl_lt.clone()],
            conjunction: true,
        };

        let custom_batch = Arc::new(CustomPredicateBatch {
            name: "NestedBatch".to_string(),
            predicates: vec![inner_pred_def.clone(), outer_pred_def.clone()],
        });
        let inner_pred_ref = build_custom_ref(custom_batch.clone(), 0);
        let outer_pred_ref = build_custom_ref(custom_batch.clone(), 1);

        let custom_definitions = setup_custom_definitions_for_test(
            vec![
                (
                    Predicate::Custom(inner_pred_ref.clone()),
                    inner_pred_def.clone(),
                    custom_batch.clone(),
                ),
                (
                    Predicate::Custom(outer_pred_ref.clone()),
                    outer_pred_def.clone(),
                    custom_batch.clone(),
                ),
            ],
            &params,
        );

        let target_stmt = Statement::Custom(
            outer_pred_ref.clone(),
            vec![
                WildcardValue::PodId(pod_a),
                WildcardValue::PodId(pod_b),
                WildcardValue::PodId(pod_c),
                WildcardValue::PodId(pod_d),
                WildcardValue::PodId(pod_m),
                WildcardValue::PodId(pod_n),
            ],
        );

        let mut state = solver_state_with_domains(vec![]);

        let result =
            try_prove_statement(&mut state, &target_stmt, &indexes, &custom_definitions, &[]);

        assert!(result.is_ok(), "Nested proof failed: {:?}", result.err());
        let proof_chain = result.unwrap();

        let expected_inner_gt = Statement::Gt(ak(1, "val"), ak(2, "val"));
        let expected_inner_eq = Statement::Equal(ak(3, "key"), ak(4, "key"));
        let expected_outer_lt = Statement::Lt(ak(5, "val"), ak(6, "val"));
        let expected_inner_custom = Statement::Custom(
            inner_pred_ref.clone(),
            vec![
                WildcardValue::PodId(pod_a),
                WildcardValue::PodId(pod_b),
                WildcardValue::PodId(pod_c),
                WildcardValue::PodId(pod_d),
            ],
        );

        assert!(!proof_chain.0.is_empty());
        let final_outer_step = proof_chain.0.last().unwrap();
        assert_eq!(
            final_outer_step.operation,
            OperationType::Custom(outer_pred_ref.clone())
        );
        assert_eq!(final_outer_step.output, target_stmt);
        assert_eq!(final_outer_step.inputs.len(), 2);
        assert!(final_outer_step.inputs.contains(&expected_inner_custom));
        assert!(final_outer_step.inputs.contains(&expected_outer_lt));

        assert!(state.proof_chains.contains_key(&expected_inner_custom));
        assert!(state.proof_chains.contains_key(&expected_outer_lt));

        let inner_proof_chain = &state.proof_chains[&expected_inner_custom];
        assert!(!inner_proof_chain.0.is_empty());
        let final_inner_step = inner_proof_chain.0.last().unwrap();
        assert_eq!(
            final_inner_step.operation,
            OperationType::Custom(inner_pred_ref.clone())
        );
        assert_eq!(final_inner_step.output, expected_inner_custom);
        assert_eq!(final_inner_step.inputs.len(), 2);
        assert!(final_inner_step.inputs.contains(&expected_inner_gt));
        assert!(final_inner_step.inputs.contains(&expected_inner_eq));

        assert!(state.proof_chains.contains_key(&expected_inner_gt));
        assert!(state.proof_chains.contains_key(&expected_inner_eq));
        assert!(state.proof_chains.contains_key(&expected_outer_lt));

        assert!(state.scope.contains(&(pod_a, fact_a_val)));
        assert!(state.scope.contains(&(pod_b, fact_b_val)));
        assert!(state.scope.contains(&(pod_c, fact_c_key)));
        assert!(state.scope.contains(&(pod_d, fact_d_key)));
        assert!(state.scope.contains(&(pod_m, fact_m_val)));
        assert!(state.scope.contains(&(pod_n, fact_n_val)));
        assert_eq!(state.scope.len(), 6);
    }

    // --- END: Custom Predicate Tests ---
}
