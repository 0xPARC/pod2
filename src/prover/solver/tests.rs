#![cfg(test)]
use std::collections::{HashMap, HashSet};

use super::{
    proof::try_prove_statement,
    pruning::{
        prune_by_literal_key, prune_by_literal_origin, prune_by_literal_value, prune_by_type,
        prune_initial_domains,
    },
    types::{Constraint, ExpectedType},
    SolverState,
};
use crate::{
    middleware::{
        self, containers::Dictionary, AnchoredKey, Key, KeyOrWildcard, NativeOperation,
        NativePredicate, OperationType, PodId, Predicate, Statement, StatementTmpl,
        StatementTmplArg, Value, Wildcard,
    },
    prover::{
        error::ProverError,
        indexing::ProverIndexes,
        types::{ConcreteValue, CustomDefinitions, ProofChain, ProofSolution},
    },
};

// Helper functions for creating test data (wc, pod, key, val, ak, cv_pod, cv_key, cv_val)
fn wc(name: &str, index: usize) -> Wildcard {
    Wildcard::new(name.to_string(), index)
}

fn pod(id: u64) -> PodId {
    PodId(middleware::hash_str(&id.to_string()))
}

fn key(name: &str) -> Key {
    Key::new(name.to_string())
}

fn val(v: i64) -> Value {
    Value::from(v)
}

fn ak(pod_id: u64, key_name: &str) -> AnchoredKey {
    AnchoredKey::new(pod(pod_id), key(key_name))
}

fn cv_pod(id: u64) -> ConcreteValue {
    ConcreteValue::Pod(pod(id))
}

fn cv_key(name: &str) -> ConcreteValue {
    ConcreteValue::Key(name.to_string())
}

fn cv_val(v: i64) -> ConcreteValue {
    ConcreteValue::Val(Value::from(v))
}

fn solver_state_with_domains(
    domains: Vec<(Wildcard, HashSet<ConcreteValue>, ExpectedType)>,
) -> SolverState {
    SolverState {
        domains: domains
            .into_iter()
            .map(|(wc, dom, et)| (wc, (dom, et)))
            .collect(),
        constraints: vec![],
        proof_chains: HashMap::new(),
        scope: HashSet::new(),
    }
}

fn dummy_prover_indexes() -> ProverIndexes {
    ProverIndexes::new(middleware::Params::default())
}

// Helper to create ProverIndexes with specific base facts for testing try_prove_statement
fn setup_indexes_with_facts(facts: Vec<(PodId, Statement)>) -> ProverIndexes {
    let params = middleware::Params::default();
    // Use the main build method which populates all necessary indexes, including value_map
    ProverIndexes::build(params, &facts)
}

#[test]
fn test_try_prove_statement_copy_base_fact() {
    let pod_a = pod(1);
    let key_foo = key("foo");
    let val_10 = val(10);
    let base_fact_stmt =
        Statement::ValueOf(AnchoredKey::new(pod_a, key_foo.clone()), val_10.clone());
    let base_fact_prover: Statement = base_fact_stmt.clone();
    let indexes = setup_indexes_with_facts(vec![(pod_a, base_fact_stmt.clone())]);
    let custom_definitions = CustomDefinitions::default();
    let mut state = solver_state_with_domains(vec![]);

    let result = try_prove_statement(&mut state, &base_fact_prover, &indexes, &custom_definitions);
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

    let result_again =
        try_prove_statement(&mut state, &base_fact_prover, &indexes, &custom_definitions);
    assert!(result_again.is_ok(), "Second proof should succeed");
    assert_eq!(
        result_again.unwrap(),
        proof_chain,
        "Should return the cached proof chain"
    );
    assert_eq!(state.scope.len(), 1, "Scope size should not change");
}

#[test]
fn test_try_prove_statement_not_found() {
    let pod_a = pod(1);
    let key_foo = key("foo");
    let val_10 = val(10);
    let target_stmt = Statement::ValueOf(AnchoredKey::new(pod_a, key_foo.clone()), val_10.clone());
    let target_prover: Statement = target_stmt.clone();

    let indexes = setup_indexes_with_facts(vec![]);
    let custom_definitions = CustomDefinitions::default();
    let mut state = solver_state_with_domains(vec![]);

    let result = try_prove_statement(&mut state, &target_prover, &indexes, &custom_definitions);

    assert!(result.is_err(), "Proof should fail");
    match result.err().unwrap() {
        // Check for Unsatisfiable error
        ProverError::Unsatisfiable(msg) => {
            assert!(
                msg.contains("Could not find or derive proof"),
                "Error message mismatch"
            );
            // Use debug formatting for comparison
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

#[test]
fn test_try_prove_statement_already_proven() {
    let pod_a = pod(1);
    let key_foo = key("foo");
    let val_10 = val(10);
    let target_stmt = Statement::ValueOf(AnchoredKey::new(pod_a, key_foo.clone()), val_10.clone());
    let target_prover: Statement = target_stmt.clone();

    let indexes = setup_indexes_with_facts(vec![]);
    let custom_definitions = CustomDefinitions::default();
    let mut state = solver_state_with_domains(vec![]);

    // Instantiate dummy chain as tuple struct
    let dummy_chain = ProofChain(vec![]);
    state
        .proof_chains
        .insert(target_prover.clone(), dummy_chain.clone());

    let result = try_prove_statement(&mut state, &target_prover, &indexes, &custom_definitions);

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

// --- Tests for Pruning Functions --- (Keep existing tests)
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
    let p3 = pod(3);
    let k_foo = key("foo");
    let k_bar = key("bar");

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
    let k_foo = key("foo");
    let k_bar = key("bar");
    let k_baz = key("baz");

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
    let p2 = pod(2);
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

    let result = prune_initial_domains(&mut state, &indexes);
    assert!(result.is_ok());

    // Expected outcome after propagation:
    // - LiteralKey removes p2 from w_pod's domain (only p1 has "foo")
    // - LiteralOrigin removes "bar" from w_key's domain (p1 doesn't have "bar")
    assert_eq!(state.domains[&w_pod].0, HashSet::from([cv_pod(1)]));
    assert_eq!(state.domains[&w_key].0, HashSet::from([cv_key("foo")]));
}

// --- Tests for try_prove_statement ---

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

    let indexes = setup_indexes_with_facts(vec![(pod_a, fact1.clone()), (pod_b, fact2.clone())]);
    let custom_definitions = CustomDefinitions::default();
    let mut state = solver_state_with_domains(vec![]);

    let result = try_prove_statement(&mut state, &target_stmt, &indexes, &custom_definitions);
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

    let indexes = setup_indexes_with_facts(vec![(pod_a, fact1.clone()), (pod_b, fact2.clone())]);
    let custom_definitions = CustomDefinitions::default();
    let mut state = solver_state_with_domains(vec![]);

    let result = try_prove_statement(&mut state, &target_stmt, &indexes, &custom_definitions);
    assert!(result.is_err());
    // Should fall through to the final Unsatisfiable error
    match result.err().unwrap() {
        ProverError::Unsatisfiable(msg) => {
            assert!(msg.contains("Could not find or derive proof"));
            assert!(msg.contains(&format!("{:?}", target_stmt)));
        }
        e => panic!("Expected Unsatisfiable, got {:?}", e),
    }
    assert!(state.proof_chains.is_empty());
    assert!(state.scope.is_empty());
}

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

    let indexes = setup_indexes_with_facts(vec![(pod_a, fact1.clone())]);
    let custom_definitions = CustomDefinitions::default();
    let mut state = solver_state_with_domains(vec![]);

    let result = try_prove_statement(&mut state, &target_stmt, &indexes, &custom_definitions);
    assert!(result.is_err());
    match result.err().unwrap() {
        ProverError::Unsatisfiable(msg) => {
            assert!(msg.contains("Could not find or derive proof"));
        }
        e => panic!("Expected Unsatisfiable, got {:?}", e),
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

    let indexes = setup_indexes_with_facts(vec![(pod_a, fact1.clone()), (pod_b, fact2.clone())]);
    let custom_definitions = CustomDefinitions::default();
    let mut state = solver_state_with_domains(vec![]);

    let result = try_prove_statement(&mut state, &target_stmt, &indexes, &custom_definitions);
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

    let indexes = setup_indexes_with_facts(vec![(pod_a, fact1.clone()), (pod_b, fact2.clone())]);
    let custom_definitions = CustomDefinitions::default();
    let mut state = solver_state_with_domains(vec![]);

    let result = try_prove_statement(&mut state, &target_stmt, &indexes, &custom_definitions);
    assert!(result.is_err());
    match result.err().unwrap() {
        ProverError::Unsatisfiable(msg) => {
            assert!(msg.contains("Could not find or derive proof"));
        }
        e => panic!("Expected Unsatisfiable, got {:?}", e),
    }
}

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

    let indexes =
        setup_indexes_with_facts(vec![(pod_a, fact_gt.clone()), (pod_b, fact_lt.clone())]);
    let custom_definitions = CustomDefinitions::default();
    let mut state = solver_state_with_domains(vec![]);

    let result = try_prove_statement(&mut state, &target_stmt, &indexes, &custom_definitions);
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

    let fact_a = Statement::ValueOf(ak_a.clone(), val_10.clone()); // 10
    let fact_b = Statement::ValueOf(ak_b.clone(), val_20.clone()); // 20
    let target_stmt = Statement::Gt(ak_a.clone(), ak_b.clone()); // Target: 10 > 20 (false)

    let indexes = setup_indexes_with_facts(vec![(pod_a, fact_a.clone()), (pod_b, fact_b.clone())]);
    let custom_definitions = CustomDefinitions::default();
    let mut state = solver_state_with_domains(vec![]);

    let result = try_prove_statement(&mut state, &target_stmt, &indexes, &custom_definitions);
    assert!(result.is_err());
    match result.err().unwrap() {
        ProverError::Unsatisfiable(msg) => {
            assert!(msg.contains("Could not find or derive proof"));
        }
        e => panic!("Expected Unsatisfiable, got {:?}", e),
    }
}

#[test]
fn test_try_prove_statement_gt_from_entries_fail_wrong_type() {
    let pod_a = pod(1);
    let pod_b = pod(2);
    let key_a = key("a");
    let key_b = key("b");
    let val_10 = val(10);
    let val_str = Value::from("hello"); // String value

    let ak_a = AnchoredKey::new(pod_a, key_a.clone());
    let ak_b = AnchoredKey::new(pod_b, key_b.clone());

    let fact_a = Statement::ValueOf(ak_a.clone(), val_10.clone());
    let fact_b = Statement::ValueOf(ak_b.clone(), val_str.clone());
    let target_stmt = Statement::Gt(ak_a.clone(), ak_b.clone());

    let indexes = setup_indexes_with_facts(vec![(pod_a, fact_a.clone()), (pod_b, fact_b.clone())]);
    let custom_definitions = CustomDefinitions::default();
    let mut state = solver_state_with_domains(vec![]);

    let result = try_prove_statement(&mut state, &target_stmt, &indexes, &custom_definitions);
    assert!(
        result.is_err(),
        "Should fail because types are incompatible for Gt"
    );
    match result.err().unwrap() {
        ProverError::Unsatisfiable(msg) => {
            assert!(msg.contains("Could not find or derive proof"));
        }
        e => panic!("Expected Unsatisfiable, got {:?}", e),
    }
}

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
    let target_stmt = Statement::Lt(ak_lt.clone(), ak_gt.clone()); // Target: 10 < 20 (true)

    let indexes =
        setup_indexes_with_facts(vec![(pod_a, fact_lt.clone()), (pod_b, fact_gt.clone())]);
    let custom_definitions = CustomDefinitions::default();
    let mut state = solver_state_with_domains(vec![]);

    let result = try_prove_statement(&mut state, &target_stmt, &indexes, &custom_definitions);
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

    let fact_a = Statement::ValueOf(ak_a.clone(), val_20.clone()); // 20
    let fact_b = Statement::ValueOf(ak_b.clone(), val_10.clone()); // 10
    let target_stmt = Statement::Lt(ak_a.clone(), ak_b.clone()); // Target: 20 < 10 (false)

    let indexes = setup_indexes_with_facts(vec![(pod_a, fact_a.clone()), (pod_b, fact_b.clone())]);
    let custom_definitions = CustomDefinitions::default();
    let mut state = solver_state_with_domains(vec![]);

    let result = try_prove_statement(&mut state, &target_stmt, &indexes, &custom_definitions);
    assert!(result.is_err());
    match result.err().unwrap() {
        ProverError::Unsatisfiable(msg) => {
            assert!(msg.contains("Could not find or derive proof"));
        }
        e => panic!("Expected Unsatisfiable, got {:?}", e),
    }
}

// --- SumOf Tests ---

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

    let indexes = setup_indexes_with_facts(vec![
        (pod_a, fact_sum.clone()),
        (pod_b, fact_add1.clone()),
        (pod_c, fact_add2.clone()),
    ]);
    let custom_definitions = CustomDefinitions::default();
    let mut state = solver_state_with_domains(vec![]);

    let result = try_prove_statement(&mut state, &target_stmt, &indexes, &custom_definitions);
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

#[test]
fn test_try_prove_statement_sumof_fail_wrong_sum() {
    let pod_a = pod(1);
    let pod_b = pod(2);
    let pod_c = pod(3);
    let key_sum = key("sum");
    let key_add1 = key("add1");
    let key_add2 = key("add2");
    let val_35 = val(35); // Incorrect sum
    let val_10 = val(10);
    let val_20 = val(20);

    let ak_sum = AnchoredKey::new(pod_a, key_sum.clone());
    let ak_add1 = AnchoredKey::new(pod_b, key_add1.clone());
    let ak_add2 = AnchoredKey::new(pod_c, key_add2.clone());

    let fact_sum = Statement::ValueOf(ak_sum.clone(), val_35.clone());
    let fact_add1 = Statement::ValueOf(ak_add1.clone(), val_10.clone());
    let fact_add2 = Statement::ValueOf(ak_add2.clone(), val_20.clone());
    let target_stmt = Statement::SumOf(ak_sum.clone(), ak_add1.clone(), ak_add2.clone());

    let indexes = setup_indexes_with_facts(vec![
        (pod_a, fact_sum.clone()),
        (pod_b, fact_add1.clone()),
        (pod_c, fact_add2.clone()),
    ]);
    let custom_definitions = CustomDefinitions::default();
    let mut state = solver_state_with_domains(vec![]);

    let result = try_prove_statement(&mut state, &target_stmt, &indexes, &custom_definitions);
    assert!(result.is_err());
    match result.err().unwrap() {
        ProverError::Unsatisfiable(msg) => {
            assert!(msg.contains("Could not find or derive proof"));
        }
        e => panic!("Expected Unsatisfiable, got {:?}", e),
    }
}

#[test]
fn test_try_prove_statement_sumof_fail_wrong_type() {
    let pod_a = pod(1);
    let pod_b = pod(2);
    let pod_c = pod(3);
    let key_sum = key("sum");
    let key_add1 = key("add1");
    let key_add2 = key("add2");
    let val_30 = val(30);
    let val_str = Value::from("ten"); // Wrong type
    let val_20 = val(20);

    let ak_sum = AnchoredKey::new(pod_a, key_sum.clone());
    let ak_add1 = AnchoredKey::new(pod_b, key_add1.clone());
    let ak_add2 = AnchoredKey::new(pod_c, key_add2.clone());

    let fact_sum = Statement::ValueOf(ak_sum.clone(), val_30.clone());
    let fact_add1 = Statement::ValueOf(ak_add1.clone(), val_str.clone());
    let fact_add2 = Statement::ValueOf(ak_add2.clone(), val_20.clone());
    let target_stmt = Statement::SumOf(ak_sum.clone(), ak_add1.clone(), ak_add2.clone());

    let indexes = setup_indexes_with_facts(vec![
        (pod_a, fact_sum.clone()),
        (pod_b, fact_add1.clone()),
        (pod_c, fact_add2.clone()),
    ]);
    let custom_definitions = CustomDefinitions::default();
    let mut state = solver_state_with_domains(vec![]);

    let result = try_prove_statement(&mut state, &target_stmt, &indexes, &custom_definitions);
    assert!(result.is_err(), "Should fail due to wrong type");
    match result.err().unwrap() {
        ProverError::Unsatisfiable(msg) => {
            assert!(msg.contains("Could not find or derive proof"));
        }
        e => panic!("Expected Unsatisfiable, got {:?}", e),
    }
}

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
    // Missing val_20

    let ak_sum = AnchoredKey::new(pod_a, key_sum.clone());
    let ak_add1 = AnchoredKey::new(pod_b, key_add1.clone());
    let ak_add2 = AnchoredKey::new(pod_c, key_add2.clone());

    let fact_sum = Statement::ValueOf(ak_sum.clone(), val_30.clone());
    let fact_add1 = Statement::ValueOf(ak_add1.clone(), val_10.clone());
    // Missing fact_add2
    let target_stmt = Statement::SumOf(ak_sum.clone(), ak_add1.clone(), ak_add2.clone());

    let indexes =
        setup_indexes_with_facts(vec![(pod_a, fact_sum.clone()), (pod_b, fact_add1.clone())]);
    let custom_definitions = CustomDefinitions::default();
    let mut state = solver_state_with_domains(vec![]);

    let result = try_prove_statement(&mut state, &target_stmt, &indexes, &custom_definitions);
    assert!(result.is_err(), "Should fail due to missing value");
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

    let indexes = setup_indexes_with_facts(vec![
        (pod_a, fact_prod.clone()),
        (pod_b, fact_fac1.clone()),
        (pod_c, fact_fac2.clone()),
    ]);
    let custom_definitions = CustomDefinitions::default();
    let mut state = solver_state_with_domains(vec![]);

    let result = try_prove_statement(&mut state, &target_stmt, &indexes, &custom_definitions);
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

    let indexes = setup_indexes_with_facts(vec![
        (pod_a, fact_prod.clone()),
        (pod_b, fact_fac1.clone()),
        (pod_c, fact_fac2.clone()),
    ]);
    let custom_definitions = CustomDefinitions::default();
    let mut state = solver_state_with_domains(vec![]);

    let result = try_prove_statement(&mut state, &target_stmt, &indexes, &custom_definitions);
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

    let indexes = setup_indexes_with_facts(vec![
        (pod_a, fact_max.clone()),
        (pod_b, fact_op1.clone()),
        (pod_c, fact_op2.clone()),
    ]);
    let custom_definitions = CustomDefinitions::default();
    let mut state = solver_state_with_domains(vec![]);

    let result = try_prove_statement(&mut state, &target_stmt, &indexes, &custom_definitions);
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

    let indexes2 = setup_indexes_with_facts(vec![
        (pod_a, fact_max2.clone()),
        (pod_b, fact_op1_2.clone()),
        (pod_c, fact_op2_2.clone()),
    ]);
    let mut state2 = solver_state_with_domains(vec![]);
    let result2 = try_prove_statement(&mut state2, &target_stmt2, &indexes2, &custom_definitions);
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

    let indexes = setup_indexes_with_facts(vec![
        (pod_a, fact_max.clone()),
        (pod_b, fact_op1.clone()),
        (pod_c, fact_op2.clone()),
    ]);
    let custom_definitions = CustomDefinitions::default();
    let mut state = solver_state_with_domains(vec![]);

    let result = try_prove_statement(&mut state, &target_stmt, &indexes, &custom_definitions);
    assert!(result.is_err());
    match result.err().unwrap() {
        ProverError::Unsatisfiable(msg) => {
            assert!(msg.contains("Could not find or derive proof"));
        }
        e => panic!("Expected Unsatisfiable, got {:?}", e),
    }
}

// --- Contains/NotContains Tests (Dictionaries) ---

#[test]
fn test_try_prove_statement_contains_dict_success() {
    let pod_a = pod(1);
    let pod_b = pod(2);
    let pod_c = pod(3);
    let pod_d = pod(4);

    let key_dict = key("my_dict");
    let key_lookup = key("lookup_key"); // This is the AK for the Key("world")
    let key_expected_val = key("expected_value"); // This is the AK for the Value("hello")

    let dict_val_str = Value::from("hello");
    let dict_key = key("world"); // Use Key type for dictionary key
    let missing_key = key("missing"); // Use Key type

    let mut map = HashMap::new();
    map.insert(dict_key.clone(), dict_val_str.clone()); // Use Key as HashMap key
    let dict_container = Value::from(Dictionary::new(map).unwrap());

    let ak_dict = AnchoredKey::new(pod_a, key_dict);
    let ak_key = AnchoredKey::new(pod_b, key_lookup);
    let ak_val = AnchoredKey::new(pod_c, key_expected_val);

    let fact_dict = Statement::ValueOf(ak_dict.clone(), dict_container.clone());
    // ValueOf statement for the *key* uses the Key type
    let fact_key = Statement::ValueOf(ak_key.clone(), Value::from(dict_key.name().to_string()));
    let fact_val = Statement::ValueOf(ak_val.clone(), dict_val_str.clone());
    let target_stmt = Statement::Contains(ak_dict.clone(), ak_key.clone(), ak_val.clone());

    let indexes = setup_indexes_with_facts(vec![
        (pod_a, fact_dict.clone()),
        (pod_b, fact_key.clone()),
        (pod_c, fact_val.clone()),
    ]);
    let custom_definitions = CustomDefinitions::default();
    let mut state = solver_state_with_domains(vec![]);

    let result = try_prove_statement(&mut state, &target_stmt, &indexes, &custom_definitions);
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

#[test]
fn test_try_prove_statement_contains_dict_fail_key_not_found() {
    let pod_a = pod(1);
    let pod_b = pod(2);
    let pod_c = pod(3);

    let key_dict = key("my_dict");
    let key_lookup_missing = key("missing_key"); // This key isn't in the dict
    let key_expected_val = key("expected_value");

    let dict_val_str = Value::from("hello");
    let dict_key = key("world"); // Use Key type
    let missing_key = key("missing"); // Use Key type

    let mut map = HashMap::new();
    map.insert(dict_key.clone(), dict_val_str.clone());
    let dict_container = Value::from(Dictionary::new(map).unwrap());

    let ak_dict = AnchoredKey::new(pod_a, key_dict);
    let ak_key_missing = AnchoredKey::new(pod_b, key_lookup_missing);
    let ak_val = AnchoredKey::new(pod_c, key_expected_val);

    let fact_dict = Statement::ValueOf(ak_dict.clone(), dict_container.clone());
    // ValueOf for the missing key
    let fact_key_missing = Statement::ValueOf(
        ak_key_missing.clone(),
        Value::from(missing_key.name().to_string()),
    );
    let fact_val = Statement::ValueOf(ak_val.clone(), dict_val_str.clone()); // Value doesn't matter here
    let target_stmt = Statement::Contains(ak_dict.clone(), ak_key_missing.clone(), ak_val.clone());

    let indexes = setup_indexes_with_facts(vec![
        (pod_a, fact_dict.clone()),
        (pod_b, fact_key_missing.clone()),
        (pod_c, fact_val.clone()),
    ]);
    let custom_definitions = CustomDefinitions::default();
    let mut state = solver_state_with_domains(vec![]);

    let result = try_prove_statement(&mut state, &target_stmt, &indexes, &custom_definitions);
    assert!(result.is_err());
    match result.err().unwrap() {
        ProverError::Unsatisfiable(msg) => {
            assert!(msg.contains("Could not find or derive proof"));
        }
        e => panic!("Expected Unsatisfiable, got {:?}", e),
    }
}

#[test]
fn test_try_prove_statement_contains_dict_fail_wrong_value() {
    let pod_a = pod(1);
    let pod_b = pod(2);
    let pod_c = pod(3);
    let pod_d = pod(4);

    let key_dict = key("my_dict");
    let key_lookup = key("lookup_key"); // AK for Key("the_key")
    let key_wrong_val = key("wrong_value"); // AK for the wrong value

    let dict_val_str_actual = Value::from("actual_value");
    let dict_key = key("the_key"); // Use Key type
    let dict_val_str_wrong = Value::from("wrong_value"); // The value we incorrectly claim

    let mut map = HashMap::new();
    map.insert(dict_key.clone(), dict_val_str_actual.clone());
    let dict_container = Value::from(Dictionary::new(map).unwrap());

    let ak_dict = AnchoredKey::new(pod_a, key_dict);
    let ak_key = AnchoredKey::new(pod_b, key_lookup);
    let ak_val_wrong = AnchoredKey::new(pod_c, key_wrong_val);

    let fact_dict = Statement::ValueOf(ak_dict.clone(), dict_container.clone());
    // ValueOf for the key
    let fact_key = Statement::ValueOf(ak_key.clone(), Value::from(dict_key.name().to_string()));
    // ValueOf for the incorrect target value
    let fact_val_wrong = Statement::ValueOf(ak_val_wrong.clone(), dict_val_str_wrong.clone());
    // Target claims the dict contains key->wrong_value
    let target_stmt = Statement::Contains(ak_dict.clone(), ak_key.clone(), ak_val_wrong.clone());

    let indexes = setup_indexes_with_facts(vec![
        (pod_a, fact_dict.clone()),
        (pod_b, fact_key.clone()),
        (pod_c, fact_val_wrong.clone()),
    ]);
    let custom_definitions = CustomDefinitions::default();
    let mut state = solver_state_with_domains(vec![]);

    let result = try_prove_statement(&mut state, &target_stmt, &indexes, &custom_definitions);
    assert!(result.is_err());
    match result.err().unwrap() {
        ProverError::Unsatisfiable(msg) => {
            assert!(msg.contains("Could not find or derive proof"));
        }
        e => panic!("Expected Unsatisfiable, got {:?}", e),
    }
}

#[test]
fn test_try_prove_statement_contains_dict_fail_missing_input_value() {
    let pod_a = pod(1);
    let pod_b = pod(2);
    let pod_c = pod(3);

    let key_dict = key("my_dict");
    let key_lookup = key("lookup_key");
    let key_expected_val = key("expected_value");

    let dict_val_str = Value::from("hello");
    let dict_key = key("world"); // Use Key type

    let mut map = HashMap::new();
    map.insert(dict_key.clone(), dict_val_str.clone());
    let dict_container = Value::from(Dictionary::new(map).unwrap());

    let ak_dict = AnchoredKey::new(pod_a, key_dict);
    let ak_key = AnchoredKey::new(pod_b, key_lookup);
    let ak_val = AnchoredKey::new(pod_c, key_expected_val);

    let fact_dict = Statement::ValueOf(ak_dict.clone(), dict_container.clone());
    // ValueOf for the key
    let fact_key = Statement::ValueOf(ak_key.clone(), Value::from(dict_key.name().to_string()));
    // Missing fact_val = Statement::ValueOf(ak_val.clone(), dict_val_str.clone());
    let target_stmt = Statement::Contains(ak_dict.clone(), ak_key.clone(), ak_val.clone());

    let indexes = setup_indexes_with_facts(vec![
        (pod_a, fact_dict.clone()),
        (pod_b, fact_key.clone()),
        // Missing fact_val
    ]);
    let custom_definitions = CustomDefinitions::default();
    let mut state = solver_state_with_domains(vec![]);

    let result = try_prove_statement(&mut state, &target_stmt, &indexes, &custom_definitions);
    assert!(
        result.is_err(),
        "Should fail due to missing ValueOf for value AK"
    );
    match result.err().unwrap() {
        ProverError::Unsatisfiable(msg) => {
            assert!(msg.contains("Could not find or derive proof"));
        }
        e => panic!("Expected Unsatisfiable, got {:?}", e),
    }
}

#[test]
fn test_try_prove_statement_notcontains_dict_success() {
    let pod_a = pod(1);
    let pod_b = pod(2);

    let key_dict = key("my_dict");
    let key_lookup_missing = key("missing_key"); // This key isn't in the dict

    let dict_val_str = Value::from("hello");
    let dict_key = key("world"); // Use Key type
    let missing_key = key("missing"); // Use Key type

    let mut map = HashMap::new();
    map.insert(dict_key.clone(), dict_val_str.clone());
    let dict_container = Value::from(Dictionary::new(map).unwrap());

    let ak_dict = AnchoredKey::new(pod_a, key_dict);
    let ak_key_missing = AnchoredKey::new(pod_b, key_lookup_missing);

    let fact_dict = Statement::ValueOf(ak_dict.clone(), dict_container.clone());
    // ValueOf for the key that should not be found
    let fact_key_missing = Statement::ValueOf(
        ak_key_missing.clone(),
        Value::from(missing_key.name().to_string()),
    );
    let target_stmt = Statement::NotContains(ak_dict.clone(), ak_key_missing.clone());

    let indexes = setup_indexes_with_facts(vec![
        (pod_a, fact_dict.clone()),
        (pod_b, fact_key_missing.clone()),
    ]);
    let custom_definitions = CustomDefinitions::default();
    let mut state = solver_state_with_domains(vec![]);

    let result = try_prove_statement(&mut state, &target_stmt, &indexes, &custom_definitions);
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
    assert_eq!(step.inputs.len(), 2); // ValueOf(dict), ValueOf(key)
    assert!(step.inputs.contains(&fact_dict));
    assert!(step.inputs.contains(&fact_key_missing));
    assert_eq!(step.output, target_stmt);

    assert!(state.proof_chains.contains_key(&target_stmt));
    assert_eq!(state.scope.len(), 2);
    assert!(state.scope.contains(&(pod_a, fact_dict)));
    assert!(state.scope.contains(&(pod_b, fact_key_missing)));
}

#[test]
fn test_try_prove_statement_notcontains_dict_fail_key_found() {
    let pod_a = pod(1);
    let pod_b = pod(2);

    let key_dict = key("my_dict");
    let key_lookup_exists = key("existing_key"); // This key *is* in the dict

    let dict_val_str = Value::from("hello");
    let dict_key = key("world"); // Use Key type

    let mut map = HashMap::new();
    map.insert(dict_key.clone(), dict_val_str.clone());
    let dict_container = Value::from(Dictionary::new(map).unwrap());

    let ak_dict = AnchoredKey::new(pod_a, key_dict);
    let ak_key_exists = AnchoredKey::new(pod_b, key_lookup_exists);

    let fact_dict = Statement::ValueOf(ak_dict.clone(), dict_container.clone());
    // Use the key that exists in the dict for the ValueOf statement
    let fact_key_exists = Statement::ValueOf(
        ak_key_exists.clone(),
        Value::from(dict_key.name().to_string()), // Use the key name as the value for this AK
    );
    // Target claims the existing key is *not* contained
    let target_stmt = Statement::NotContains(ak_dict.clone(), ak_key_exists.clone());

    let indexes = setup_indexes_with_facts(vec![
        (pod_a, fact_dict.clone()),
        (pod_b, fact_key_exists.clone()),
    ]);
    let custom_definitions = CustomDefinitions::default();
    let mut state = solver_state_with_domains(vec![]);

    let result = try_prove_statement(&mut state, &target_stmt, &indexes, &custom_definitions);
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

// --- Tests for solve function ---

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
    let indexes = setup_indexes_with_facts(facts);
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

    let result = super::solve(&request, &indexes, &custom_definitions);

    // Expect error because search is needed but not implemented
    assert!(result.is_err());
    match result.err().unwrap() {
        ProverError::NotImplemented(stage) => {
            assert!(
                stage.contains("Solver stage 4 (Search)"),
                "Expected Search stage error, got: {}",
                stage
            );
        }
        e => panic!("Expected NotImplemented(Search), got {:?}", e),
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
        (pod_a, Statement::ValueOf(ak(1, "foo"), val_10)),
        (pod_c, Statement::ValueOf(ak(3, "quux"), val_20)),
    ];
    let indexes = setup_indexes_with_facts(facts);
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
    let result = super::solve(&request_templates, &indexes, &custom_definitions);

    // Assert: Expect the solver to run to completion and hit the
    // unimplemented Solution Extraction stage.
    assert!(
        result.is_err(),
        "Expected solver to error at extraction stage"
    );
    match result.err().unwrap() {
        ProverError::NotImplemented(stage) => {
            assert!(
                stage.contains("Solver stage 5 (Solution Extraction)"),
                "Expected Solution Extraction stage error, got: {}",
                stage
            );
        }
        e => panic!("Expected NotImplemented(Solution Extraction), got {:?}", e),
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
    let indexes = setup_indexes_with_facts(facts);
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
    let result = super::solve(&request_templates, &indexes, &custom_definitions);

    // Assert: Expect the solver to return Unsatisfiable because Gt(10, 20) fails.
    assert!(
        result.is_err(),
        "Expected solver to return an Unsatisfiable error"
    );
    match result.err().unwrap() {
        ProverError::Unsatisfiable(msg) => {
            // Check that the error message indicates the failure of the specific Gt candidate
            assert!(
                msg.contains("Failed to prove required candidate statement"),
                "Error message missing expected prefix, got: {}",
                msg
            );
            assert!(
                msg.contains("Gt(AnchoredKey(PodId(Field(..)), Key { name: \"foo\" }), AnchoredKey(PodId(Field(..)), Key { name: \"bar\" }))"),
                "Error message missing expected Gt statement details, got: {}",
                msg
            );
            assert!(
                msg.contains("Could not find or derive proof"), // Check for the inner reason from try_prove_statement
                "Error message missing inner failure reason, got: {}",
                msg
            );
        }
        e => panic!("Expected Unsatisfiable error, got {:?}", e),
    }
}

#[test]
fn test_transitive_equality_proof() {
    // Inputs: Eq(A["foo"], B["bar"]), Eq(B["bar"], C["quux"])
    // Target: Eq(A["foo"], C["quux"])

    // Use test helpers for construction
    let pod_a = pod(1);
    let pod_b = pod(2);
    let pod_c = pod(3);
    let key_foo = key("foo");
    let key_bar = key("bar");
    let key_quux = key("quux");
    let val_10 = val(10);

    let ak_a_foo = ak(1, "foo"); // Use ak helper
    let ak_b_bar = ak(2, "bar"); // Use ak helper
    let ak_c_quux = ak(3, "quux"); // Use ak helper

    let initial_facts = vec![
        // Remove ValueOf statements to force transitive path
        // (pod_a, Statement::ValueOf(ak_a_foo.clone(), val_10.clone())),
        // (pod_b, Statement::ValueOf(ak_b_bar.clone(), val_10.clone())),
        // (pod_c, Statement::ValueOf(ak_c_quux.clone(), val_10.clone())),
        // Direct Equality statements are the required inputs
        (pod_a, Statement::Equal(ak_a_foo.clone(), ak_b_bar.clone())),
        (pod_b, Statement::Equal(ak_b_bar.clone(), ak_c_quux.clone())),
    ];

    // Use setup_indexes_with_facts
    let indexes = setup_indexes_with_facts(initial_facts);

    let custom_definitions: CustomDefinitions = HashMap::new();

    // Request template for the target statement - Use wildcards
    let wc_pod_a = wc("?pod_a", 0); // Use wc helper
    let wc_pod_c = wc("?pod_c", 1); // Use wc helper
    let request_templates = vec![StatementTmpl {
        pred: Predicate::Native(NativePredicate::Equal),
        args: vec![
            StatementTmplArg::Key(
                wc_pod_a.clone(),                    // Use wildcard
                KeyOrWildcard::Key(key_foo.clone()), // Fixed key
            ),
            StatementTmplArg::Key(
                wc_pod_c.clone(),                     // Use wildcard
                KeyOrWildcard::Key(key_quux.clone()), // Fixed key
            ),
        ],
    }];

    // --- Call the solver ---
    // Need to import solve explicitly or use super::solve
    let result = super::solve(&request_templates, &indexes, &custom_definitions);

    // --- Assertions ---
    assert!(result.is_ok(), "Solver failed: {:?}", result.err());
    let solution = result.unwrap();

    // Check bindings (should now contain bindings for the wildcards)
    assert_eq!(solution.bindings.len(), 2, "Expected 2 bindings");
    // Use cv_pod helper for expected value
    assert_eq!(
        solution.bindings.get(&wc_pod_a),
        Some(&cv_pod(1)),
        "Incorrect binding for ?pod_a"
    );
    assert_eq!(
        solution.bindings.get(&wc_pod_c),
        Some(&cv_pod(3)),
        "Incorrect binding for ?pod_c"
    );

    // Check scope (should contain only the two input Eq statements now)
    let expected_scope_statements: HashSet<Statement> = [
        Statement::Equal(ak_a_foo.clone(), ak_b_bar.clone()),
        Statement::Equal(ak_b_bar.clone(), ak_c_quux.clone()),
    ]
    .iter()
    .cloned()
    .collect();

    let actual_scope_statements: HashSet<Statement> = solution
        .scope
        .iter()
        .map(|(_, stmt)| stmt.clone())
        .collect();

    // Allow scope to contain ValueOf if needed by sub-proofs
    assert!(
        actual_scope_statements.is_superset(&expected_scope_statements),
        "Scope missing required statements. Expected superset of {:?}, got {:?}",
        expected_scope_statements,
        actual_scope_statements
    );

    // Check proof chain for the target statement
    let target_statement = Statement::Equal(ak_a_foo.clone(), ak_c_quux.clone());
    assert!(
        solution.proof_chains.contains_key(&target_statement),
        "Proof chain for target statement {:?} not found",
        target_statement
    );

    let proof_chain = solution.proof_chains.get(&target_statement).unwrap();
    assert!(
        !proof_chain.0.is_empty(),
        "Proof chain is unexpectedly empty"
    );

    // Check the final step is TransitiveEqualFromStatements
    let final_step = proof_chain.0.last().unwrap();
    assert_eq!(
        final_step.operation,
        OperationType::Native(NativeOperation::TransitiveEqualFromStatements)
    );
    assert_eq!(final_step.output, target_statement);
    assert_eq!(final_step.inputs.len(), 2);
    assert_eq!(
        final_step.inputs[0],
        Statement::Equal(ak_a_foo.clone(), ak_b_bar.clone())
    );
    assert_eq!(
        final_step.inputs[1],
        Statement::Equal(ak_b_bar.clone(), ak_c_quux.clone())
    );

    // Optional: Check earlier steps (likely CopyStatement for the inputs)
    // This depends on how the proof search finds the inputs.
    // If the inputs were base facts, expect CopyStatement steps for them earlier in the chain.
    // Example check (adjust based on actual chain structure):
    if proof_chain.0.len() > 1 {
        // Assuming CopyStatement proof for the two direct Equal inputs first
        let first_input_proof_step = proof_chain
            .0
            .iter()
            .find(|step| step.output == final_step.inputs[0]);
        let second_input_proof_step = proof_chain
            .0
            .iter()
            .find(|step| step.output == final_step.inputs[1]);

        assert!(
            first_input_proof_step.is_some(),
            "Proof step for first input Eq not found"
        );
        assert!(
            second_input_proof_step.is_some(),
            "Proof step for second input Eq not found"
        );

        // Inputs are now base facts, so their proof should be CopyStatement
        assert_eq!(
            first_input_proof_step.unwrap().operation,
            OperationType::Native(NativeOperation::CopyStatement)
        );
        assert_eq!(
            second_input_proof_step.unwrap().operation,
            OperationType::Native(NativeOperation::CopyStatement)
        );
        // Remove the matches! assertions as we now expect only CopyStatement
        // assert!(
        //     matches!(
        //         first_input_proof_step.unwrap().operation,
        //         OperationType::Native(NativeOperation::CopyStatement)
        //             | OperationType::Native(NativeOperation::EqualFromEntries)
        //     ),
        //     "First input proof step was not CopyStatement or EqualFromEntries"
        // );
        // assert!(
        //     matches!(
        //         second_input_proof_step.unwrap().operation,
        //         OperationType::Native(NativeOperation::CopyStatement)
        //             | OperationType::Native(NativeOperation::EqualFromEntries)
        //     ),
        //     "Second input proof step was not CopyStatement or EqualFromEntries"
        // );
    }

    // Check that the solver identified the intermediate key correctly (B["bar"]) implicitly.
    // This is verified by the structure of the final proof step's inputs.
}
