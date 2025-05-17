#![cfg(test)]
use std::{
    collections::{HashMap, HashSet},
    sync::Arc,
};

pub mod proof;
pub mod pruning;
pub mod search;

// --- Common Test Helper Functions ---
use super::{types::ExpectedType, SolverState};
use crate::{
    middleware::{
        self,
        containers::{Array, Dictionary, Set},
        AnchoredKey, CustomPredicate, CustomPredicateBatch, Key, KeyOrWildcard, NativeOperation,
        NativePredicate, OperationType, Params, PodId, Predicate, Statement, StatementTmpl,
        StatementTmplArg, ToFields, Value, Wildcard,
    },
    prover::{
        error::ProverError,
        indexing::ProverIndexes,
        types::{ConcreteValue, CustomDefinitions},
    },
};

pub(crate) fn wc(name: &str, index: usize) -> Wildcard {
    Wildcard::new(name.to_string(), index)
}

pub(crate) fn pod(id: u64) -> PodId {
    PodId(middleware::hash_str(&id.to_string()))
}

pub(crate) fn key(name: &str) -> Key {
    Key::new(name.to_string())
}

pub(crate) fn val(v: i64) -> Value {
    Value::from(v)
}

pub(crate) fn ak(pod_id: u64, key_name: &str) -> AnchoredKey {
    AnchoredKey::new(pod(pod_id), key(key_name))
}

pub(crate) fn cv_pod(id: u64) -> ConcreteValue {
    ConcreteValue::Pod(pod(id))
}

pub(crate) fn cv_key(name: &str) -> ConcreteValue {
    ConcreteValue::Key(name.to_string())
}

pub(crate) fn cv_val(v: i64) -> ConcreteValue {
    ConcreteValue::Val(Value::from(v))
}

pub(crate) fn solver_state_with_domains(
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
        params: middleware::Params::default(),
        memoization_cache: HashMap::new(),
        active_custom_calls: HashSet::new(),
    }
}

pub(crate) fn dummy_prover_indexes() -> ProverIndexes {
    ProverIndexes::new(middleware::Params::default())
}

pub(crate) fn setup_indexes_with_facts(facts: &[(PodId, Statement)]) -> (ProverIndexes, Params) {
    let params = middleware::Params::default();
    let indexes = ProverIndexes::build(params.clone(), facts);
    (indexes, params)
}

pub(crate) fn setup_custom_definitions_for_test(
    definitions: Vec<(Predicate, CustomPredicate, Arc<CustomPredicateBatch>)>,
    params: &Params,
) -> CustomDefinitions {
    let mut custom_defs = CustomDefinitions::new();
    for (predicate_ref_variant, definition, batch_arc) in definitions {
        let key = predicate_ref_variant.to_fields(params);
        custom_defs.insert(key, (definition, batch_arc));
    }
    custom_defs
}

pub(crate) fn dict_val(kvs: Vec<(&str, i64)>) -> Value {
    let map: HashMap<Key, Value> = kvs.into_iter().map(|(k, v)| (key(k), val(v))).collect();
    Value::from(Dictionary::new(map).unwrap())
}

pub(crate) fn set_val(vals: Vec<i64>) -> Value {
    let set: HashSet<Value> = vals.into_iter().map(val).collect();
    Value::from(Set::new(set).unwrap())
}

pub(crate) fn array_val(vals: Vec<i64>) -> Value {
    let array: Vec<Value> = vals.into_iter().map(val).collect();
    Value::from(Array::new(array).unwrap())
}
