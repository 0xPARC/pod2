use std::{collections::HashMap, sync::Arc};

use super::{
    predicates::{
        BinaryPredicateHandler, ContainsHandler, EqualHandler, LtEqHandler, LtHandler,
        PredicateHandler, SumOfHandler, TernaryPredicateHandler,
    },
    SolverError,
};
use crate::{
    middleware::{
        AnchoredKey, CustomPredicateRef, Hash, Key, NativePredicate, PodId, Predicate, RawValue,
        TypedValue, Value, ValueRef,
    },
    solver::{
        db::FactDB,
        ir,
        semantics::enumerator::{CandidateTupleStream, FactEnumerator, TypeFilter},
    },
};

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum JustificationKind {
    Fact,
    Computation,
}

/// A `SemanticsProvider` that resolves goals by consulting a `FactDB`.
#[derive(Clone)]
pub struct PodSemantics {
    pub db: Arc<FactDB>,
    enumerator: FactEnumerator,
    pub native_handlers: HashMap<NativePredicate, PredicateHandler>,
}

impl PodSemantics {
    pub fn new(db: Arc<FactDB>) -> Self {
        let mut handlers = HashMap::new();
        handlers.insert(NativePredicate::Lt, PredicateHandler::Lt(LtHandler));
        handlers.insert(NativePredicate::LtEq, PredicateHandler::LtEq(LtEqHandler));
        handlers.insert(
            NativePredicate::Equal,
            PredicateHandler::Equal(EqualHandler),
        );
        handlers.insert(
            NativePredicate::Contains,
            PredicateHandler::Contains(ContainsHandler),
        );
        handlers.insert(
            NativePredicate::SumOf,
            PredicateHandler::SumOf(SumOfHandler),
        );

        Self {
            db: Arc::clone(&db),
            enumerator: FactEnumerator::new(db),
            native_handlers: handlers,
        }
    }

    pub fn value_ref_to_value(&self, vr: &ValueRef) -> Option<Value> {
        match vr {
            ValueRef::Literal(v) => Some(v.clone()),
            ValueRef::Key(ak) => self.db.get_value_by_anchored_key(ak).cloned(),
        }
    }

    /// Provides a generic way to iterate over all known facts for a binary
    /// predicate, with optional filters for each argument. This is intended
    /// for use by a bottom-up evaluation engine.
    pub fn iter_binary_facts<'a, C>(
        &'a self,
        filters: [Option<ValueRef>; 2],
        checker: C,
        db_facts: &'a HashMap<[ValueRef; 2], Vec<PodId>>,
        type_filters: [TypeFilter; 2],
    ) -> Result<CandidateTupleStream<'a, 2>, SolverError>
    where
        C: BinaryPredicateHandler + 'a,
    {
        self.enumerator
            .enumerate_binary_candidates_core(filters, checker, db_facts, type_filters)
    }

    /// Provides a generic way to iterate over all known facts for a ternary
    /// predicate, with optional filters for each argument. This is intended
    /// for use by a bottom-up evaluation engine.
    pub fn iter_ternary_facts<'a, C>(
        &'a self,
        filters: [Option<ValueRef>; 3],
        checker: C,
        db_facts: &'a HashMap<[ValueRef; 3], Vec<PodId>>,
        type_filters: [TypeFilter; 3],
    ) -> Result<CandidateTupleStream<'a, 3>, SolverError>
    where
        C: TernaryPredicateHandler + 'a,
    {
        self.enumerator
            .enumerate_ternary_candidates_core(filters, checker, db_facts, type_filters)
    }

    /// Iterates over potential facts for a `GetValue(pod, key, value)` literal.
    pub fn iter_get_value_facts<'a>(
        &'a self,
        pod: Option<&Value>,
        key: Option<&Value>,
    ) -> impl Iterator<Item = Vec<Value>> + 'a {
        let mut results = Vec::new();

        if let (Some(pod_val), Some(key_val)) = (pod, key) {
            // Case 1: Pod and Key are both bound.
            if let (TypedValue::Raw(raw_pod_id), TypedValue::String(key_s)) =
                (pod_val.typed(), key_val.typed())
            {
                let pod_id = PodId(Hash(raw_pod_id.0));
                let key = Key::new(key_s.clone());
                let ak = AnchoredKey::new(pod_id, key);
                if let Some(found_val) = self.db.get_value_by_anchored_key(&ak) {
                    results.push(vec![pod_val.clone(), key_val.clone(), found_val.clone()]);
                }
            }
        } else if let Some(key_val) = key {
            // Case 2: Only Key is bound. Iterate all pods.
            if let TypedValue::String(key_s) = key_val.typed() {
                let key = Key::new(key_s.clone());
                for pod_id in self.db.all_pod_ids_domain() {
                    let ak = AnchoredKey::new(pod_id, key.clone());
                    if let Some(found_val) = self.db.get_value_by_anchored_key(&ak) {
                        let pod_id_val = Value::from(RawValue(pod_id.0 .0));
                        results.push(vec![pod_id_val, key_val.clone(), found_val.clone()]);
                    }
                }
            }
        }

        results.into_iter()
    }

    /// Provides a generic way to iterate over all known EDB facts for a custom
    /// predicate, with optional filters for each argument.
    pub fn iter_custom_facts<'a>(
        &'a self,
        cpr: &'a CustomPredicateRef,
        filters: &'a [Option<Value>],
    ) -> impl Iterator<Item = Vec<Value>> + 'a {
        self.enumerator
            .enumerate_custom_candidates_core(cpr, filters)
    }

    /// Checks if a fully-instantiated (ground) literal is true according to the
    /// base facts (EDB) of the system. This is used during proof reconstruction
    /// to justify premises that are not derived facts but are true by computation.
    /// TODO: consider removing this once we materialize derived facts properly.
    pub fn is_edb_fact(&self, literal: &ir::Literal) -> Result<bool, SolverError> {
        let pred = if let ir::PredicateIdentifier::Normal(Predicate::Native(p)) = &literal.predicate
        {
            p
        } else {
            // Only native predicates can be EDB facts in this context. Custom predicates are,
            // by definition, IDB.
            return Ok(false);
        };

        // Helper to get a value from a term, ensuring it's a constant. This function
        // should only operate on fully ground (instantiated) literals.
        let get_val = |term: &ir::Term| -> Result<Value, SolverError> {
            if let ir::Term::Constant(v) = term {
                Ok(v.clone())
            } else {
                Err(SolverError::Internal(
                    "is_edb_fact called with non-constant term".to_string(),
                ))
            }
        };

        let args: Vec<Value> = literal
            .terms
            .iter()
            .map(get_val)
            .collect::<Result<_, _>>()?;

        let handler = self.native_handlers.get(pred).ok_or_else(|| {
            SolverError::Internal(format!(
                "is_edb_fact: No handler for native predicate {:?}",
                pred
            ))
        })?;

        let result = match handler {
            PredicateHandler::Lt(h) => h.is_edb_fact(self, &args),
            PredicateHandler::LtEq(h) => h.is_edb_fact(self, &args),
            PredicateHandler::Equal(h) => h.is_edb_fact(self, &args),
            PredicateHandler::Contains(h) => h.is_edb_fact(self, &args),
            PredicateHandler::SumOf(h) => h.is_edb_fact(self, &args),
            PredicateHandler::ProductOf(h) => h.is_edb_fact(self, &args),
            PredicateHandler::MaxOf(h) => h.is_edb_fact(self, &args),
            PredicateHandler::NotEqual(h) => h.is_edb_fact(self, &args),
            PredicateHandler::NotContains(h) => h.is_edb_fact(self, &args),
            PredicateHandler::HashOf(h) => h.is_edb_fact(self, &args),
        };

        Ok(result)
    }
}
