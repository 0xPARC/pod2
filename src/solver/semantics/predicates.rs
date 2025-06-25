//! Defines the traits and implementations for handling native Datalog predicates.
//! This modular approach allows for easy extension and testing of predicate logic.

use std::collections::HashSet;

use log::trace;

use crate::{
    frontend::Operation,
    middleware::{
        hash_values, Key, NativeOperation, NativePredicate, Statement, TypedValue, Value, ValueRef,
    },
    solver::{
        db::FactDB,
        engine::semi_naive::{Fact, FactSource},
        error::SolverError,
    },
};

/// An enum that dispatches to the correct handler for a given native predicate.
#[derive(Clone, Copy)]
pub enum PredicateHandler {
    Lt(LtHandler),
    LtEq(LtEqHandler),
    Equal(EqualHandler),
    Contains(ContainsHandler),
    SumOf(SumOfHandler),
    ProductOf(ProductOfHandler),
    NotEqual(NotEqualHandler),
    NotContains(NotContainsHandler),
    MaxOf(MaxOfHandler),
    HashOf(HashOfHandler),
    // TODO: Add other handlers here as they are implemented
}

impl PredicateHandler {
    pub fn for_native_predicate(native_pred: NativePredicate) -> Self {
        match native_pred {
            NativePredicate::Lt => Self::Lt(LtHandler),
            NativePredicate::LtEq => Self::LtEq(LtEqHandler),
            NativePredicate::Equal => Self::Equal(EqualHandler),
            NativePredicate::Contains => Self::Contains(ContainsHandler),
            NativePredicate::SumOf => Self::SumOf(SumOfHandler),
            NativePredicate::ProductOf => Self::ProductOf(ProductOfHandler),
            NativePredicate::NotEqual => Self::NotEqual(NotEqualHandler),
            NativePredicate::NotContains => Self::NotContains(NotContainsHandler),
            NativePredicate::MaxOf => Self::MaxOf(MaxOfHandler),
            NativePredicate::HashOf => Self::HashOf(HashOfHandler),
            // Syntactic sugar predicates:
            NativePredicate::None => unimplemented!(),
            NativePredicate::False => unimplemented!(),
            NativePredicate::DictContains => unimplemented!(),
            NativePredicate::DictNotContains => unimplemented!(),
            NativePredicate::SetContains => unimplemented!(),
            NativePredicate::SetNotContains => unimplemented!(),
            NativePredicate::ArrayContains => unimplemented!(),
            NativePredicate::Gt => unimplemented!(),
            NativePredicate::GtEq => unimplemented!(),
            // If you see an error here, you've added a new native predicate.
            // Please add a handler for it.
        }
    }

    pub fn explain_special_derivation(
        &self,
        args: &[ValueRef],
        db: &FactDB,
    ) -> Result<Vec<Operation>, SolverError> {
        match self {
            PredicateHandler::Lt(h) => h.explain_special_derivation(args, db),
            PredicateHandler::LtEq(h) => h.explain_special_derivation(args, db),
            PredicateHandler::Equal(h) => h.explain_special_derivation(args, db),
            PredicateHandler::Contains(h) => h.explain_special_derivation(args, db),
            PredicateHandler::SumOf(h) => h.explain_special_derivation(args, db),
            PredicateHandler::ProductOf(h) => h.explain_special_derivation(args, db),
            PredicateHandler::NotEqual(h) => h.explain_special_derivation(args, db),
            PredicateHandler::NotContains(h) => h.explain_special_derivation(args, db),
            PredicateHandler::MaxOf(h) => h.explain_special_derivation(args, db),
            PredicateHandler::HashOf(h) => h.explain_special_derivation(args, db),
        }
    }

    pub fn materialize(&self, args: &[Option<ValueRef>], db: &FactDB) -> HashSet<Fact> {
        match self {
            PredicateHandler::Lt(h) => h.materialize(args, db),
            PredicateHandler::LtEq(h) => h.materialize(args, db),
            PredicateHandler::Equal(h) => h.materialize(args, db),
            PredicateHandler::Contains(h) => h.materialize(args, db),
            PredicateHandler::SumOf(h) => h.materialize(args, db),
            PredicateHandler::ProductOf(h) => h.materialize(args, db),
            PredicateHandler::NotEqual(h) => h.materialize(args, db),
            PredicateHandler::NotContains(h) => h.materialize(args, db),
            PredicateHandler::MaxOf(h) => h.materialize(args, db),
            PredicateHandler::HashOf(h) => h.materialize(args, db),
        }
    }
}

/// A base trait for predicate handlers.
pub trait BasePredicateHandler {
    const NATIVE_PREDICATE: NativePredicate;
    const VALUE_COMPARISON_OPERATION: NativeOperation;
    const ARITY: usize;

    /// Given a set of arguments, materialize the statements that satisfy the predicate.
    ///
    /// Arguments are Options, with None representing a free variable.
    /// Otherwise arguments are ValueRefs, and as such may be anchored keys or Values.
    /// This method is not intended to be overridden by concrete handlers; instead, it
    /// provides a default implementation which delegates to the methods `check_values`,
    /// `lookup_statement`, `deduce_with_free_args`, and `special_derivation`, which can
    /// be overridden by concrete handlers to provide predicate-specific behavior.
    fn materialize(&self, args: &[Option<ValueRef>], db: &FactDB) -> HashSet<Fact> {
        let mut facts = HashSet::new();

        // Are all args bound?
        let maybe_value_refs: Option<Vec<ValueRef>> = args.iter().cloned().collect();

        if let Some(value_refs) = maybe_value_refs {
            // Can all args be resolved to values?
            let values: Option<Vec<Value>> = value_refs
                .iter()
                .map(|vr| db.value_ref_to_value(vr))
                .collect();
            // If so, we can attempt to construct a statement based on the concrete
            // values.
            if let Some(values) = values {
                // Do all values satisfy the predicate?
                if self.check_values(&values) {
                    facts.insert(Fact {
                        source: FactSource::Native(Self::VALUE_COMPARISON_OPERATION),
                        args: value_refs,
                    });
                }
            } else {
                // Some arguments are ValueRef anchored keys, for which we do not know the
                // values. We can check if a statement already exists for these arguments.
                if self.lookup_statement(&value_refs, db) {
                    facts.insert(Fact {
                        source: FactSource::Copy,
                        args: value_refs,
                    });
                }
            }
        } else {
            // We have some unbound args. We can attempt to deduce the values of the unbound
            // args.
            let deduced_args = self.deduce_with_free_args(args, db);
            if let Some(deduced_args) = deduced_args {
                facts.insert(Fact {
                    source: FactSource::Native(Self::VALUE_COMPARISON_OPERATION),
                    args: deduced_args,
                });
            }
        }

        // We can also attempt to derive the statement using special rules, e.g. transitive
        // equality.
        facts.extend(self.special_derivation(args, db));

        facts
    }

    /// Takes a set of arguments, of which at least one is None, representing a free variable.
    /// Returns a complete set of arguments, with the free variables replaced by the deduced
    /// values, or None if the arguments cannot be deduced.
    ///
    /// Where a new argument is deduced, it MUST be a Value, and cannot be an anchored key.
    #[allow(unused_variables)]
    fn deduce_with_free_args(
        &self,
        args: &[Option<ValueRef>],
        db: &FactDB,
    ) -> Option<Vec<ValueRef>> {
        None
    }

    /// Performs the predicate-specific "value-based" check. For example, Lt checks if the
    /// first argument is less than the second, and Contains checks if the the second and
    /// third arguments are contents of the first (e.g. key-value pairs in a dictionary).
    fn check_values(&self, args: &[Value]) -> bool;

    /// Checks if a statement already exists for the given arguments.
    fn lookup_statement(&self, args: &[ValueRef], db: &FactDB) -> bool {
        if Self::ARITY == 2 {
            if let Some(index) = db.get_binary_statement_index(&Self::NATIVE_PREDICATE) {
                index.contains_key(&[args[0].clone(), args[1].clone()])
            } else {
                false
            }
        } else if Self::ARITY == 3 {
            if let Some(index) = db.get_ternary_statement_index(&Self::NATIVE_PREDICATE) {
                index.contains_key(&[args[0].clone(), args[1].clone(), args[2].clone()])
            } else {
                false
            }
        } else {
            false
        }
    }

    /// Performs the predicate-specific "special" derivation. For example, Equal can be
    /// derived from transitive equality.
    #[allow(unused_variables)]
    fn special_derivation(&self, args: &[Option<ValueRef>], db: &FactDB) -> Option<Fact> {
        None
    }

    /// For other derivations, we know that we are either using CopyStatement or the
    /// predicate's VALUE_COMPARISON_OPERATION. For special derivations, we need to
    /// construct the specific operations needed.
    #[allow(unused_variables)]
    fn explain_special_derivation(
        &self,
        args: &[ValueRef],
        db: &FactDB,
    ) -> Result<Vec<Operation>, SolverError> {
        Ok(vec![])
    }
}

// --- Concrete Handler Implementations ---

#[derive(Clone, Copy)]
pub struct LtHandler;

impl BasePredicateHandler for LtHandler {
    const NATIVE_PREDICATE: NativePredicate = NativePredicate::Lt;
    const VALUE_COMPARISON_OPERATION: NativeOperation = NativeOperation::LtFromEntries;
    const ARITY: usize = 2;

    fn check_values(&self, args: &[Value]) -> bool {
        if let (TypedValue::Int(i1), TypedValue::Int(i2)) = (args[0].typed(), args[1].typed()) {
            i1 < i2
        } else {
            false
        }
    }
}

#[derive(Clone, Copy)]
pub struct LtEqHandler;

impl BasePredicateHandler for LtEqHandler {
    const NATIVE_PREDICATE: NativePredicate = NativePredicate::LtEq;
    const VALUE_COMPARISON_OPERATION: NativeOperation = NativeOperation::LtEqFromEntries;
    const ARITY: usize = 2;

    fn check_values(&self, args: &[Value]) -> bool {
        if let (TypedValue::Int(i1), TypedValue::Int(i2)) = (args[0].typed(), args[1].typed()) {
            i1 <= i2
        } else {
            false
        }
    }
}

#[derive(Clone, Copy)]
pub struct EqualHandler;

impl BasePredicateHandler for EqualHandler {
    const NATIVE_PREDICATE: NativePredicate = NativePredicate::Equal;
    const VALUE_COMPARISON_OPERATION: NativeOperation = NativeOperation::EqualFromEntries;
    const ARITY: usize = 2;

    fn check_values(&self, args: &[Value]) -> bool {
        let is_equal = args[0] == args[1];
        if is_equal {
            trace!("EqualHandler: {} == {}", args[0], args[1]);
        }
        is_equal
    }

    fn deduce_with_free_args(
        &self,
        args: &[Option<ValueRef>],
        db: &FactDB,
    ) -> Option<Vec<ValueRef>> {
        if args.len() != 2 {
            return None;
        }

        match (&args[0], &args[1]) {
            // ?X == bound -> bind ?X
            (None, Some(vr1)) => {
                if let ValueRef::Key(_) = vr1 {
                    // If the bound argument is an anchored key, we can set the
                    // wildcard to its *value*, but only if we know it.
                    db.value_ref_to_value(vr1)
                        .map(|value| vec![ValueRef::from(value.clone()), vr1.clone()])
                } else {
                    Some(vec![vr1.clone(), vr1.clone()])
                }
            }
            // bound == ?Y -> bind ?Y
            (Some(vr0), None) => {
                if let ValueRef::Key(_) = vr0 {
                    db.value_ref_to_value(vr0)
                        .map(|value| vec![vr0.clone(), ValueRef::from(value.clone())])
                } else {
                    // The bound argument is a value, so we can set the wildcard to it
                    // directly.
                    Some(vec![vr0.clone(), vr0.clone()])
                }
            }
            // Both sides already bound – nothing to deduce here.
            _ => None,
        }
    }

    // Equality can be derived via transitivity. We don't materialize the full set of
    // statements here, but we flag that it's possible. The full path will be materialized
    // during proof construction.
    fn special_derivation(&self, args: &[Option<ValueRef>], db: &FactDB) -> Option<Fact> {
        if args.len() == 2 {
            if let (Some(ValueRef::Key(key0)), Some(ValueRef::Key(key1))) = (&args[0], &args[1]) {
                if let Some(path) = db.find_path_and_nodes(key0, key1) {
                    if path.len() > 2 {
                        println!("Equality path: {:?}", path);
                        // If the path length is 2 (A and B), we don't need transitive equality.
                        return Some(Fact {
                            source: FactSource::Special,
                            args: vec![args[0].clone().unwrap(), args[1].clone().unwrap()],
                        });
                    } else {
                        return None;
                    }
                }
            }
        }

        None
    }

    fn explain_special_derivation(
        &self,
        args: &[ValueRef],
        db: &FactDB,
    ) -> Result<Vec<Operation>, SolverError> {
        if let (ValueRef::Key(key0), ValueRef::Key(key1)) = (&args[0], &args[1]) {
            if let Some(path) = db.find_path_and_nodes(key0, key1) {
                // Build a transitive-equality operation for every triple (A,B,C) along the path
                // A==B & B==C  =>  transitive_eq(A,B,C)
                let ops_res: Result<Vec<Operation>, SolverError> = path
                    .windows(3)
                    .map(|w| {
                        let (k0, k1, k2) = (w[0].clone(), w[1].clone(), w[2].clone());
                        let left_args = [ValueRef::Key(k0.clone()), ValueRef::Key(k1.clone())];
                        let right_args = [ValueRef::Key(k1), ValueRef::Key(k2)];

                        // Ensure both required Equal statements are asserted; otherwise bail.
                        if let Some(idx) = db.get_binary_statement_index(&NativePredicate::Equal) {
                            if idx.contains_key(&left_args) && idx.contains_key(&right_args) {
                                Ok(Operation::transitive_eq(
                                    &Statement::Equal(left_args[0].clone(), left_args[1].clone()),
                                    &Statement::Equal(right_args[0].clone(), right_args[1].clone()),
                                ))
                            } else {
                                Err(SolverError::Internal(
                                    "Equality path contains non-equal statements".to_string(),
                                ))
                            }
                        } else {
                            Err(SolverError::Internal(
                                "Equality index missing during proof construction".to_string(),
                            ))
                        }
                    })
                    .collect();

                return ops_res;
            }
        }
        Err(SolverError::Internal(
            "Equality path not found during proof construction".to_string(),
        ))
    }
}

#[derive(Clone, Copy)]
pub struct ContainsHandler;

impl BasePredicateHandler for ContainsHandler {
    const NATIVE_PREDICATE: NativePredicate = NativePredicate::Contains;
    const VALUE_COMPARISON_OPERATION: NativeOperation = NativeOperation::ContainsFromEntries;
    const ARITY: usize = 3;

    fn check_values(&self, args: &[Value]) -> bool {
        match args[0].typed() {
            TypedValue::Array(arr) => {
                if let TypedValue::Int(idx) = args[1].typed() {
                    if let Ok(i) = usize::try_from(*idx) {
                        arr.get(i).is_ok_and(|v| v == &args[2])
                    } else {
                        false
                    }
                } else {
                    false
                }
            }
            TypedValue::Dictionary(dict) => {
                if let TypedValue::String(s) = args[1].typed() {
                    dict.get(&Key::new(s.clone())).is_ok_and(|v| v == &args[2])
                } else {
                    false
                }
            }
            TypedValue::Set(set) => {
                // For a set, key and value must be the same.
                args[1] == args[2] && set.contains(&args[1])
            }
            _ => false,
        }
    }

    fn deduce_with_free_args(
        &self,
        args: &[Option<ValueRef>],
        db: &FactDB,
    ) -> Option<Vec<ValueRef>> {
        match (&args[0], &args[1], &args[2]) {
            (Some(vr1), Some(vr2), None) => {
                if let (Some(val1), Some(val2)) =
                    (db.value_ref_to_value(vr1), db.value_ref_to_value(vr2))
                {
                    if let TypedValue::Array(arr) = val1.typed() {
                        if let TypedValue::Int(idx) = val2.typed() {
                            if let Ok(i) = usize::try_from(*idx) {
                                if let Ok(val) = arr.get(i) {
                                    return Some(vec![
                                        vr1.clone(),
                                        vr2.clone(),
                                        ValueRef::from(val.clone()),
                                    ]);
                                }
                            }
                        }
                    }
                    if let TypedValue::Dictionary(dict) = val1.typed() {
                        if let TypedValue::String(s) = val2.typed() {
                            if let Ok(val) = dict.get(&Key::new(s.clone())) {
                                return Some(vec![
                                    vr1.clone(),
                                    vr2.clone(),
                                    ValueRef::from(val.clone()),
                                ]);
                            }
                        }
                    }
                    None
                } else {
                    None
                }
            }
            _ => None,
        }
    }
}

#[derive(Clone, Copy)]
pub struct NotContainsHandler;

impl BasePredicateHandler for NotContainsHandler {
    const NATIVE_PREDICATE: NativePredicate = NativePredicate::NotContains;
    const VALUE_COMPARISON_OPERATION: NativeOperation = NativeOperation::NotContainsFromEntries;
    const ARITY: usize = 2;

    fn check_values(&self, args: &[Value]) -> bool {
        match args[0].typed() {
            TypedValue::Array(arr) => {
                if let TypedValue::Int(idx) = args[1].typed() {
                    if let Ok(i) = usize::try_from(*idx) {
                        arr.get(i).is_err()
                    } else {
                        false
                    }
                } else {
                    false
                }
            }
            TypedValue::Dictionary(dict) => {
                if let TypedValue::String(s) = args[1].typed() {
                    dict.get(&Key::new(s.clone())).is_err()
                } else {
                    false
                }
            }
            TypedValue::Set(set) => !set.contains(&args[1]),
            _ => false,
        }
    }
}

#[derive(Copy, Clone)]
pub struct SumOfHandler;

impl BasePredicateHandler for SumOfHandler {
    const NATIVE_PREDICATE: NativePredicate = NativePredicate::SumOf;
    const VALUE_COMPARISON_OPERATION: NativeOperation = NativeOperation::SumOf;
    const ARITY: usize = 3;

    fn check_values(&self, args: &[Value]) -> bool {
        if let (TypedValue::Int(i1), TypedValue::Int(i2), TypedValue::Int(i3)) =
            (args[0].typed(), args[1].typed(), args[2].typed())
        {
            *i1 == *i2 + *i3
        } else {
            false
        }
    }

    fn deduce_with_free_args(
        &self,
        args: &[Option<ValueRef>],
        db: &FactDB,
    ) -> Option<Vec<ValueRef>> {
        let int = |vr: &ValueRef| {
            db.value_ref_to_value(vr).and_then(|v| match v.typed() {
                TypedValue::Int(i) => Some(*i),
                _ => None,
            })
        };

        match (&args[0], &args[1], &args[2]) {
            // SumOf(?x, 5, 10) -> x = 15
            (None, Some(vr1), Some(vr2)) => {
                if let (Some(i1), Some(i2)) = (int(vr1), int(vr2)) {
                    Some(vec![ValueRef::from(i1 + i2), vr1.clone(), vr2.clone()])
                } else {
                    None
                }
            }
            // SumOf(15, ?y, 10) -> y = 5
            (Some(vr0), None, Some(vr2)) => {
                if let (Some(i0), Some(i2)) = (int(vr0), int(vr2)) {
                    Some(vec![vr0.clone(), ValueRef::from(i0 - i2), vr2.clone()])
                } else {
                    None
                }
            }
            // SumOf(15, 5, ?z) -> z = 10
            (Some(vr0), Some(vr1), None) => {
                if let (Some(i0), Some(i1)) = (int(vr0), int(vr1)) {
                    Some(vec![vr0.clone(), vr1.clone(), ValueRef::from(i0 - i1)])
                } else {
                    None
                }
            }
            _ => None,
        }
    }
}

#[derive(Copy, Clone)]
pub struct ProductOfHandler;

impl BasePredicateHandler for ProductOfHandler {
    const NATIVE_PREDICATE: NativePredicate = NativePredicate::ProductOf;
    const VALUE_COMPARISON_OPERATION: NativeOperation = NativeOperation::ProductOf;
    const ARITY: usize = 3;

    fn check_values(&self, args: &[Value]) -> bool {
        if let (TypedValue::Int(i1), TypedValue::Int(i2), TypedValue::Int(i3)) =
            (args[0].typed(), args[1].typed(), args[2].typed())
        {
            *i1 == *i2 * *i3
        } else {
            false
        }
    }

    fn deduce_with_free_args(
        &self,
        args: &[Option<ValueRef>],
        db: &FactDB,
    ) -> Option<Vec<ValueRef>> {
        let int = |vr: &ValueRef| {
            db.value_ref_to_value(vr).and_then(|v| match v.typed() {
                TypedValue::Int(i) => Some(*i),
                _ => None,
            })
        };

        match (&args[0], &args[1], &args[2]) {
            // ProductOf(?x, 5, 10) -> x = 50
            (None, Some(vr1), Some(vr2)) => {
                if let (Some(i1), Some(i2)) = (int(vr1), int(vr2)) {
                    Some(vec![ValueRef::from(i1 * i2), vr1.clone(), vr2.clone()])
                } else {
                    None
                }
            }
            // ProductOf(50, ?y, 10) -> y = 5
            (Some(vr0), None, Some(vr2)) => {
                if let (Some(i0), Some(i2)) = (int(vr0), int(vr2)) {
                    Some(vec![vr0.clone(), ValueRef::from(i0 / i2), vr2.clone()])
                } else {
                    None
                }
            }
            // ProductOf(50, 5, ?z) -> z = 10
            (Some(vr0), Some(vr1), None) => {
                if let (Some(i0), Some(i1)) = (int(vr0), int(vr1)) {
                    Some(vec![vr0.clone(), vr1.clone(), ValueRef::from(i0 / i1)])
                } else {
                    None
                }
            }
            _ => None,
        }
    }
}

#[derive(Clone, Copy)]
pub struct NotEqualHandler;

impl BasePredicateHandler for NotEqualHandler {
    const NATIVE_PREDICATE: NativePredicate = NativePredicate::NotEqual;
    const VALUE_COMPARISON_OPERATION: NativeOperation = NativeOperation::NotEqualFromEntries;
    const ARITY: usize = 2;

    fn check_values(&self, args: &[Value]) -> bool {
        args[0] != args[1]
    }
}

#[derive(Copy, Clone)]
pub struct MaxOfHandler;

impl BasePredicateHandler for MaxOfHandler {
    const NATIVE_PREDICATE: NativePredicate = NativePredicate::MaxOf;
    const VALUE_COMPARISON_OPERATION: NativeOperation = NativeOperation::MaxOf;
    const ARITY: usize = 3;

    fn check_values(&self, args: &[Value]) -> bool {
        if let (TypedValue::Int(i1), TypedValue::Int(i2), TypedValue::Int(i3)) =
            (args[0].typed(), args[1].typed(), args[2].typed())
        {
            *i1 == *i2.max(i3)
        } else {
            false
        }
    }

    fn deduce_with_free_args(
        &self,
        args: &[Option<ValueRef>],
        db: &FactDB,
    ) -> Option<Vec<ValueRef>> {
        let int = |vr: &ValueRef| {
            db.value_ref_to_value(vr).and_then(|v| match v.typed() {
                TypedValue::Int(i) => Some(*i),
                _ => None,
            })
        };

        match (&args[0], &args[1], &args[2]) {
            // MaxOf(?x, 5, 10) -> x = 10
            (None, Some(vr1), Some(vr2)) => {
                if let (Some(i1), Some(i2)) = (int(vr1), int(vr2)) {
                    Some(vec![ValueRef::from(i1.max(i2)), vr1.clone(), vr2.clone()])
                } else {
                    None
                }
            }
            // MaxOf(10, ?y, 10) -> y = 10
            (Some(vr0), None, Some(vr2)) => {
                if let (Some(i0), Some(i2)) = (int(vr0), int(vr2)) {
                    Some(vec![vr0.clone(), ValueRef::from(i0.max(i2)), vr2.clone()])
                } else {
                    None
                }
            }
            // MaxOf(10, 10, ?z) -> z = 10
            (Some(vr0), Some(vr1), None) => {
                if let (Some(i0), Some(i1)) = (int(vr0), int(vr1)) {
                    Some(vec![vr0.clone(), vr1.clone(), ValueRef::from(i0.max(i1))])
                } else {
                    None
                }
            }
            _ => None,
        }
    }
}

#[derive(Copy, Clone)]
pub struct HashOfHandler;

impl BasePredicateHandler for HashOfHandler {
    const NATIVE_PREDICATE: NativePredicate = NativePredicate::HashOf;
    const VALUE_COMPARISON_OPERATION: NativeOperation = NativeOperation::HashOf;
    const ARITY: usize = 3;

    fn check_values(&self, args: &[Value]) -> bool {
        let hash_val = Value::from(hash_values(&[args[1].clone(), args[2].clone()]));
        args[0] == hash_val
    }

    fn deduce_with_free_args(
        &self,
        args: &[Option<ValueRef>],
        db: &FactDB,
    ) -> Option<Vec<ValueRef>> {
        match (&args[0], &args[1], &args[2]) {
            // HashOf(?x, 5, 10) -> x = hash(5, 10)
            (None, Some(vr1), Some(vr2)) => {
                if let (Some(val1), Some(val2)) =
                    (db.value_ref_to_value(vr1), db.value_ref_to_value(vr2))
                {
                    Some(vec![
                        ValueRef::from(hash_values(&[val1, val2])),
                        vr1.clone(),
                        vr2.clone(),
                    ])
                } else {
                    None
                }
            }
            // HashOf(hash(5, 10), 5, 10) -> x = hash(5, 10)
            (Some(vr0), None, Some(vr2)) => {
                if let (Some(val0), Some(val2)) =
                    (db.value_ref_to_value(vr0), db.value_ref_to_value(vr2))
                {
                    Some(vec![
                        vr0.clone(),
                        ValueRef::from(hash_values(&[val0, val2])),
                        vr2.clone(),
                    ])
                } else {
                    None
                }
            }
            _ => None,
        }
    }
}
