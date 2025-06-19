//! Defines the traits and implementations for handling native Datalog predicates.
//! This modular approach allows for easy extension and testing of predicate logic.

use std::collections::HashSet;

use log::trace;

use crate::{
    middleware::{hash_values, Key, NativePredicate, TypedValue, Value, ValueRef},
    solver::{
        db::FactDB,
        engine::semi_naive::{Fact, FactSource, JustificationKind},
    },
};

// --- Handler Enum ---

/// An enum that dispatches to the correct handler for a given native predicate.
/// This uses static dispatch, avoiding vtable lookups for performance.
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
pub trait SimplePredicateHandler {
    const NATIVE_PREDICATE: NativePredicate;
    const ARITY: usize;

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
            if let Some(values) = values {
                // Do all values satisfy the predicate?
                if Self::NATIVE_PREDICATE == NativePredicate::Equal {
                    trace!(
                        "EqualHandler candidate: {:?} == {:?}",
                        db.value_ref_to_value(&value_refs[0]),
                        db.value_ref_to_value(&value_refs[1])
                    );
                }

                if self.check_values(&values) {
                    facts.insert(Fact {
                        source: FactSource::External(JustificationKind::Computation),
                        args: value_refs,
                    });
                }
            } else {
                // We don't know the values, so let's see if we can find a statement to copy.
                if self.lookup_statement(&value_refs, db) {
                    facts.insert(Fact {
                        source: FactSource::External(JustificationKind::Fact),
                        args: value_refs,
                    });
                }
            }
        } else {
            // We have some unbound args.
            let deduced_args = self.deduce_with_free_args(args, db);
            if let Some(deduced_args) = deduced_args {
                facts.insert(Fact {
                    source: FactSource::External(JustificationKind::Computation),
                    args: deduced_args,
                });
            }
        }

        facts.extend(self.special_derivation(args, db));
        trace!("materialize result: {:?}", facts);
        facts
    }

    #[allow(unused_variables)]
    fn deduce_with_free_args(
        &self,
        args: &[Option<ValueRef>],
        db: &FactDB,
    ) -> Option<Vec<ValueRef>> {
        None
    }

    fn check_values(&self, args: &[Value]) -> bool;

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

    #[allow(unused_variables)]
    fn special_derivation(&self, args: &[Option<ValueRef>], db: &FactDB) -> HashSet<Fact> {
        HashSet::new()
    }

    // We want predicate handlers to be able to materialize statements.
    // This can occur in four different scenarios:
    // - All args resolve to values
    // - Some args are unbound
    // - At least some args are anchored keys which do not resolve to values
    // - "Special" derivations, e.g. transitive equality
}

// --- Concrete Handler Implementations ---

#[derive(Clone, Copy)]
pub struct LtHandler;

impl SimplePredicateHandler for LtHandler {
    const NATIVE_PREDICATE: NativePredicate = NativePredicate::Lt;
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

impl SimplePredicateHandler for LtEqHandler {
    const NATIVE_PREDICATE: NativePredicate = NativePredicate::LtEq;
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

impl SimplePredicateHandler for EqualHandler {
    const NATIVE_PREDICATE: NativePredicate = NativePredicate::Equal;
    const ARITY: usize = 2;

    fn check_values(&self, args: &[Value]) -> bool {
        let is_equal = args[0] == args[1];
        if is_equal {
            trace!("EqualHandler: {}", is_equal);
        }
        is_equal
    }

    fn deduce_with_free_args(
        &self,
        args: &[Option<ValueRef>],
        _db: &FactDB,
    ) -> Option<Vec<ValueRef>> {
        if args.len() == 2 {
            // If the first arg is bound, second must not be.
            if let Some(val0) = &args[0] {
                Some(vec![val0.clone(), val0.clone()])
                // Other way around
            } else if let Some(val1) = &args[1] {
                Some(vec![val1.clone(), val1.clone()])
            } else {
                panic!("At least one arg must be bound");
            }
        } else {
            panic!("EqualHandler should have 2 args");
        }
    }
}

#[derive(Clone, Copy)]
pub struct ContainsHandler;

impl SimplePredicateHandler for ContainsHandler {
    const NATIVE_PREDICATE: NativePredicate = NativePredicate::Contains;
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
}

#[derive(Clone, Copy)]
pub struct NotContainsHandler;

impl SimplePredicateHandler for NotContainsHandler {
    const NATIVE_PREDICATE: NativePredicate = NativePredicate::NotContains;
    const ARITY: usize = 3;

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

impl SimplePredicateHandler for SumOfHandler {
    const NATIVE_PREDICATE: NativePredicate = NativePredicate::SumOf;
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

impl SimplePredicateHandler for ProductOfHandler {
    const NATIVE_PREDICATE: NativePredicate = NativePredicate::ProductOf;
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

impl SimplePredicateHandler for NotEqualHandler {
    const NATIVE_PREDICATE: NativePredicate = NativePredicate::NotEqual;
    const ARITY: usize = 2;

    fn check_values(&self, args: &[Value]) -> bool {
        args[0] != args[1]
    }
}

#[derive(Copy, Clone)]
pub struct MaxOfHandler;

impl SimplePredicateHandler for MaxOfHandler {
    const NATIVE_PREDICATE: NativePredicate = NativePredicate::MaxOf;
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

impl SimplePredicateHandler for HashOfHandler {
    const NATIVE_PREDICATE: NativePredicate = NativePredicate::HashOf;
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
