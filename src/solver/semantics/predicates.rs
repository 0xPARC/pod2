//! Defines the traits and implementations for handling native Datalog predicates.
//! This modular approach allows for easy extension and testing of predicate logic.

use crate::{
    middleware::{
        hash_values, Key, NativePredicate, StatementTmplArg, TypedValue, Value, ValueRef,
    },
    solver::{
        engine::semi_naive::{self, Fact, FactSource},
        error::SolverError,
        ir::{self},
        semantics::{
            enumerator::{StreamItem, TypeFilter},
            provider::PodSemantics,
        },
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
    // The fact that we have to know the types of the semi-naive engine is a bit of a code smell
    // TODO think about how to fix this
    fn iter_binary_facts_helper<'a, H>(
        &self,
        handler: H,
        semantics: &'a PodSemantics,
        literal: &'a ir::Literal,
        bindings: &'a semi_naive::Bindings,
    ) -> Result<Box<dyn Iterator<Item = Fact> + 'a>, SolverError>
    where
        H: BinaryPredicateHandler,
    {
        let native_pred = H::NATIVE_PREDICATE;
        let arg_to_vr = |arg: &StatementTmplArg| -> Option<ValueRef> {
            match arg {
                StatementTmplArg::Literal(v) => Some(ValueRef::Literal(v.clone())),
                StatementTmplArg::Wildcard(w) => {
                    let binding = bindings.get(w);
                    if let Some(vr) = binding {
                        if let Some(val) = semantics.db.value_ref_to_value(vr) {
                            Some(ValueRef::Literal(val))
                        } else {
                            None
                        }
                    } else {
                        None
                    }
                }
                // TODO: AnchoredKey?
                _ => None,
            }
        };

        let filters = [arg_to_vr(&literal.terms[0]), arg_to_vr(&literal.terms[1])];
        if let Some(db_facts) = semantics.db.get_binary_statement_index(&native_pred) {
            let fact_iter =
                semantics.iter_binary_facts(filters, handler, db_facts, handler.type_filters())?;
            let mapped_iter = fact_iter.filter_map(move |(fact_vrs, justification)| {
                if let (Some(v1), Some(v2)) = (
                    semantics.db.value_ref_to_value(&fact_vrs[0]),
                    semantics.db.value_ref_to_value(&fact_vrs[1]),
                ) {
                    Some(Fact {
                        source: FactSource::External(justification),
                        tuple: vec![ValueRef::Literal(v1), ValueRef::Literal(v2)],
                    })
                } else {
                    None
                }
            });
            Ok(Box::new(mapped_iter))
        } else {
            Ok(Box::new(std::iter::empty()))
        }
    }

    fn iter_ternary_facts_helper<'a, H>(
        &self,
        handler: H,
        semantics: &'a PodSemantics,
        literal: &'a ir::Literal,
        bindings: &'a semi_naive::Bindings,
    ) -> Result<Box<dyn Iterator<Item = Fact> + 'a>, SolverError>
    where
        H: TernaryPredicateHandler,
    {
        let native_pred = H::NATIVE_PREDICATE;
        let arg_to_vr = |arg: &StatementTmplArg| -> Option<ValueRef> {
            match arg {
                StatementTmplArg::Literal(v) => Some(ValueRef::Literal(v.clone())),
                StatementTmplArg::Wildcard(w) => {
                    let binding = bindings.get(w);
                    if let Some(vr) = binding {
                        if let Some(val) = semantics.db.value_ref_to_value(vr) {
                            Some(ValueRef::Literal(val))
                        } else {
                            None
                        }
                    } else {
                        None
                    }
                }
                // TODO: AnchoredKey?
                _ => None,
            }
        };

        let filters = [
            arg_to_vr(&literal.terms[0]),
            arg_to_vr(&literal.terms[1]),
            arg_to_vr(&literal.terms[2]),
        ];
        if let Some(db_facts) = semantics.db.get_ternary_statement_index(&native_pred) {
            let fact_iter =
                semantics.iter_ternary_facts(filters, handler, db_facts, handler.type_filters())?;
            let mapped_iter = fact_iter.filter_map(move |(fact_vrs, justification)| {
                if let (Some(v1), Some(v2), Some(v3)) = (
                    semantics.db.value_ref_to_value(&fact_vrs[0]),
                    semantics.db.value_ref_to_value(&fact_vrs[1]),
                    semantics.db.value_ref_to_value(&fact_vrs[2]),
                ) {
                    Some(Fact {
                        source: FactSource::External(justification),
                        tuple: vec![
                            ValueRef::Literal(v1),
                            ValueRef::Literal(v2),
                            ValueRef::Literal(v3),
                        ],
                    })
                } else {
                    None
                }
            });
            Ok(Box::new(mapped_iter))
        } else {
            Ok(Box::new(std::iter::empty()))
        }
    }

    pub fn iter_facts<'a>(
        &self,
        semantics: &'a PodSemantics,
        literal: &'a ir::Literal,
        bindings: &'a semi_naive::Bindings,
    ) -> Result<impl Iterator<Item = Fact> + 'a, SolverError> {
        let iter: Box<dyn Iterator<Item = Fact> + 'a> = match self {
            PredicateHandler::Lt(h) => {
                self.iter_binary_facts_helper(*h, semantics, literal, bindings)?
            }
            PredicateHandler::LtEq(h) => {
                self.iter_binary_facts_helper(*h, semantics, literal, bindings)?
            }
            PredicateHandler::Equal(h) => {
                self.iter_binary_facts_helper(*h, semantics, literal, bindings)?
            }
            PredicateHandler::Contains(h) => {
                self.iter_ternary_facts_helper(*h, semantics, literal, bindings)?
            }
            PredicateHandler::SumOf(h) => {
                self.iter_ternary_facts_helper(*h, semantics, literal, bindings)?
            }
            PredicateHandler::ProductOf(h) => {
                self.iter_ternary_facts_helper(*h, semantics, literal, bindings)?
            }
            PredicateHandler::NotEqual(h) => {
                self.iter_binary_facts_helper(*h, semantics, literal, bindings)?
            }
            PredicateHandler::NotContains(h) => {
                self.iter_binary_facts_helper(*h, semantics, literal, bindings)?
            }
            PredicateHandler::MaxOf(h) => {
                self.iter_ternary_facts_helper(*h, semantics, literal, bindings)?
            }
            PredicateHandler::HashOf(h) => {
                self.iter_ternary_facts_helper(*h, semantics, literal, bindings)?
            }
        };
        Ok(iter)
    }
}

// --- Handler Traits ---

/// A contract for native predicates that take two arguments.
pub trait BinaryPredicateHandler: Copy + Send + Sync + 'static {
    const NATIVE_PREDICATE: NativePredicate;

    /// Returns the required types for the arguments (e.g., Numeric).
    fn type_filters(&self) -> [TypeFilter; 2];

    /// The core value-checking logic for the predicate.
    fn check_values(&self, val1: &Value, val2: &Value) -> bool;

    /// Attempts to deduce any unbound arguments from the bound ones.
    /// Mutates the slice in place and returns `true` if a value was deduced.
    fn deduce_args(&self, _args: &mut [StreamItem; 2]) -> bool {
        // Default implementation does nothing.
        false
    }

    /// PROVIDED: Default implementation for checking StreamItems.
    /// This contains the boilerplate and calls check_values.
    fn check_streams(&self, v1: &StreamItem, v2: &StreamItem) -> Option<(StreamItem, StreamItem)> {
        let mut items = [v1.clone(), v2.clone()];

        // Attempt to deduce any free variables first.
        self.deduce_args(&mut items);

        // After deduction, check if all arguments are now concrete.
        if let (StreamItem::Concrete(val1), StreamItem::Concrete(val2)) = (&items[0], &items[1]) {
            if self.check_values(val1, val2) {
                Some((items[0].clone(), items[1].clone()))
            } else {
                None
            }
        } else {
            // If deduction was not possible and args are still not concrete.
            None
        }
    }

    /// PROVIDED: A default implementation for checking if a ground literal is
    /// a valid EDB fact. Used during proof reconstruction.
    fn is_edb_fact(&self, _semantics: &PodSemantics, args: &[Value]) -> bool {
        if args.len() == 2 {
            self.check_values(&args[0], &args[1])
        } else {
            false
        }
    }
}

/// A contract for native predicates that take three arguments.
pub trait TernaryPredicateHandler: Copy + Send + Sync + 'static {
    const NATIVE_PREDICATE: NativePredicate;

    /// Returns the required types for the arguments.
    fn type_filters(&self) -> [TypeFilter; 3];

    /// The core value-checking logic for the predicate.
    fn check_values(&self, v1: &Value, v2: &Value, v3: &Value) -> bool;

    /// Attempts to deduce any unbound arguments from the bound ones.
    /// Mutates the slice in place and returns `true` if a value was deduced.
    fn deduce_args(&self, _args: &mut [StreamItem; 3]) -> bool {
        // Default implementation does nothing.
        false
    }

    /// PROVIDED: Default implementation for checking StreamItems.
    fn check_streams(
        &self,
        v1: &StreamItem,
        v2: &StreamItem,
        v3: &StreamItem,
    ) -> Option<(StreamItem, StreamItem, StreamItem)> {
        let mut items = [v1.clone(), v2.clone(), v3.clone()];

        // Attempt to deduce any free variables first.
        self.deduce_args(&mut items);

        if let (
            StreamItem::Concrete(val1),
            StreamItem::Concrete(val2),
            StreamItem::Concrete(val3),
        ) = (&items[0], &items[1], &items[2])
        {
            if self.check_values(val1, val2, val3) {
                Some((items[0].clone(), items[1].clone(), items[2].clone()))
            } else {
                None
            }
        } else {
            None
        }
    }

    /// PROVIDED: A default implementation for checking if a ground literal is a valid EDB fact.
    fn is_edb_fact(&self, _semantics: &PodSemantics, args: &[Value]) -> bool {
        if args.len() == 3 {
            self.check_values(&args[0], &args[1], &args[2])
        } else {
            false
        }
    }
}

// --- Concrete Handler Implementations ---

#[derive(Clone, Copy)]
pub struct LtHandler;

impl BinaryPredicateHandler for LtHandler {
    const NATIVE_PREDICATE: NativePredicate = NativePredicate::Lt;

    fn type_filters(&self) -> [TypeFilter; 2] {
        [TypeFilter::Int, TypeFilter::Int]
    }

    fn check_values(&self, val1: &Value, val2: &Value) -> bool {
        if let (TypedValue::Int(i1), TypedValue::Int(i2)) = (val1.typed(), val2.typed()) {
            i1 < i2
        } else {
            false
        }
    }
}

#[derive(Clone, Copy)]
pub struct LtEqHandler;

impl BinaryPredicateHandler for LtEqHandler {
    const NATIVE_PREDICATE: NativePredicate = NativePredicate::LtEq;

    fn type_filters(&self) -> [TypeFilter; 2] {
        [TypeFilter::Int, TypeFilter::Int]
    }

    fn check_values(&self, val1: &Value, val2: &Value) -> bool {
        // This leverages the derived PartialOrd on `Value`
        val1 <= val2
    }
}

#[derive(Clone, Copy)]
pub struct EqualHandler;

impl BinaryPredicateHandler for EqualHandler {
    const NATIVE_PREDICATE: NativePredicate = NativePredicate::Equal;

    fn type_filters(&self) -> [TypeFilter; 2] {
        [TypeFilter::Any, TypeFilter::Any]
    }

    fn check_values(&self, val1: &Value, val2: &Value) -> bool {
        val1 == val2
    }

    fn deduce_args(&self, args: &mut [StreamItem; 2]) -> bool {
        match (&args[0], &args[1]) {
            // Case 1: ?x = 5. Bind ?x to 5.
            (StreamItem::UnboundWildcard, StreamItem::Concrete(val)) => {
                args[0] = StreamItem::Concrete(val.clone());
                true
            }
            // Case 2: 5 = ?x. Bind ?x to 5.
            (StreamItem::Concrete(val), StreamItem::UnboundWildcard) => {
                args[1] = StreamItem::Concrete(val.clone());
                true
            }
            // No other cases can be deduced.
            _ => false,
        }
    }
}

#[derive(Clone, Copy)]
pub struct ContainsHandler;

impl TernaryPredicateHandler for ContainsHandler {
    const NATIVE_PREDICATE: NativePredicate = NativePredicate::Contains;

    fn type_filters(&self) -> [TypeFilter; 3] {
        [
            TypeFilter::Container,
            TypeFilter::Any, // Key can be int or string
            TypeFilter::Any,
        ]
    }

    fn check_values(&self, container: &Value, key: &Value, value: &Value) -> bool {
        match container.typed() {
            TypedValue::Array(arr) => {
                if let TypedValue::Int(idx) = key.typed() {
                    if let Ok(i) = usize::try_from(*idx) {
                        arr.get(i).is_ok_and(|v| v == value)
                    } else {
                        false
                    }
                } else {
                    false
                }
            }
            TypedValue::Dictionary(dict) => {
                if let TypedValue::String(s) = key.typed() {
                    dict.get(&Key::new(s.clone())).is_ok_and(|v| v == value)
                } else {
                    false
                }
            }
            TypedValue::Set(set) => {
                // For a set, key and value must be the same.
                key == value && set.contains(key)
            }
            _ => false,
        }
    }
}

#[derive(Clone, Copy)]
pub struct NotContainsHandler;

impl BinaryPredicateHandler for NotContainsHandler {
    const NATIVE_PREDICATE: NativePredicate = NativePredicate::NotContains;

    fn type_filters(&self) -> [TypeFilter; 2] {
        [TypeFilter::Container, TypeFilter::Any]
    }

    fn check_values(&self, container: &Value, key: &Value) -> bool {
        match container.typed() {
            TypedValue::Array(arr) => {
                if let TypedValue::Int(idx) = key.typed() {
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
                if let TypedValue::String(s) = key.typed() {
                    dict.get(&Key::new(s.clone())).is_err()
                } else {
                    false
                }
            }
            TypedValue::Set(set) => !set.contains(key),
            _ => false,
        }
    }
}

#[derive(Copy, Clone)]
pub struct SumOfHandler;

impl TernaryPredicateHandler for SumOfHandler {
    const NATIVE_PREDICATE: NativePredicate = NativePredicate::SumOf;

    fn type_filters(&self) -> [TypeFilter; 3] {
        [TypeFilter::Int, TypeFilter::Int, TypeFilter::Int]
    }

    fn check_values(&self, v1: &Value, v2: &Value, v3: &Value) -> bool {
        if let (&TypedValue::Int(i1), &TypedValue::Int(i2), &TypedValue::Int(i3)) =
            (v1.typed(), v2.typed(), v3.typed())
        {
            i1 == i2 + i3
        } else {
            false
        }
    }

    fn deduce_args(&self, args: &mut [StreamItem; 3]) -> bool {
        match (&args[0], &args[1], &args[2]) {
            // SumOf(?x, 5, 10) -> x = 15
            (
                StreamItem::UnboundWildcard,
                StreamItem::Concrete(val2),
                StreamItem::Concrete(val3),
            ) => {
                if let (&TypedValue::Int(i2), &TypedValue::Int(i3)) = (val2.typed(), val3.typed()) {
                    let new_val = Value::from(i2 + i3);
                    args[0] = StreamItem::Concrete(new_val);
                    return true;
                }
            }
            // SumOf(15, ?y, 10) -> y = 5
            (
                StreamItem::Concrete(val1),
                StreamItem::UnboundWildcard,
                StreamItem::Concrete(val3),
            ) => {
                if let (&TypedValue::Int(i1), &TypedValue::Int(i3)) = (val1.typed(), val3.typed()) {
                    let new_val = Value::from(i1 - i3);
                    args[1] = StreamItem::Concrete(new_val);
                    return true;
                }
            }
            // SumOf(15, 5, ?z) -> z = 10
            (
                StreamItem::Concrete(val1),
                StreamItem::Concrete(val2),
                StreamItem::UnboundWildcard,
            ) => {
                if let (&TypedValue::Int(i1), &TypedValue::Int(i2)) = (val1.typed(), val2.typed()) {
                    let new_val = Value::from(i1 - i2);
                    args[2] = StreamItem::Concrete(new_val);
                    return true;
                }
            }
            _ => {}
        }
        false
    }
}

#[derive(Copy, Clone)]
pub struct ProductOfHandler;

impl TernaryPredicateHandler for ProductOfHandler {
    const NATIVE_PREDICATE: NativePredicate = NativePredicate::ProductOf;

    fn type_filters(&self) -> [TypeFilter; 3] {
        [TypeFilter::Int, TypeFilter::Int, TypeFilter::Int]
    }

    fn check_values(&self, v1: &Value, v2: &Value, v3: &Value) -> bool {
        if let (&TypedValue::Int(i1), &TypedValue::Int(i2), &TypedValue::Int(i3)) =
            (v1.typed(), v2.typed(), v3.typed())
        {
            i1 == i2 * i3
        } else {
            false
        }
    }

    fn deduce_args(&self, args: &mut [StreamItem; 3]) -> bool {
        match (&args[0], &args[1], &args[2]) {
            // ProductOf(?x, 5, 10) -> x = 50
            (
                StreamItem::UnboundWildcard,
                StreamItem::Concrete(val2),
                StreamItem::Concrete(val3),
            ) => {
                if let (&TypedValue::Int(i2), &TypedValue::Int(i3)) = (val2.typed(), val3.typed()) {
                    let new_val = Value::from(i2 * i3);
                    args[0] = StreamItem::Concrete(new_val);
                    return true;
                }
            }
            // ProductOf(50, ?y, 10) -> y = 5
            (
                StreamItem::Concrete(val1),
                StreamItem::UnboundWildcard,
                StreamItem::Concrete(val3),
            ) => {
                if let (&TypedValue::Int(i1), &TypedValue::Int(i3)) = (val1.typed(), val3.typed()) {
                    let i2 = i1 / i3;
                    // Check if the division is exact
                    if i2 * i3 != i1 {
                        return false;
                    }
                    let new_val = Value::from(i2);
                    args[1] = StreamItem::Concrete(new_val);
                    return true;
                }
            }
            // ProductOf(50, 5, ?z) -> z = 10
            (
                StreamItem::Concrete(val1),
                StreamItem::Concrete(val2),
                StreamItem::UnboundWildcard,
            ) => {
                if let (&TypedValue::Int(i1), &TypedValue::Int(i2)) = (val1.typed(), val2.typed()) {
                    let i3 = i1 / i2;
                    // Check if the division is exact
                    if i3 * i2 != i1 {
                        return false;
                    }
                    let new_val = Value::from(i3);
                    args[2] = StreamItem::Concrete(new_val);
                    return true;
                }
            }
            _ => {}
        }
        false
    }
}

#[derive(Clone, Copy)]
pub struct NotEqualHandler;

impl BinaryPredicateHandler for NotEqualHandler {
    const NATIVE_PREDICATE: NativePredicate = NativePredicate::NotEqual;

    fn type_filters(&self) -> [TypeFilter; 2] {
        [TypeFilter::Any, TypeFilter::Any]
    }

    fn check_values(&self, val1: &Value, val2: &Value) -> bool {
        val1 != val2
    }
}

#[derive(Copy, Clone)]
pub struct MaxOfHandler;

impl TernaryPredicateHandler for MaxOfHandler {
    const NATIVE_PREDICATE: NativePredicate = NativePredicate::MaxOf;

    fn type_filters(&self) -> [TypeFilter; 3] {
        [TypeFilter::Int, TypeFilter::Int, TypeFilter::Int]
    }

    fn check_values(&self, v1: &Value, v2: &Value, v3: &Value) -> bool {
        if let (&TypedValue::Int(i1), &TypedValue::Int(i2), &TypedValue::Int(i3)) =
            (v1.typed(), v2.typed(), v3.typed())
        {
            i1 == i2.max(i3)
        } else {
            false
        }
    }

    fn deduce_args(&self, args: &mut [StreamItem; 3]) -> bool {
        match (&args[0], &args[1], &args[2]) {
            // MaxOf(?x, 5, 10) -> x = 10
            (
                StreamItem::UnboundWildcard,
                StreamItem::Concrete(val2),
                StreamItem::Concrete(val3),
            ) => {
                if let (&TypedValue::Int(i2), &TypedValue::Int(i3)) = (val2.typed(), val3.typed()) {
                    let new_val = Value::from(i2.max(i3));
                    args[0] = StreamItem::Concrete(new_val);
                    return true;
                }
            }
            // MaxOf(10, ?y, 10) -> y = 10
            (
                StreamItem::Concrete(val1),
                StreamItem::UnboundWildcard,
                StreamItem::Concrete(val3),
            ) => {
                if let (&TypedValue::Int(i1), &TypedValue::Int(i3)) = (val1.typed(), val3.typed()) {
                    let new_val = Value::from(i1.max(i3));
                    args[1] = StreamItem::Concrete(new_val);
                    return true;
                }
            }
            // MaxOf(10, 10, ?z) -> z = 10
            (
                StreamItem::Concrete(val1),
                StreamItem::Concrete(val2),
                StreamItem::UnboundWildcard,
            ) => {
                if let (&TypedValue::Int(i1), &TypedValue::Int(i2)) = (val1.typed(), val2.typed()) {
                    let new_val = Value::from(i1.max(i2));
                    args[2] = StreamItem::Concrete(new_val);
                    return true;
                }
            }
            _ => {}
        }
        false
    }
}

#[derive(Copy, Clone)]
pub struct HashOfHandler;

impl TernaryPredicateHandler for HashOfHandler {
    const NATIVE_PREDICATE: NativePredicate = NativePredicate::HashOf;

    fn type_filters(&self) -> [TypeFilter; 3] {
        [TypeFilter::Int, TypeFilter::Int, TypeFilter::Int]
    }

    fn check_values(&self, v1: &Value, v2: &Value, v3: &Value) -> bool {
        let hash_val = Value::from(hash_values(&[v2.clone(), v3.clone()]));
        *v1 == hash_val
    }

    fn deduce_args(&self, args: &mut [StreamItem; 3]) -> bool {
        match (&args[0], &args[1], &args[2]) {
            // HashOf(?x, 5, 10) -> x = hash(5, 10)
            (
                StreamItem::UnboundWildcard,
                StreamItem::Concrete(val2),
                StreamItem::Concrete(val3),
            ) => {
                let new_val = Value::from(hash_values(&[val2.clone(), val3.clone()]));
                args[0] = StreamItem::Concrete(new_val);
                return true;
            }
            _ => {}
        }
        false
    }
}
