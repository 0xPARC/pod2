use std::{collections::HashMap, sync::Arc};

use crate::{
    middleware::{CustomPredicateRef, PodId, TypedValue, Value, ValueRef},
    solver::{
        db::FactDB,
        error::SolverError,
        semantics::{
            predicates::{BinaryPredicateHandler, TernaryPredicateHandler},
            provider::JustificationKind,
        },
    },
};

/// Represents an item produced by a value stream during the solving process.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum StreamItem {
    /// A concrete value, sourced from either a literal in the goal
    /// or a fact in the database.
    Concrete(Value),
    /// Represents an unbound wildcard literal. This signals to the predicate
    /// handler that this argument slot could be a target for a new binding.
    UnboundWildcard,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum TypeFilter {
    Any,
    Int,
    Container,
    String,
}

fn check_type(value: &Value, filter: &TypeFilter) -> bool {
    match filter {
        TypeFilter::Any => true,
        TypeFilter::Int => matches!(value.typed(), TypedValue::Int(_)),
        TypeFilter::Container => matches!(
            value.typed(),
            TypedValue::Array(_) | TypedValue::Dictionary(_) | TypedValue::Set(_)
        ),
        TypeFilter::String => matches!(value.typed(), TypedValue::String(_)),
    }
}

pub struct ValueStream<'a> {
    inner: Box<dyn Iterator<Item = (ValueRef, StreamItem)> + 'a>,
}

impl<'a> ValueStream<'a> {
    pub fn new(iter: Box<dyn Iterator<Item = (ValueRef, StreamItem)> + 'a>) -> Self {
        Self { inner: iter }
    }

    pub fn with_type_filter(self, filter: TypeFilter) -> Self {
        if filter == TypeFilter::Any {
            return self;
        }

        let new_iter = self.inner.filter(move |(_, item)| {
            if let StreamItem::Concrete(v) = item {
                return check_type(v, &filter);
            }
            true // Don't filter out unbound wildcards yet
        });

        Self::new(Box::new(new_iter))
    }
}

impl Iterator for ValueStream<'_> {
    type Item = (ValueRef, StreamItem);

    fn next(&mut self) -> Option<Self::Item> {
        self.inner.next()
    }
}

pub type CandidateTupleStream<'a, const N: usize> =
    Box<dyn Iterator<Item = ([ValueRef; N], JustificationKind)> + 'a>;

/// A `FactEnumerator` is responsible for the generic, low-level machinery
/// for finding and streaming candidate value-tuples from the database.
#[derive(Clone)]
pub struct FactEnumerator {
    db: Arc<FactDB>,
}

impl FactEnumerator {
    pub fn new(db: Arc<FactDB>) -> Self {
        Self { db }
    }

    /// This is used by the generic core enumerator.
    fn get_stream_for_filter<'a>(&'a self, filter: Option<ValueRef>) -> ValueStream<'a> {
        let iter: Box<dyn Iterator<Item = (ValueRef, StreamItem)> + 'a> = if let Some(vr) = filter {
            // If filter is bound, produce a single concrete value if it can be resolved.
            if let Some(val) = self.db.value_ref_to_value(&vr) {
                Box::new(std::iter::once((vr, StreamItem::Concrete(val))))
            } else {
                Box::new(std::iter::empty())
            }
        } else {
            // If filter is unbound, produce the `UnboundWildcard` sentinel.
            Box::new(std::iter::once((
                // This ValueRef is a placeholder for provenance, since there's no
                // concrete source for an unbound variable.
                ValueRef::Literal(Value::from("unbound_placeholder")),
                StreamItem::UnboundWildcard,
            )))
        };
        ValueStream::new(iter)
    }

    /// Core logic for finding binary predicate candidates. It is generic over
    /// its filters and can be used by both top-down and bottom-up engines.
    pub(super) fn enumerate_binary_candidates_core<'a, C>(
        &'a self,
        filters: [Option<ValueRef>; 2],
        checker: C,
        db_facts: &'a HashMap<[ValueRef; 2], Vec<PodId>>,
        type_filters: [TypeFilter; 2],
    ) -> Result<CandidateTupleStream<'a, 2>, SolverError>
    where
        C: BinaryPredicateHandler + 'a,
    {
        // --- Path 0: Fast path for fully-bound computation ---
        if let (Some(vr1), Some(vr2)) = (&filters[0], &filters[1]) {
            let val1 = self.db.value_ref_to_value(vr1);
            let val2 = self.db.value_ref_to_value(vr2);

            if let (Some(v1), Some(v2)) = (val1, val2) {
                if check_type(&v1, &type_filters[0])
                    && check_type(&v2, &type_filters[1])
                    && checker
                        .check_streams(&StreamItem::Concrete(v1), &StreamItem::Concrete(v2))
                        .is_some()
                {
                    let iter: Box<dyn Iterator<Item = _> + 'a> = Box::new(std::iter::once((
                        [vr1.clone(), vr2.clone()],
                        JustificationKind::Computation,
                    )));
                    return Ok(iter);
                }
            }
        }

        // --- Path 1: Unification against the statement index. ---
        // Find all facts that match the (potentially sparse) filters.
        let unification_solutions = db_facts
            .keys()
            .filter({
                let filters = filters.clone();
                move |[vr1, vr2]| {
                    let p1 = filters[0].as_ref().map_or(true, |f| f == vr1);
                    let p2 = filters[1].as_ref().map_or(true, |f| f == vr2);
                    p1 && p2
                }
            })
            .map(|fact| (fact.clone(), JustificationKind::Fact));

        // --- Path 2: Solve by computation using value streams. ---
        let stream1 = self
            .get_stream_for_filter(filters[0].clone())
            .with_type_filter(type_filters[0]);

        let computation_solutions = stream1.flat_map(move |(vr1, item1)| {
            self.get_stream_for_filter(filters[1].clone())
                .with_type_filter(type_filters[1])
                .filter_map({
                    let item1 = item1.clone();
                    let vr1 = vr1.clone();
                    move |(vr2, item2)| {
                        checker.check_streams(&item1, &item2).map(
                            |(checked_item1, checked_item2)| {
                                // If the original item was unbound, the new ValueRef should be a Literal.
                                // Otherwise, keep the original ValueRef for provenance.
                                let result_vr1 = if item1 == StreamItem::UnboundWildcard {
                                    match checked_item1 {
                                        StreamItem::Concrete(v) => ValueRef::Literal(v),
                                        _ => vr1.clone(), // Should be unreachable
                                    }
                                } else {
                                    vr1.clone()
                                };

                                let result_vr2 = if item2 == StreamItem::UnboundWildcard {
                                    match checked_item2 {
                                        StreamItem::Concrete(v) => ValueRef::Literal(v),
                                        _ => vr2, // Should be unreachable
                                    }
                                } else {
                                    vr2
                                };

                                ([result_vr1, result_vr2], JustificationKind::Computation)
                            },
                        )
                    }
                })
        });

        Ok(Box::new(unification_solutions.chain(computation_solutions)))
    }

    /// Core logic for finding ternary predicate candidates.
    pub(super) fn enumerate_ternary_candidates_core<'a, C>(
        &'a self,
        filters: [Option<ValueRef>; 3],
        checker: C,
        db_facts: &'a HashMap<[ValueRef; 3], Vec<PodId>>,
        type_filters: [TypeFilter; 3],
    ) -> Result<CandidateTupleStream<'a, 3>, SolverError>
    where
        C: TernaryPredicateHandler + 'a,
    {
        // --- Path 0: Fast path for fully-bound computation ---
        if let (Some(vr1), Some(vr2), Some(vr3)) = (&filters[0], &filters[1], &filters[2]) {
            let val1 = self.db.value_ref_to_value(vr1);
            let val2 = self.db.value_ref_to_value(vr2);
            let val3 = self.db.value_ref_to_value(vr3);

            if let (Some(v1), Some(v2), Some(v3)) = (val1, val2, val3) {
                if check_type(&v1, &type_filters[0])
                    && check_type(&v2, &type_filters[1])
                    && check_type(&v3, &type_filters[2])
                    && checker
                        .check_streams(
                            &StreamItem::Concrete(v1),
                            &StreamItem::Concrete(v2),
                            &StreamItem::Concrete(v3),
                        )
                        .is_some()
                {
                    let iter: Box<dyn Iterator<Item = _> + 'a> = Box::new(std::iter::once((
                        [vr1.clone(), vr2.clone(), vr3.clone()],
                        JustificationKind::Computation,
                    )));
                    return Ok(iter);
                }
            }
        }

        // --- Path 1: Unification against the statement index ---
        let unification_solutions = db_facts
            .keys()
            .filter({
                let filters = filters.clone();
                move |[vr1, vr2, vr3]| {
                    let p1 = filters[0].as_ref().map_or(true, |f| f == vr1);
                    let p2 = filters[1].as_ref().map_or(true, |f| f == vr2);
                    let p3 = filters[2].as_ref().map_or(true, |f| f == vr3);
                    p1 && p2 && p3
                }
            })
            .map(|fact| (fact.clone(), JustificationKind::Fact));

        // --- Path 2: Solve by computation using value streams ---
        let stream1_results: Vec<_> = self
            .get_stream_for_filter(filters[0].clone())
            .with_type_filter(type_filters[0])
            .collect();

        let computation_solutions = stream1_results.into_iter().flat_map(move |(vr1, item1)| {
            self.get_stream_for_filter(filters[1].clone())
                .with_type_filter(type_filters[1])
                .flat_map({
                    let filters = filters.clone();
                    let item1 = item1.clone();
                    let vr1 = vr1.clone();
                    move |(vr2, item2)| {
                        self.get_stream_for_filter(filters[2].clone())
                            .with_type_filter(type_filters[2])
                            .filter_map({
                                let item1 = item1.clone();
                                let vr1 = vr1.clone();
                                let item2 = item2.clone();
                                let vr2 = vr2.clone();
                                move |(vr3, item3)| {
                                    checker.check_streams(&item1, &item2, &item3).map(
                                        |(checked_item1, checked_item2, checked_item3)| {
                                            let result_vr1 = if item1 == StreamItem::UnboundWildcard
                                            {
                                                match checked_item1 {
                                                    StreamItem::Concrete(v) => ValueRef::Literal(v),
                                                    _ => vr1.clone(),
                                                }
                                            } else {
                                                vr1.clone()
                                            };
                                            let result_vr2 = if item2 == StreamItem::UnboundWildcard
                                            {
                                                match checked_item2 {
                                                    StreamItem::Concrete(v) => ValueRef::Literal(v),
                                                    _ => vr2.clone(),
                                                }
                                            } else {
                                                vr2.clone()
                                            };
                                            let result_vr3 = if item3 == StreamItem::UnboundWildcard
                                            {
                                                match checked_item3 {
                                                    StreamItem::Concrete(v) => ValueRef::Literal(v),
                                                    _ => vr3,
                                                }
                                            } else {
                                                vr3
                                            };
                                            (
                                                [result_vr1, result_vr2, result_vr3],
                                                JustificationKind::Computation,
                                            )
                                        },
                                    )
                                }
                            })
                    }
                })
        });

        Ok(Box::new(unification_solutions.chain(computation_solutions)))
    }

    /// Core logic for finding custom predicate candidates.
    pub(super) fn enumerate_custom_candidates_core<'a>(
        &'a self,
        cpr: &'a CustomPredicateRef,
        filters: &'a [Option<ValueRef>],
    ) -> impl Iterator<Item = Vec<Value>> + 'a {
        // This is a temporary implementation that bridges the ValueRef-based solver
        // with the Value-based custom fact storage.
        let resolved_filters: Vec<Option<Value>> = filters
            .iter()
            .map(|opt_vr| {
                opt_vr
                    .as_ref()
                    .and_then(|vr| self.db.value_ref_to_value(vr))
            })
            .collect();

        let facts_for_pred =
            self.db
                .statement_index
                .custom
                .get(&(cpr.batch.id(), cpr.index, vec![]));

        if let Some(facts) = facts_for_pred {
            println!("Facts for pred: {:?}", facts);
        }

        self.db
            .statement_index
            .custom
            .iter()
            .filter(move |((batch_id, pred_idx, _), _)| {
                *batch_id == cpr.batch.id() && *pred_idx == cpr.index
            })
            .map(|((_, _, values), _)| values.clone())
            .filter(move |values| {
                resolved_filters
                    .iter()
                    .zip(values.iter())
                    .all(|(filter, value)| filter.as_ref().map_or(true, |f| f == value))
            })
    }

    fn value_ref_to_value(&self, vr: &ValueRef) -> Option<Value> {
        match vr {
            ValueRef::Literal(v) => Some(v.clone()),
            ValueRef::Key(ak) => self.db.get_value_by_anchored_key(ak).cloned(),
        }
    }
}
