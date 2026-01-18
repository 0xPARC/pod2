//! Resource cost analysis for statements and operations.
//!
//! This module provides cost analysis for multi-POD packing. Each operation
//! consumes various resources that have per-POD limits.

use std::collections::BTreeSet;

use crate::{
    frontend::{Operation, OperationArg},
    middleware::{
        CustomPredicateBatch, Hash, NativeOperation, OperationType, Params, RawValue, Statement,
        ValueRef,
    },
};

/// Unique identifier for a custom predicate batch.
///
/// Uses the batch's cryptographic hash as identifier. Two batches with the same
/// hash are considered identical for resource counting purposes.
#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct CustomBatchId(pub Hash);

impl From<&CustomPredicateBatch> for CustomBatchId {
    fn from(batch: &CustomPredicateBatch) -> Self {
        Self(batch.id())
    }
}

/// Unique identifier for an anchored key (dict, key) pair.
///
/// When a Contains statement is used as an argument to operations like gt(), eq(), etc.,
/// the value is accessed via an "anchored key" - a reference to a specific key in a
/// specific dictionary. Each unique anchored key used in a POD requires a Contains
/// statement to be present in that POD (auto-inserted by MainPodBuilder if needed).
///
/// We use the raw values of the dict and key for comparison, as they uniquely identify
/// the anchored key regardless of the specific Value types involved.
#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct AnchoredKeyId {
    /// The dictionary root value (raw representation for Ord).
    pub dict: RawValue,
    /// The key within the dictionary (raw representation for Ord).
    pub key: RawValue,
}

impl AnchoredKeyId {
    /// Create a new anchored key ID from raw values.
    pub fn new(dict: RawValue, key: RawValue) -> Self {
        Self { dict, key }
    }

    /// Try to extract an anchored key ID from a Contains statement with all literal values.
    pub fn from_contains_statement(stmt: &Statement) -> Option<Self> {
        if let Statement::Contains(
            ValueRef::Literal(dict),
            ValueRef::Literal(key),
            ValueRef::Literal(_value),
        ) = stmt
        {
            Some(Self::new(dict.raw(), key.raw()))
        } else {
            None
        }
    }
}

/// Resource costs for a single statement/operation.
///
/// Each field corresponds to a resource with a per-POD limit in `Params`.
#[derive(Clone, Debug, Default)]
pub struct StatementCost {
    /// Number of merkle proofs used (for Contains/NotContains).
    /// Limit: `params.max_merkle_proofs_containers`
    pub merkle_proofs: usize,

    /// Number of merkle tree state transition proofs (for Insert/Update/Delete).
    /// Limit: `params.max_merkle_tree_state_transition_proofs_containers`
    pub merkle_state_transitions: usize,

    /// Number of custom predicate verifications.
    /// Limit: `params.max_custom_predicate_verifications`
    pub custom_pred_verifications: usize,

    /// Number of SignedBy operations.
    /// Limit: `params.max_signed_by`
    pub signed_by: usize,

    /// Number of PublicKeyOf operations.
    /// Limit: `params.max_public_key_of`
    pub public_key_of: usize,

    /// Custom predicate batches used (for batch cardinality constraint).
    /// Limit: `params.max_custom_predicate_batches` distinct batches per POD.
    pub custom_batch_ids: BTreeSet<CustomBatchId>,

    /// Anchored keys referenced by this operation.
    ///
    /// When a Contains statement with all literal values is used as an argument,
    /// the operation references an "anchored key" (dict, key pair). Each unique
    /// anchored key used in a POD incurs an additional Contains statement cost,
    /// as MainPodBuilder::add_entries_contains will auto-insert it if not already present.
    pub anchored_keys: BTreeSet<AnchoredKeyId>,
}

impl StatementCost {
    /// Compute the resource cost of an operation.
    pub fn from_operation(op: &Operation) -> Self {
        let mut cost = Self::default();

        match &op.0 {
            OperationType::Native(native_op) => {
                match native_op {
                    // Operations that use merkle proofs
                    NativeOperation::ContainsFromEntries
                    | NativeOperation::NotContainsFromEntries
                    | NativeOperation::DictContainsFromEntries
                    | NativeOperation::DictNotContainsFromEntries
                    | NativeOperation::SetContainsFromEntries
                    | NativeOperation::SetNotContainsFromEntries
                    | NativeOperation::ArrayContainsFromEntries => {
                        cost.merkle_proofs = 1;
                    }

                    // Operations that use merkle state transitions
                    NativeOperation::ContainerInsertFromEntries
                    | NativeOperation::ContainerUpdateFromEntries
                    | NativeOperation::ContainerDeleteFromEntries
                    | NativeOperation::DictInsertFromEntries
                    | NativeOperation::DictUpdateFromEntries
                    | NativeOperation::DictDeleteFromEntries
                    | NativeOperation::SetInsertFromEntries
                    | NativeOperation::SetDeleteFromEntries
                    | NativeOperation::ArrayUpdateFromEntries => {
                        cost.merkle_state_transitions = 1;
                    }

                    // SignedBy operation
                    NativeOperation::SignedBy => {
                        cost.signed_by = 1;
                    }

                    // PublicKeyOf operation
                    NativeOperation::PublicKeyOf => {
                        cost.public_key_of = 1;
                    }

                    // Operations with no special resource costs
                    NativeOperation::None
                    | NativeOperation::CopyStatement
                    | NativeOperation::EqualFromEntries
                    | NativeOperation::NotEqualFromEntries
                    | NativeOperation::LtEqFromEntries
                    | NativeOperation::LtFromEntries
                    | NativeOperation::TransitiveEqualFromStatements
                    | NativeOperation::LtToNotEqual
                    | NativeOperation::SumOf
                    | NativeOperation::ProductOf
                    | NativeOperation::MaxOf
                    | NativeOperation::HashOf
                    // Syntactic sugar variants (lowered before proving)
                    | NativeOperation::GtEqFromEntries
                    | NativeOperation::GtFromEntries
                    | NativeOperation::GtToNotEqual => {}
                }
            }
            OperationType::Custom(cpr) => {
                cost.custom_pred_verifications = 1;
                cost.custom_batch_ids
                    .insert(CustomBatchId::from(&*cpr.batch));
            }
        }

        // Extract anchored keys from operation arguments.
        // Any argument that is a Contains statement with all literal values
        // represents an anchored key reference that will require a Contains
        // statement in the POD (auto-inserted by MainPodBuilder if needed).
        for arg in &op.1 {
            if let OperationArg::Statement(stmt) = arg {
                if let Some(anchored_key) = AnchoredKeyId::from_contains_statement(stmt) {
                    cost.anchored_keys.insert(anchored_key);
                }
            }
        }

        cost
    }
}

/// Aggregate costs for multiple statements.
#[derive(Clone, Debug, Default)]
pub struct AggregateCost {
    pub statements: usize,
    pub merkle_proofs: usize,
    pub merkle_state_transitions: usize,
    pub custom_pred_verifications: usize,
    pub signed_by: usize,
    pub public_key_of: usize,
    pub custom_batch_ids: BTreeSet<CustomBatchId>,
}

impl AggregateCost {
    pub fn new() -> Self {
        Self::default()
    }

    /// Add a statement's cost to the aggregate.
    pub fn add(&mut self, cost: &StatementCost) {
        self.statements += 1;
        self.merkle_proofs += cost.merkle_proofs;
        self.merkle_state_transitions += cost.merkle_state_transitions;
        self.custom_pred_verifications += cost.custom_pred_verifications;
        self.signed_by += cost.signed_by;
        self.public_key_of += cost.public_key_of;
        self.custom_batch_ids
            .extend(cost.custom_batch_ids.iter().cloned());
    }

    /// Compute a lower bound on the number of PODs needed.
    ///
    /// This is a quick heuristic that can be used for branch pruning
    /// in a logic solver without running the full MILP.
    pub fn lower_bound_pods(&self, params: &Params) -> usize {
        let by_statements = self.statements.div_ceil(params.max_statements);
        let by_merkle_proofs = self
            .merkle_proofs
            .div_ceil(params.max_merkle_proofs_containers);
        let by_merkle_transitions = self
            .merkle_state_transitions
            .div_ceil(params.max_merkle_tree_state_transition_proofs_containers);
        let by_custom_verifications = self
            .custom_pred_verifications
            .div_ceil(params.max_custom_predicate_verifications);
        let by_signed_by = self.signed_by.div_ceil(params.max_signed_by);
        let by_public_key_of = self.public_key_of.div_ceil(params.max_public_key_of);
        let by_batches = self
            .custom_batch_ids
            .len()
            .div_ceil(params.max_custom_predicate_batches);

        [
            by_statements,
            by_merkle_proofs,
            by_merkle_transitions,
            by_custom_verifications,
            by_signed_by,
            by_public_key_of,
            by_batches,
        ]
        .into_iter()
        .max()
        .unwrap() // Array is non-empty
        .max(1) // At least 1 POD
    }
}

/// Quick estimate of POD count for a set of operations.
///
/// This is useful for the logic solver to estimate costs without
/// running the full MILP solver.
pub fn estimate_pod_count(operations: &[Operation], params: &Params) -> usize {
    let mut aggregate = AggregateCost::new();
    for op in operations {
        aggregate.add(&StatementCost::from_operation(op));
    }
    // Add a fudge factor for dependency overhead and public statement constraints
    let lower_bound = aggregate.lower_bound_pods(params);
    // Heuristic: add ~20% overhead for dependencies
    lower_bound + lower_bound / 5
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{
        frontend::Operation as FrontendOp,
        middleware::{NativeOperation, OperationAux, OperationType},
    };

    fn make_native_op(native_op: NativeOperation) -> FrontendOp {
        FrontendOp(OperationType::Native(native_op), vec![], OperationAux::None)
    }

    #[test]
    fn test_cost_from_native_ops() {
        // Test merkle proof ops
        let contains_op = make_native_op(NativeOperation::ContainsFromEntries);
        let cost = StatementCost::from_operation(&contains_op);
        assert_eq!(cost.merkle_proofs, 1);
        assert_eq!(cost.merkle_state_transitions, 0);

        // Test merkle state transition ops
        let insert_op = make_native_op(NativeOperation::ContainerInsertFromEntries);
        let cost = StatementCost::from_operation(&insert_op);
        assert_eq!(cost.merkle_proofs, 0);
        assert_eq!(cost.merkle_state_transitions, 1);

        // Test signed_by
        let signed_op = make_native_op(NativeOperation::SignedBy);
        let cost = StatementCost::from_operation(&signed_op);
        assert_eq!(cost.signed_by, 1);

        // Test public_key_of
        let pk_op = make_native_op(NativeOperation::PublicKeyOf);
        let cost = StatementCost::from_operation(&pk_op);
        assert_eq!(cost.public_key_of, 1);
    }

    #[test]
    fn test_aggregate_cost() {
        let params = Params::default();

        let mut aggregate = AggregateCost::new();

        // Add some operations
        for _ in 0..10 {
            aggregate.add(&StatementCost::from_operation(&make_native_op(
                NativeOperation::ContainsFromEntries,
            )));
        }

        assert_eq!(aggregate.statements, 10);
        assert_eq!(aggregate.merkle_proofs, 10);

        // 10 statements / 48 max = 1 POD, 10 merkle proofs / 20 max = 1 POD
        let lower_bound = aggregate.lower_bound_pods(&params);
        assert_eq!(lower_bound, 1);
    }

    #[test]
    fn test_lower_bound_by_statements() {
        let params = Params {
            max_statements: 10,
            ..Params::default()
        };

        let mut aggregate = AggregateCost::new();
        aggregate.statements = 25;

        // 25 statements / 10 per pod = 3 pods
        assert_eq!(aggregate.lower_bound_pods(&params), 3);
    }
}
