//! Resource cost analysis for statements and operations.
//!
//! This module provides cost analysis for multi-POD packing. Each operation
//! consumes various resources that have per-POD limits.

use std::collections::BTreeSet;

use crate::{
    frontend::Operation,
    middleware::{CustomPredicateRef, Hash, NativeOperation, OperationType, Predicate},
};

/// Unique identifier for a custom predicate in a module.
///
/// Uses the predicate's cryptographic hash as identifier. Two predicates with the same
/// hash are considered identical for resource counting purposes.
#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct CustomPredicateId(pub Hash);

impl From<&CustomPredicateRef> for CustomPredicateId {
    fn from(predicate: &CustomPredicateRef) -> Self {
        Self(Predicate::Custom(predicate.clone()).hash())
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

    /// Custom predicates used (for custom predicate cardinality constraint).
    /// Limit: `params.max_custom_predicates` distinct custom predicates per POD.
    pub custom_predicates_ids: BTreeSet<CustomPredicateId>,
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
                cost.custom_predicates_ids
                    .insert(CustomPredicateId::from(cpr));
            }
        }

        cost
    }
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
}
