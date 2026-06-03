//! Per-operation resource cost analysis.
//!
//! Each operation consumes resources from several per-POD budgets. This
//! module maps an `Operation` to its [`OperationCost`] and exposes the
//! tree-specific caps as module-level constants until they land in
//! `middleware::Params`.

use std::collections::BTreeSet;

use serde::{Deserialize, Serialize};

use crate::{
    frontend::Operation,
    middleware::{
        CustomPredicateRef, Hash, NativeOperation, OperationAux, OperationType, Params, Predicate,
    },
};

/// Identifier for a custom predicate, used to count distinct predicates
/// per POD against `max_custom_predicates`.
#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Serialize, Deserialize)]
pub struct CustomPredicateId(pub Hash);

impl From<&CustomPredicateRef> for CustomPredicateId {
    fn from(predicate: &CustomPredicateRef) -> Self {
        Self(Predicate::Custom(predicate.clone()).hash())
    }
}

/// Resource cost of a single operation. Each field corresponds to a
/// per-POD limit in `Params`.
///
/// Merkle proofs and state transitions are split into `_small` and
/// `_medium` because the POD circuit exposes two slot pools per category
/// (`Params.containers.{state,transition}.{max_small,max_medium}`) with an
/// absorbable-bin rule: medium ops must use medium slots, small-eligible
/// ops can substitute up into medium when small is exhausted.
///
/// Eligibility rules (see `ParamsContainers` comments):
/// - state (proofs): small slots only support `Contains` (existence).
///   `NotContains` always counts as medium.
/// - transition: small slots only support `Update`. `Insert` / `Delete`
///   always count as medium.
/// - Additionally, any proof on a tree deeper than
///   `params.containers.max_depth_small` counts as medium regardless of
///   op kind.
#[derive(Clone, Debug, Default, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub struct OperationCost {
    /// `Contains`-family proofs on a shallow tree (depth <=
    /// `max_depth_small`). May occupy either a small or medium state slot.
    pub merkle_proofs_small: usize,
    /// `NotContains`-family proofs, or `Contains` on a deep tree. Medium
    /// state slots only.
    pub merkle_proofs_medium: usize,
    /// `Update` transitions on a shallow tree. May occupy either a small
    /// or medium transition slot.
    pub merkle_state_transitions_small: usize,
    /// `Insert` / `Delete` transitions, or `Update` on a deep tree. Medium
    /// transition slots only.
    pub merkle_state_transitions_medium: usize,
    /// Custom predicate verifications.
    pub custom_pred_verifications: usize,
    /// SignedBy operations.
    pub signed_by: usize,
    /// PublicKeyOf operations.
    pub public_key_of: usize,
    /// Custom predicates used by this operation. Drives the per-POD
    /// `max_custom_predicates` distinct-count cap.
    pub custom_predicates_ids: BTreeSet<CustomPredicateId>,
}

/// The total resources consumed over an arbitrary range of operations, as
/// specified in the input. We can use this to estimate the total number of
/// PODs needed to perform some set of operations, or to calculate whether
/// a given set of operations can be performed in a single POD.
///
/// Does not account for the cost of publishing or importing statements,
/// which is tracked separately.
#[derive(Clone, Debug, Default)]
pub struct ResourceTotals {
    pub num_operations: usize,
    pub merkle_proofs_small: usize,
    pub merkle_proofs_medium: usize,
    pub merkle_state_transitions_small: usize,
    pub merkle_state_transitions_medium: usize,
    pub custom_pred_verifications: usize,
    pub signed_by: usize,
    pub public_key_of: usize,
    pub distinct_custom_predicates: usize,
}

impl ResourceTotals {
    /// Custom predicates are deduped across the stream, so the distinct
    /// count reflects the union rather than the sum.
    pub fn accumulate<'a>(costs: impl IntoIterator<Item = &'a OperationCost>) -> Self {
        let mut t = Self::default();
        let mut distinct: BTreeSet<&CustomPredicateId> = BTreeSet::new();
        for c in costs {
            t.add(c);
            distinct.extend(&c.custom_predicates_ids);
        }
        t.distinct_custom_predicates = distinct.len();
        t
    }

    /// Minimum number of PODs required to perform the input operations, not
    /// accounting for any additional cost of publishing and importing
    /// statements across POD boundaries. This provides us with a lower bound
    /// estimate, allowing us to exit early from the solver if we find any
    /// configuration which achieves this lower bound.
    pub fn min_pods(&self, params: &Params) -> usize {
        if self.num_operations == 0 {
            return 0;
        }
        let mut bound = 1_usize;
        let bump = |bound: &mut usize, used: usize, cap: usize| {
            if used > 0 {
                *bound = (*bound).max(used.div_ceil(cap.max(1)));
            }
        };

        bump(&mut bound, self.num_operations, params.max_statements);
        bump(
            &mut bound,
            self.custom_pred_verifications,
            params.max_custom_predicate_verifications,
        );
        bump(&mut bound, self.signed_by, params.max_signed_by);
        bump(&mut bound, self.public_key_of, params.max_public_key_of);
        bump(
            &mut bound,
            self.distinct_custom_predicates,
            params.max_custom_predicates,
        );

        let state = &params.containers.state;
        bump(&mut bound, self.merkle_proofs_medium, state.max_medium);
        bump(
            &mut bound,
            self.merkle_proofs_small + self.merkle_proofs_medium,
            state.max_total(),
        );

        let transition = &params.containers.transition;
        bump(
            &mut bound,
            self.merkle_state_transitions_medium,
            transition.max_medium,
        );
        bump(
            &mut bound,
            self.merkle_state_transitions_small + self.merkle_state_transitions_medium,
            transition.max_total(),
        );

        bound
    }

    /// Updates the scalar sums for one operation. The caller is
    /// responsible for keeping `distinct_custom_predicates` correct
    /// (typically by deduping CP IDs in its own structure) before
    /// calling [`fits_in_pod`].
    pub fn add(&mut self, cost: &OperationCost) {
        self.num_operations += 1;
        self.merkle_proofs_small += cost.merkle_proofs_small;
        self.merkle_proofs_medium += cost.merkle_proofs_medium;
        self.merkle_state_transitions_small += cost.merkle_state_transitions_small;
        self.merkle_state_transitions_medium += cost.merkle_state_transitions_medium;
        self.custom_pred_verifications += cost.custom_pred_verifications;
        self.signed_by += cost.signed_by;
        self.public_key_of += cost.public_key_of;
    }

    /// True iff all sums fit in one POD under `params`.
    ///
    /// The `num_operations` vs `max_statements` term is the local-output
    /// contribution only; callers that need to account for publishing and
    /// importing statements must do that separately.
    pub fn fits_in_pod(&self, params: &Params) -> bool {
        let state = &params.containers.state;
        let transition = &params.containers.transition;
        self.num_operations <= params.max_statements
            && self.merkle_proofs_medium <= state.max_medium
            && self.merkle_proofs_small + self.merkle_proofs_medium <= state.max_total()
            && self.merkle_state_transitions_medium <= transition.max_medium
            && self.merkle_state_transitions_small + self.merkle_state_transitions_medium
                <= transition.max_total()
            && self.custom_pred_verifications <= params.max_custom_predicate_verifications
            && self.signed_by <= params.max_signed_by
            && self.public_key_of <= params.max_public_key_of
            && self.distinct_custom_predicates <= params.max_custom_predicates
    }
}

impl OperationCost {
    /// Compute the resource cost of a frontend operation.
    ///
    /// Inspects `op.2` (the [`OperationAux`]) to determine merkle-tree
    /// depth; operations on trees deeper than
    /// `params.containers.max_depth_small` are charged to the medium pool.
    pub fn from_operation(op: &Operation, params: &Params) -> Self {
        let mut cost = Self::default();
        let max_depth_small = params.containers.max_depth_small;

        match &op.0 {
            OperationType::Native(native_op) => match native_op {
                // Existence / Contains: small-eligible when the tree is
                // shallow; medium-required otherwise.
                NativeOperation::ContainsFromEntries
                | NativeOperation::DictContainsFromEntries
                | NativeOperation::SetContainsFromEntries
                | NativeOperation::ArrayContainsFromEntries => {
                    if merkle_proof_depth(&op.2) <= max_depth_small {
                        cost.merkle_proofs_small = 1;
                    } else {
                        cost.merkle_proofs_medium = 1;
                    }
                }
                // NotContains: medium-only (small slots support exists only).
                NativeOperation::NotContainsFromEntries
                | NativeOperation::DictNotContainsFromEntries
                | NativeOperation::SetNotContainsFromEntries => {
                    cost.merkle_proofs_medium = 1;
                }
                // Update: small-eligible when shallow; medium-required otherwise.
                NativeOperation::ContainerUpdateFromEntries
                | NativeOperation::DictUpdateFromEntries
                | NativeOperation::ArrayUpdateFromEntries => {
                    if transition_proof_depth(&op.2) <= max_depth_small {
                        cost.merkle_state_transitions_small = 1;
                    } else {
                        cost.merkle_state_transitions_medium = 1;
                    }
                }
                // Insert / Delete: medium-only (small slots support update only).
                NativeOperation::ContainerInsertFromEntries
                | NativeOperation::ContainerDeleteFromEntries
                | NativeOperation::DictInsertFromEntries
                | NativeOperation::DictDeleteFromEntries
                | NativeOperation::SetInsertFromEntries
                | NativeOperation::SetDeleteFromEntries => {
                    cost.merkle_state_transitions_medium = 1;
                }
                NativeOperation::SignedByFromEntries => {
                    cost.signed_by = 1;
                }
                NativeOperation::PublicKeyFromEntries => {
                    cost.public_key_of = 1;
                }
                // Zero-cost ops (no per-POD resource consumed).
                NativeOperation::None
                | NativeOperation::EqualFromEntries
                | NativeOperation::NotEqualFromEntries
                | NativeOperation::LtEqFromEntries
                | NativeOperation::LtFromEntries
                | NativeOperation::TransitiveEqualFromStatements
                | NativeOperation::LtToNotEqual
                | NativeOperation::SumFromEntries
                | NativeOperation::ProductFromEntries
                | NativeOperation::MaxFromEntries
                | NativeOperation::HashFromEntries
                // Tracked separately by the partitioner.
                | NativeOperation::OpenInputStatement
                // Syntactic sugar variants (lowered before proving).
                | NativeOperation::GtEqFromEntries
                | NativeOperation::GtFromEntries
                | NativeOperation::GtToNotEqual
                | NativeOperation::ReplaceValueWithEntry => {}
            },
            OperationType::Custom(cpr) => {
                cost.custom_pred_verifications = 1;
                cost.custom_predicates_ids
                    .insert(CustomPredicateId::from(cpr));
            }
        }

        cost
    }
}

/// Depth of the merkle proof attached to a Contains/NotContains
/// operation. Tree depth equals the sibling-path length.
fn merkle_proof_depth(aux: &OperationAux) -> usize {
    match aux {
        OperationAux::MerkleProof(proof) => proof.siblings.len(),
        _ => unreachable!(
            "Contains/NotContains operation must carry a MerkleProof aux \
             (set by MainPodBuilder::fill_in_aux)"
        ),
    }
}

/// Depth of the merkle proof attached to a state-transition operation.
fn transition_proof_depth(aux: &OperationAux) -> usize {
    match aux {
        OperationAux::MerkleTreeStateTransitionProof(proof) => proof.siblings.len(),
        _ => unreachable!(
            "Container Insert/Update/Delete must carry a \
             MerkleTreeStateTransitionProof aux (set by \
             MainPodBuilder::fill_in_aux)"
        ),
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{
        backends::plonky2::primitives::merkletree::{
            MerkleProof, MerkleTreeOp, MerkleTreeStateTransitionProof,
        },
        middleware::{RawValue, EMPTY_HASH},
    };

    fn native_op(op: NativeOperation, aux: OperationAux) -> Operation {
        Operation(OperationType::Native(op), vec![], aux)
    }

    fn merkle_proof_aux(depth: usize) -> OperationAux {
        OperationAux::MerkleProof(MerkleProof {
            existence: true,
            siblings: vec![EMPTY_HASH; depth],
            other_leaf: None,
        })
    }

    fn state_transition_aux(depth: usize, op: MerkleTreeOp) -> OperationAux {
        OperationAux::MerkleTreeStateTransitionProof(MerkleTreeStateTransitionProof {
            op,
            old_root: EMPTY_HASH,
            op_proof: MerkleProof {
                existence: true,
                siblings: vec![],
                other_leaf: None,
            },
            new_root: EMPTY_HASH,
            op_key: RawValue::from(0),
            op_value: RawValue::from(0),
            value: None,
            siblings: vec![EMPTY_HASH; depth],
        })
    }

    /// Scalar-cost ops (SignedBy / PublicKeyOf) don't inspect the aux and
    /// land in their own cost dimension.
    #[test]
    fn scalar_native_ops_map_to_their_cost_dimension() {
        let params = Params::default();
        let sb = OperationCost::from_operation(
            &native_op(NativeOperation::SignedByFromEntries, OperationAux::None),
            &params,
        );
        assert_eq!(sb.signed_by, 1);
        assert_eq!(sb.public_key_of, 0);

        let pk = OperationCost::from_operation(
            &native_op(NativeOperation::PublicKeyFromEntries, OperationAux::None),
            &params,
        );
        assert_eq!(pk.public_key_of, 1);
        assert_eq!(pk.signed_by, 0);
    }

    /// Contains on a tree at depth `<= max_depth_small` is small-eligible;
    /// at depth `> max_depth_small` it must use a medium slot.
    #[test]
    fn contains_routes_by_tree_depth() {
        let params = Params::default();
        let max_depth_small = params.containers.max_depth_small;

        let shallow = OperationCost::from_operation(
            &native_op(
                NativeOperation::ContainsFromEntries,
                merkle_proof_aux(max_depth_small),
            ),
            &params,
        );
        assert_eq!(shallow.merkle_proofs_small, 1);
        assert_eq!(shallow.merkle_proofs_medium, 0);

        let deep = OperationCost::from_operation(
            &native_op(
                NativeOperation::ContainsFromEntries,
                merkle_proof_aux(max_depth_small + 1),
            ),
            &params,
        );
        assert_eq!(deep.merkle_proofs_small, 0);
        assert_eq!(deep.merkle_proofs_medium, 1);
    }

    /// NotContains has no small-slot path; even shallow proofs land in
    /// medium because the small state pool supports existence only.
    #[test]
    fn not_contains_always_uses_medium_slot() {
        let params = Params::default();
        let max_depth_small = params.containers.max_depth_small;
        let cost = OperationCost::from_operation(
            &native_op(
                NativeOperation::NotContainsFromEntries,
                merkle_proof_aux(max_depth_small),
            ),
            &params,
        );
        assert_eq!(cost.merkle_proofs_small, 0);
        assert_eq!(cost.merkle_proofs_medium, 1);
    }

    /// Update on a shallow tree is small-eligible; Insert / Delete /
    /// deep-Update all route to medium transition slots.
    #[test]
    fn state_transitions_route_by_op_and_depth() {
        let params = Params::default();
        let max_depth_small = params.containers.max_depth_small;

        let update_shallow = OperationCost::from_operation(
            &native_op(
                NativeOperation::ContainerUpdateFromEntries,
                state_transition_aux(max_depth_small, MerkleTreeOp::Update),
            ),
            &params,
        );
        assert_eq!(update_shallow.merkle_state_transitions_small, 1);
        assert_eq!(update_shallow.merkle_state_transitions_medium, 0);

        let update_deep = OperationCost::from_operation(
            &native_op(
                NativeOperation::ContainerUpdateFromEntries,
                state_transition_aux(max_depth_small + 1, MerkleTreeOp::Update),
            ),
            &params,
        );
        assert_eq!(update_deep.merkle_state_transitions_small, 0);
        assert_eq!(update_deep.merkle_state_transitions_medium, 1);

        let insert = OperationCost::from_operation(
            &native_op(
                NativeOperation::ContainerInsertFromEntries,
                state_transition_aux(max_depth_small, MerkleTreeOp::Insert),
            ),
            &params,
        );
        assert_eq!(insert.merkle_state_transitions_small, 0);
        assert_eq!(insert.merkle_state_transitions_medium, 1);
    }
}
