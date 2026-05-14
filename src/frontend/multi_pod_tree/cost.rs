//! Per-statement resource cost analysis.
//!
//! Each operation consumes resources from several per-POD budgets. This
//! module maps an `Operation` to a [`StatementCost`] vector and exposes the
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

/// Maximum number of statements a POD may import from its input trees
/// (chain predecessor in slot 0 and external PODs in slots 1+ combined).
///
/// Stubbed here until the field lands in `middleware::Params`.
pub const MAX_TREE_IMPORTS: usize = 20;

/// Depth of each POD's Merkle statement tree. Capacity is `2^TREE_DEPTH`.
pub const TREE_DEPTH: usize = 10;

/// Total chain-tree capacity. The chain tree is shared across all PODs in
/// a single chain, so this caps the total number of statements that can
/// flow forward through chained PODs.
pub const CHAIN_TREE_CAPACITY: usize = 1 << TREE_DEPTH;

/// Identifier for a custom predicate, used to count distinct predicates
/// per POD against `max_custom_predicates`.
#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Serialize, Deserialize)]
pub struct CustomPredicateId(pub Hash);

impl From<&CustomPredicateRef> for CustomPredicateId {
    fn from(predicate: &CustomPredicateRef) -> Self {
        Self(Predicate::Custom(predicate.clone()).hash())
    }
}

/// Resource cost of a single statement/operation. Each field corresponds
/// to a per-POD limit in `Params`.
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
pub struct StatementCost {
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
    /// Custom predicates used by this statement. Drives the per-POD
    /// `max_custom_predicates` distinct-count cap.
    pub custom_predicates_ids: BTreeSet<CustomPredicateId>,
}

/// Aggregate of [`StatementCost`]s over an arbitrary subset of
/// statements: per-resource sums plus the count of distinct custom
/// predicates. Replaces per-call hand-rolled sums in the partitioner,
/// MILP oracle, and diagnostics.
#[derive(Clone, Debug, Default)]
pub struct ResourceTotals {
    pub num_statements: usize,
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
    /// Sum a stream of [`StatementCost`]s into a single [`ResourceTotals`].
    /// Distinct custom predicates are deduped across the stream.
    pub fn accumulate<'a>(costs: impl IntoIterator<Item = &'a StatementCost>) -> Self {
        let mut t = Self::default();
        let mut distinct: BTreeSet<&CustomPredicateId> = BTreeSet::new();
        for c in costs {
            t.add(c);
            distinct.extend(&c.custom_predicates_ids);
        }
        t.distinct_custom_predicates = distinct.len();
        t
    }

    /// Minimum PODs needed to hold these totals under `params`' per-POD
    /// caps. Returns `max_r ceil(used_r / cap_r)` across every dimension;
    /// 0 if empty, 1 if non-empty with all zero sums (a single POD still
    /// holds the statements).
    ///
    /// For the absorbable-bin merkle dimensions (state, transition), the
    /// per-dimension bound is `max(ceil(m / cap_m), ceil((s + m) / (cap_s +
    /// cap_m)))`: medium ops must fit in medium slots, and the combined
    /// load must fit across both pools.
    pub fn min_pods(&self, params: &Params) -> usize {
        if self.num_statements == 0 {
            return 0;
        }
        let mut bound = 1_usize;
        let bump = |bound: &mut usize, used: usize, cap: usize| {
            if used > 0 {
                *bound = (*bound).max(used.div_ceil(cap.max(1)));
            }
        };

        bump(
            &mut bound,
            self.num_statements,
            params.max_priv_statements(),
        );
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

    /// Incrementally add a single statement's resource cost to these
    /// totals. Updates the scalar sums only; callers that track distinct
    /// custom predicates must set `distinct_custom_predicates` themselves
    /// (typically from the size of their own dedup structure) before
    /// calling [`fits_in_pod`].
    pub fn add(&mut self, cost: &StatementCost) {
        self.num_statements += 1;
        self.merkle_proofs_small += cost.merkle_proofs_small;
        self.merkle_proofs_medium += cost.merkle_proofs_medium;
        self.merkle_state_transitions_small += cost.merkle_state_transitions_small;
        self.merkle_state_transitions_medium += cost.merkle_state_transitions_medium;
        self.custom_pred_verifications += cost.custom_pred_verifications;
        self.signed_by += cost.signed_by;
        self.public_key_of += cost.public_key_of;
    }

    /// True iff all sums fit in one POD under `params`. Used by the DP's
    /// segment-feasibility check to replace a multi-condition cap check.
    /// Applies the absorbable-bin rule for merkle dimensions.
    pub fn fits_in_pod(&self, params: &Params) -> bool {
        let state = &params.containers.state;
        let transition = &params.containers.transition;
        self.num_statements <= params.max_priv_statements()
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

impl StatementCost {
    /// Compute the resource cost of a frontend operation.
    ///
    /// Inspects `op.2` (the [`OperationAux`]) to determine merkle-tree
    /// depth; operations on trees deeper than
    /// `params.containers.max_depth_small` are charged to the medium pool
    /// regardless of op kind. The caller is expected to have run
    /// `MainPodBuilder::fill_in_aux` on `op` (which `MainPodBuilder::op`
    /// does automatically); merkle operations without a populated aux
    /// trip an `unreachable!`.
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
                NativeOperation::SignedBy => {
                    cost.signed_by = 1;
                }
                NativeOperation::PublicKeyOf => {
                    cost.public_key_of = 1;
                }
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
