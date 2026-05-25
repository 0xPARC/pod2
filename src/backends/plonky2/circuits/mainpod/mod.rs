use std::{array, iter};

use itertools::{izip, zip_eq, Itertools};
use num::{BigUint, One};
use plonky2::{
    field::types::Field,
    hash::{hash_types::HashOutTarget, poseidon::PoseidonHash},
    iop::{
        target::{BoolTarget, Target},
        witness::{PartialWitness, WitnessWrite},
    },
};
use plonky2_u32::gadgets::multiple_comparison::list_le_circuit;
use serde::{Deserialize, Serialize};

#[cfg(test)]
mod tests;

use crate::{
    backends::plonky2::{
        basetypes::{CircuitBuilder, VDSet},
        circuits::{
            common::{
                CircuitBuilderPod, CustomPredicateEntryTarget, CustomPredicateInBatchTarget,
                CustomPredicateTarget, CustomPredicateVerifyEntryTarget,
                CustomPredicateVerifyQueryTarget, Flattenable, InputPodEntryTarget,
                MerkleClaimTarget, MerkleTreeStateTransitionClaimTarget, OperationTarget,
                OperationTypeTarget, PredicateHashOrWildcardTarget, PredicateTarget,
                StatementArgTarget, StatementTarget, StatementTmplArgTarget, StatementTmplTarget,
                ValueTarget,
            },
            mux_table::{MuxTableTarget, TableEntryTarget},
        },
        error::Result,
        mainpod::{self, MerkleProofs, MerkleTransitionProofs, SignedBy},
        primitives::{
            ec::{
                bits::{BigUInt320Target, CircuitBuilderBits},
                curve::{
                    CircuitBuilderElliptic, CircuitBuilderSignature, Point, PointTarget,
                    WitnessWriteCurve, GROUP_ORDER,
                },
                schnorr::{CircuitBuilderSchnorr, SecretKey, SignatureTarget, WitnessWriteSchnorr},
            },
            merkletree::{
                verify_merkle_proof_circuit, verify_merkle_proof_existence_circuit,
                verify_merkle_state_transition_circuit, MerkleClaimAndProof,
                MerkleClaimAndProofTarget, MerkleProof, MerkleProofExistenceTarget, MerkleTree,
                MerkleTreeOp, MerkleTreeStateTransitionProof, MerkleTreeStateTransitionProofTarget,
            },
            signature::{verify_signature_circuit, SignatureVerifyTarget},
        },
        recursion::{InnerCircuit, VerifiedProofTarget},
    },
    measure_gates_begin, measure_gates_end,
    middleware::{
        CustomPredicate, CustomPredicateBatch, CustomPredicateRef, HashOut, InputPodOpenStatement,
        NativeOperation, NativePredicate, Params, PredicatePrefix, StatementTmplArgPrefix, Value,
        BASE_PARAMS, EMPTY_HASH, EMPTY_VALUE, F, HASH_SIZE, VALUE_SIZE,
    },
};
//
// MainPod verification
//

/// Offset in public inputs where we store the statements root
pub const PI_OFFSET_STATEMENTS_ROOT: usize = 0;
/// Offset in public inputs where we store the verified data array root
pub const PI_OFFSET_VDSROOT: usize = 4;
/// Offset in public inputs where we store the is_main flag
pub const PI_OFFSET_IS_MAIN: usize = 8;

pub const NUM_PUBLIC_INPUTS: usize = 9;

const MAX_VALUE_ARGS: usize = 5;

struct StatementArgCache {
    rhs: ValueTarget,
    lhs: StatementArgTarget,
    valid: BoolTarget,
    pred_is_none: BoolTarget,
    is_reference: BoolTarget,
    // if `is_reference` then this is the AnchoredKey found in the Contains statement
    reference: StatementArgTarget,
    // if `is_reference` then this is the value found in the Contains statement
    value: ValueTarget,
}

struct StatementCache<const MAX_EQS: usize> {
    equations: [StatementArgCache; MAX_EQS],
    first_n_equations_valid: [BoolTarget; MAX_EQS],
    op_args: Vec<StatementTarget>,
}

impl<const MAX_EQS: usize> StatementCache<MAX_EQS> {
    fn new(
        params: &Params,
        max_operation_args: usize,
        builder: &mut CircuitBuilder,
        op: &OperationTarget,
        st: &StatementTarget,
        prev_statement_flatteneds: &[Vec<Target>],
        prev_statement_hashes: &[HashOutTarget],
    ) -> Self {
        let op_args = if prev_statement_flatteneds.is_empty() {
            (0..max_operation_args)
                .map(|_| StatementTarget::new_native(builder, params, NativePredicate::None, &[]))
                .collect_vec()
        } else {
            // `op.args` is a vector of arrays of length 1, so `.flatten()` is just
            // converting a length 1 array into a scalar.
            op.args
                .iter()
                .take(max_operation_args)
                .map(|i| {
                    builder.vec_ref_projected(
                        params,
                        prev_statement_flatteneds,
                        prev_statement_hashes,
                        i,
                    )
                })
                .collect::<Vec<_>>()
        };
        assert!(Params::max_statement_args() >= MAX_VALUE_ARGS);
        let equations = array::from_fn(|i| {
            let pred_is_none = op_args[i].has_native_type(builder, NativePredicate::None);
            let arg_is_value = builder.statement_arg_is_value(&st.args[i]);
            let is_literal = builder.and(pred_is_none, arg_is_value);
            let pred_is_contains = op_args[i].has_native_type(builder, NativePredicate::Contains);
            let ref_is_value_arg: [_; 3] =
                array::from_fn(|j| builder.statement_arg_is_value(&op_args[i].args[j]));
            let ref_is_value = builder.and(ref_is_value_arg[0], ref_is_value_arg[1]);
            let ref_is_value = builder.and(ref_is_value, ref_is_value_arg[2]);

            let is_reference = builder.and(pred_is_contains, ref_is_value);
            let valid = builder.or(is_literal, is_reference);
            let rhs_from_literal = st.args[i].as_value();
            let rhs_from_reference = op_args[i].args[2].as_value();
            let rhs = builder.select_value(pred_is_none, rhs_from_literal, rhs_from_reference);
            let lhs_literal = &st.args[i];
            let lhs_reference = StatementArgTarget::anchored_key(
                builder,
                &op_args[i].args[0].as_value(),
                &op_args[i].args[1].as_value(),
            );
            let lhs = builder.select_statement_arg(pred_is_none, lhs_literal, &lhs_reference);
            StatementArgCache {
                rhs,
                lhs,
                valid,
                pred_is_none,
                is_reference,
                reference: lhs_reference,
                value: rhs_from_reference,
            }
        });
        let mut first_n_equations_valid = if MAX_EQS != 0 {
            [equations[0].valid; MAX_EQS]
        } else {
            [builder._false(); MAX_EQS]
        };
        for i in 1..MAX_EQS {
            first_n_equations_valid[i] =
                builder.and(equations[i].valid, first_n_equations_valid[i - 1]);
        }
        StatementCache {
            equations,
            first_n_equations_valid,
            op_args,
        }
    }

    /// Attempts to interpret the first `N` arguments as values.
    ///
    /// If the operation argument is a statement of type  `None`, then the value
    /// should be the corresponding argument of the current statement.
    /// If the operation argument is a statement of type `Contains`, then the value
    /// should be the argument at index 1 of that statement.
    /// If the function successfully interprets the arguments as values,
    /// returns `True` along with those values.  Otherwise, returns `False`
    /// along with some arbitrary values.
    fn first_n_args_as_values<const N: usize>(&self) -> (BoolTarget, [ValueTarget; N]) {
        (
            self.first_n_equations_valid[N - 1],
            array::from_fn(|i| self.equations[i].rhs),
        )
    }
}

/// Statement cache for private statements
type StatementCachePriv = StatementCache<MAX_VALUE_ARGS>;

enum OperationAuxTableTag {
    None = 0,
    MerkleProof = 1,
    MerkleTransitionProof = 2,
    OpenInputStatement = 3,
    CustomPredVerify = 4,
    PublicKeyOf = 5,
    SignedBy = 6,
}

fn max_operation_aux_entry_len(params: &Params) -> usize {
    [
        (params.containers.state.max_total() > 0).then(|| MerkleClaimTarget::size(params)),
        (params.containers.transition.max_total() > 0)
            .then(|| MerkleTreeStateTransitionClaimTarget::size(params)),
        (params.max_custom_predicate_verifications > 0)
            .then(|| CustomPredicateVerifyQueryTarget::size(params)),
        (params.max_open_input_statements > 0).then(|| StatementTarget::size(params)),
        (params.max_public_key_of > 0).then(|| PubKeySecKeyTarget::size(params)),
        (params.max_signed_by > 0).then(|| MsgPubKeyTarget::size(params)),
    ]
    .into_iter()
    .flatten()
    .max()
    .unwrap_or(0)
}

#[derive(Copy, Clone)]
struct HashPairTarget(HashOutTarget, HashOutTarget);

impl Flattenable for HashPairTarget {
    fn flatten(&self) -> Vec<Target> {
        self.0.elements.into_iter().chain(self.1.elements).collect()
    }
    fn from_flattened(params: &Params, vs: &[Target]) -> Self {
        assert_eq!(vs.len(), Self::size(params));
        Self(
            HashOutTarget::try_from(&vs[..4]).expect("len = 4"),
            HashOutTarget::try_from(&vs[4..]).expect("len = 4"),
        )
    }
    fn size(_params: &Params) -> usize {
        8
    }
}

type PubKeySecKeyTarget = HashPairTarget; // (public_key, secret_key)
type MsgPubKeyTarget = HashPairTarget; // (message, public_key)

#[derive(Clone, Serialize, Deserialize)]
struct SignedByTarget {
    msg: ValueTarget,
    pk: PointTarget,
    sig: SignatureTarget,
}

impl SignedByTarget {
    pub fn set_targets(&self, pw: &mut PartialWitness<F>, signed_by: &SignedBy) -> Result<()> {
        self.msg.set_targets(pw, &Value::from(signed_by.msg))?;
        pw.set_point_target(&self.pk, &signed_by.pk)?;
        pw.set_signature_target(&self.sig, &signed_by.sig)?;
        Ok(())
    }

    pub fn new_virtual(builder: &mut CircuitBuilder) -> Self {
        Self {
            msg: builder.add_virtual_value(),
            pk: builder.add_virtual_point_target(),
            sig: builder.add_virtual_schnorr_signature_target(),
        }
    }
}

#[derive(Clone, Serialize, Deserialize)]
struct OpenInputStatementTarget {
    input_pod_table_index: Target,
    proof_siblings: Vec<HashOutTarget>,
    st_index: Target,
    raw_statement: StatementTarget,
}

impl OpenInputStatementTarget {
    pub fn set_targets(
        &self,
        pw: &mut PartialWitness<F>,
        data: &InputPodOpenStatement,
    ) -> Result<()> {
        pw.set_target(
            self.input_pod_table_index,
            F::from_canonical_usize(data.pod_index),
        )?;
        for (i, sibling_target) in self.proof_siblings.iter().enumerate() {
            let sibling = data.proof.siblings.get(i).unwrap_or(&EMPTY_HASH);
            pw.set_hash_target(*sibling_target, HashOut::from(*sibling))?;
        }
        pw.set_target(self.st_index, F::from_canonical_usize(data.st_index))?;
        self.raw_statement
            .set_targets(pw, &mainpod::Statement::from(data.raw_statement.clone()))?;
        Ok(())
    }

    pub fn new_virtual(builder: &mut CircuitBuilder) -> Self {
        Self {
            input_pod_table_index: builder.add_virtual_target(),
            proof_siblings: (0..BASE_PARAMS.max_depth_public_statements_mt)
                .map(|_| builder.add_virtual_hash())
                .collect(),
            st_index: builder.add_virtual_target(),
            raw_statement: builder.add_virtual_statement(true),
        }
    }
}

fn append_container_proofs_operation_aux_table_circuit(
    builder: &mut CircuitBuilder,
    table: &mut MuxTableTarget,
    merkle_proofs: &MerkleProofsTarget,
    merkle_transition_proofs: &MerkleTransitionProofsTarget,
) {
    // Small MerkleProofs: verify container merkle proofs (only inclusion)
    for merkle_proof in &merkle_proofs.small {
        verify_merkle_proof_existence_circuit(builder, merkle_proof);
        let entry = MerkleClaimTarget::from_proof_existence(builder, merkle_proof.clone());

        table.push(builder, OperationAuxTableTag::MerkleProof as u32, &entry);
    }
    // Medium MerkleProofs: verify container merkle proofs (inclusion/non-inclusion)
    for merkle_proof in &merkle_proofs.medium {
        verify_merkle_proof_circuit(builder, merkle_proof);
        let entry = MerkleClaimTarget::from(merkle_proof.clone());

        table.push(builder, OperationAuxTableTag::MerkleProof as u32, &entry);
    }

    // Small Merkle state transition proofs: verify op proof (only update)
    for merkle_transition_proof in &merkle_transition_proofs.small {
        verify_merkle_state_transition_circuit(builder, merkle_transition_proof);
        let entry = MerkleTreeStateTransitionClaimTarget::from(merkle_transition_proof.clone());

        table.push(
            builder,
            OperationAuxTableTag::MerkleTransitionProof as u32,
            &entry,
        );
    }
    // Medium Merkle state transition proofs: verify op proof (insert/update/delete)
    for merkle_transition_proof in &merkle_transition_proofs.medium {
        verify_merkle_state_transition_circuit(builder, merkle_transition_proof);
        let entry = MerkleTreeStateTransitionClaimTarget::from(merkle_transition_proof.clone());

        table.push(
            builder,
            OperationAuxTableTag::MerkleTransitionProof as u32,
            &entry,
        );
    }
}

fn append_open_input_statements_aux_table_circuit(
    params: &Params,
    builder: &mut CircuitBuilder,
    table: &mut MuxTableTarget,
    input_pod_table: &[InputPodEntryTarget],
    open_input_statements: &[OpenInputStatementTarget],
) {
    if !open_input_statements.is_empty() {
        assert!(!input_pod_table.is_empty());
    }
    assert_eq!(params.max_input_pods, input_pod_table.len());
    assert_eq!(
        params.max_open_input_statements,
        open_input_statements.len()
    );
    for data in open_input_statements {
        let measure = measure_gates_begin!(builder, "OpenInputSt");
        let pod = builder.vec_ref_small(params, input_pod_table, data.input_pod_table_index);
        let key = ValueTarget::from_int_lo(builder, data.st_index);
        let raw_st_hash =
            builder.hash_n_to_hash_no_pad::<PoseidonHash>(data.raw_statement.flatten());
        let value = ValueTarget {
            elements: raw_st_hash.elements,
        };
        let proof = MerkleProofExistenceTarget {
            max_depth: BASE_PARAMS.max_depth_public_statements_mt,
            root: pod.sts_root,
            key,
            value,
            siblings: data.proof_siblings.clone(),
        };
        verify_merkle_proof_existence_circuit(builder, &proof);
        let is_intro = builder.not(pod.is_main);
        let st = normalize_statement_circuit(
            params,
            builder,
            &data.raw_statement,
            is_intro,
            &pod.vd_hash,
        );
        table.push(
            builder,
            OperationAuxTableTag::OpenInputStatement as u32,
            &st,
        );
        measure_gates_end!(builder, measure);
    }
}

#[allow(clippy::too_many_arguments)]
fn build_operation_aux_table_circuit(
    params: &Params,
    builder: &mut CircuitBuilder,
    custom_predicate_table: &[HashOutTarget],
    input_pod_table: &[InputPodEntryTarget],
    input: &AuxTableInputTargets,
) -> Result<MuxTableTarget> {
    let measure = measure_gates_begin!(builder, "BuildOpAuxTbl");
    assert_eq!(
        params.max_custom_predicate_verifications,
        input.custom_predicate_verifications.len()
    );
    assert_eq!(
        params.containers.state.max_small,
        input.merkle_proofs.small.len()
    );
    assert_eq!(
        params.containers.state.max_medium,
        input.merkle_proofs.medium.len()
    );
    let max_entry_len = max_operation_aux_entry_len(params);
    let mut table = MuxTableTarget::new(params, max_entry_len);

    // None
    table.push_flattened(builder, OperationAuxTableTag::None as u32, &[]);

    append_container_proofs_operation_aux_table_circuit(
        builder,
        &mut table,
        &input.merkle_proofs,
        &input.merkle_transition_proofs,
    );

    append_open_input_statements_aux_table_circuit(
        params,
        builder,
        &mut table,
        input_pod_table,
        &input.open_input_statements,
    );

    // CustomPredVerify: verify custom predicate statements verification against operations
    for entry in &input.custom_predicate_verifications {
        let measure = measure_gates_begin!(builder, "CustomPredVerify");
        // Verify the custom predicate operation
        let (statement, op_type) = make_custom_statement_circuit(
            params,
            builder,
            &entry.custom_predicate,
            &entry.op_args,
            &entry.args,
        )?;

        // Check that the batch id is correct by querying the custom predicate batches table
        let table_query_hash = builder.vec_ref(
            params,
            custom_predicate_table,
            &entry.custom_predicate_table_index,
        );
        let out_query_hash = entry.custom_predicate.hash(builder);
        builder.connect_array(table_query_hash.elements, out_query_hash.elements);

        let query = CustomPredicateVerifyQueryTarget {
            statement,                      // output
            op_type,                        // output
            op_args: entry.op_args.clone(), // input
        };
        table.push(
            builder,
            OperationAuxTableTag::CustomPredVerify as u32,
            &query,
        );
        measure_gates_end!(builder, measure);
    }

    // PublicKeyOf: verify the derivation from a Schnorr secret key to public key
    let invgenerator = builder.constant_point(Point::generator().inverse());
    let zero_bits: [BoolTarget; 320] = array::from_fn(|_| builder._false());
    for sk in &input.public_key_of_sks {
        let measure = measure_gates_begin!(builder, "PublicKeyOf");
        let group_orderm1 = &*GROUP_ORDER - BigUint::one();
        let group_orderm1target = builder.constant_biguint320(&group_orderm1);
        let compare_ok = list_le_circuit(
            builder,
            sk.limbs.to_vec(),
            group_orderm1target.limbs.to_vec(),
            32,
        );
        builder.assert_one(compare_ok.target);
        // public_key = g^-secret key
        // Use the windowed ECAddXuGate (3-bit windows, 107 iterations) instead of the
        // naive multiply_point (1-bit double-and-add, 320 iterations) for fewer gates.
        let pk = builder.linear_combination_point_gen(&zero_bits, &sk.bits, &invgenerator);
        let sk_hash = builder.hash_n_to_hash_no_pad::<PoseidonHash>(sk.limbs.to_vec());
        let pk_hash = builder.hash_n_to_hash_no_pad::<PoseidonHash>(
            pk.x.components.into_iter().chain(pk.u.components).collect(),
        );

        let entry: PubKeySecKeyTarget = HashPairTarget(pk_hash, sk_hash);

        table.push(builder, OperationAuxTableTag::PublicKeyOf as u32, &entry);
        measure_gates_end!(builder, measure);
    }

    // SignedBy: verify the Schnorr signature of a message with a public key
    for signed_by in &input.signed_bys {
        let measure = measure_gates_begin!(builder, "SignedBy");

        let signature_verify = SignatureVerifyTarget {
            enabled: builder._true(),
            pk: signed_by.pk.clone(),
            msg: signed_by.msg,
            sig: signed_by.sig.clone(),
        };
        verify_signature_circuit(builder, &signature_verify);

        // TODO: Add a function to hash the public key
        let pk_hash = builder.hash_n_to_hash_no_pad::<PoseidonHash>(
            signed_by
                .pk
                .x
                .components
                .into_iter()
                .chain(signed_by.pk.u.components)
                .collect(),
        );
        let entry: MsgPubKeyTarget = HashPairTarget(HashOutTarget::from(signed_by.msg), pk_hash);

        table.push(builder, OperationAuxTableTag::SignedBy as u32, &entry);
        measure_gates_end!(builder, measure);
    }

    measure_gates_end!(builder, measure);
    Ok(table)
}

#[allow(clippy::too_many_arguments)]
fn verify_operation_circuit(
    params: &Params,
    builder: &mut CircuitBuilder,
    st: &StatementTarget,
    op: &OperationTarget,
    prev_statement_flatteneds: &[Vec<Target>],
    prev_statement_hashes: &[HashOutTarget],
    aux_table: &MuxTableTarget,
) -> Result<()> {
    let measure = measure_gates_begin!(builder, "OpVerifyPriv");
    let _true = builder._true();
    let _false = builder._false();

    // Verify that the operation `op` correctly generates the statement `st`.  The operation
    // can reference any of the `prev_statements`.
    // TODO: Clean this up.
    let measure_resolve_op_args = measure_gates_begin!(builder, "ResolveOpArgs");
    let cache = StatementCachePriv::new(
        params,
        BASE_PARAMS.max_operation_args,
        builder,
        op,
        st,
        prev_statement_flatteneds,
        prev_statement_hashes,
    );
    measure_gates_end!(builder, measure_resolve_op_args);

    // Certain operations (e.g.: Contains/NotContains) will refer to one of the provided verified
    // entries in a table (e.g.: Merkle proofs ). These entries have already been verified, so we
    // need only look up the claim.

    // The aux table always has a fixed zero entry, so we check if there are more than 1 entries to
    // trigger the unhashing.
    let resolved_aux = (aux_table.len() > 1).then(|| aux_table.get(builder, &op.aux_index));

    // Op checks to carry out. Each 'verify_X_circuit' should be thought of as operation check
    // restricted to the op of type X, where the returned target is `false` if the input targets
    // lie outside of the domain.
    let mut op_checks = Vec::new();
    op_checks.extend_from_slice(&[verify_none_circuit(params, builder, st, &op.op_type)]);
    // Skip these if there are no resolved op args
    if !cache.op_args.is_empty() {
        op_checks.extend_from_slice(&[
            verify_eq_neq_from_entries_circuit(builder, st, &op.op_type, &cache),
            verify_lt_lteq_from_entries_circuit(builder, st, &op.op_type, &cache),
            verify_transitive_eq_circuit(params, builder, st, &op.op_type, &cache.op_args),
            verify_lt_to_neq_circuit(params, builder, st, &op.op_type, &cache.op_args),
            verify_hash_of_circuit(params, builder, st, &op.op_type, &cache),
            verify_sum_of_circuit(params, builder, st, &op.op_type, &cache),
            verify_product_of_circuit(params, builder, st, &op.op_type, &cache),
            verify_max_of_circuit(params, builder, st, &op.op_type, &cache),
            verify_replace_value_with_entry_circuit(params, builder, st, &op.op_type, &cache),
        ]);
    }
    // Skip these if there are no resolved aux entries
    if let Some(resolved_aux) = resolved_aux {
        if params.containers.state.max_total() > 0 {
            op_checks.extend_from_slice(&[
                verify_contains_from_entries_circuit(
                    params,
                    builder,
                    st,
                    &op.op_type,
                    &resolved_aux,
                    &cache,
                ),
                verify_not_contains_from_entries_circuit(
                    params,
                    builder,
                    st,
                    &op.op_type,
                    &resolved_aux,
                    &cache,
                ),
            ]);
        }
        if params.max_public_key_of > 0 {
            op_checks.push(verify_public_key_of_circuit(
                params,
                builder,
                st,
                &op.op_type,
                &resolved_aux,
                &cache,
            ));
        }
        if params.max_signed_by > 0 {
            op_checks.push(verify_signed_by_circuit(
                params,
                builder,
                st,
                &op.op_type,
                &resolved_aux,
                &cache,
            ));
        }
        if params.containers.transition.max_total() > 0 {
            op_checks.extend_from_slice(&[
                verify_merkle_insert_circuit(
                    params,
                    builder,
                    st,
                    &op.op_type,
                    &resolved_aux,
                    &cache,
                ),
                verify_merkle_update_circuit(
                    params,
                    builder,
                    st,
                    &op.op_type,
                    &resolved_aux,
                    &cache,
                ),
                verify_merkle_delete_circuit(
                    params,
                    builder,
                    st,
                    &op.op_type,
                    &resolved_aux,
                    &cache,
                ),
            ]);
        }
        if params.max_custom_predicate_verifications > 0 {
            op_checks.push(verify_custom_circuit(
                builder,
                st,
                &op.op_type,
                &resolved_aux,
                &cache.op_args,
            ));
        }
        if params.max_open_input_statements > 0 {
            op_checks.extend_from_slice(&[verify_open_input_statement_circuit(
                builder,
                st,
                &op.op_type,
                &resolved_aux,
            )]);
        }
    }

    let ok = builder.any(op_checks);
    builder.assert_one(ok.target);

    measure_gates_end!(builder, measure);
    Ok(())
}

//
// Native operation constraints
//

fn verify_contains_from_entries_circuit(
    params: &Params,
    builder: &mut CircuitBuilder,
    st: &StatementTarget,
    op_type: &OperationTypeTarget,
    aux: &TableEntryTarget,
    cache: &StatementCachePriv,
) -> BoolTarget {
    let measure = measure_gates_begin!(builder, "OpContainsFromEntries");
    let (aux_tag_ok, resolved_merkle_claim) =
        aux.as_type::<MerkleClaimTarget>(builder, OperationAuxTableTag::MerkleProof as u32);
    let op_code_ok = op_type.has_native(builder, NativeOperation::ContainsFromEntries);

    let (arg_types_ok, [merkle_root_value, key_value, value_value]) =
        cache.first_n_args_as_values();

    // Check Merkle proof (verified elsewhere) against op args.
    let merkle_proof_checks = [
        /* ...and it must be an existence proof. */
        resolved_merkle_claim.existence,
        /* ...for the root-key-value triple in the resolved op args. */
        builder.is_equal_slice(
            &merkle_root_value.elements,
            &resolved_merkle_claim.root.elements,
        ),
        builder.is_equal_slice(&key_value.elements, &resolved_merkle_claim.key.elements),
        builder.is_equal_slice(&value_value.elements, &resolved_merkle_claim.value.elements),
    ];

    let merkle_proof_ok = builder.all(merkle_proof_checks);

    // Check output statement
    let arg1_expected = cache.equations[0].lhs.clone();
    let arg2_expected = cache.equations[1].lhs.clone();
    let arg3_expected = cache.equations[2].lhs.clone();
    let expected_statement = StatementTarget::new_native(
        builder,
        params,
        NativePredicate::Contains,
        &[arg1_expected, arg2_expected, arg3_expected],
    );
    let st_ok = builder.is_equal_flattenable(st, &expected_statement);

    let ok = builder.all([op_code_ok, aux_tag_ok, arg_types_ok, merkle_proof_ok, st_ok]);
    measure_gates_end!(builder, measure);
    ok
}

fn verify_not_contains_from_entries_circuit(
    params: &Params,
    builder: &mut CircuitBuilder,
    st: &StatementTarget,
    op_type: &OperationTypeTarget,
    aux: &TableEntryTarget,
    cache: &StatementCachePriv,
) -> BoolTarget {
    let measure = measure_gates_begin!(builder, "OpNotContainsFromEntries");
    let (aux_tag_ok, resolved_merkle_claim) =
        aux.as_type::<MerkleClaimTarget>(builder, OperationAuxTableTag::MerkleProof as u32);
    let op_code_ok = op_type.has_native(builder, NativeOperation::NotContainsFromEntries);

    let (arg_types_ok, [merkle_root_value, key_value]) = cache.first_n_args_as_values();

    // Check Merkle proof (verified elsewhere) against op args.
    let merkle_proof_checks = [
        /* ...and it must be a nonexistence proof. */
        builder.not(resolved_merkle_claim.existence),
        /* ...for the root-key pair in the resolved op args. */
        builder.is_equal_slice(
            &merkle_root_value.elements,
            &resolved_merkle_claim.root.elements,
        ),
        builder.is_equal_slice(&key_value.elements, &resolved_merkle_claim.key.elements),
    ];

    let merkle_proof_ok = builder.all(merkle_proof_checks);

    // Check output statement
    let arg1_expected = cache.equations[0].lhs.clone();
    let arg2_expected = cache.equations[1].lhs.clone();
    let expected_statement = StatementTarget::new_native(
        builder,
        params,
        NativePredicate::NotContains,
        &[arg1_expected, arg2_expected],
    );
    let st_ok = builder.is_equal_flattenable(st, &expected_statement);

    let ok = builder.all([op_code_ok, aux_tag_ok, arg_types_ok, merkle_proof_ok, st_ok]);
    measure_gates_end!(builder, measure);
    ok
}

fn verify_merkle_insert_circuit(
    params: &Params,
    builder: &mut CircuitBuilder,
    st: &StatementTarget,
    op_type: &OperationTypeTarget,
    aux: &TableEntryTarget,
    cache: &StatementCachePriv,
) -> BoolTarget {
    let measure = measure_gates_begin!(builder, "MerkleInsertOp");
    let (aux_tag_ok, resolved_merkle_tree_state_transition_claim) =
        aux.as_type::<MerkleTreeStateTransitionClaimTarget>(
            builder,
            OperationAuxTableTag::MerkleTransitionProof as u32,
        );
    let op_code_ok = op_type.has_native(builder, NativeOperation::ContainerInsertFromEntries);

    let (arg_types_ok, [new_root_value, old_root_value, op_key_value, op_value_value]) =
        cache.first_n_args_as_values();

    let expected_merkle_op = builder.constant(F::from_canonical_u8(MerkleTreeOp::Insert as u8));

    // Check Merkle proof (verified elsewhere) against op args.
    let merkle_proof_checks = [
        /* ...and it must be an insertion proof. */
        builder.is_equal(
            resolved_merkle_tree_state_transition_claim.op,
            expected_merkle_op,
        ),
        /* ...for the root-key-value combination in the resolved op args. */
        builder.is_equal_slice(
            &old_root_value.elements,
            &resolved_merkle_tree_state_transition_claim
                .old_root
                .elements,
        ),
        builder.is_equal_slice(
            &new_root_value.elements,
            &resolved_merkle_tree_state_transition_claim
                .new_root
                .elements,
        ),
        builder.is_equal_slice(
            &op_key_value.elements,
            &resolved_merkle_tree_state_transition_claim.op_key.elements,
        ),
        builder.is_equal_slice(
            &op_value_value.elements,
            &resolved_merkle_tree_state_transition_claim
                .op_value
                .elements,
        ),
    ];

    let merkle_proof_ok = builder.all(merkle_proof_checks);

    // Check output statement
    let arg1_expected = cache.equations[0].lhs.clone();
    let arg2_expected = cache.equations[1].lhs.clone();
    let arg3_expected = cache.equations[2].lhs.clone();
    let arg4_expected = cache.equations[3].lhs.clone();
    let expected_statement = StatementTarget::new_native(
        builder,
        params,
        NativePredicate::ContainerInsert,
        &[arg1_expected, arg2_expected, arg3_expected, arg4_expected],
    );
    let st_ok = builder.is_equal_flattenable(st, &expected_statement);

    let ok = builder.all([op_code_ok, aux_tag_ok, arg_types_ok, merkle_proof_ok, st_ok]);
    measure_gates_end!(builder, measure);
    ok
}

fn verify_merkle_update_circuit(
    params: &Params,
    builder: &mut CircuitBuilder,
    st: &StatementTarget,
    op_type: &OperationTypeTarget,
    aux: &TableEntryTarget,
    cache: &StatementCachePriv,
) -> BoolTarget {
    let measure = measure_gates_begin!(builder, "MerkleUpdateOp");
    let (aux_tag_ok, resolved_merkle_tree_state_transition_claim) =
        aux.as_type::<MerkleTreeStateTransitionClaimTarget>(
            builder,
            OperationAuxTableTag::MerkleTransitionProof as u32,
        );
    let op_code_ok = op_type.has_native(builder, NativeOperation::ContainerUpdateFromEntries);

    let (arg_types_ok, [new_root_value, old_root_value, op_key_value, op_value_value]) =
        cache.first_n_args_as_values();

    let expected_merkle_op = builder.constant(F::from_canonical_u8(MerkleTreeOp::Update as u8));

    // Check Merkle proof (verified elsewhere) against op args.
    let merkle_proof_checks = [
        /* ...and it must be an update proof. */
        builder.is_equal(
            resolved_merkle_tree_state_transition_claim.op,
            expected_merkle_op,
        ),
        /* ...for the root-key-value combination in the resolved op args. */
        builder.is_equal_slice(
            &old_root_value.elements,
            &resolved_merkle_tree_state_transition_claim
                .old_root
                .elements,
        ),
        builder.is_equal_slice(
            &new_root_value.elements,
            &resolved_merkle_tree_state_transition_claim
                .new_root
                .elements,
        ),
        builder.is_equal_slice(
            &op_key_value.elements,
            &resolved_merkle_tree_state_transition_claim.op_key.elements,
        ),
        builder.is_equal_slice(
            &op_value_value.elements,
            &resolved_merkle_tree_state_transition_claim
                .op_value
                .elements,
        ),
    ];

    let merkle_proof_ok = builder.all(merkle_proof_checks);

    // Check output statement
    let arg1_expected = cache.equations[0].lhs.clone();
    let arg2_expected = cache.equations[1].lhs.clone();
    let arg3_expected = cache.equations[2].lhs.clone();
    let arg4_expected = cache.equations[3].lhs.clone();
    let expected_statement = StatementTarget::new_native(
        builder,
        params,
        NativePredicate::ContainerUpdate,
        &[arg1_expected, arg2_expected, arg3_expected, arg4_expected],
    );
    let st_ok = builder.is_equal_flattenable(st, &expected_statement);

    let ok = builder.all([op_code_ok, aux_tag_ok, arg_types_ok, merkle_proof_ok, st_ok]);
    measure_gates_end!(builder, measure);
    ok
}

fn verify_merkle_delete_circuit(
    params: &Params,
    builder: &mut CircuitBuilder,
    st: &StatementTarget,
    op_type: &OperationTypeTarget,
    aux: &TableEntryTarget,
    cache: &StatementCachePriv,
) -> BoolTarget {
    let measure = measure_gates_begin!(builder, "MerkleDeleteOp");
    let (aux_tag_ok, resolved_merkle_tree_state_transition_claim) =
        aux.as_type::<MerkleTreeStateTransitionClaimTarget>(
            builder,
            OperationAuxTableTag::MerkleTransitionProof as u32,
        );
    let op_code_ok = op_type.has_native(builder, NativeOperation::ContainerDeleteFromEntries);

    let (arg_types_ok, [new_root_value, old_root_value, op_key_value]) =
        cache.first_n_args_as_values();

    let expected_merkle_op = builder.constant(F::from_canonical_u8(MerkleTreeOp::Delete as u8));

    // Check Merkle proof (verified elsewhere) against op args.
    let merkle_proof_checks = [
        /* ...and it must be a deletion proof. */
        builder.is_equal(
            resolved_merkle_tree_state_transition_claim.op,
            expected_merkle_op,
        ),
        /* ...for the root-key combination in the resolved op args. */
        builder.is_equal_slice(
            &old_root_value.elements,
            &resolved_merkle_tree_state_transition_claim
                .old_root
                .elements,
        ),
        builder.is_equal_slice(
            &new_root_value.elements,
            &resolved_merkle_tree_state_transition_claim
                .new_root
                .elements,
        ),
        builder.is_equal_slice(
            &op_key_value.elements,
            &resolved_merkle_tree_state_transition_claim.op_key.elements,
        ),
    ];

    let merkle_proof_ok = builder.all(merkle_proof_checks);

    // Check output statement
    let arg1_expected = cache.equations[0].lhs.clone();
    let arg2_expected = cache.equations[1].lhs.clone();
    let arg3_expected = cache.equations[2].lhs.clone();
    let expected_statement = StatementTarget::new_native(
        builder,
        params,
        NativePredicate::ContainerDelete,
        &[arg1_expected, arg2_expected, arg3_expected],
    );
    let st_ok = builder.is_equal_flattenable(st, &expected_statement);

    let ok = builder.all([op_code_ok, aux_tag_ok, arg_types_ok, merkle_proof_ok, st_ok]);
    measure_gates_end!(builder, measure);
    ok
}

fn verify_custom_circuit(
    builder: &mut CircuitBuilder,
    st: &StatementTarget,
    op_type: &OperationTypeTarget,
    aux: &TableEntryTarget,
    resolved_op_args: &[StatementTarget],
) -> BoolTarget {
    let measure = measure_gates_begin!(builder, "OpCustom");
    let (aux_tag_ok, resolved_query) = aux.as_type::<CustomPredicateVerifyQueryTarget>(
        builder,
        OperationAuxTableTag::CustomPredVerify as u32,
    );

    let query_ok = builder.is_equal_flattenable(
        &resolved_query,
        &CustomPredicateVerifyQueryTarget {
            statement: st.clone(),
            op_type: op_type.clone(),
            op_args: resolved_op_args.to_vec(),
        },
    );
    let ok = builder.all([aux_tag_ok, query_ok]);
    measure_gates_end!(builder, measure);
    ok
}

fn verify_open_input_statement_circuit(
    builder: &mut CircuitBuilder,
    st: &StatementTarget,
    op_type: &OperationTypeTarget,
    aux: &TableEntryTarget,
) -> BoolTarget {
    let measure = measure_gates_begin!(builder, "OpOpenInputSt");
    let (aux_tag_ok, resolved_statement) =
        aux.as_type::<StatementTarget>(builder, OperationAuxTableTag::OpenInputStatement as u32);
    let op_code_ok = op_type.has_native(builder, NativeOperation::OpenInputStatement);
    let query_ok = builder.is_equal_flattenable(&resolved_statement, st);

    let ok = builder.all([op_code_ok, aux_tag_ok, query_ok]);
    measure_gates_end!(builder, measure);
    ok
}

/// Carries out the checks necessary for EqualFromEntries and
/// NotEqualFromEntries.
fn verify_eq_neq_from_entries_circuit(
    builder: &mut CircuitBuilder,
    st: &StatementTarget,
    op_type: &OperationTypeTarget,
    cache: &StatementCachePriv,
) -> BoolTarget {
    let measure = measure_gates_begin!(builder, "OpEqNeqFromEntries");
    let eq_op_st_code_ok = {
        let op_code_ok = op_type.has_native(builder, NativeOperation::EqualFromEntries);
        let st_code_ok = st.has_native_type(builder, NativePredicate::Equal);
        builder.and(op_code_ok, st_code_ok)
    };
    let neq_op_st_code_ok = {
        let op_code_ok = op_type.has_native(builder, NativeOperation::NotEqualFromEntries);
        let st_code_ok = st.has_native_type(builder, NativePredicate::NotEqual);
        builder.and(op_code_ok, st_code_ok)
    };
    let op_st_code_ok = builder.or(eq_op_st_code_ok, neq_op_st_code_ok);

    let (arg_types_ok, [arg1_value, arg2_value]) = cache.first_n_args_as_values();

    let op_args_eq = builder.is_equal_slice(&arg1_value.elements, &arg2_value.elements);
    let op_args_ok = builder.is_equal(op_args_eq.target, eq_op_st_code_ok.target);

    let arg1_expected = cache.equations[0].lhs.clone();
    let arg2_expected = cache.equations[1].lhs.clone();

    let expected_st_args: Vec<_> = [arg1_expected, arg2_expected]
        .into_iter()
        .chain(std::iter::repeat_with(|| StatementArgTarget::none(builder)))
        .take(Params::max_statement_args())
        .flat_map(|arg| arg.elements)
        .collect();

    let st_args_ok = builder.is_equal_slice(
        &expected_st_args,
        &st.args
            .iter()
            .flat_map(|arg| arg.elements)
            .collect::<Vec<_>>(),
    );

    let ok = builder.all([op_st_code_ok, arg_types_ok, op_args_ok, st_args_ok]);
    measure_gates_end!(builder, measure);
    ok
}

/// Carries out the checks necessary for LtFromEntries and
/// LtEqFromEntries.
fn verify_lt_lteq_from_entries_circuit(
    builder: &mut CircuitBuilder,
    st: &StatementTarget,
    op_type: &OperationTypeTarget,
    cache: &StatementCachePriv,
) -> BoolTarget {
    let measure = measure_gates_begin!(builder, "OpLtEqFromEntries");
    let zero = ValueTarget::zero(builder);
    let one = ValueTarget::one(builder);

    let lt_op_st_code_ok = {
        let op_code_ok = op_type.has_native(builder, NativeOperation::LtFromEntries);
        let st_code_ok = st.has_native_type(builder, NativePredicate::Lt);
        builder.and(op_code_ok, st_code_ok)
    };
    let lteq_op_st_code_ok = {
        let op_code_ok = op_type.has_native(builder, NativeOperation::LtEqFromEntries);
        let st_code_ok = st.has_native_type(builder, NativePredicate::LtEq);
        builder.and(op_code_ok, st_code_ok)
    };
    let op_st_code_ok = builder.or(lt_op_st_code_ok, lteq_op_st_code_ok);

    let (arg_types_ok, [arg1_value, arg2_value]) = cache.first_n_args_as_values();

    // If we are not dealing with the right op & statement types,
    // replace args with dummy values in the following checks.
    let value1 = builder.select_value(op_st_code_ok, arg1_value, zero);
    let value2 = builder.select_value(op_st_code_ok, arg2_value, one);

    // Range check
    builder.assert_i64(value1);
    builder.assert_i64(value2);

    // Check for equality.
    let args_equal = builder.is_equal_slice(&value1.elements, &value2.elements);

    // Check < if applicable.
    let lt_check_flag = {
        let not_args_equal = builder.not(args_equal);
        let lteq_eq_case = builder.and(lteq_op_st_code_ok, not_args_equal);
        builder.or(lt_op_st_code_ok, lteq_eq_case)
    };
    builder.assert_i64_less_if(lt_check_flag, value1, value2);

    let arg1_expected = cache.equations[0].lhs.clone();
    let arg2_expected = cache.equations[1].lhs.clone();

    let expected_st_args: Vec<_> = [arg1_expected, arg2_expected]
        .into_iter()
        .chain(std::iter::repeat_with(|| StatementArgTarget::none(builder)))
        .take(Params::max_statement_args())
        .flat_map(|arg| arg.elements)
        .collect();

    let st_args_ok = builder.is_equal_slice(
        &expected_st_args,
        &st.args
            .iter()
            .flat_map(|arg| arg.elements)
            .collect::<Vec<_>>(),
    );

    let ok = builder.all([op_st_code_ok, arg_types_ok, st_args_ok]);
    measure_gates_end!(builder, measure);
    ok
}

fn verify_hash_of_circuit(
    params: &Params,
    builder: &mut CircuitBuilder,
    st: &StatementTarget,
    op_type: &OperationTypeTarget,
    cache: &StatementCachePriv,
) -> BoolTarget {
    let measure = measure_gates_begin!(builder, "OpHashOf");
    let op_code_ok = op_type.has_native(builder, NativeOperation::HashOf);

    let (arg_types_ok, [arg1_value, arg2_value, arg3_value]) = cache.first_n_args_as_values();

    let expected_hash_value = builder.hash_values(arg2_value, arg3_value);

    let hash_value_ok = builder.is_equal_slice(&arg1_value.elements, &expected_hash_value.elements);

    let arg1_expected = cache.equations[0].lhs.clone();
    let arg2_expected = cache.equations[1].lhs.clone();
    let arg3_expected = cache.equations[2].lhs.clone();
    let expected_statement = StatementTarget::new_native(
        builder,
        params,
        NativePredicate::HashOf,
        &[arg1_expected, arg2_expected, arg3_expected],
    );
    let st_ok = builder.is_equal_flattenable(st, &expected_statement);

    let ok = builder.all([op_code_ok, arg_types_ok, hash_value_ok, st_ok]);
    measure_gates_end!(builder, measure);
    ok
}

fn verify_public_key_of_circuit(
    params: &Params,
    builder: &mut CircuitBuilder,
    st: &StatementTarget,
    op_type: &OperationTypeTarget,
    aux: &TableEntryTarget,
    cache: &StatementCachePriv,
) -> BoolTarget {
    let measure = measure_gates_begin!(builder, "OpPublicKeyOf");
    let (aux_tag_ok, resolved_pk_sk) =
        aux.as_type::<PubKeySecKeyTarget>(builder, OperationAuxTableTag::PublicKeyOf as u32);

    let op_code_ok = op_type.has_native(builder, NativeOperation::PublicKeyOf);
    let (arg_types_ok, [arg1_value, arg2_value]) = cache.first_n_args_as_values();
    // inputting public_key, secret_key
    let pk_hash = arg1_value;
    let sk_hash = arg2_value;

    let pk_ok = builder.is_equal_slice(&pk_hash.elements, &resolved_pk_sk.0.elements);
    let sk_ok = builder.is_equal_slice(&sk_hash.elements, &resolved_pk_sk.1.elements);

    let arg1_expected = cache.equations[0].lhs.clone();
    let arg2_expected = cache.equations[1].lhs.clone();
    let expected_statement = StatementTarget::new_native(
        builder,
        params,
        NativePredicate::PublicKeyOf,
        &[arg1_expected, arg2_expected],
    );
    let st_ok = builder.is_equal_flattenable(st, &expected_statement);

    let ok = builder.all([op_code_ok, aux_tag_ok, arg_types_ok, pk_ok, sk_ok, st_ok]);
    measure_gates_end!(builder, measure);
    ok
}

fn verify_signed_by_circuit(
    params: &Params,
    builder: &mut CircuitBuilder,
    st: &StatementTarget,
    op_type: &OperationTypeTarget,
    aux: &TableEntryTarget,
    cache: &StatementCachePriv,
) -> BoolTarget {
    let measure = measure_gates_begin!(builder, "OpSignedBy");
    let (aux_tag_ok, resolved_msg_pk) =
        aux.as_type::<MsgPubKeyTarget>(builder, OperationAuxTableTag::SignedBy as u32);

    let op_code_ok = op_type.has_native(builder, NativeOperation::SignedBy);
    let (arg_types_ok, [arg1_value, arg2_value]) = cache.first_n_args_as_values();
    // inputting msg, pub_key
    let msg = arg1_value;
    let pk_hash = arg2_value;

    let msg_ok = builder.is_equal_slice(&msg.elements, &resolved_msg_pk.0.elements);
    let pk_ok = builder.is_equal_slice(&pk_hash.elements, &resolved_msg_pk.1.elements);

    let arg1_expected = cache.equations[0].lhs.clone();
    let arg2_expected = cache.equations[1].lhs.clone();
    let expected_statement = StatementTarget::new_native(
        builder,
        params,
        NativePredicate::SignedBy,
        &[arg1_expected, arg2_expected],
    );
    let st_ok = builder.is_equal_flattenable(st, &expected_statement);

    let ok = builder.all([op_code_ok, aux_tag_ok, arg_types_ok, msg_ok, pk_ok, st_ok]);
    measure_gates_end!(builder, measure);
    ok
}

fn verify_sum_of_circuit(
    params: &Params,
    builder: &mut CircuitBuilder,
    st: &StatementTarget,
    op_type: &OperationTypeTarget,
    cache: &StatementCachePriv,
) -> BoolTarget {
    let measure = measure_gates_begin!(builder, "OpSumOf");
    let value_zero = ValueTarget::zero(builder);

    let op_code_ok = op_type.has_native(builder, NativeOperation::SumOf);

    let (arg_types_ok, [arg1_value, arg2_value, arg3_value]) = cache.first_n_args_as_values();

    // Select to avoid overflow.
    let summand1 = builder.select_value(op_code_ok, arg2_value, value_zero);
    let summand2 = builder.select_value(op_code_ok, arg3_value, value_zero);

    let expected_sum = builder.i64_add(summand1, summand2);

    let sum_ok = builder.is_equal_slice(&arg1_value.elements, &expected_sum.elements);

    let arg1_expected = cache.equations[0].lhs.clone();
    let arg2_expected = cache.equations[1].lhs.clone();
    let arg3_expected = cache.equations[2].lhs.clone();
    let expected_statement = StatementTarget::new_native(
        builder,
        params,
        NativePredicate::SumOf,
        &[arg1_expected, arg2_expected, arg3_expected],
    );
    let st_ok = builder.is_equal_flattenable(st, &expected_statement);

    let ok = builder.all([op_code_ok, arg_types_ok, sum_ok, st_ok]);
    measure_gates_end!(builder, measure);
    ok
}

fn verify_product_of_circuit(
    params: &Params,
    builder: &mut CircuitBuilder,
    st: &StatementTarget,
    op_type: &OperationTypeTarget,
    cache: &StatementCachePriv,
) -> BoolTarget {
    let measure = measure_gates_begin!(builder, "OpProductOf");
    let value_zero = ValueTarget::zero(builder);

    let op_code_ok = op_type.has_native(builder, NativeOperation::ProductOf);

    let (arg_types_ok, [arg1_value, arg2_value, arg3_value]) = cache.first_n_args_as_values();

    // Select to avoid overflow.
    let factor1 = builder.select_value(op_code_ok, arg2_value, value_zero);
    let factor2 = builder.select_value(op_code_ok, arg3_value, value_zero);

    let expected_product = builder.i64_mul(factor1, factor2);

    let product_ok = builder.is_equal_slice(&arg1_value.elements, &expected_product.elements);

    let arg1_expected = cache.equations[0].lhs.clone();
    let arg2_expected = cache.equations[1].lhs.clone();
    let arg3_expected = cache.equations[2].lhs.clone();
    let expected_statement = StatementTarget::new_native(
        builder,
        params,
        NativePredicate::ProductOf,
        &[arg1_expected, arg2_expected, arg3_expected],
    );
    let st_ok = builder.is_equal_flattenable(st, &expected_statement);

    let ok = builder.all([op_code_ok, arg_types_ok, product_ok, st_ok]);
    measure_gates_end!(builder, measure);
    ok
}

fn verify_max_of_circuit(
    params: &Params,
    builder: &mut CircuitBuilder,
    st: &StatementTarget,
    op_type: &OperationTypeTarget,
    cache: &StatementCachePriv,
) -> BoolTarget {
    let measure = measure_gates_begin!(builder, "OpMaxOf");
    let op_code_ok = op_type.has_native(builder, NativeOperation::MaxOf);

    let (arg_types_ok, [arg1_value, arg2_value, arg3_value]) = cache.first_n_args_as_values();

    // Check that arg1_value is equal to one of the other two
    // values.
    let arg1_eq_arg2 = builder.is_equal_slice(&arg1_value.elements, &arg2_value.elements);
    let arg1_eq_arg3 = builder.is_equal_slice(&arg1_value.elements, &arg3_value.elements);

    let all_eq = builder.and(arg1_eq_arg2, arg1_eq_arg3);
    let not_all_eq = builder.not(all_eq);

    let arg1_check = builder.or(arg1_eq_arg2, arg1_eq_arg3);

    // If it is not equal to any of the other two values, it must be greater than it.
    let lower_bound = builder.select_value(arg1_eq_arg2, arg3_value, arg2_value);

    // Only check lower bound if not all args are equal.
    let lt_check_enabled = builder.and(not_all_eq, op_code_ok);
    builder.assert_i64_less_if(lt_check_enabled, lower_bound, arg1_value);

    let arg1_expected = cache.equations[0].lhs.clone();
    let arg2_expected = cache.equations[1].lhs.clone();
    let arg3_expected = cache.equations[2].lhs.clone();
    let expected_statement = StatementTarget::new_native(
        builder,
        params,
        NativePredicate::MaxOf,
        &[arg1_expected, arg2_expected, arg3_expected],
    );
    let st_ok = builder.is_equal_flattenable(st, &expected_statement);

    let ok = builder.all([op_code_ok, arg_types_ok, arg1_check, st_ok]);
    measure_gates_end!(builder, measure);
    ok
}

fn verify_replace_value_with_entry_circuit(
    params: &Params,
    builder: &mut CircuitBuilder,
    st: &StatementTarget,
    op_type: &OperationTypeTarget,
    cache: &StatementCachePriv,
) -> BoolTarget {
    let measure = measure_gates_begin!(builder, "OpReplaceValueWithEntry");
    let op_code_ok = op_type.has_native(builder, NativeOperation::ReplaceValueWithEntry);

    let st_in = &cache.op_args[BASE_PARAMS.max_statement_args];

    let mut args = Vec::new();
    let mut args_ok = builder._true();
    for (arg_in, entry_cache) in zip_eq(&st_in.args, &cache.equations) {
        // if the op_arg is None, keep the original argument, if it's a Contains swap the value by
        // the reference Entry while checking that the value in Contains matches the original
        // argument.
        let arg = builder.select_flattenable(
            params,
            entry_cache.pred_is_none,
            arg_in,
            &entry_cache.reference,
        );
        args.push(arg);
        let arg_ref_ok = {
            let arg_in_is_value = builder.statement_arg_is_value(arg_in);
            let value_eq = builder.is_equal_flattenable(&arg_in.as_value(), &entry_cache.value);
            builder.all([entry_cache.is_reference, arg_in_is_value, value_eq])
        };
        let arg_ok = builder.or(entry_cache.pred_is_none, arg_ref_ok);
        args_ok = builder.and(args_ok, arg_ok);
    }
    let expected_statement = StatementTarget::new(*st_in.pred_hash(), args);
    let st_ok = builder.is_equal_flattenable(st, &expected_statement);

    let ok = builder.all([op_code_ok, args_ok, st_ok]);
    measure_gates_end!(builder, measure);
    ok
}

fn verify_transitive_eq_circuit(
    params: &Params,
    builder: &mut CircuitBuilder,
    st: &StatementTarget,
    op_type: &OperationTypeTarget,
    resolved_op_args: &[StatementTarget],
) -> BoolTarget {
    let measure = measure_gates_begin!(builder, "OpTransitiveEq");
    let op_code_ok = op_type.has_native(builder, NativeOperation::TransitiveEqualFromStatements);

    let arg1_type_ok = resolved_op_args[0].has_native_type(builder, NativePredicate::Equal);
    let arg2_type_ok = resolved_op_args[1].has_native_type(builder, NativePredicate::Equal);
    let arg_types_ok = builder.all([arg1_type_ok, arg2_type_ok]);

    let arg1_lhs = &resolved_op_args[0].args[0];
    let arg1_rhs = &resolved_op_args[0].args[1];
    let arg2_lhs = &resolved_op_args[1].args[0];
    let arg2_rhs = &resolved_op_args[1].args[1];

    let inner_args_match = builder.is_equal_slice(&arg1_rhs.elements, &arg2_lhs.elements);

    let expected_statement = StatementTarget::new_native(
        builder,
        params,
        NativePredicate::Equal,
        &[arg1_lhs.clone(), arg2_rhs.clone()],
    );
    let st_ok = builder.is_equal_flattenable(st, &expected_statement);

    let ok = builder.all([op_code_ok, arg_types_ok, inner_args_match, st_ok]);
    measure_gates_end!(builder, measure);
    ok
}

fn verify_none_circuit(
    params: &Params,
    builder: &mut CircuitBuilder,
    st: &StatementTarget,
    op_type: &OperationTypeTarget,
) -> BoolTarget {
    let measure = measure_gates_begin!(builder, "OpNone");
    let op_code_ok = op_type.has_native(builder, NativeOperation::None);

    let expected_statement =
        StatementTarget::new_native(builder, params, NativePredicate::None, &[]);
    let st_ok = builder.is_equal_flattenable(st, &expected_statement);

    let ok = builder.all([op_code_ok, st_ok]);
    measure_gates_end!(builder, measure);
    ok
}

fn verify_lt_to_neq_circuit(
    params: &Params,
    builder: &mut CircuitBuilder,
    st: &StatementTarget,
    op_type: &OperationTypeTarget,
    resolved_op_args: &[StatementTarget],
) -> BoolTarget {
    let measure = measure_gates_begin!(builder, "OpLtToNeq");
    let op_code_ok = op_type.has_native(builder, NativeOperation::LtToNotEqual);

    let arg_type_ok = resolved_op_args[0].has_native_type(builder, NativePredicate::Lt);

    let arg1_expected = resolved_op_args[0].args[0].clone();
    let arg2_expected = resolved_op_args[0].args[1].clone();

    let expected_statement = StatementTarget::new_native(
        builder,
        params,
        NativePredicate::NotEqual,
        &[arg1_expected, arg2_expected],
    );
    let st_ok = builder.is_equal_flattenable(st, &expected_statement);

    let ok = builder.all([op_code_ok, arg_type_ok, st_ok]);
    measure_gates_end!(builder, measure);
    ok
}

//
// Custom Predicate constraints
//

// NOTE: This is a bit messy.  The target types are defined in `common.rs` because they are used in
// `add_virtual_foo` methods in the trait for the `CircuitBuilder`.  But the constraint logic is
// here.  Maybe we want to move everything related to custom predicates to its own module, but then
// should we add a new trait for the `add_virtual_foo` methods so that everything is contained in a
// module?
fn make_statement_arg_from_template_circuit(
    params: &Params,
    builder: &mut CircuitBuilder,
    st_tmpl_arg: &StatementTmplArgTarget,
    args: &[ValueTarget],
) -> StatementArgTarget {
    let zero = builder.zero();
    let (is_literal, value_literal) = st_tmpl_arg.as_literal(builder);
    let (is_ak, ak_id_wc_index, ak_key) = st_tmpl_arg.as_anchored_key(builder);
    let (is_wc_literal, wc_index) = st_tmpl_arg.as_wildcard_literal(builder);

    // optimization: ak_id_wc_index and wc_index use the same signals, so we only need to do one
    // random access to resolve both of them
    assert_eq!(ak_id_wc_index, wc_index);

    // If the index is not used, use a 0 instead to still pass the range constraints from
    // vec_ref
    let first_index = ak_id_wc_index;
    let is_first_index_valid = builder.or(is_ak, is_wc_literal);
    let first_index = builder.select(is_first_index_valid, first_index, zero);
    let resolved_ak_id = builder.vec_ref_small(params, args, first_index);
    let resolved_wc = resolved_ak_id;

    let first = ValueTarget::zero(builder); // is_none
    let first = builder.select_flattenable(params, is_literal, &value_literal, &first);
    let first = builder.select_flattenable(params, is_ak, &resolved_ak_id, &first);
    let first = builder.select_flattenable(params, is_wc_literal, &resolved_wc, &first);

    let second = ValueTarget::zero(builder); // is_none or is_literal or is_wc_literal
    let second = builder.select_flattenable(params, is_ak, &ak_key, &second);

    StatementArgTarget::new(first, second)
}

fn make_predicate_from_template_circuit(
    params: &Params,
    builder: &mut CircuitBuilder,
    pred_hash_or_wc: &PredicateHashOrWildcardTarget,
    args: &[ValueTarget],
) -> HashOutTarget {
    let zero = builder.zero();
    let is_pred = pred_hash_or_wc.is_pred(builder);
    // If the index is not used, use a 0 instead to still pass the range constraints from
    // vec_ref
    let index = builder.select(is_pred, zero, pred_hash_or_wc.wc_index());
    let resolved_pred_hash = HashOutTarget::from(builder.vec_ref_small(params, args, index));
    builder.select_flattenable(
        params,
        is_pred,
        &pred_hash_or_wc.pred_hash(),
        &resolved_pred_hash,
    )
}

fn make_statement_from_template_circuit(
    params: &Params,
    builder: &mut CircuitBuilder,
    st_tmpl: &StatementTmplTarget,
    args: &[ValueTarget],
) -> StatementTarget {
    let measure = measure_gates_begin!(builder, "StArgFromTmpl");
    let st_args = st_tmpl
        .args
        .iter()
        .map(|st_tmpl_arg| {
            make_statement_arg_from_template_circuit(params, builder, st_tmpl_arg, args)
        })
        .collect();
    measure_gates_end!(builder, measure);
    let measure = measure_gates_begin!(builder, "PredFromTmpl");
    let pred_hash =
        make_predicate_from_template_circuit(params, builder, st_tmpl.pred_hash_or_wc(), args);
    measure_gates_end!(builder, measure);
    StatementTarget::new(pred_hash, st_args)
}

/// Given a custom predicate, a list of operation arguments (statements) and a list of wildcard
/// values (args):
/// - Verify that the custom predicate is satisfied with the given statements
/// - Build the output statement
/// - Build the expected operation type
fn make_custom_statement_circuit(
    params: &Params,
    builder: &mut CircuitBuilder,
    custom_predicate: &CustomPredicateEntryTarget,
    op_args: &[StatementTarget],
    args: &[ValueTarget], // arguments to the custom predicate, public and private
) -> Result<(StatementTarget, OperationTypeTarget)> {
    let measure = measure_gates_begin!(builder, "CustomOpVerify");
    // Some sanity checks
    assert_eq!(BASE_PARAMS.max_operation_args, op_args.len());
    assert_eq!(params.max_custom_predicate_wildcards, args.len());

    let (batch_id, index) = (custom_predicate.id, custom_predicate.index);
    let op_type = OperationTypeTarget::new_custom(builder, batch_id, index);

    // Build the statement
    let st_predicate = PredicateTarget::new_custom(builder, batch_id, index);
    let arg_none = ValueTarget::zero(builder);
    let lt_mask = builder.lt_mask(
        Params::max_statement_args(),
        custom_predicate.predicate.args_len,
    );
    let st_args = std::iter::zip(lt_mask, args)
        .map(|(mask, arg)| {
            let v = builder.select_flattenable(params, mask, arg, &arg_none);
            StatementArgTarget::wildcard_literal(builder, &v)
        })
        .collect_vec();
    let statement_with_pred =
        StatementTarget::new_with_pred(builder, params, st_predicate, &st_args);

    // Check the operation arguments
    // From each statement template we generate an expected statement using replacing the
    // wildcards by the arguments.  Then we compare the expected statement with the operation
    // argument.
    let expected_sts: Vec<_> = custom_predicate
        .predicate
        .statements
        .iter()
        .map(|st_tmpl| make_statement_from_template_circuit(params, builder, st_tmpl, args))
        .collect();
    // expected_sts.len() == params.max_custom_predicate_arity
    // op_args.len() == params.max_operation_args;

    let sts_eq: Vec<_> = expected_sts
        .iter()
        .zip(op_args.iter())
        .map(|(expected_st, st)| builder.is_equal_flattenable(expected_st, st))
        .collect();
    let all_st_eq = builder.all(sts_eq.clone());
    let some_st_eq = builder.any(sts_eq);
    // NOTE: This BoolTarget is safe because both inputs to the select are safe
    let is_op_args_ok = BoolTarget::new_unsafe(builder.select(
        custom_predicate.predicate.conjunction,
        all_st_eq.target,
        some_st_eq.target,
    ));

    builder.assert_one(is_op_args_ok.target);
    measure_gates_end!(builder, measure);
    Ok((statement_with_pred, op_type))
}

/// Replace the blank verifier_data_hash slots in intro predicates by `vd_hash`
fn normalize_statement_circuit(
    params: &Params,
    builder: &mut CircuitBuilder,
    raw_st: &StatementTarget,
    is_intro: BoolTarget,
    vd_hash: &HashOutTarget,
) -> StatementTarget {
    let is_none = raw_st.pred_is_none(params, builder);
    let is_not_none = builder.not(is_none);
    let replace = builder.and(is_intro, is_not_none);
    let old_pred_hash = raw_st.pred_hash();
    let intro_pred_hash = PredicateTarget::new_intro(builder, *vd_hash).hash(builder);
    let new_pred_hash =
        builder.select_flattenable(params, replace, &intro_pred_hash, old_pred_hash);

    StatementTarget::new(new_pred_hash, raw_st.args.clone())
}

// Replace BatchSelf predicates with the corresponding Custom(batch_id, index), and
// SelfPredicateHash args with Literal(hash(Custom(batch_id, index))).
fn normalize_st_tmpl_circuit(
    params: &Params,
    builder: &mut CircuitBuilder,
    st_tmpl: &StatementTmplTarget,
    id: HashOutTarget,
) -> StatementTmplTarget {
    // If the custom predicate is self, we normalize it and then hash it.
    let old_pred = st_tmpl.pred().expect("StatementTmpl contains predicate");
    let prefix_batch_self = builder.constant(F::from(PredicatePrefix::BatchSelf));
    let is_batch_self = builder.is_equal(old_pred.elements[0], prefix_batch_self);

    let pred_index = old_pred.elements[1];
    let normalized_custom_pred = PredicateTarget::new_custom(builder, id, pred_index);
    let normalized_custom_pred_hash = normalized_custom_pred.hash(builder);

    // If the template is using a predicate and it is batch self we use the freshly computed
    // normalized predicate hash, otherwise we keep the original data.
    let old_data = st_tmpl.pred_hash_or_wc().data();
    let is_pred = st_tmpl.pred_hash_or_wc().is_pred(builder);
    let is_pred_batch_self = builder.and(is_pred, is_batch_self);
    let data = builder.select_flattenable(
        params,
        is_pred_batch_self,
        &ValueTarget::from(normalized_custom_pred_hash),
        &old_data,
    );
    let pred_hash_or_wc =
        PredicateHashOrWildcardTarget::new(st_tmpl.pred_hash_or_wc().elements[0], data);

    // Normalize SelfPredicateHash args: replace prefix 4 with Literal containing the resolved
    // predicate hash. Same pattern as the predicate normalization above.
    let prefix_sph = builder.constant(F::from(StatementTmplArgPrefix::SelfPredicateHash));
    let prefix_literal = builder.constant(F::from(StatementTmplArgPrefix::Literal));
    let zero = builder.zero();
    let normalized_args = st_tmpl
        .args
        .iter()
        .map(|arg| {
            let is_sph = builder.is_equal(arg.elements[0], prefix_sph);

            // The predicate index is in elements[1] (same slot as WildcardLiteral).
            let pred_index = arg.elements[1];

            // Compute hash(Custom(batch_id, pred_index))
            let pred_target = PredicateTarget::new_custom(builder, id, pred_index);
            let pred_hash = pred_target.hash(builder);

            // Build a Literal-encoded arg: [1, hash[0..4], 0, 0, 0, 0]
            let mut literal_elements = [zero; Params::statement_tmpl_arg_size()];
            literal_elements[0] = prefix_literal;
            literal_elements[1] = pred_hash.elements[0];
            literal_elements[2] = pred_hash.elements[1];
            literal_elements[3] = pred_hash.elements[2];
            literal_elements[4] = pred_hash.elements[3];
            let normalized = StatementTmplArgTarget {
                elements: literal_elements,
            };

            builder.select_flattenable(params, is_sph, &normalized, arg)
        })
        .collect();

    StatementTmplTarget::new(pred_hash_or_wc, normalized_args)
}

/// Build a table of [batch_id, custom_predicate_index, custom_predicate] with queryable part as
/// hash([batch_id, custom_predicate_index, custom_predicate]).  While building the table we
/// calculate the id of each batch.  Return the hash of each table entry.
fn build_custom_predicate_table_circuit(
    params: &Params,
    builder: &mut CircuitBuilder,
    custom_predicates: &[CustomPredicateInBatchTarget],
) -> Result<Vec<HashOutTarget>> {
    let measure = measure_gates_begin!(builder, "BuildCustomPredTbl");
    let mut custom_predicate_table = Vec::with_capacity(params.max_custom_predicates);
    for cp in custom_predicates {
        let measure_cp = measure_gates_begin!(builder, "CustomPred");
        cp.verify_circuit(builder);
        let statements = cp
            .self_predicate
            .statements
            .iter()
            .map(|st_with_pred_tmpl| {
                normalize_st_tmpl_circuit(params, builder, st_with_pred_tmpl, cp.id)
            })
            .collect_vec();
        let entry = CustomPredicateEntryTarget {
            id: cp.id,       // output
            index: cp.index, // input
            predicate: CustomPredicateTarget {
                conjunction: cp.self_predicate.conjunction,
                statements,
                args_len: cp.self_predicate.args_len,
            }, // input
        };

        let in_query_hash = entry.hash(builder);
        custom_predicate_table.push(in_query_hash);
        measure_gates_end!(builder, measure_cp);
    }
    measure_gates_end!(builder, measure);
    Ok(custom_predicate_table)
}

// Entry for StsRoots transition table, where one statement is inserted.
struct StsRootsEntry {
    old_root: HashOutTarget,
    new_root: HashOutTarget,
    st_hash: ValueTarget,
}

impl Flattenable for StsRootsEntry {
    fn flatten(&self) -> Vec<Target> {
        self.old_root
            .elements
            .into_iter()
            .chain(self.new_root.elements)
            .chain(self.st_hash.elements)
            .collect()
    }
    fn from_flattened(params: &Params, vs: &[Target]) -> Self {
        assert_eq!(vs.len(), Self::size(params));
        Self {
            old_root: HashOutTarget::try_from(&vs[..4]).expect("len = 4"),
            new_root: HashOutTarget::try_from(&vs[4..8]).expect("len = 4"),
            st_hash: ValueTarget::from_slice(&vs[8..12]),
        }
    }
    fn size(params: &Params) -> usize {
        2 * HashOutTarget::size(params) + ValueTarget::size(params)
    }
}

fn verify_main_pod_circuit(
    builder: &mut CircuitBuilder,
    main_pod: &MainPodVerifyTarget,
    verified_proofs: &[VerifiedProofTarget],
) -> Result<HashOutTarget> {
    let params = &main_pod.params;
    assert_eq!(params.max_input_pods, verified_proofs.len());

    let measure = measure_gates_begin!(builder, "MainPodVerify");

    let mut input_pod_table = Vec::with_capacity(params.max_input_pods);
    let mut pod0_sts_root = None;
    // 1a. Verify all input recursive pods
    for (i, (verified_proof, vd_mt_proof)) in
        izip!(verified_proofs, &main_pod.vd_mt_proofs,).enumerate()
    {
        let measure_in_pod = measure_gates_begin!(builder, "VerifyInPod");

        let is_main = BoolTarget::new_unsafe(verified_proof.public_inputs[PI_OFFSET_IS_MAIN]);
        builder.assert_bool(is_main);

        //
        // Verify that all main input pod proofs use verifier data from the public input VD
        // array. This requires merkle proofs.  introduction pods are not checked here because
        // their verifier_data_hash appears in their introduction statement.
        //
        verify_merkle_proof_existence_circuit(builder, vd_mt_proof);

        // connect the vd_mt_proof's root to the actual vds_root, to ensure that the mt proof
        // verifies against the vds_root
        builder.connect_hashes(main_pod.vds_root, vd_mt_proof.root);
        // connect vd_mt_proof's value with the verified_proof.verifier_data_hash only when is_main
        for i in 0..VALUE_SIZE {
            builder.conditional_assert_eq(
                is_main.target,
                verified_proof.verifier_data_hash.elements[i],
                vd_mt_proof.value.elements[i],
            )
        }

        //
        // Verify that VD array that input pod uses is the same we use now.
        //
        let verified_proof_vds_root = HashOutTarget::try_from(
            &verified_proof.public_inputs[PI_OFFSET_VDSROOT..PI_OFFSET_VDSROOT + HASH_SIZE],
        )
        .expect("4 elements");
        builder.connect_hashes(main_pod.vds_root, verified_proof_vds_root);

        let sts_root = HashOutTarget::try_from(
            &verified_proof.public_inputs
                [PI_OFFSET_STATEMENTS_ROOT..PI_OFFSET_STATEMENTS_ROOT + HASH_SIZE],
        )
        .expect("4 elements");
        if i == 0 {
            pod0_sts_root = Some(sts_root);
        }
        input_pod_table.push(InputPodEntryTarget {
            is_main,
            sts_root,
            vd_hash: verified_proof.verifier_data_hash,
        });

        measure_gates_end!(builder, measure_in_pod);
    }

    let empty = HashOutTarget {
        elements: builder.constant_value(EMPTY_VALUE).elements,
    };
    let mut sts_root = if let Some(pod0_sts_root) = pod0_sts_root {
        builder.select_flattenable(
            params,
            main_pod.extend_pod0_pub_statements,
            &pod0_sts_root,
            &empty,
        )
    } else {
        // Case where the params specify 0 max input pods
        empty
    };

    // Table of custom predicate batches with batch_id calculation
    let custom_predicate_table =
        build_custom_predicate_table_circuit(params, builder, &main_pod.custom_predicates)?;

    let aux_table = build_operation_aux_table_circuit(
        params,
        builder,
        &custom_predicate_table,
        &input_pod_table,
        &main_pod.aux_table_input,
    )?;

    let mut sts_roots_table = Vec::new();
    for sts_mt_proof in &main_pod.sts_mt_proofs {
        let measure = measure_gates_begin!(builder, "StsMtProof");
        // For correct usage the proof should be insertion, but update or deletion don't affect
        // soundness (we always check the transition value), so there's no need to enforce any
        // check.
        // We don't verify the key either, a prover could leave gaps in the array but that would
        // only break the verification (correctness).
        verify_merkle_state_transition_circuit(builder, sts_mt_proof);

        sts_roots_table.push(StsRootsEntry {
            old_root: sts_mt_proof.old_root,
            new_root: sts_mt_proof.new_root,
            st_hash: sts_mt_proof.op_value,
        });
        measure_gates_end!(builder, measure);
    }

    // Statement at index 0 is always None to be used for padding operation arguments in custom
    // predicate statements
    let st_none = StatementTarget::new_native(builder, params, NativePredicate::None, &[]);
    let statements = iter::once(&st_none).chain(main_pod.statements.iter());

    // Precompute flattened statements and their hashes once, then resolve operation args using
    // projected lookups. Reusing the flattened forms avoids re-flattening per op-arg lookup.
    let statement_flatteneds: Vec<Vec<Target>> =
        statements.clone().map(|st| st.flatten()).collect();
    let statement_hashes = statement_flatteneds
        .iter()
        .map(|flat| builder.hash_n_to_hash_no_pad::<PoseidonHash>(flat.clone()))
        .collect_vec();

    // 5. Verify statements
    for (j, (is_pub, pub_insert_idx, st, op)) in izip!(
        &main_pod.statements_is_pub,
        &main_pod.pub_insert_idx,
        &main_pod.statements,
        &main_pod.operations
    )
    .enumerate()
    {
        let i = j + 1; // Previous statement have a hardcoded None at index 0
        let prev_statement_flatteneds = &statement_flatteneds[..i];
        let prev_statement_hashes = &statement_hashes[..i];
        verify_operation_circuit(
            params,
            builder,
            st,
            op,
            prev_statement_flatteneds,
            prev_statement_hashes,
            &aux_table,
        )?;
        let measure = measure_gates_begin!(builder, "PubSt");
        let st_hash = statement_hashes[i];
        let sts_roots_entry = builder.vec_ref_small(params, &sts_roots_table, *pub_insert_idx);
        builder.conditional_assert_eq_flattenable(
            is_pub.target,
            &sts_roots_entry.old_root,
            &sts_root,
        );
        builder.conditional_assert_eq_flattenable(
            is_pub.target,
            &sts_roots_entry.st_hash,
            &ValueTarget::from(st_hash),
        );
        let new_sts_root =
            builder.select_flattenable(params, *is_pub, &sts_roots_entry.new_root, &sts_root);
        sts_root = new_sts_root;
        measure_gates_end!(builder, measure);
    }

    measure_gates_end!(builder, measure);
    Ok(sts_root)
}

#[derive(Clone, Serialize, Deserialize)]
pub struct MerkleProofsTarget {
    small: Vec<MerkleProofExistenceTarget>,
    medium: Vec<MerkleClaimAndProofTarget>,
}

impl MerkleProofsTarget {
    pub fn new_virtual(params: &Params, builder: &mut CircuitBuilder) -> Self {
        Self {
            small: (0..params.containers.state.max_small)
                .map(|_| {
                    MerkleProofExistenceTarget::new_virtual(
                        params.containers.max_depth_small,
                        builder,
                    )
                })
                .collect(),
            medium: (0..params.containers.state.max_medium)
                .map(|_| {
                    MerkleClaimAndProofTarget::new_virtual(
                        params.containers.max_depth_medium,
                        builder,
                    )
                })
                .collect(),
        }
    }
}

#[derive(Clone, Serialize, Deserialize)]
pub struct MerkleTransitionProofsTarget {
    small: Vec<MerkleTreeStateTransitionProofTarget>,
    medium: Vec<MerkleTreeStateTransitionProofTarget>,
}

impl MerkleTransitionProofsTarget {
    pub fn new_virtual(params: &Params, builder: &mut CircuitBuilder) -> Self {
        Self {
            small: (0..params.containers.transition.max_small)
                .map(|_| {
                    MerkleTreeStateTransitionProofTarget::new_virtual(
                        params.containers.max_depth_small,
                        builder,
                    )
                })
                .collect(),
            medium: (0..params.containers.transition.max_medium)
                .map(|_| {
                    MerkleTreeStateTransitionProofTarget::new_virtual(
                        params.containers.max_depth_medium,
                        builder,
                    )
                })
                .collect(),
        }
    }
}

#[derive(Clone, Serialize, Deserialize)]
struct AuxTableInputTargets {
    merkle_proofs: MerkleProofsTarget,
    merkle_transition_proofs: MerkleTransitionProofsTarget,
    open_input_statements: Vec<OpenInputStatementTarget>,
    public_key_of_sks: Vec<BigUInt320Target>,
    signed_bys: Vec<SignedByTarget>,
    custom_predicate_verifications: Vec<CustomPredicateVerifyEntryTarget>,
}

impl AuxTableInputTargets {
    fn set_container_mtp_targets(
        &self,
        params: &Params,
        pw: &mut PartialWitness<F>,
        merkle_proofs: &MerkleProofs,
        merkle_transition_proofs: &MerkleTransitionProofs,
    ) -> Result<()> {
        assert!(merkle_proofs.small.len() <= params.containers.state.max_small);
        for (i, mp) in merkle_proofs.small.iter().enumerate() {
            self.merkle_proofs.small[i].set_targets(pw, mp)?;
        }
        // Padding
        let pad_mp = MerkleClaimAndProof::pad();
        for i in merkle_proofs.small.len()..params.containers.state.max_small {
            self.merkle_proofs.small[i].set_targets(pw, &pad_mp)?;
        }

        assert!(merkle_proofs.medium.len() <= params.containers.state.max_medium);
        for (i, mp) in merkle_proofs.medium.iter().enumerate() {
            self.merkle_proofs.medium[i].set_targets(pw, mp)?;
        }
        // Padding
        let pad_mp = MerkleClaimAndProof::pad();
        for i in merkle_proofs.medium.len()..params.containers.state.max_medium {
            self.merkle_proofs.medium[i].set_targets(pw, &pad_mp)?;
        }

        assert!(merkle_transition_proofs.small.len() <= params.containers.transition.max_small);
        for (i, mtp) in merkle_transition_proofs.small.iter().enumerate() {
            self.merkle_transition_proofs.small[i].set_targets(pw, mtp)?;
        }
        // Padding
        let pad_mtp = MerkleTreeStateTransitionProof::pad();
        for i in merkle_transition_proofs.small.len()..params.containers.transition.max_small {
            self.merkle_transition_proofs.small[i].set_targets(pw, &pad_mtp)?;
        }

        assert!(merkle_transition_proofs.medium.len() <= params.containers.transition.max_medium);
        for (i, mtp) in merkle_transition_proofs.medium.iter().enumerate() {
            self.merkle_transition_proofs.medium[i].set_targets(pw, mtp)?;
        }
        // Padding
        let pad_mtp = MerkleTreeStateTransitionProof::pad();
        for i in merkle_transition_proofs.medium.len()..params.containers.transition.max_medium {
            self.merkle_transition_proofs.medium[i].set_targets(pw, &pad_mtp)?;
        }

        Ok(())
    }

    fn set_targets(
        &self,
        params: &Params,
        pw: &mut PartialWitness<F>,
        input: &AuxTableInput,
    ) -> Result<()> {
        self.set_container_mtp_targets(
            params,
            pw,
            &input.merkle_proofs,
            &input.merkle_transition_proofs,
        )?;

        assert!(input.open_input_statements.len() <= params.max_open_input_statements);
        for (i, data) in input.open_input_statements.iter().enumerate() {
            self.open_input_statements[i].set_targets(pw, data)?;
        }
        // Padding
        if let Some(pad_data) = &input.pad_open_input_statement {
            for i in input.open_input_statements.len()..params.max_open_input_statements {
                self.open_input_statements[i].set_targets(pw, pad_data)?;
            }
        }

        assert!(input.public_key_of_sks.len() <= params.max_public_key_of);
        for (i, sk) in input.public_key_of_sks.iter().enumerate() {
            pw.set_biguint320_target(&self.public_key_of_sks[i], &sk.0)?;
        }
        // Padding
        let pad_sk = BigUint::ZERO;
        for i in input.public_key_of_sks.len()..params.max_public_key_of {
            pw.set_biguint320_target(&self.public_key_of_sks[i], &pad_sk)?;
        }

        assert!(input.signed_bys.len() <= params.max_signed_by);
        for (i, signed_by) in input.signed_bys.iter().enumerate() {
            self.signed_bys[i].set_targets(pw, signed_by)?;
        }
        // Padding
        let pad_signed_by = SignedBy::dummy();
        for i in input.signed_bys.len()..params.max_signed_by {
            self.signed_bys[i].set_targets(pw, &pad_signed_by)?;
        }

        assert!(
            input.custom_predicate_verifications.len() <= params.max_custom_predicate_verifications
        );
        for (i, cpv) in input.custom_predicate_verifications.iter().enumerate() {
            self.custom_predicate_verifications[i].set_targets(pw, params, cpv)?;
        }
        // Padding.  Use the first input if it exists.  If it doesnt, all batches in this MainPod
        // are padding so refer to the first padding entry.
        let pad_cpb =
            CustomPredicateBatch::new("empty".to_string(), vec![CustomPredicate::empty()]);
        let empty_cpv = CustomPredicateVerification {
            custom_predicate_table_index: 0,
            custom_predicate: CustomPredicateRef::new(pad_cpb, 0),
            args: vec![],
            op_args: vec![],
        };
        let pad_cpv = input
            .custom_predicate_verifications
            .first()
            .unwrap_or(&empty_cpv);
        for i in
            input.custom_predicate_verifications.len()..params.max_custom_predicate_verifications
        {
            self.custom_predicate_verifications[i].set_targets(pw, params, pad_cpv)?;
        }

        Ok(())
    }
}

#[derive(Clone, Serialize, Deserialize)]
pub struct MainPodVerifyTarget {
    params: Params,
    vds_root: HashOutTarget,
    vd_mt_proofs: Vec<MerkleProofExistenceTarget>,
    extend_pod0_pub_statements: BoolTarget,
    statements_is_pub: Vec<BoolTarget>,
    pub_insert_idx: Vec<Target>,
    statements: Vec<StatementTarget>,
    operations: Vec<OperationTarget>,
    sts_mt_proofs: Vec<MerkleTreeStateTransitionProofTarget>,
    custom_predicates: Vec<CustomPredicateInBatchTarget>,
    aux_table_input: AuxTableInputTargets,
}

impl MainPodVerifyTarget {
    pub fn new_virtual(params: &Params, builder: &mut CircuitBuilder) -> Self {
        // Params validation
        if params.max_open_input_statements > 0 {
            assert!(params.max_input_pods > 0);
        }
        MainPodVerifyTarget {
            params: params.clone(),
            vds_root: builder.add_virtual_hash(),
            vd_mt_proofs: (0..params.max_input_pods)
                .map(|_| MerkleProofExistenceTarget::new_virtual(params.max_depth_mt_vds, builder))
                .collect(),
            extend_pod0_pub_statements: builder.add_virtual_bool_target_safe(),
            statements_is_pub: (0..params.max_statements)
                .map(|_| builder.add_virtual_bool_target_safe())
                .collect(),
            pub_insert_idx: (0..params.max_statements)
                .map(|_| builder.add_virtual_target())
                .collect(),
            statements: (0..params.max_statements)
                .map(|_| builder.add_virtual_statement(false))
                .collect(),
            operations: (0..params.max_statements)
                .map(|_| builder.add_virtual_operation(params))
                .collect(),
            sts_mt_proofs: (0..params.max_public_statements)
                .map(|_| {
                    MerkleTreeStateTransitionProofTarget::new_virtual(
                        BASE_PARAMS.max_depth_public_statements_mt,
                        builder,
                    )
                })
                .collect(),
            custom_predicates: (0..params.max_custom_predicates)
                .map(|_| CustomPredicateInBatchTarget::new_virtual(builder))
                .collect(),
            aux_table_input: AuxTableInputTargets {
                merkle_proofs: MerkleProofsTarget::new_virtual(params, builder),
                merkle_transition_proofs: MerkleTransitionProofsTarget::new_virtual(
                    params, builder,
                ),
                open_input_statements: (0..params.max_open_input_statements)
                    .map(|_| OpenInputStatementTarget::new_virtual(builder))
                    .collect(),
                public_key_of_sks: (0..params.max_public_key_of)
                    .map(|_| builder.add_virtual_biguint320_target())
                    .collect(),
                signed_bys: (0..params.max_signed_by)
                    .map(|_| SignedByTarget::new_virtual(builder))
                    .collect(),
                custom_predicate_verifications: (0..params.max_custom_predicate_verifications)
                    .map(|_| CustomPredicateVerifyEntryTarget::new_virtual(params, builder))
                    .collect(),
            },
        }
    }
}

pub struct CustomPredicateVerification {
    pub custom_predicate_table_index: usize,
    pub custom_predicate: CustomPredicateRef,
    pub args: Vec<Value>,
    pub op_args: Vec<mainpod::Statement>,
}

pub struct AuxTableInput {
    pub merkle_proofs: MerkleProofs,
    pub merkle_transition_proofs: MerkleTransitionProofs,
    pub open_input_statements: Vec<InputPodOpenStatement>,
    pub pad_open_input_statement: Option<InputPodOpenStatement>,
    pub public_key_of_sks: Vec<SecretKey>,
    pub signed_bys: Vec<SignedBy>,
    pub custom_predicate_verifications: Vec<CustomPredicateVerification>,
}

pub struct MainPodVerifyInput {
    pub vds_set: VDSet,
    /// field containing the `vd_mt_proofs` aside from the `vds_set`, because
    /// inside the MainPodVerifyTarget circuit, since it is the InnerCircuit for
    /// the RecursiveCircuit, we don't have access to the used verifier_datas.
    pub vd_mt_proofs: Vec<MerkleClaimAndProof>,
    pub extend_pod0_pub_statements: bool,
    pub statements_is_pub: Vec<bool>,
    pub sts_mt_proofs: Vec<MerkleTreeStateTransitionProof>,
    pub statements: Vec<mainpod::Statement>,
    pub operations: Vec<mainpod::Operation>,
    pub custom_predicates_with_mpt_proofs: Vec<(CustomPredicateRef, MerkleProof)>,
    pub aux_table_input: AuxTableInput,
}

impl InnerCircuit for MainPodVerifyTarget {
    type Input = MainPodVerifyInput;
    type Params = Params;

    fn build(
        builder: &mut CircuitBuilder,
        params: &Self::Params,
        verified_proofs: &[VerifiedProofTarget],
    ) -> Result<Self> {
        let main_pod = MainPodVerifyTarget::new_virtual(params, builder);
        let sts_root = verify_main_pod_circuit(builder, &main_pod, verified_proofs)?;
        builder.register_public_inputs(&sts_root.elements);
        builder.register_public_inputs(&main_pod.vds_root.elements);
        let is_main = builder._true();
        builder.register_public_input(is_main.target);
        Ok(main_pod)
    }

    /// assigns the values to the targets
    fn set_targets(&self, pw: &mut PartialWitness<F>, input: &Self::Input) -> Result<()> {
        let vds_root = input.vds_set.root();
        pw.set_target_arr(&self.vds_root.elements, &vds_root.0)?;

        pw.set_bool_target(
            self.extend_pod0_pub_statements,
            input.extend_pod0_pub_statements,
        )?;

        let input_pods_len = input.vd_mt_proofs.len();
        assert!(input_pods_len <= self.params.max_input_pods);
        for (i, vd_mt_proof) in input.vd_mt_proofs.iter().enumerate() {
            self.vd_mt_proofs[i].set_targets(pw, vd_mt_proof)?;
        }
        // Padding
        if input_pods_len != self.params.max_input_pods {
            let pad_mt_proof = input.vds_set.get_vds_proof_0();

            for i in input_pods_len..self.params.max_input_pods {
                self.vd_mt_proofs[i].set_targets(pw, &pad_mt_proof)?;
            }
        }

        for (i, sts_mt_proof) in input.sts_mt_proofs.iter().enumerate() {
            self.sts_mt_proofs[i].set_targets(pw, sts_mt_proof)?;
        }
        let pad_sts_mt_proof = MerkleTreeStateTransitionProof::pad();
        for i in input.sts_mt_proofs.len()..self.params.max_public_statements {
            self.sts_mt_proofs[i].set_targets(pw, &pad_sts_mt_proof)?;
        }

        // Skip statement and operation 0 which are a hardcoded None
        let statements_is_pub = &input.statements_is_pub[1..];
        let statements = &input.statements[1..];
        let operations = &input.operations[1..];
        let mut sts_mt_proofs_idx = 0;
        assert_eq!(statements.len(), self.params.max_statements);
        for (i, (is_pub, st, op)) in izip!(statements_is_pub, statements, operations).enumerate() {
            pw.set_bool_target(self.statements_is_pub[i], *is_pub)?;
            pw.set_target(
                self.pub_insert_idx[i],
                F::from_canonical_usize(sts_mt_proofs_idx),
            )?;
            if *is_pub {
                sts_mt_proofs_idx += 1;
            }
            self.statements[i].set_targets(pw, st)?;
            self.operations[i].set_targets(pw, &self.params, op)?;
        }

        assert!(input.custom_predicates_with_mpt_proofs.len() <= self.params.max_custom_predicates);
        for (i, (cp, mtp)) in input.custom_predicates_with_mpt_proofs.iter().enumerate() {
            self.custom_predicates[i].set_targets(pw, cp, mtp)?;
        }
        // Padding
        let pad_cpb =
            CustomPredicateBatch::new("empty".to_string(), vec![CustomPredicate::empty()]);
        let pad_cp = pad_cpb.predicate_ref_by_index(0).expect("index 0 exists");
        let (_, pad_mtp) = pad_cpb
            .mt()
            .prove(&Value::from(0i64).raw())
            .expect("exists");
        for i in input.custom_predicates_with_mpt_proofs.len()..self.params.max_custom_predicates {
            self.custom_predicates[i].set_targets(pw, &pad_cp, &pad_mtp)?;
        }

        self.aux_table_input
            .set_targets(&self.params, pw, &input.aux_table_input)?;

        Ok(())
    }
}
