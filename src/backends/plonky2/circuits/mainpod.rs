use std::{array, iter, sync::Arc};

use itertools::{izip, zip_eq, Itertools};
use num::{BigUint, One};
use plonky2::{
    field::types::Field,
    hash::{
        hash_types::HashOutTarget,
        poseidon::{PoseidonHash, PoseidonPermutation},
    },
    iop::{
        target::{BoolTarget, Target},
        witness::{PartialWitness, WitnessWrite},
    },
};
use plonky2_u32::gadgets::multiple_comparison::list_le_circuit;
use serde::{Deserialize, Serialize};

use crate::{
    backends::plonky2::{
        basetypes::{CircuitBuilder, VDSet},
        circuits::{
            common::{
                CircuitBuilderPod, CustomPredicateBatchTarget, CustomPredicateEntryTarget,
                CustomPredicateTarget, CustomPredicateVerifyEntryTarget,
                CustomPredicateVerifyQueryTarget, Flattenable, MerkleClaimTarget, OperationTarget,
                OperationTypeTarget, PredicateTarget, StatementArgTarget, StatementTarget,
                StatementTmplArgTarget, StatementTmplTarget, ValueTarget,
            },
            hash::{hash_from_state_circuit, precompute_hash_state},
            mux_table::{MuxTableTarget, TableEntryTarget},
            signedpod::{verify_signed_pod_circuit, SignedPodVerifyTarget},
        },
        emptypod::{cache_get_standard_empty_pod_circuit_data, EmptyPod},
        error::Result,
        mainpod::{self, pad_statement},
        primitives::{
            ec::{
                bits::{BigUInt320Target, CircuitBuilderBits},
                curve::{CircuitBuilderElliptic, Point, WitnessWriteCurve, GROUP_ORDER},
                schnorr::SecretKey,
            },
            merkletree::{
                verify_merkle_proof_circuit, MerkleClaimAndProof, MerkleClaimAndProofTarget,
            },
        },
        recursion::{InnerCircuit, VerifiedProofTarget},
        signedpod::SignedPod,
    },
    measure_gates_begin, measure_gates_end,
    middleware::{
        AnchoredKey, CustomPredicate, CustomPredicateBatch, CustomPredicateRef, NativeOperation,
        NativePredicate, Params, PodType, PredicatePrefix, Statement, StatementArg, ToFields,
        Value, ValueRef, F, HASH_SIZE, KEY_TYPE, SELF, VALUE_SIZE,
    },
};
//
// MainPod verification
//

/// Offset in public inputs where we store the pod id
pub const PI_OFFSET_ID: usize = 0;
/// Offset in public inputs where we store the verified data array root
pub const PI_OFFSET_VDSROOT: usize = 4;

pub const NUM_PUBLIC_INPUTS: usize = 8;

const MAX_VALUE_ARGS: usize = 3;

struct StatementArgCache {
    rhs: ValueTarget,
    lhs: StatementArgTarget,
    valid: BoolTarget,
}

struct StatementCache {
    equations: [StatementArgCache; MAX_VALUE_ARGS],
    first_n_equations_valid: [BoolTarget; MAX_VALUE_ARGS],
    op_args: Vec<StatementTarget>,
}

impl StatementCache {
    fn new(
        params: &Params,
        builder: &mut CircuitBuilder,
        op: &OperationTarget,
        st: &StatementTarget,
        prev_statements: &[StatementTarget],
    ) -> Self {
        let op_args = if prev_statements.is_empty() {
            (0..params.max_operation_args)
                .map(|_| StatementTarget::new_native(builder, params, NativePredicate::None, &[]))
                .collect_vec()
        } else {
            // `op.args` is a vector of arrays of length 1, so `.flatten()` is just
            // converting a length 1 array into a scalar.
            op.args
                .iter()
                .map(|i| builder.vec_ref(params, prev_statements, i))
                .collect::<Vec<_>>()
        };
        assert!(params.max_operation_args >= 3);
        assert!(params.max_statement_args >= 3);
        let equations = array::from_fn(|i| {
            let pred_is_none = op_args[i].has_native_type(builder, params, NativePredicate::None);
            let arg_is_value = builder.statement_arg_is_value(&st.args[i]);
            let is_literal = builder.and(pred_is_none, arg_is_value);
            let pred_is_eq = op_args[i].has_native_type(builder, params, NativePredicate::Equal);
            let ref_is_value = builder.statement_arg_is_value(&op_args[i].args[1]);
            let is_reference = builder.and(pred_is_eq, ref_is_value);
            let valid = builder.or(is_literal, is_reference);
            let rhs_literal = st.args[i].as_value();
            let rhs_reference = op_args[i].args[1].as_value();
            let rhs = builder.select_value(pred_is_none, rhs_literal, rhs_reference);
            let lhs = builder.select_statement_arg(pred_is_none, &st.args[i], &op_args[i].args[0]);
            StatementArgCache { rhs, lhs, valid }
        });
        let mut first_n_equations_valid = [equations[0].valid; MAX_VALUE_ARGS];
        for i in 1..MAX_VALUE_ARGS {
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
    /// If the operation argument is a statement of type `Equals`, then the value
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

/// Specialized implementation of `verify_operation_circuit` for operations that generate public
/// statement.  This only allows operations to be None, NewEntry or Copy and accounts for the fact
/// that public statements in the current implementation are always generated by copying private
/// statements (or NewEntry for the `KEY_TYPE` public entry).
fn verify_operation_public_statement_circuit(
    params: &Params,
    builder: &mut CircuitBuilder,
    st: &StatementTarget,
    op: &OperationTarget,
    prev_statements: &[StatementTarget],
    input_statements_offset: usize,
) -> Result<()> {
    let measure = measure_gates_begin!(builder, "OpVerify");

    // Verify that the operation `op` correctly generates the statement `st`.  The operation
    // can reference any of the `prev_statements`.
    // TODO: Clean this up.
    let measure_resolve_op_args = measure_gates_begin!(builder, "ResolveOpArgs");
    let cache = StatementCache::new(params, builder, op, st, prev_statements);
    measure_gates_end!(builder, measure_resolve_op_args);

    let op_checks = vec![
        verify_none_circuit(params, builder, st, &op.op_type),
        verify_new_entry_circuit(
            params,
            builder,
            st,
            &op.op_type,
            prev_statements,
            input_statements_offset,
        ),
        verify_copy_circuit(builder, st, &op.op_type, &cache.op_args),
    ];

    let ok = builder.any(op_checks);
    builder.assert_one(ok.target);

    measure_gates_end!(builder, measure);
    Ok(())
}

enum OperationAuxTableTag {
    None = 0,
    MerkleProof = 1,
    PublicKeyOf = 2,
    CustomPredVerify = 3,
}

fn max_operation_aux_entry_len(params: &Params) -> usize {
    [
        (params.max_merkle_proofs_containers > 0).then(|| MerkleClaimTarget::size(params)),
        (params.max_public_key_of > 0).then(|| KeyPairTarget::size(params)),
        (params.max_custom_predicate_verifications > 0)
            .then(|| CustomPredicateVerifyQueryTarget::size(params)),
    ]
    .into_iter()
    .flatten()
    .max()
    .unwrap_or(0)
}

#[derive(Copy, Clone)]
struct KeyPairTarget {
    pk_hash: HashOutTarget,
    sk_hash: HashOutTarget,
}

impl Flattenable for KeyPairTarget {
    fn flatten(&self) -> Vec<Target> {
        self.pk_hash
            .elements
            .into_iter()
            .chain(self.sk_hash.elements)
            .collect()
    }
    fn from_flattened(params: &Params, vs: &[Target]) -> Self {
        assert_eq!(vs.len(), Self::size(params));
        Self {
            pk_hash: HashOutTarget::try_from(&vs[..4]).expect("len = 4"),
            sk_hash: HashOutTarget::try_from(&vs[4..]).expect("len = 4"),
        }
    }
    fn size(_params: &Params) -> usize {
        8
    }
}

fn build_operation_aux_table_circuit(
    params: &Params,
    builder: &mut CircuitBuilder,
    merkle_proofs: &[MerkleClaimAndProofTarget],
    public_key_of_sks: &[BigUInt320Target],
    custom_predicate_verifications: &[CustomPredicateVerifyEntryTarget],
    custom_predicate_table: &[HashOutTarget],
) -> Result<MuxTableTarget> {
    let measure = measure_gates_begin!(builder, "BuildOpAuxTbl");
    assert_eq!(
        params.max_custom_predicate_verifications,
        custom_predicate_verifications.len()
    );
    assert_eq!(params.max_merkle_proofs_containers, merkle_proofs.len());
    let max_entry_len = max_operation_aux_entry_len(params);
    let mut table = MuxTableTarget::new(params, max_entry_len);

    // None
    table.push_flattened(builder, OperationAuxTableTag::None as u32, &[]);

    // MerkleProofs: verify container merkle proofs (inclusion/non-inclusion)
    for merkle_proof in merkle_proofs {
        verify_merkle_proof_circuit(builder, merkle_proof);
        let entry = MerkleClaimTarget::from(merkle_proof.clone());

        table.push(builder, OperationAuxTableTag::MerkleProof as u32, &entry);
    }

    // PublicKeyOf: verify the derivation from a Schnorr secret key to public key
    for sk in public_key_of_sks {
        let measure = measure_gates_begin!(builder, "PublicKeyOf");
        let invgenerator = builder.constant_point(Point::generator().inverse());
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
        let pk = builder.multiply_point(&sk.bits, &invgenerator);
        let sk_hash = builder.hash_n_to_hash_no_pad::<PoseidonHash>(sk.limbs.to_vec());
        let pk_hash = builder.hash_n_to_hash_no_pad::<PoseidonHash>(
            pk.x.components.into_iter().chain(pk.u.components).collect(),
        );

        let entry = KeyPairTarget { pk_hash, sk_hash };

        table.push(builder, OperationAuxTableTag::PublicKeyOf as u32, &entry);
        measure_gates_end!(builder, measure);
    }

    // CustomPredVerify: verify custom predicate statements verification against operations
    for entry in custom_predicate_verifications {
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

    measure_gates_end!(builder, measure);
    Ok(table)
}

#[allow(clippy::too_many_arguments)]
fn verify_operation_circuit(
    params: &Params,
    builder: &mut CircuitBuilder,
    st: &StatementTarget,
    op: &OperationTarget,
    prev_statements: &[StatementTarget],
    input_statements_offset: usize,
    aux_table: &MuxTableTarget,
) -> Result<()> {
    let measure = measure_gates_begin!(builder, "OpVerify");
    let _true = builder._true();
    let _false = builder._false();

    // Verify that the operation `op` correctly generates the statement `st`.  The operation
    // can reference any of the `prev_statements`.
    // TODO: Clean this up.
    let measure_resolve_op_args = measure_gates_begin!(builder, "ResolveOpArgs");
    let cache = StatementCache::new(params, builder, op, st, prev_statements);
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
    op_checks.extend_from_slice(&[
        verify_none_circuit(params, builder, st, &op.op_type),
        verify_new_entry_circuit(
            params,
            builder,
            st,
            &op.op_type,
            prev_statements,
            input_statements_offset,
        ),
    ]);
    // Skip these if there are no resolved op args
    if !cache.op_args.is_empty() {
        op_checks.extend_from_slice(&[
            verify_copy_circuit(builder, st, &op.op_type, &cache.op_args),
            verify_eq_neq_from_entries_circuit(params, builder, st, &op.op_type, &cache),
            verify_lt_lteq_from_entries_circuit(params, builder, st, &op.op_type, &cache),
            verify_transitive_eq_circuit(params, builder, st, &op.op_type, &cache.op_args),
            verify_lt_to_neq_circuit(params, builder, st, &op.op_type, &cache.op_args),
            verify_hash_of_circuit(params, builder, st, &op.op_type, &cache),
            verify_sum_of_circuit(params, builder, st, &op.op_type, &cache),
            verify_product_of_circuit(params, builder, st, &op.op_type, &cache),
            verify_max_of_circuit(params, builder, st, &op.op_type, &cache),
        ]);
    }
    // Skip these if there are no resolved aux entries
    if let Some(resolved_aux) = resolved_aux {
        if params.max_merkle_proofs_containers > 0 {
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
        if params.max_custom_predicate_verifications > 0 {
            op_checks.push(verify_custom_circuit(
                builder,
                st,
                &op.op_type,
                &resolved_aux,
                &cache.op_args,
            ));
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
    cache: &StatementCache,
) -> BoolTarget {
    let measure = measure_gates_begin!(builder, "OpContainsFromEntries");
    let (aux_tag_ok, resolved_merkle_claim) =
        aux.as_type::<MerkleClaimTarget>(builder, OperationAuxTableTag::MerkleProof as u32);
    let op_code_ok = op_type.has_native(builder, NativeOperation::ContainsFromEntries);

    let (arg_types_ok, [merkle_root_value, key_value, value_value]) =
        cache.first_n_args_as_values();

    // Check Merkle proof (verified elsewhere) against op args.
    let merkle_proof_checks = [
        /* The supplied Merkle proof must be enabled. */
        resolved_merkle_claim.enabled,
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
    cache: &StatementCache,
) -> BoolTarget {
    let measure = measure_gates_begin!(builder, "OpNotContainsFromEntries");
    let (aux_tag_ok, resolved_merkle_claim) =
        aux.as_type::<MerkleClaimTarget>(builder, OperationAuxTableTag::MerkleProof as u32);
    let op_code_ok = op_type.has_native(builder, NativeOperation::NotContainsFromEntries);

    let (arg_types_ok, [merkle_root_value, key_value]) = cache.first_n_args_as_values();

    // Check Merkle proof (verified elsewhere) against op args.
    let merkle_proof_checks = [
        /* The supplied Merkle proof must be enabled. */
        resolved_merkle_claim.enabled,
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

/// Carries out the checks necessary for EqualFromEntries and
/// NotEqualFromEntries.
fn verify_eq_neq_from_entries_circuit(
    params: &Params,
    builder: &mut CircuitBuilder,
    st: &StatementTarget,
    op_type: &OperationTypeTarget,
    cache: &StatementCache,
) -> BoolTarget {
    let measure = measure_gates_begin!(builder, "OpEqNeqFromEntries");
    let eq_op_st_code_ok = {
        let op_code_ok = op_type.has_native(builder, NativeOperation::EqualFromEntries);
        let st_code_ok = st.has_native_type(builder, params, NativePredicate::Equal);
        builder.and(op_code_ok, st_code_ok)
    };
    let neq_op_st_code_ok = {
        let op_code_ok = op_type.has_native(builder, NativeOperation::NotEqualFromEntries);
        let st_code_ok = st.has_native_type(builder, params, NativePredicate::NotEqual);
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
        .take(params.max_statement_args)
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
    params: &Params,
    builder: &mut CircuitBuilder,
    st: &StatementTarget,
    op_type: &OperationTypeTarget,
    cache: &StatementCache,
) -> BoolTarget {
    let measure = measure_gates_begin!(builder, "OpLtLteqFromEntries");
    let zero = ValueTarget::zero(builder);
    let one = ValueTarget::one(builder);

    let lt_op_st_code_ok = {
        let op_code_ok = op_type.has_native(builder, NativeOperation::LtFromEntries);
        let st_code_ok = st.has_native_type(builder, params, NativePredicate::Lt);
        builder.and(op_code_ok, st_code_ok)
    };
    let lteq_op_st_code_ok = {
        let op_code_ok = op_type.has_native(builder, NativeOperation::LtEqFromEntries);
        let st_code_ok = st.has_native_type(builder, params, NativePredicate::LtEq);
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
        .take(params.max_statement_args)
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
    cache: &StatementCache,
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
    cache: &StatementCache,
) -> BoolTarget {
    let measure = measure_gates_begin!(builder, "OpPublicKeyOf");
    let (aux_tag_ok, resolved_key_pair) =
        aux.as_type::<KeyPairTarget>(builder, OperationAuxTableTag::PublicKeyOf as u32);

    let op_code_ok = op_type.has_native(builder, NativeOperation::PublicKeyOf);
    let (arg_types_ok, [arg1_value, arg2_value]) = cache.first_n_args_as_values();
    // inputting public_key, secret_key
    let public_key_hash = arg1_value;
    let secret_key_hash = arg2_value;

    let skey_hash_ok = builder.is_equal_slice(
        &secret_key_hash.elements,
        &resolved_key_pair.sk_hash.elements,
    );
    let pkey_hash_ok = builder.is_equal_slice(
        &public_key_hash.elements,
        &resolved_key_pair.pk_hash.elements,
    );

    let arg1_expected = cache.equations[0].lhs.clone();
    let arg2_expected = cache.equations[1].lhs.clone();
    let expected_statement = StatementTarget::new_native(
        builder,
        params,
        NativePredicate::PublicKeyOf,
        &[arg1_expected, arg2_expected],
    );
    let st_ok = builder.is_equal_flattenable(st, &expected_statement);

    let ok = builder.all([
        op_code_ok,
        aux_tag_ok,
        arg_types_ok,
        pkey_hash_ok,
        skey_hash_ok,
        st_ok,
    ]);
    measure_gates_end!(builder, measure);
    ok
}

fn verify_sum_of_circuit(
    params: &Params,
    builder: &mut CircuitBuilder,
    st: &StatementTarget,
    op_type: &OperationTypeTarget,
    cache: &StatementCache,
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
    cache: &StatementCache,
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
    cache: &StatementCache,
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

fn verify_transitive_eq_circuit(
    params: &Params,
    builder: &mut CircuitBuilder,
    st: &StatementTarget,
    op_type: &OperationTypeTarget,
    resolved_op_args: &[StatementTarget],
) -> BoolTarget {
    let measure = measure_gates_begin!(builder, "OpTransitiveEq");
    let op_code_ok = op_type.has_native(builder, NativeOperation::TransitiveEqualFromStatements);

    let arg1_type_ok = resolved_op_args[0].has_native_type(builder, params, NativePredicate::Equal);
    let arg2_type_ok = resolved_op_args[1].has_native_type(builder, params, NativePredicate::Equal);
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

fn verify_new_entry_circuit(
    params: &Params,
    builder: &mut CircuitBuilder,
    st: &StatementTarget,
    op_type: &OperationTypeTarget,
    prev_statements: &[StatementTarget],
    input_statements_offset: usize,
) -> BoolTarget {
    let measure = measure_gates_begin!(builder, "OpNewEntry");
    let op_code_ok = op_type.has_native(builder, NativeOperation::NewEntry);
    let st_code_ok = st.has_native_type(builder, params, NativePredicate::Equal);

    let expected_arg_prefix = builder.constants(
        &StatementArg::Key(AnchoredKey::from((SELF, ""))).to_fields(params)[..VALUE_SIZE],
    );
    let arg_prefix_ok =
        builder.is_equal_slice(&st.args[0].elements[..VALUE_SIZE], &expected_arg_prefix);

    let input_statements = &prev_statements[input_statements_offset..];
    let individual_dupe_checks = input_statements
        .iter()
        .map(|ps| builder.is_equal_slice(&st.args[0].elements, &ps.args[0].elements))
        .collect::<Vec<_>>();
    let dupe_check = builder.any(individual_dupe_checks);
    let no_dupes_ok = builder.not(dupe_check);

    let ok = builder.all([op_code_ok, st_code_ok, arg_prefix_ok, no_dupes_ok]);
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

    let arg_type_ok = resolved_op_args[0].has_native_type(builder, params, NativePredicate::Lt);

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

fn verify_copy_circuit(
    builder: &mut CircuitBuilder,
    st: &StatementTarget,
    op_type: &OperationTypeTarget,
    resolved_op_args: &[StatementTarget],
) -> BoolTarget {
    let measure = measure_gates_begin!(builder, "OpCopy");
    let op_code_ok = op_type.has_native(builder, NativeOperation::CopyStatement);

    let expected_statement = &resolved_op_args[0];
    let st_ok = builder.is_equal_flattenable(st, expected_statement);

    let ok = builder.all([op_code_ok, st_ok]);
    measure_gates_end!(builder, measure);
    ok
}

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
    let (is_ak, ak_id_wc_index, ak_key_lit_or_wc) = st_tmpl_arg.as_anchored_key(builder);
    let (is_wc_literal, wc_index) = st_tmpl_arg.as_wildcard_literal(builder);

    let ((_is_ak_key_lit, ak_key_lit), (is_ak_key_wc, ak_key_wc_index)) =
        ak_key_lit_or_wc.cases(builder);

    // optimization: ak_id_wc_index and wc_index use the same signals, so we only need to do one
    // random access to resolve both of them
    assert_eq!(ak_id_wc_index, wc_index);
    // optimization: the wildcard indices have an offset of +1.  This allows us to set a fixed
    // SELF in args[0] to resolve SelfOrWildcard::SELF encoded as a wildcard at index 0.
    let value_self = ValueTarget::from_slice(&builder.constants(&SELF.0 .0));
    let args = iter::once(value_self)
        .chain(args.iter().cloned())
        .collect_vec();
    // If the index is not used, use a 0 instead to still pass the range constraints from
    // vec_ref
    let first_index = ak_id_wc_index;
    let is_first_index_valid = builder.or(is_ak, is_wc_literal);
    let first_index = builder.select(is_first_index_valid, first_index, zero);
    let resolved_ak_id = builder.vec_ref_small(params, &args, first_index);
    let resolved_wc = resolved_ak_id;

    // If the index is not used, use a 0 instead to still pass the range constraints from
    // vec_ref
    let second_index = ak_key_wc_index;
    let is_second_index_valid = builder.and(is_ak, is_ak_key_wc);
    let second_index = builder.select(is_second_index_valid, second_index, zero);
    let resolved_ak_key = builder.vec_ref_small(params, &args, second_index);

    let ak_key = ak_key_lit; // is_ak_key_lit
    let ak_key = builder.select_flattenable(params, is_ak_key_wc, &resolved_ak_key, &ak_key);

    let first = ValueTarget::zero(builder); // is_none
    let first = builder.select_flattenable(params, is_literal, &value_literal, &first);
    let first = builder.select_flattenable(params, is_ak, &resolved_ak_id, &first);
    let first = builder.select_flattenable(params, is_wc_literal, &resolved_wc, &first);

    let second = ValueTarget::zero(builder); // is_none or is_literal or is_wc_literal
    let second = builder.select_flattenable(params, is_ak, &ak_key, &second);

    StatementArgTarget::new(first, second)
}

fn make_statement_from_template_circuit(
    params: &Params,
    builder: &mut CircuitBuilder,
    st_tmpl: &StatementTmplTarget,
    args: &[ValueTarget],
) -> StatementTarget {
    let measure = measure_gates_begin!(builder, "StArgFromTmpl");
    let args = st_tmpl
        .args
        .iter()
        .map(|st_tmpl_arg| {
            make_statement_arg_from_template_circuit(params, builder, st_tmpl_arg, args)
        })
        .collect();
    measure_gates_end!(builder, measure);
    StatementTarget {
        predicate: st_tmpl.pred.clone(),
        args,
    }
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
    assert_eq!(params.max_operation_args, op_args.len());
    assert_eq!(params.max_custom_predicate_wildcards, args.len());

    let (batch_id, index) = (custom_predicate.id, custom_predicate.index);
    let op_type = OperationTypeTarget::new_custom(builder, batch_id, index);

    // Build the statement
    let st_predicate = PredicateTarget::new_custom(builder, batch_id, index);
    let arg_none = ValueTarget::zero(builder);
    let lt_mask = builder.lt_mask(
        params.max_statement_args,
        custom_predicate.predicate.args_len,
    );
    let st_args = (0..params.max_statement_args)
        .map(|i| {
            let v = builder.select_flattenable(params, lt_mask[i], &args[i], &arg_none);
            StatementArgTarget::wildcard_literal(builder, &v)
        })
        .collect();
    let statement = StatementTarget {
        predicate: st_predicate,
        args: st_args,
    };

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
    assert!(params.max_custom_predicate_arity <= params.max_operation_args);

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
    Ok((statement, op_type))
}

/// Replace references to SELF by `self_id` in a statement.
fn normalize_statement_circuit(
    params: &Params,
    builder: &mut CircuitBuilder,
    statement: &StatementTarget,
    self_id: &ValueTarget,
) -> StatementTarget {
    let self_value = builder.constant_value(SELF.0.into());
    let args = statement
        .args
        .iter()
        .map(|arg| {
            let first = ValueTarget::from_slice(&arg.elements[..VALUE_SIZE]);
            let second = ValueTarget::from_slice(&arg.elements[VALUE_SIZE..]);
            let is_self = builder.is_equal_flattenable(&self_value, &first);
            let first_normalized = builder.select_flattenable(params, is_self, self_id, &first);
            StatementArgTarget::new(first_normalized, second)
        })
        .collect_vec();
    StatementTarget {
        predicate: statement.predicate.clone(),
        args,
    }
}

/// `params.num_public_statements_id` is the total number of statements that will be hashed.
/// The id is calculated with front-padded none-statements and then the input statements
/// reversed.  The part of the hash from the front-padded none-statements is precomputed.
pub fn calculate_id_circuit(
    params: &Params,
    builder: &mut CircuitBuilder,
    // These statements will be padded to reach `num_statements`
    statements: &[StatementTarget],
) -> HashOutTarget {
    assert!(statements.len() <= params.num_public_statements_id);
    let measure = measure_gates_begin!(builder, "CalculateId");
    let statements_rev_flattened = statements.iter().rev().flat_map(|s| s.flatten());
    let mut none_st = mainpod::Statement::from(Statement::None);
    pad_statement(params, &mut none_st);
    let front_pad_elts = iter::repeat(&none_st)
        .take(params.num_public_statements_id - statements.len())
        .flat_map(|s| s.to_fields(params))
        .collect_vec();
    let (perm, front_pad_elts_rem) =
        precompute_hash_state::<F, PoseidonPermutation<F>>(&front_pad_elts);

    // Precompute the Poseidon state for the initial padding chunks
    let inputs = front_pad_elts_rem
        .iter()
        .map(|v| builder.constant(*v))
        .chain(statements_rev_flattened)
        .collect_vec();
    let id =
        hash_from_state_circuit::<PoseidonHash, PoseidonPermutation<F>>(builder, perm, &inputs);

    measure_gates_end!(builder, measure);
    id
}

// Replace predicates of batch-self with the corresponding global custom predicate batch_id and
// index
fn normalize_st_tmpl_circuit(
    params: &Params,
    builder: &mut CircuitBuilder,
    st_tmpl: &StatementTmplTarget,
    id: HashOutTarget,
) -> StatementTmplTarget {
    let prefix_batch_self = builder.constant(F::from(PredicatePrefix::BatchSelf));
    let is_batch_self = builder.is_equal(st_tmpl.pred.elements[0], prefix_batch_self);
    let pred_index = st_tmpl.pred.elements[1];
    let custom_pred = PredicateTarget::new_custom(builder, id, pred_index);
    let pred = builder.select_flattenable(params, is_batch_self, &custom_pred, &st_tmpl.pred);
    StatementTmplTarget {
        pred,
        args: st_tmpl.args.clone(),
    }
}

/// Build a table of [batch_id, custom_predicate_index, custom_predicate] with queryable part as
/// hash([batch_id, custom_predicate_index, custom_predicate]).  While building the table we
/// calculate the id of each batch.  Return the hash of each table entry.
fn build_custom_predicate_table_circuit(
    params: &Params,
    builder: &mut CircuitBuilder,
    custom_predicate_batches: &[CustomPredicateBatchTarget],
) -> Result<Vec<HashOutTarget>> {
    let measure = measure_gates_begin!(builder, "BuildCustomPredTbl");
    let mut custom_predicate_table =
        Vec::with_capacity(params.max_custom_predicate_batches * params.max_custom_batch_size);
    for cpb in custom_predicate_batches {
        let id = cpb.id(builder); // constrain the id
        for (index, cp) in cpb.predicates.iter().enumerate() {
            let statements = cp
                .statements
                .iter()
                .map(|st_tmpl| normalize_st_tmpl_circuit(params, builder, st_tmpl, id))
                .collect_vec();
            let cp = CustomPredicateTarget {
                conjunction: cp.conjunction,
                statements,
                args_len: cp.args_len,
            };
            let entry = CustomPredicateEntryTarget {
                id,                                                      // output
                index: builder.constant(F::from_canonical_usize(index)), // constant
                predicate: cp.clone(),                                   // input
            };

            let in_query_hash = entry.hash(builder);
            custom_predicate_table.push(in_query_hash);
        }
    }
    measure_gates_end!(builder, measure);
    Ok(custom_predicate_table)
}

fn verify_main_pod_circuit(
    builder: &mut CircuitBuilder,
    main_pod: &MainPodVerifyTarget,
    verified_proofs: &[VerifiedProofTarget],
) -> Result<HashOutTarget> {
    let params = &main_pod.params;
    assert_eq!(params.max_input_recursive_pods, verified_proofs.len());

    let measure = measure_gates_begin!(builder, "MainPodVerify");
    // 1a. Verify all input signed pods
    for signed_pod in &main_pod.signed_pods {
        verify_signed_pod_circuit(builder, signed_pod)?;
        builder.assert_one(signed_pod.signature.enabled.target);
    }

    // Build the statement array
    let mut statements = Vec::new();
    // Statement at index 0 is always None to be used for padding operation arguments in custom
    // predicate statements
    let st_none = StatementTarget::new_native(builder, params, NativePredicate::None, &[]);
    statements.push(st_none);
    for signed_pod in &main_pod.signed_pods {
        statements.extend_from_slice(signed_pod.pub_statements(builder, false).as_slice());
    }
    debug_assert_eq!(
        statements.len(),
        1 + params.max_input_signed_pods * params.max_signed_pod_values
    );

    // 1b. Verify all input recursive pods
    for (verified_proof, vd_mt_proof, input_pod_self_statements) in izip!(
        verified_proofs,
        &main_pod.vd_mt_proofs,
        &main_pod.input_pods_self_statements
    ) {
        let measure_in_pod = measure_gates_begin!(builder, "VerifyInPod");

        //
        // Verify id from the statements
        //
        let expected_id = HashOutTarget::try_from(
            &verified_proof.public_inputs[PI_OFFSET_ID..PI_OFFSET_ID + HASH_SIZE],
        )
        .expect("4 elements");
        let id_value = ValueTarget {
            elements: expected_id.elements,
        };

        for self_st in input_pod_self_statements {
            let normalized_st = normalize_statement_circuit(params, builder, self_st, &id_value);
            statements.push(normalized_st);
        }
        let id = calculate_id_circuit(params, builder, input_pod_self_statements);
        builder.connect_hashes(expected_id, id);

        //
        // Verify that all input pod proofs use verifier data from the public input VD
        // array. This requires merkle proofs
        //

        verify_merkle_proof_circuit(builder, vd_mt_proof);

        // ensure that mt_proof is enabled
        let true_targ = builder._true();
        builder.connect(vd_mt_proof.enabled.target, true_targ.target);
        // connect the vd_mt_proof's root to the actual vds_root, to ensure that the mt proof
        // verifies against the vds_root
        builder.connect_hashes(main_pod.vds_root, vd_mt_proof.root);
        // connect vd_mt_proof's value with the verified_proof.verifier_data_hash
        builder.connect_hashes(
            verified_proof.verifier_data_hash,
            HashOutTarget::from_vec(vd_mt_proof.value.elements.to_vec()),
        );

        //
        // Verify that VD array that input pod uses is the same we use now.
        //
        let verified_proof_vds_root = HashOutTarget::try_from(
            &verified_proof.public_inputs[PI_OFFSET_VDSROOT..PI_OFFSET_VDSROOT + HASH_SIZE],
        )
        .expect("4 elements");
        builder.connect_hashes(main_pod.vds_root, verified_proof_vds_root);

        measure_gates_end!(builder, measure_in_pod);
    }

    let input_statements_offset = statements.len();
    // Add the input (private and public) statements
    for statement in &main_pod.input_statements {
        statements.push(statement.clone());
    }
    let public_statements_offset = main_pod.input_statements.len() - params.max_public_statements;
    let pub_statements = &main_pod.input_statements[public_statements_offset..];

    // Table of custom predicate batches with batch_id calculation
    let custom_predicate_table =
        build_custom_predicate_table_circuit(params, builder, &main_pod.custom_predicate_batches)?;

    let aux_table = build_operation_aux_table_circuit(
        params,
        builder,
        &main_pod.merkle_proofs,
        &main_pod.public_key_of_sks,
        &main_pod.custom_predicate_verifications,
        &custom_predicate_table,
    )?;

    // 2. Calculate the Pod Id from the public statements
    let id = calculate_id_circuit(params, builder, pub_statements);

    // 4. Verify type
    let type_statement = &pub_statements[0];
    // TODO: Store this hash in a global static with lazy init so that we don't have to
    // compute it every time.
    let expected_type_statement = StatementTarget::from_flattened(
        params,
        &builder.constants(
            &Statement::equal(
                ValueRef::Key(AnchoredKey::from((SELF, KEY_TYPE))),
                ValueRef::Literal(Value::from(PodType::Main)),
            )
            .to_fields(params),
        ),
    );
    builder.connect_flattenable(type_statement, &expected_type_statement);

    // 3. check that all `input_statements` of type `ValueOf` with origin=SELF have unique keys
    // (no duplicates).  We do this in the verification of NewEntry operation.
    // 5. Verify input statements
    for (i, (st, op)) in izip!(&main_pod.input_statements, &main_pod.operations).enumerate() {
        let prev_statements = &statements[..input_statements_offset + i];
        if i < public_statements_offset {
            verify_operation_circuit(
                params,
                builder,
                st,
                op,
                prev_statements,
                input_statements_offset,
                &aux_table,
            )?;
        } else {
            verify_operation_public_statement_circuit(
                params,
                builder,
                st,
                op,
                prev_statements,
                input_statements_offset,
            )?;
        }
    }

    measure_gates_end!(builder, measure);
    Ok(id)
}

#[derive(Clone, Serialize, Deserialize)]
pub struct MainPodVerifyTarget {
    params: Params,
    vds_root: HashOutTarget,
    vd_mt_proofs: Vec<MerkleClaimAndProofTarget>,
    signed_pods: Vec<SignedPodVerifyTarget>,
    input_pods_self_statements: Vec<Vec<StatementTarget>>,
    // The KEY_TYPE statement must be the first public one
    input_statements: Vec<StatementTarget>,
    operations: Vec<OperationTarget>,
    merkle_proofs: Vec<MerkleClaimAndProofTarget>,
    public_key_of_sks: Vec<BigUInt320Target>,
    custom_predicate_batches: Vec<CustomPredicateBatchTarget>,
    custom_predicate_verifications: Vec<CustomPredicateVerifyEntryTarget>,
}

impl MainPodVerifyTarget {
    pub fn new_virtual(params: &Params, builder: &mut CircuitBuilder) -> Self {
        MainPodVerifyTarget {
            params: params.clone(),
            vds_root: builder.add_virtual_hash(),
            vd_mt_proofs: (0..params.max_input_recursive_pods)
                .map(|_| MerkleClaimAndProofTarget::new_virtual(params.max_depth_mt_vds, builder))
                .collect(),
            signed_pods: (0..params.max_input_signed_pods)
                .map(|_| SignedPodVerifyTarget::new_virtual(params, builder))
                .collect(),
            input_pods_self_statements: (0..params.max_input_recursive_pods)
                .map(|_| {
                    (0..params.max_input_pods_public_statements)
                        .map(|_| builder.add_virtual_statement(params))
                        .collect_vec()
                })
                .collect(),
            input_statements: (0..params.max_statements)
                .map(|_| builder.add_virtual_statement(params))
                .collect(),
            operations: (0..params.max_statements)
                .map(|_| builder.add_virtual_operation(params))
                .collect(),
            merkle_proofs: (0..params.max_merkle_proofs_containers)
                .map(|_| {
                    MerkleClaimAndProofTarget::new_virtual(params.max_depth_mt_containers, builder)
                })
                .collect(),
            public_key_of_sks: (0..params.max_public_key_of)
                .map(|_| builder.add_virtual_biguint320_target())
                .collect(),
            custom_predicate_batches: (0..params.max_custom_predicate_batches)
                .map(|_| builder.add_virtual_custom_predicate_batch(params))
                .collect(),
            custom_predicate_verifications: (0..params.max_custom_predicate_verifications)
                .map(|_| CustomPredicateVerifyEntryTarget::new_virtual(params, builder))
                .collect(),
        }
    }
}

pub struct CustomPredicateVerification {
    pub custom_predicate_table_index: usize,
    pub custom_predicate: CustomPredicateRef,
    pub args: Vec<Value>,
    pub op_args: Vec<mainpod::Statement>,
}

pub struct MainPodVerifyInput {
    pub vds_set: VDSet,
    // field containing the `vd_mt_proofs` aside from the `vds_set`, because
    // inide the MainPodVerifyTarget circuit, since it is the InnerCircuit for
    // the RecursiveCircuit, we don't have access to the used verifier_datas.
    pub vd_mt_proofs: Vec<MerkleClaimAndProof>,
    pub signed_pods: Vec<SignedPod>,
    pub recursive_pods_pub_self_statements: Vec<Vec<Statement>>,
    pub statements: Vec<mainpod::Statement>,
    pub operations: Vec<mainpod::Operation>,
    pub merkle_proofs: Vec<MerkleClaimAndProof>,
    pub public_key_of_sks: Vec<SecretKey>,
    pub custom_predicate_batches: Vec<Arc<CustomPredicateBatch>>,
    pub custom_predicate_verifications: Vec<CustomPredicateVerification>,
}

fn set_targets_input_pods_self_statements(
    pw: &mut PartialWitness<F>,
    params: &Params,
    statements_target: &[StatementTarget],
    statements: &[Statement],
) -> Result<()> {
    assert_eq!(
        statements_target.len(),
        params.max_input_pods_public_statements
    );
    assert!(statements.len() <= params.num_public_statements_id);

    for (i, statement) in statements.iter().enumerate() {
        statements_target[i].set_targets(pw, params, &statement.clone().into())?;
    }
    // Padding
    let mut none_st = mainpod::Statement::from(Statement::None);
    pad_statement(params, &mut none_st);
    for statement_target in statements_target.iter().skip(statements.len()) {
        statement_target.set_targets(pw, params, &none_st)?;
    }
    Ok(())
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
        let id = verify_main_pod_circuit(builder, &main_pod, verified_proofs)?;
        builder.register_public_inputs(&id.elements);
        builder.register_public_inputs(&main_pod.vds_root.elements);
        Ok(main_pod)
    }

    /// assigns the values to the targets
    fn set_targets(&self, pw: &mut PartialWitness<F>, input: &Self::Input) -> Result<()> {
        let vds_root = input.vds_set.root();
        pw.set_target_arr(&self.vds_root.elements, &vds_root.0)?;

        for (i, vd_mt_proof) in input.vd_mt_proofs.iter().enumerate() {
            self.vd_mt_proofs[i].set_targets(pw, true, vd_mt_proof)?;
        }
        // the rest of vd_mt_proofs set them to the empty_pod vd_mt_proof
        let vd_emptypod_mt_proof =
            input
                .vds_set
                .get_vds_proofs(&[cache_get_standard_empty_pod_circuit_data()
                    .1
                    .verifier_only
                    .clone()])?;
        let vd_emptypod_mt_proof = vd_emptypod_mt_proof[0].clone();
        for i in input.vd_mt_proofs.len()..self.vd_mt_proofs.len() {
            self.vd_mt_proofs[i].set_targets(pw, true, &vd_emptypod_mt_proof)?;
        }

        assert!(input.signed_pods.len() <= self.params.max_input_signed_pods);
        for (i, signed_pod) in input.signed_pods.iter().enumerate() {
            self.signed_pods[i].set_targets(pw, signed_pod)?;
        }
        // Padding
        if input.signed_pods.len() != self.params.max_input_signed_pods {
            let dummy = SignedPod::dummy();
            for i in input.signed_pods.len()..self.params.max_input_signed_pods {
                self.signed_pods[i].set_targets(pw, &dummy)?;
            }
        }

        assert!(
            input.recursive_pods_pub_self_statements.len() <= self.params.max_input_recursive_pods
        );
        for (i, pod_pub_statements) in input.recursive_pods_pub_self_statements.iter().enumerate() {
            set_targets_input_pods_self_statements(
                pw,
                &self.params,
                &self.input_pods_self_statements[i],
                pod_pub_statements,
            )?;
        }
        // Padding
        if input.recursive_pods_pub_self_statements.len() != self.params.max_input_recursive_pods {
            let empty_pod = EmptyPod::new_boxed(&self.params, input.vds_set.clone());
            let empty_pod_statements = empty_pod.pub_statements();
            for i in
                input.recursive_pods_pub_self_statements.len()..self.params.max_input_recursive_pods
            {
                set_targets_input_pods_self_statements(
                    pw,
                    &self.params,
                    &self.input_pods_self_statements[i],
                    &empty_pod_statements,
                )?;
            }
        }

        assert_eq!(input.statements.len(), self.params.max_statements);
        for (i, (st, op)) in zip_eq(&input.statements, &input.operations).enumerate() {
            self.input_statements[i].set_targets(pw, &self.params, st)?;
            self.operations[i].set_targets(pw, &self.params, op)?;
        }

        assert!(input.merkle_proofs.len() <= self.params.max_merkle_proofs_containers);
        for (i, mp) in input.merkle_proofs.iter().enumerate() {
            self.merkle_proofs[i].set_targets(pw, true, mp)?;
        }
        // Padding
        let pad_mp = MerkleClaimAndProof::empty();
        for i in input.merkle_proofs.len()..self.params.max_merkle_proofs_containers {
            self.merkle_proofs[i].set_targets(pw, false, &pad_mp)?;
        }

        assert!(input.public_key_of_sks.len() <= self.params.max_public_key_of);
        for (i, sk) in input.public_key_of_sks.iter().enumerate() {
            pw.set_biguint320_target(&self.public_key_of_sks[i], &sk.0)?;
        }
        // Padding
        let pad_sk = BigUint::ZERO;
        for i in input.public_key_of_sks.len()..self.params.max_public_key_of {
            pw.set_biguint320_target(&self.public_key_of_sks[i], &pad_sk)?;
        }

        assert!(input.custom_predicate_batches.len() <= self.params.max_custom_predicate_batches);
        for (i, cpb) in input.custom_predicate_batches.iter().enumerate() {
            self.custom_predicate_batches[i].set_targets(pw, &self.params, cpb)?;
        }
        // Padding
        let pad_cpb = CustomPredicateBatch::new(
            &self.params,
            "empty".to_string(),
            vec![CustomPredicate::empty()],
        );
        for i in input.custom_predicate_batches.len()..self.params.max_custom_predicate_batches {
            self.custom_predicate_batches[i].set_targets(pw, &self.params, &pad_cpb)?;
        }

        assert!(
            input.custom_predicate_verifications.len()
                <= self.params.max_custom_predicate_verifications
        );
        for (i, cpv) in input.custom_predicate_verifications.iter().enumerate() {
            self.custom_predicate_verifications[i].set_targets(pw, &self.params, cpv)?;
        }
        // Padding.  Use the first input if it exists.  If it doesnt, all batches in this MainPod
        // are padding so refer to the first padding entry.
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
        for i in input.custom_predicate_verifications.len()
            ..self.params.max_custom_predicate_verifications
        {
            self.custom_predicate_verifications[i].set_targets(pw, &self.params, pad_cpv)?;
        }

        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use std::{iter, ops::Not};

    use plonky2::{
        field::{goldilocks_field::GoldilocksField, types::Field},
        hash::hash_types::HashOut,
        iop::witness::WitnessWrite,
        plonk::{circuit_builder::CircuitBuilder, circuit_data::CircuitConfig},
    };

    use super::*;
    use crate::{
        backends::plonky2::{
            basetypes::C,
            circuits::common::tests::I64_TEST_PAIRS,
            mainpod::{calculate_id, OperationArg, OperationAux},
            primitives::{
                ec::schnorr::SecretKey,
                merkletree::{MerkleClaimAndProof, MerkleTree},
            },
        },
        frontend::{self, literal, CustomPredicateBatchBuilder, StatementTmplBuilder},
        middleware::{
            hash_str, hash_values, Hash, Key, OperationType, PodId, Predicate, RawValue,
            StatementTmpl, StatementTmplArg, TypedValue, Wildcard,
        },
    };

    fn operation_verify(
        st: mainpod::Statement,
        op: mainpod::Operation,
        prev_statements: Vec<mainpod::Statement>,
        merkle_proofs: Vec<MerkleClaimAndProof>,
        secret_keys: Vec<SecretKey>,
    ) -> Result<()> {
        let params = Params {
            max_custom_predicate_batches: 0,
            max_custom_predicate_verifications: 0,
            max_merkle_proofs_containers: merkle_proofs.len(),
            max_public_key_of: secret_keys.len(),
            ..Default::default()
        };

        let config = CircuitConfig::standard_recursion_config();
        let mut builder = CircuitBuilder::new(config);

        let st_target = builder.add_virtual_statement(&params);
        let op_target = builder.add_virtual_operation(&params);
        let prev_statements_target: Vec<_> = (0..prev_statements.len())
            .map(|_| builder.add_virtual_statement(&params))
            .collect();

        let merkle_proofs_target: Vec<_> = merkle_proofs
            .iter()
            .map(|_| {
                MerkleClaimAndProofTarget::new_virtual(params.max_depth_mt_containers, &mut builder)
            })
            .collect();

        let secret_keys_target: Vec<_> = secret_keys
            .iter()
            .map(|sk| builder.constant_biguint320(&sk.0))
            .collect();

        let aux_table = build_operation_aux_table_circuit(
            &params,
            &mut builder,
            &merkle_proofs_target,
            &secret_keys_target,
            &[],
            &[],
        )?;
        // let max_aux_entry_len = max_operation_aux_entry_len(&params);
        // let aux = builder.add_virtual_targets(1 + max_aux_entry_len);

        verify_operation_circuit(
            &params,
            &mut builder,
            &st_target,
            &op_target,
            &prev_statements_target,
            0,
            &aux_table,
        )?;

        let mut pw = PartialWitness::<F>::new();
        st_target.set_targets(&mut pw, &params, &st)?;
        op_target.set_targets(&mut pw, &params, &op)?;
        for (prev_st_target, prev_st) in prev_statements_target.iter().zip(prev_statements.iter()) {
            prev_st_target.set_targets(&mut pw, &params, prev_st)?;
        }
        for (merkle_proof_target, merkle_proof) in
            merkle_proofs_target.iter().zip(merkle_proofs.iter())
        {
            merkle_proof_target.set_targets(&mut pw, true, merkle_proof)?
        }

        // generate & verify proof
        let data = builder.build::<C>();
        let proof = data.prove(pw)?;
        data.verify(proof)?;

        Ok(())
    }

    #[test]
    fn test_lt_lteq_verify_failures() {
        let st1: mainpod::Statement =
            Statement::equal(AnchoredKey::from((SELF, "hello")), Value::from(55)).into();
        let st2: mainpod::Statement = Statement::equal(
            AnchoredKey::from((PodId(RawValue::from(75).into()), "world")),
            Value::from(56),
        )
        .into();
        let st3: mainpod::Statement = Statement::equal(
            AnchoredKey::from((PodId(RawValue::from(88).into()), "hola")),
            Value::from(RawValue([
                GoldilocksField::NEG_ONE,
                GoldilocksField::ZERO,
                GoldilocksField::ZERO,
                GoldilocksField::ZERO,
            ])),
        )
        .into();
        let st4: mainpod::Statement = Statement::equal(
            AnchoredKey::from((PodId(RawValue::from(74).into()), "mundo")),
            Value::from(-55),
        )
        .into();
        let st5: mainpod::Statement = Statement::equal(
            AnchoredKey::from((PodId(RawValue::from(70).into()), "que")),
            Value::from(-56),
        )
        .into();

        let prev_statements = [st1, st2, st3, st4, st5];

        [
            // 56 < 55, 55 < 55, 56 <= 55, -55 < -55, -55 < -56, -55 <= -56 should fail to verify
            (
                mainpod::Operation(
                    OperationType::Native(NativeOperation::LtFromEntries),
                    vec![OperationArg::Index(1), OperationArg::Index(0)],
                    OperationAux::None,
                ),
                Statement::lt(
                    AnchoredKey::from((PodId(RawValue::from(75).into()), "world")),
                    AnchoredKey::from((SELF, "hello")),
                )
                .into(),
            ),
            (
                mainpod::Operation(
                    OperationType::Native(NativeOperation::LtFromEntries),
                    vec![OperationArg::Index(0), OperationArg::Index(0)],
                    OperationAux::None,
                ),
                Statement::lt(
                    AnchoredKey::from((SELF, "hello")),
                    AnchoredKey::from((SELF, "hello")),
                )
                .into(),
            ),
            (
                mainpod::Operation(
                    OperationType::Native(NativeOperation::LtEqFromEntries),
                    vec![OperationArg::Index(1), OperationArg::Index(0)],
                    OperationAux::None,
                ),
                Statement::lt_eq(
                    AnchoredKey::from((PodId(RawValue::from(75).into()), "world")),
                    AnchoredKey::from((SELF, "hello")),
                )
                .into(),
            ),
            (
                mainpod::Operation(
                    OperationType::Native(NativeOperation::LtFromEntries),
                    vec![OperationArg::Index(3), OperationArg::Index(3)],
                    OperationAux::None,
                ),
                Statement::lt(
                    AnchoredKey::from((PodId(RawValue::from(74).into()), "mundo")),
                    AnchoredKey::from((PodId(RawValue::from(74).into()), "mundo")),
                )
                .into(),
            ),
            (
                mainpod::Operation(
                    OperationType::Native(NativeOperation::LtFromEntries),
                    vec![OperationArg::Index(3), OperationArg::Index(4)],
                    OperationAux::None,
                ),
                Statement::lt(
                    AnchoredKey::from((PodId(RawValue::from(74).into()), "mundo")),
                    AnchoredKey::from((PodId(RawValue::from(70).into()), "que")),
                )
                .into(),
            ),
            (
                mainpod::Operation(
                    OperationType::Native(NativeOperation::LtEqFromEntries),
                    vec![OperationArg::Index(3), OperationArg::Index(4)],
                    OperationAux::None,
                ),
                Statement::lt_eq(
                    AnchoredKey::from((PodId(RawValue::from(74).into()), "mundo")),
                    AnchoredKey::from((PodId(RawValue::from(70).into()), "que")),
                )
                .into(),
            ),
            // 56 < p-1 and p-1 <= p-1 should fail to verify, where p
            // is the Goldilocks prime and 'p-1' occupies a single
            // limb.
            (
                mainpod::Operation(
                    OperationType::Native(NativeOperation::LtFromEntries),
                    vec![OperationArg::Index(1), OperationArg::Index(2)],
                    OperationAux::None,
                ),
                Statement::lt(
                    AnchoredKey::from((PodId(RawValue::from(75).into()), "world")),
                    AnchoredKey::from((PodId(RawValue::from(88).into()), "hola")),
                )
                .into(),
            ),
            (
                mainpod::Operation(
                    OperationType::Native(NativeOperation::LtEqFromEntries),
                    vec![OperationArg::Index(2), OperationArg::Index(2)],
                    OperationAux::None,
                ),
                Statement::lt_eq(
                    AnchoredKey::from((PodId(RawValue::from(88).into()), "hola")),
                    AnchoredKey::from((PodId(RawValue::from(88).into()), "hola")),
                )
                .into(),
            ),
        ]
        .into_iter()
        .for_each(|(op, st)| {
            let check = std::panic::catch_unwind(|| {
                operation_verify(st, op, prev_statements.to_vec(), vec![], vec![])
            });
            match check {
                Err(e) => {
                    let err_string = e.downcast_ref::<String>().unwrap();
                    if !err_string.contains("Integer too large to fit") {
                        panic!("Test failed with an unexpected error: {}", err_string);
                    }
                }
                Ok(Err(_)) => {}
                _ => panic!("Test passed, yet it should have failed!"),
            }
        });
    }

    #[test]
    fn test_eq_neq_verify_failures() {
        let st1: mainpod::Statement =
            Statement::equal(AnchoredKey::from((SELF, "hello")), Value::from(55)).into();
        let st2: mainpod::Statement = Statement::equal(
            AnchoredKey::from((PodId(RawValue::from(75).into()), "world")),
            Value::from(56),
        )
        .into();
        let st3: mainpod::Statement = Statement::equal(
            AnchoredKey::from((PodId(RawValue::from(88).into()), "hola")),
            Value::from(RawValue([
                GoldilocksField::NEG_ONE,
                GoldilocksField::ZERO,
                GoldilocksField::ZERO,
                GoldilocksField::ZERO,
            ])),
        )
        .into();
        let prev_statements = [st1, st2, st3];

        [
            // 56 == 55, 55 != 55 should fail to verify
            (
                mainpod::Operation(
                    OperationType::Native(NativeOperation::EqualFromEntries),
                    vec![OperationArg::Index(1), OperationArg::Index(0)],
                    OperationAux::None,
                ),
                Statement::equal(
                    AnchoredKey::from((PodId(RawValue::from(75).into()), "world")),
                    AnchoredKey::from((SELF, "hello")),
                )
                .into(),
            ),
            (
                mainpod::Operation(
                    OperationType::Native(NativeOperation::NotEqualFromEntries),
                    vec![OperationArg::Index(0), OperationArg::Index(0)],
                    OperationAux::None,
                ),
                Statement::not_equal(
                    AnchoredKey::from((SELF, "hello")),
                    AnchoredKey::from((SELF, "hello")),
                )
                .into(),
            ),
        ]
        .into_iter()
        .for_each(|(op, st)| {
            assert!(operation_verify(st, op, prev_statements.to_vec(), vec![], vec![]).is_err())
        });
    }

    #[test]
    fn test_operation_verify_none() -> Result<()> {
        let st: mainpod::Statement = Statement::None.into();
        let op = mainpod::Operation(
            OperationType::Native(NativeOperation::None),
            vec![],
            OperationAux::None,
        );
        let prev_statements = vec![Statement::None.into()];
        operation_verify(st, op, prev_statements, vec![], vec![])
    }

    #[test]
    fn test_operation_verify_newentry() -> Result<()> {
        let st1: mainpod::Statement =
            Statement::equal(AnchoredKey::from((SELF, "hello")), Value::from(55)).into();
        let st2: mainpod::Statement = Statement::equal(
            AnchoredKey::from((PodId(RawValue::from(75).into()), "hello")),
            Value::from(55),
        )
        .into();
        let prev_statements = vec![st2];
        let op = mainpod::Operation(
            OperationType::Native(NativeOperation::NewEntry),
            vec![],
            OperationAux::None,
        );
        operation_verify(st1, op, prev_statements, vec![], vec![])
    }

    #[test]
    fn test_operation_verify_copy() -> Result<()> {
        let st: mainpod::Statement = Statement::None.into();
        let op = mainpod::Operation(
            OperationType::Native(NativeOperation::CopyStatement),
            vec![OperationArg::Index(0)],
            OperationAux::None,
        );
        let prev_statements = vec![Statement::None.into()];
        operation_verify(st, op, prev_statements, vec![], vec![])
    }

    #[test]
    fn test_operation_verify_eq() -> Result<()> {
        let st1: mainpod::Statement =
            Statement::equal(AnchoredKey::from((SELF, "hello")), Value::from(55)).into();
        let st2: mainpod::Statement = Statement::equal(
            AnchoredKey::from((PodId(RawValue::from(75).into()), "world")),
            Value::from(55),
        )
        .into();
        let st: mainpod::Statement = Statement::equal(
            AnchoredKey::from((SELF, "hello")),
            AnchoredKey::from((PodId(RawValue::from(75).into()), "world")),
        )
        .into();
        let op = mainpod::Operation(
            OperationType::Native(NativeOperation::EqualFromEntries),
            vec![OperationArg::Index(0), OperationArg::Index(1)],
            OperationAux::None,
        );
        let prev_statements = vec![st1, st2];
        operation_verify(st, op, prev_statements, vec![], vec![])
    }

    #[test]
    fn test_operation_verify_neq() -> Result<()> {
        let st1: mainpod::Statement =
            Statement::equal(AnchoredKey::from((SELF, "hello")), Value::from(55)).into();
        let st2: mainpod::Statement = Statement::equal(
            AnchoredKey::from((PodId(RawValue::from(75).into()), "world")),
            Value::from(58),
        )
        .into();
        let st: mainpod::Statement = Statement::not_equal(
            AnchoredKey::from((SELF, "hello")),
            AnchoredKey::from((PodId(RawValue::from(75).into()), "world")),
        )
        .into();
        let op = mainpod::Operation(
            OperationType::Native(NativeOperation::NotEqualFromEntries),
            vec![OperationArg::Index(0), OperationArg::Index(1)],
            OperationAux::None,
        );
        let prev_statements = vec![st1, st2];
        operation_verify(st, op, prev_statements, vec![], vec![])
    }

    #[test]
    fn test_operation_verify_lt() -> Result<()> {
        let st1: mainpod::Statement =
            Statement::equal(AnchoredKey::from((SELF, "hello")), Value::from(55)).into();
        let st2: mainpod::Statement = Statement::equal(
            AnchoredKey::from((PodId(RawValue::from(88).into()), "hello")),
            Value::from(56),
        )
        .into();
        let st: mainpod::Statement = Statement::lt(
            AnchoredKey::from((SELF, "hello")),
            AnchoredKey::from((PodId(RawValue::from(88).into()), "hello")),
        )
        .into();
        let op = mainpod::Operation(
            OperationType::Native(NativeOperation::LtFromEntries),
            vec![OperationArg::Index(0), OperationArg::Index(1)],
            OperationAux::None,
        );
        let prev_statements = vec![st1, st2.clone()];
        operation_verify(st, op, prev_statements, vec![], vec![])?;

        // Also check negative < negative
        let st3: mainpod::Statement = Statement::equal(
            AnchoredKey::from((PodId(RawValue::from(89).into()), "hola")),
            Value::from(-56),
        )
        .into();
        let st4: mainpod::Statement = Statement::equal(
            AnchoredKey::from((PodId(RawValue::from(84).into()), "mundo")),
            Value::from(-55),
        )
        .into();
        let st: mainpod::Statement = Statement::lt(
            AnchoredKey::from((PodId(RawValue::from(89).into()), "hola")),
            AnchoredKey::from((PodId(RawValue::from(84).into()), "mundo")),
        )
        .into();
        let op = mainpod::Operation(
            OperationType::Native(NativeOperation::LtFromEntries),
            vec![OperationArg::Index(0), OperationArg::Index(1)],
            OperationAux::None,
        );
        let prev_statements = vec![st3.clone(), st4];
        operation_verify(st, op, prev_statements, vec![], vec![])?;

        // Also check negative < positive
        let st: mainpod::Statement = Statement::lt(
            AnchoredKey::from((PodId(RawValue::from(89).into()), "hola")),
            AnchoredKey::from((PodId(RawValue::from(88).into()), "hello")),
        )
        .into();
        let op = mainpod::Operation(
            OperationType::Native(NativeOperation::LtFromEntries),
            vec![OperationArg::Index(0), OperationArg::Index(1)],
            OperationAux::None,
        );
        let prev_statements = vec![st3, st2];
        operation_verify(st, op, prev_statements, vec![], vec![])
    }

    #[test]
    fn test_operation_verify_lteq() -> Result<()> {
        let st1: mainpod::Statement =
            Statement::equal(AnchoredKey::from((SELF, "hello")), Value::from(55)).into();
        let st2: mainpod::Statement = Statement::equal(
            AnchoredKey::from((PodId(RawValue::from(88).into()), "hello")),
            Value::from(56),
        )
        .into();
        let st: mainpod::Statement = Statement::lt_eq(
            AnchoredKey::from((SELF, "hello")),
            AnchoredKey::from((PodId(RawValue::from(88).into()), "hello")),
        )
        .into();
        let op = mainpod::Operation(
            OperationType::Native(NativeOperation::LtEqFromEntries),
            vec![OperationArg::Index(0), OperationArg::Index(1)],
            OperationAux::None,
        );
        let prev_statements = vec![st1, st2.clone()];
        operation_verify(st, op, prev_statements, vec![], vec![])?;

        // Also check negative <= negative
        let st3: mainpod::Statement = Statement::equal(
            AnchoredKey::from((PodId(RawValue::from(89).into()), "hola")),
            Value::from(-56),
        )
        .into();
        let st4: mainpod::Statement = Statement::equal(
            AnchoredKey::from((PodId(RawValue::from(84).into()), "mundo")),
            Value::from(-55),
        )
        .into();
        let st: mainpod::Statement = Statement::lt_eq(
            AnchoredKey::from((PodId(RawValue::from(89).into()), "hola")),
            AnchoredKey::from((PodId(RawValue::from(84).into()), "mundo")),
        )
        .into();
        let op = mainpod::Operation(
            OperationType::Native(NativeOperation::LtEqFromEntries),
            vec![OperationArg::Index(0), OperationArg::Index(1)],
            OperationAux::None,
        );
        let prev_statements = vec![st3.clone(), st4];
        operation_verify(st, op, prev_statements, vec![], vec![])?;

        // Also check negative <= positive
        let st: mainpod::Statement = Statement::lt_eq(
            AnchoredKey::from((PodId(RawValue::from(89).into()), "hola")),
            AnchoredKey::from((PodId(RawValue::from(88).into()), "hello")),
        )
        .into();
        let op = mainpod::Operation(
            OperationType::Native(NativeOperation::LtEqFromEntries),
            vec![OperationArg::Index(0), OperationArg::Index(1)],
            OperationAux::None,
        );
        let prev_statements = vec![st3, st2];
        operation_verify(st, op, prev_statements.clone(), vec![], vec![])?;

        // Also check equality, both positive and negative.
        let st: mainpod::Statement = Statement::lt_eq(
            AnchoredKey::from((PodId(RawValue::from(89).into()), "hola")),
            AnchoredKey::from((PodId(RawValue::from(89).into()), "hola")),
        )
        .into();
        let op = mainpod::Operation(
            OperationType::Native(NativeOperation::LtEqFromEntries),
            vec![OperationArg::Index(0), OperationArg::Index(0)],
            OperationAux::None,
        );
        operation_verify(st, op, prev_statements.clone(), vec![], vec![])?;
        let st: mainpod::Statement = Statement::lt_eq(
            AnchoredKey::from((PodId(RawValue::from(88).into()), "hello")),
            AnchoredKey::from((PodId(RawValue::from(88).into()), "hello")),
        )
        .into();
        let op = mainpod::Operation(
            OperationType::Native(NativeOperation::LtEqFromEntries),
            vec![OperationArg::Index(1), OperationArg::Index(1)],
            OperationAux::None,
        );
        operation_verify(st, op, prev_statements, vec![], vec![])
    }

    #[test]
    fn test_operation_verify_hashof() -> Result<()> {
        let input_values = [
            Value::from(RawValue([
                GoldilocksField(1),
                GoldilocksField(2),
                GoldilocksField(3),
                GoldilocksField(4),
            ])),
            Value::from(512),
        ];
        let v1 = hash_values(&input_values);
        let [v2, v3] = input_values;

        let st1: mainpod::Statement = Statement::equal(
            AnchoredKey::from((PodId(RawValue::from(88).into()), "hola")),
            Value::from(v1),
        )
        .into();
        let st2: mainpod::Statement = Statement::equal(
            AnchoredKey::from((PodId(RawValue::from(128).into()), "mundo")),
            v2,
        )
        .into();
        let st3: mainpod::Statement = Statement::equal(
            AnchoredKey::from((PodId(RawValue::from(256).into()), "!")),
            v3,
        )
        .into();

        let st: mainpod::Statement = Statement::hash_of(
            AnchoredKey::from((PodId(RawValue::from(88).into()), "hola")),
            AnchoredKey::from((PodId(RawValue::from(128).into()), "mundo")),
            AnchoredKey::from((PodId(RawValue::from(256).into()), "!")),
        )
        .into();
        let op = mainpod::Operation(
            OperationType::Native(NativeOperation::HashOf),
            vec![
                OperationArg::Index(0),
                OperationArg::Index(1),
                OperationArg::Index(2),
            ],
            OperationAux::None,
        );
        let prev_statements = vec![st1, st2, st3];
        operation_verify(st, op, prev_statements, vec![], vec![])
    }

    #[test]
    fn test_operation_verify_sumof() -> Result<()> {
        I64_TEST_PAIRS
            .into_iter()
            .flat_map(|(a, b)| {
                let (sum, overflow) = a.overflowing_add(b);
                overflow.not().then_some((a, b, sum))
            })
            .try_for_each(|(a, b, sum)| {
                let st1: mainpod::Statement = Statement::equal(
                    AnchoredKey::from((PodId(RawValue::from(88).into()), "hola")),
                    sum,
                )
                .into();

                let st2: mainpod::Statement = Statement::equal(
                    AnchoredKey::from((PodId(RawValue::from(128).into()), "mundo")),
                    a,
                )
                .into();

                let st3: mainpod::Statement = Statement::equal(
                    AnchoredKey::from((PodId(RawValue::from(256).into()), "!")),
                    b,
                )
                .into();

                let st: mainpod::Statement = Statement::sum_of(
                    AnchoredKey::from((PodId(RawValue::from(88).into()), "hola")),
                    AnchoredKey::from((PodId(RawValue::from(128).into()), "mundo")),
                    AnchoredKey::from((PodId(RawValue::from(256).into()), "!")),
                )
                .into();
                let op = mainpod::Operation(
                    OperationType::Native(NativeOperation::SumOf),
                    vec![
                        OperationArg::Index(0),
                        OperationArg::Index(1),
                        OperationArg::Index(2),
                    ],
                    OperationAux::None,
                );
                let prev_statements = vec![st1, st2, st3];
                operation_verify(st, op, prev_statements, vec![], vec![])
            })
    }

    #[test]
    fn test_operation_verify_productof() -> Result<()> {
        I64_TEST_PAIRS
            .into_iter()
            .flat_map(|(a, b)| {
                let (prod, overflow) = a.overflowing_mul(b);
                overflow.not().then_some((a, b, prod))
            })
            .try_for_each(|(a, b, prod)| {
                let st1: mainpod::Statement = Statement::equal(
                    AnchoredKey::from((PodId(RawValue::from(88).into()), "hola")),
                    prod,
                )
                .into();

                let st2: mainpod::Statement = Statement::equal(
                    AnchoredKey::from((PodId(RawValue::from(128).into()), "mundo")),
                    a,
                )
                .into();

                let st3: mainpod::Statement = Statement::equal(
                    AnchoredKey::from((PodId(RawValue::from(256).into()), "!")),
                    b,
                )
                .into();

                let st: mainpod::Statement = Statement::product_of(
                    AnchoredKey::from((PodId(RawValue::from(88).into()), "hola")),
                    AnchoredKey::from((PodId(RawValue::from(128).into()), "mundo")),
                    AnchoredKey::from((PodId(RawValue::from(256).into()), "!")),
                )
                .into();
                let op = mainpod::Operation(
                    OperationType::Native(NativeOperation::ProductOf),
                    vec![
                        OperationArg::Index(0),
                        OperationArg::Index(1),
                        OperationArg::Index(2),
                    ],
                    OperationAux::None,
                );
                let prev_statements = vec![st1, st2, st3];
                operation_verify(st, op, prev_statements, vec![], vec![])
            })
    }

    #[test]
    fn test_operation_verify_maxof() -> Result<()> {
        I64_TEST_PAIRS.into_iter().try_for_each(|(a, b)| {
            let max = i64::max(a, b);
            let st1: mainpod::Statement = Statement::equal(
                AnchoredKey::from((PodId(RawValue::from(88).into()), "hola")),
                max,
            )
            .into();

            let st2: mainpod::Statement = Statement::equal(
                AnchoredKey::from((PodId(RawValue::from(128).into()), "mundo")),
                a,
            )
            .into();

            let st3: mainpod::Statement = Statement::equal(
                AnchoredKey::from((PodId(RawValue::from(256).into()), "!")),
                b,
            )
            .into();

            let st: mainpod::Statement = Statement::max_of(
                AnchoredKey::from((PodId(RawValue::from(88).into()), "hola")),
                AnchoredKey::from((PodId(RawValue::from(128).into()), "mundo")),
                AnchoredKey::from((PodId(RawValue::from(256).into()), "!")),
            )
            .into();
            let op = mainpod::Operation(
                OperationType::Native(NativeOperation::MaxOf),
                vec![
                    OperationArg::Index(0),
                    OperationArg::Index(1),
                    OperationArg::Index(2),
                ],
                OperationAux::None,
            );
            let prev_statements = vec![st1, st2, st3];
            operation_verify(st, op, prev_statements, vec![], vec![])
        })
    }

    #[test]
    fn test_operation_verify_maxof_failures() {
        [(5, 3, 4), (5, 5, 8), (3, 4, 5)]
            .into_iter()
            .for_each(|(max, a, b)| {
                let st1: mainpod::Statement = Statement::equal(
                    AnchoredKey::from((PodId(RawValue::from(88).into()), "hola")),
                    max,
                )
                .into();

                let st2: mainpod::Statement = Statement::equal(
                    AnchoredKey::from((PodId(RawValue::from(128).into()), "mundo")),
                    a,
                )
                .into();

                let st3: mainpod::Statement = Statement::equal(
                    AnchoredKey::from((PodId(RawValue::from(256).into()), "!")),
                    b,
                )
                .into();

                let st: mainpod::Statement = Statement::max_of(
                    AnchoredKey::from((PodId(RawValue::from(88).into()), "hola")),
                    AnchoredKey::from((PodId(RawValue::from(128).into()), "mundo")),
                    AnchoredKey::from((PodId(RawValue::from(256).into()), "!")),
                )
                .into();
                let op = mainpod::Operation(
                    OperationType::Native(NativeOperation::MaxOf),
                    vec![
                        OperationArg::Index(0),
                        OperationArg::Index(1),
                        OperationArg::Index(2),
                    ],
                    OperationAux::None,
                );
                let prev_statements = [st1, st2, st3];

                let check = std::panic::catch_unwind(|| {
                    operation_verify(st, op, prev_statements.to_vec(), vec![], vec![])
                });
                match check {
                    Err(e) => {
                        let err_string = e.downcast_ref::<String>().unwrap();
                        if !err_string.contains("Integer too large to fit") {
                            panic!("Test failed with an unexpected error: {}", err_string);
                        }
                    }
                    Ok(Err(_)) => {}
                    _ => panic!("Test passed, yet it should have failed!"),
                }
            })
    }

    #[test]
    fn test_operation_verify_lt_to_neq() -> Result<()> {
        let st: mainpod::Statement = Statement::not_equal(
            AnchoredKey::from((SELF, "hello")),
            AnchoredKey::from((PodId(RawValue::from(88).into()), "hello")),
        )
        .into();
        let st1: mainpod::Statement = Statement::lt(
            AnchoredKey::from((SELF, "hello")),
            AnchoredKey::from((PodId(RawValue::from(88).into()), "hello")),
        )
        .into();
        let op = mainpod::Operation(
            OperationType::Native(NativeOperation::LtToNotEqual),
            vec![OperationArg::Index(0)],
            OperationAux::None,
        );
        let prev_statements = vec![st1];
        operation_verify(st, op, prev_statements, vec![], vec![])
    }

    #[test]
    fn test_operation_verify_transitive_eq() -> Result<()> {
        let st: mainpod::Statement = Statement::equal(
            AnchoredKey::from((SELF, "hello")),
            AnchoredKey::from((PodId(RawValue::from(88).into()), "hola")),
        )
        .into();
        let st1: mainpod::Statement = Statement::equal(
            AnchoredKey::from((SELF, "hello")),
            AnchoredKey::from((PodId(RawValue::from(89).into()), "world")),
        )
        .into();
        let st2: mainpod::Statement = Statement::equal(
            AnchoredKey::from((PodId(RawValue::from(89).into()), "world")),
            AnchoredKey::from((PodId(RawValue::from(88).into()), "hola")),
        )
        .into();
        let op = mainpod::Operation(
            OperationType::Native(NativeOperation::TransitiveEqualFromStatements),
            vec![OperationArg::Index(0), OperationArg::Index(1)],
            OperationAux::None,
        );
        let prev_statements = vec![st1, st2];
        operation_verify(st, op, prev_statements, vec![], vec![])
    }

    #[test]
    fn test_operation_verify_sintains() -> Result<()> {
        let params = Params::default();

        let kvs = [
            (1.into(), 55.into()),
            (2.into(), 88.into()),
            (175.into(), 0.into()),
        ]
        .into_iter()
        .collect();
        let mt = MerkleTree::new(params.max_depth_mt_containers, &kvs)?;

        let root = Value::from(mt.root());
        let root_ak = AnchoredKey::from((PodId(RawValue::from(88).into()), "merkle root"));

        let key = 5.into();
        let key_ak = AnchoredKey::from((PodId(RawValue::from(88).into()), "key"));

        let no_key_pf = mt.prove_nonexistence(&key)?;

        let root_st: mainpod::Statement = Statement::equal(root_ak.clone(), root.clone()).into();
        let key_st: mainpod::Statement = Statement::equal(key_ak.clone(), key).into();
        let st: mainpod::Statement = Statement::not_contains(root_ak, key_ak).into();
        let op = mainpod::Operation(
            OperationType::Native(NativeOperation::NotContainsFromEntries),
            vec![OperationArg::Index(0), OperationArg::Index(1)],
            OperationAux::MerkleProofIndex(0),
        );

        let merkle_proofs = vec![MerkleClaimAndProof::new(
            Hash::from(root.raw()),
            key,
            None,
            no_key_pf,
        )];
        let prev_statements = vec![root_st, key_st];
        operation_verify(st, op, prev_statements, merkle_proofs, vec![])
    }

    #[test]
    fn test_operation_verify_contains() -> Result<()> {
        let params = Params::default();

        let kvs = [
            (1.into(), 55.into()),
            (2.into(), 88.into()),
            (175.into(), 0.into()),
        ]
        .into_iter()
        .collect();
        let mt = MerkleTree::new(params.max_depth_mt_containers, &kvs)?;

        let root = Value::from(mt.root());
        let root_ak = AnchoredKey::from((PodId(RawValue::from(88).into()), "merkle root"));

        let key = 175.into();
        let key_ak = AnchoredKey::from((PodId(RawValue::from(70).into()), "key"));

        let (value, key_pf) = mt.prove(&key)?;
        let value_ak = AnchoredKey::from((PodId(RawValue::from(72).into()), "value"));

        let root_st: mainpod::Statement = Statement::equal(root_ak.clone(), root.clone()).into();
        let key_st: mainpod::Statement = Statement::equal(key_ak.clone(), key).into();
        let value_st: mainpod::Statement = Statement::equal(value_ak.clone(), value).into();

        let st: mainpod::Statement = Statement::contains(root_ak, key_ak, value_ak).into();
        let op = mainpod::Operation(
            OperationType::Native(NativeOperation::ContainsFromEntries),
            vec![
                OperationArg::Index(0),
                OperationArg::Index(1),
                OperationArg::Index(2),
            ],
            OperationAux::MerkleProofIndex(0),
        );

        let merkle_proofs = vec![MerkleClaimAndProof::new(
            Hash::from(root.raw()),
            key,
            Some(value),
            key_pf,
        )];
        let prev_statements = vec![root_st, key_st, value_st];
        operation_verify(st, op, prev_statements, merkle_proofs, vec![])
    }

    #[test]
    fn test_operation_verify_publickeyof_ok() -> Result<()> {
        [
            SecretKey(BigUint::one()),
            SecretKey::new_rand(),
            SecretKey(&*GROUP_ORDER - BigUint::one()),
        ]
        .into_iter()
        .try_for_each(|secret_key| {
            let public_key = secret_key.public_key();
            let public_key_value = Value::from(TypedValue::from(public_key));
            let secret_key_value = Value::from(TypedValue::from(secret_key.clone()));
            let public_key_ak = AnchoredKey::from((PodId(RawValue::from(88).into()), "public key"));
            let secret_key_ak = AnchoredKey::from((PodId(RawValue::from(70).into()), "secret key"));
            let public_key_st: mainpod::Statement =
                Statement::equal(public_key_ak.clone(), public_key_value.clone()).into();
            let secret_key_st: mainpod::Statement =
                Statement::equal(secret_key_ak.clone(), secret_key_value.clone()).into();
            let st: mainpod::Statement =
                Statement::public_key_of(public_key_ak, secret_key_ak).into();
            let op = mainpod::Operation(
                OperationType::Native(NativeOperation::PublicKeyOf),
                vec![OperationArg::Index(0), OperationArg::Index(1)],
                OperationAux::PublicKeyOfIndex(0),
            );
            let prev_statements = vec![public_key_st, secret_key_st];
            operation_verify(st, op, prev_statements, vec![], vec![secret_key])
        })
    }

    #[test]
    fn test_operation_verify_publickeyof_failure_wrong_key() {
        let secret_key = SecretKey(BigUint::one());
        let public_key = SecretKey(BigUint::ZERO).public_key();
        let public_key_value = Value::from(TypedValue::from(public_key));
        let secret_key_value = Value::from(TypedValue::from(secret_key.clone()));
        let public_key_ak = AnchoredKey::from((PodId(RawValue::from(88).into()), "public key"));
        let secret_key_ak = AnchoredKey::from((PodId(RawValue::from(70).into()), "secret key"));
        let public_key_st: mainpod::Statement =
            Statement::equal(public_key_ak.clone(), public_key_value.clone()).into();
        let secret_key_st: mainpod::Statement =
            Statement::equal(secret_key_ak.clone(), secret_key_value.clone()).into();
        let st: mainpod::Statement = Statement::public_key_of(public_key_ak, secret_key_ak).into();
        let op = mainpod::Operation(
            OperationType::Native(NativeOperation::PublicKeyOf),
            vec![OperationArg::Index(0), OperationArg::Index(1)],
            OperationAux::PublicKeyOfIndex(0),
        );
        let prev_statements = vec![public_key_st, secret_key_st];
        assert!(operation_verify(st, op, prev_statements, vec![], vec![secret_key]).is_err())
    }

    #[test]
    fn test_operation_verify_publickeyof_failure_pk_type() {
        let secret_key = SecretKey(BigUint::one());
        let public_key = 123i64;
        let public_key_value = Value::from(TypedValue::from(public_key));
        let secret_key_value = Value::from(TypedValue::from(secret_key.clone()));
        let public_key_ak = AnchoredKey::from((PodId(RawValue::from(88).into()), "public key"));
        let secret_key_ak = AnchoredKey::from((PodId(RawValue::from(70).into()), "secret key"));
        let public_key_st: mainpod::Statement =
            Statement::equal(public_key_ak.clone(), public_key_value.clone()).into();
        let secret_key_st: mainpod::Statement =
            Statement::equal(secret_key_ak.clone(), secret_key_value.clone()).into();
        let st: mainpod::Statement = Statement::public_key_of(public_key_ak, secret_key_ak).into();
        let op = mainpod::Operation(
            OperationType::Native(NativeOperation::PublicKeyOf),
            vec![OperationArg::Index(0), OperationArg::Index(1)],
            OperationAux::None,
        );
        let prev_statements = vec![public_key_st, secret_key_st];
        assert!(operation_verify(st, op, prev_statements, vec![], vec![secret_key]).is_err())
    }

    #[test]
    fn test_operation_verify_publickeyof_failure_sk_type() {
        let secret_key = 123i64;
        let public_key = SecretKey(BigUint::from(123u32)).public_key();
        let public_key_value = Value::from(TypedValue::from(public_key));
        let secret_key_value = Value::from(TypedValue::from(secret_key));
        let public_key_ak = AnchoredKey::from((PodId(RawValue::from(88).into()), "public key"));
        let secret_key_ak = AnchoredKey::from((PodId(RawValue::from(70).into()), "secret key"));
        let public_key_st: mainpod::Statement =
            Statement::equal(public_key_ak.clone(), public_key_value.clone()).into();
        let secret_key_st: mainpod::Statement =
            Statement::equal(secret_key_ak.clone(), secret_key_value.clone()).into();
        let st: mainpod::Statement = Statement::public_key_of(public_key_ak, secret_key_ak).into();
        let op = mainpod::Operation(
            OperationType::Native(NativeOperation::PublicKeyOf),
            vec![OperationArg::Index(0), OperationArg::Index(1)],
            OperationAux::PublicKeyOfIndex(0),
        );
        let prev_statements = vec![public_key_st, secret_key_st];
        assert!(operation_verify(
            st,
            op,
            prev_statements,
            vec![],
            vec![SecretKey(BigUint::from(123u32))]
        )
        .is_err())
    }

    #[test]
    fn test_operation_verify_publickeyof_failure_sk_size() {
        let secret_key = SecretKey(&*GROUP_ORDER - BigUint::ZERO);
        let public_key = secret_key.public_key();
        let public_key_value = Value::from(TypedValue::from(public_key));
        let secret_key_value = Value::from(TypedValue::from(secret_key.clone()));
        let public_key_ak = AnchoredKey::from((PodId(RawValue::from(88).into()), "public key"));
        let secret_key_ak = AnchoredKey::from((PodId(RawValue::from(70).into()), "secret key"));
        let public_key_st: mainpod::Statement =
            Statement::equal(public_key_ak.clone(), public_key_value.clone()).into();
        let secret_key_st: mainpod::Statement =
            Statement::equal(secret_key_ak.clone(), secret_key_value.clone()).into();
        let st: mainpod::Statement = Statement::public_key_of(public_key_ak, secret_key_ak).into();
        let op = mainpod::Operation(
            OperationType::Native(NativeOperation::PublicKeyOf),
            vec![OperationArg::Index(0), OperationArg::Index(1)],
            OperationAux::PublicKeyOfIndex(0),
        );
        let prev_statements = vec![public_key_st, secret_key_st];
        assert!(operation_verify(st, op, prev_statements, vec![], vec![secret_key]).is_err())
    }

    fn helper_statement_arg_from_template(
        params: &Params,
        st_tmpl_arg: StatementTmplArg,
        args: Vec<Value>,
        expected_st_arg: StatementArg,
    ) -> Result<()> {
        let config = CircuitConfig::standard_recursion_config();
        let mut builder = CircuitBuilder::new(config);

        let st_tmpl_arg_target = builder.add_virtual_statement_tmpl_arg();
        let args_target: Vec<_> = (0..args.len())
            .map(|_| builder.add_virtual_value())
            .collect();
        let st_arg_target = make_statement_arg_from_template_circuit(
            params,
            &mut builder,
            &st_tmpl_arg_target,
            &args_target,
        );
        // TODO: Instead of connect, assign witness to result
        let expected_st_arg_target = builder.add_virtual_statement_arg();
        builder.connect_array(expected_st_arg_target.elements, st_arg_target.elements);

        let mut pw = PartialWitness::<F>::new();

        st_tmpl_arg_target.set_targets(&mut pw, params, &st_tmpl_arg)?;
        for (arg_target, arg) in args_target.iter().zip(args.iter()) {
            arg_target.set_targets(&mut pw, arg)?;
        }
        expected_st_arg_target.set_targets(&mut pw, params, &expected_st_arg)?;

        // generate & verify proof
        let data = builder.build::<C>();
        let proof = data.prove(pw).unwrap();
        data.verify(proof.clone()).unwrap();

        Ok(())
    }

    #[test]
    fn test_statement_arg_from_template() -> Result<()> {
        let params = Params::default();

        let pod_id = PodId(hash_str("pod_id"));

        // case: None
        let st_tmpl_arg = StatementTmplArg::None;
        let args = vec![Value::from(1), Value::from(2), Value::from(3)];
        let expected_st_arg = StatementArg::None;
        helper_statement_arg_from_template(&params, st_tmpl_arg, args, expected_st_arg)?;

        // case: Literal
        let st_tmpl_arg = StatementTmplArg::Literal(Value::from("foo"));
        let args = vec![Value::from(1), Value::from(2), Value::from(3)];
        let expected_st_arg = StatementArg::Literal(Value::from("foo"));
        helper_statement_arg_from_template(&params, st_tmpl_arg, args, expected_st_arg)?;

        // case: AnchoredKey(id_wildcard, key_literal)
        let st_tmpl_arg =
            StatementTmplArg::AnchoredKey(Wildcard::new("a".to_string(), 1), Key::from("foo"));
        let args = vec![Value::from(1), Value::from(pod_id), Value::from(3)];
        let expected_st_arg = StatementArg::Key(AnchoredKey::new(pod_id, Key::from("foo")));
        helper_statement_arg_from_template(&params, st_tmpl_arg, args, expected_st_arg)?;

        // case: WildcardLiteral(wildcard)
        let st_tmpl_arg = StatementTmplArg::Wildcard(Wildcard::new("a".to_string(), 1));
        let args = vec![Value::from(1), Value::from("key"), Value::from(3)];
        let expected_st_arg = StatementArg::Literal(Value::from("key"));
        helper_statement_arg_from_template(&params, st_tmpl_arg, args, expected_st_arg)?;

        Ok(())
    }

    fn helper_statement_from_template(
        params: &Params,
        st_tmpl: StatementTmpl,
        args: Vec<Value>,
        expected_st: Statement,
    ) -> Result<()> {
        let config = CircuitConfig::standard_recursion_config();
        let mut builder = CircuitBuilder::new(config);

        let st_tmpl_target = builder.add_virtual_statement_tmpl(params);
        let args_target: Vec<_> = (0..args.len())
            .map(|_| builder.add_virtual_value())
            .collect();
        let st_target = make_statement_from_template_circuit(
            params,
            &mut builder,
            &st_tmpl_target,
            &args_target,
        );
        // TODO: Instead of connect, assign witness to result
        let expected_st_target = builder.add_virtual_statement(params);
        builder.connect_flattenable(&expected_st_target, &st_target);

        let mut pw = PartialWitness::<F>::new();

        st_tmpl_target.set_targets(&mut pw, params, &st_tmpl)?;
        for (arg_target, arg) in args_target.iter().zip(args.iter()) {
            arg_target.set_targets(&mut pw, arg)?;
        }
        expected_st_target.set_targets(&mut pw, params, &expected_st.into())?;

        // generate & verify proof
        let data = builder.build::<C>();
        let proof = data.prove(pw).unwrap();
        data.verify(proof.clone()).unwrap();

        Ok(())
    }

    #[test]
    fn test_statement_from_template() -> Result<()> {
        let params = Params::default();

        let pod_id = PodId(hash_str("pod_id"));

        let st_tmpl = StatementTmpl {
            pred: Predicate::Native(NativePredicate::Equal),
            args: vec![
                StatementTmplArg::AnchoredKey(Wildcard::new("a".to_string(), 1), Key::from("key")),
                StatementTmplArg::Literal(Value::from("value")),
            ],
        };
        let args = vec![Value::from(1), Value::from(pod_id.0), Value::from(3)];
        let expected_st = Statement::equal(
            AnchoredKey::new(pod_id, Key::from("key")),
            Value::from("value"),
        );
        helper_statement_from_template(&params, st_tmpl, args, expected_st)?;

        Ok(())
    }

    fn helper_custom_operation_verify_gadget(
        params: &Params,
        custom_predicate: CustomPredicateRef,
        op_args: Vec<Statement>,
        args: Vec<Value>,
        expected_st: Option<Statement>,
    ) -> Result<()> {
        let config = CircuitConfig::standard_recursion_config();
        let mut builder = CircuitBuilder::new(config);

        let custom_predicate_target = builder.add_virtual_custom_predicate_entry(params);
        let op_args_target: Vec<_> = (0..args.len())
            .map(|_| builder.add_virtual_statement(params))
            .collect();
        let args_target: Vec<_> = (0..args.len())
            .map(|_| builder.add_virtual_value())
            .collect();
        let (st_target, op_type_target) = make_custom_statement_circuit(
            params,
            &mut builder,
            &custom_predicate_target,
            &op_args_target,
            &args_target,
        )?;

        let mut pw = PartialWitness::<F>::new();

        // Input
        custom_predicate_target.set_targets(&mut pw, params, &custom_predicate)?;
        for (op_arg_target, op_arg) in op_args_target.iter().zip(op_args.into_iter()) {
            op_arg_target.set_targets(&mut pw, params, &op_arg.into())?;
        }
        for (arg_target, arg) in args_target.iter().zip(args.iter()) {
            arg_target.set_targets(&mut pw, &Value::from(arg.raw()))?;
        }
        // Expected Output
        if let Some(expected_st) = expected_st {
            st_target.set_targets(&mut pw, params, &expected_st.into())?;
        }

        let expected_op_type = OperationType::Custom(custom_predicate);
        op_type_target.set_targets(&mut pw, params, &expected_op_type)?;

        // generate & verify proof
        let data = builder.build::<C>();
        let proof = data.prove(pw)?;
        Ok(data.verify(proof.clone())?)
    }

    // TODO: Add negative tests
    #[test]
    fn test_custom_operation_verify_gadget_positive() -> frontend::Result<()> {
        // We set the parameters to the exact sizes we have in the test so that we don't have to
        // pad.
        let params = Params {
            max_custom_predicate_arity: 2,
            max_custom_predicate_wildcards: 2,
            max_operation_args: 2,
            max_statement_args: 2,
            ..Default::default()
        };

        use NativePredicate as NP;
        use StatementTmplBuilder as STB;
        let mut builder = CustomPredicateBatchBuilder::new(params.clone(), "batch".into());
        let stb0 = STB::new(NP::Equal).arg(("id", "score")).arg(literal(42));
        let stb1 = STB::new(NP::Equal).arg(("id", "key")).arg("secret");
        let _ = builder.predicate_and(
            "pred_and",
            &["id"],
            &["secret"],
            &[stb0.clone(), stb1.clone()],
        )?;
        let _ = builder.predicate_or("pred_or", &["id"], &["secret"], &[stb0, stb1])?;
        let batch = builder.finish();

        let pod_id = PodId(hash_str("pod_id"));

        // AND
        let custom_predicate = CustomPredicateRef::new(batch.clone(), 0);
        let op_args = vec![
            Statement::equal(
                AnchoredKey::new(pod_id, Key::from("score")),
                Value::from(42),
            ),
            Statement::equal(
                AnchoredKey::new(pod_id, Key::from("key")),
                Value::from(1234),
            ),
        ];
        let args = vec![Value::from(pod_id), Value::from(1234)];
        let expected_st = Statement::Custom(
            custom_predicate.clone(),
            vec![args[0].clone(), Value::from(0)],
        );

        helper_custom_operation_verify_gadget(
            &params,
            custom_predicate,
            op_args,
            args,
            Some(expected_st),
        )
        .unwrap();

        // OR (1)
        let custom_predicate = CustomPredicateRef::new(batch.clone(), 1);
        let op_args = vec![
            Statement::equal(
                AnchoredKey::new(pod_id, Key::from("score")),
                Value::from(42),
            ),
            Statement::None,
        ];
        let args = vec![Value::from(pod_id), Value::from(0)];
        let expected_st = Statement::Custom(
            custom_predicate.clone(),
            vec![args[0].clone(), Value::from(0)],
        );

        helper_custom_operation_verify_gadget(
            &params,
            custom_predicate,
            op_args,
            args,
            Some(expected_st),
        )
        .unwrap();

        // OR (2)
        let custom_predicate = CustomPredicateRef::new(batch.clone(), 1);
        let op_args = vec![
            Statement::None,
            Statement::equal(
                AnchoredKey::new(pod_id, Key::from("key")),
                Value::from(1234),
            ),
        ];
        let args = vec![Value::from(pod_id), Value::from(1234)];
        let expected_st = Statement::Custom(
            custom_predicate.clone(),
            vec![args[0].clone(), Value::from(0)],
        );

        helper_custom_operation_verify_gadget(
            &params,
            custom_predicate,
            op_args,
            args,
            Some(expected_st),
        )
        .unwrap();

        Ok(())
    }

    #[test]
    fn test_custom_operation_verify_gadget_negative() -> frontend::Result<()> {
        // We set the parameters to the exact sizes we have in the test so that we don't have to
        // pad.
        let params = Params {
            max_custom_predicate_arity: 2,
            max_custom_predicate_wildcards: 2,
            max_operation_args: 2,
            max_statement_args: 2,
            ..Default::default()
        };

        use NativePredicate as NP;
        use StatementTmplBuilder as STB;
        let mut builder = CustomPredicateBatchBuilder::new(params.clone(), "batch".into());
        let stb0 = STB::new(NP::Equal).arg(("id", "score")).arg(literal(42));
        let stb1 = STB::new(NP::Equal)
            .arg(("secret_id", "key"))
            .arg(("id", "score"));
        let _ = builder.predicate_and(
            "pred_and",
            &["id"],
            &["secret_id"],
            &[stb0.clone(), stb1.clone()],
        )?;
        let _ = builder.predicate_or("pred_or", &["id"], &["secret_id"], &[stb0, stb1])?;
        let batch = builder.finish();

        let pod_id = PodId(hash_str("pod_id"));
        let secret_pod_id = PodId(hash_str("secret_pod_id"));

        // AND (0) Sanity check with correct values
        let custom_predicate = CustomPredicateRef::new(batch.clone(), 0);
        let op_args = vec![
            Statement::equal(
                AnchoredKey::new(pod_id, Key::from("score")),
                Value::from(42),
            ),
            Statement::equal(
                AnchoredKey::new(secret_pod_id, Key::from("key")),
                AnchoredKey::new(pod_id, Key::from("score")),
            ),
        ];
        let args = vec![Value::from(pod_id), Value::from(secret_pod_id)];
        let expected_st = Statement::Custom(
            custom_predicate.clone(),
            vec![args[0].clone(), Value::from(0)],
        );

        helper_custom_operation_verify_gadget(
            &params,
            custom_predicate,
            op_args,
            args,
            Some(expected_st),
        )
        .unwrap();

        // AND (1) Different pod_id for same wildcard
        let custom_predicate = CustomPredicateRef::new(batch.clone(), 0);
        let op_args = vec![
            Statement::equal(
                AnchoredKey::new(pod_id, Key::from("score")),
                Value::from(42),
            ),
            Statement::equal(
                AnchoredKey::new(secret_pod_id, Key::from("key")),
                AnchoredKey::new(PodId(hash_str("BAD")), Key::from("score")),
            ),
        ];
        let args = vec![Value::from(pod_id), Value::from(secret_pod_id)];

        assert!(helper_custom_operation_verify_gadget(
            &params,
            custom_predicate,
            op_args,
            args,
            None,
        )
        .is_err());

        // AND (2) key doesn't match template
        let custom_predicate = CustomPredicateRef::new(batch.clone(), 0);
        let op_args = vec![
            Statement::equal(AnchoredKey::new(pod_id, Key::from("BAD")), Value::from(42)),
            Statement::equal(
                AnchoredKey::new(secret_pod_id, Key::from("key")),
                AnchoredKey::new(pod_id, Key::from("score")),
            ),
        ];
        let args = vec![Value::from(pod_id), Value::from(secret_pod_id)];

        assert!(helper_custom_operation_verify_gadget(
            &params,
            custom_predicate,
            op_args,
            args,
            None,
        )
        .is_err());

        // AND (3) literal doesn't match template
        let custom_predicate = CustomPredicateRef::new(batch.clone(), 0);
        let op_args = vec![
            Statement::equal(
                AnchoredKey::new(pod_id, Key::from("score")),
                Value::from(0xbad),
            ),
            Statement::equal(
                AnchoredKey::new(secret_pod_id, Key::from("key")),
                AnchoredKey::new(pod_id, Key::from("score")),
            ),
        ];
        let args = vec![Value::from(pod_id), Value::from(secret_pod_id)];

        assert!(helper_custom_operation_verify_gadget(
            &params,
            custom_predicate,
            op_args,
            args,
            None,
        )
        .is_err());

        // AND (4) predicate doesn't match template
        let custom_predicate = CustomPredicateRef::new(batch.clone(), 0);
        let op_args = vec![
            Statement::equal(
                AnchoredKey::new(pod_id, Key::from("score")),
                Value::from(42),
            ),
            Statement::not_equal(
                AnchoredKey::new(secret_pod_id, Key::from("key")),
                AnchoredKey::new(pod_id, Key::from("score")),
            ),
        ];
        let args = vec![Value::from(pod_id), Value::from(secret_pod_id)];

        assert!(helper_custom_operation_verify_gadget(
            &params,
            custom_predicate,
            op_args,
            args,
            None,
        )
        .is_err());

        // OR (1) Two Nones
        let custom_predicate = CustomPredicateRef::new(batch.clone(), 1);
        let op_args = vec![Statement::None, Statement::None];
        let args = vec![Value::from(pod_id), Value::from(0)];

        assert!(helper_custom_operation_verify_gadget(
            &params,
            custom_predicate,
            op_args,
            args,
            None
        )
        .is_err());

        Ok(())
    }

    fn helper_calculate_id(params: &Params, statements: &[Statement]) -> Result<()> {
        let config = CircuitConfig::standard_recursion_config();
        let mut builder = CircuitBuilder::new(config);

        let statements_target = (0..params.max_public_statements)
            .map(|_| builder.add_virtual_statement(params))
            .collect_vec();
        let id_target = calculate_id_circuit(params, &mut builder, &statements_target);

        let mut pw = PartialWitness::<F>::new();

        // Input
        let statements = statements
            .iter()
            .map(|st| {
                let mut st = mainpod::Statement::from(st.clone());
                pad_statement(params, &mut st);
                st
            })
            .collect_vec();
        for (st_target, st) in statements_target.iter().zip(statements.iter()) {
            st_target.set_targets(&mut pw, params, st)?;
        }
        // Expected Output
        let expected_id = calculate_id(&statements, params);
        pw.set_hash_target(
            id_target,
            HashOut {
                elements: expected_id.0,
            },
        )?;

        // generate & verify proof
        let data = builder.build::<C>();
        let proof = data.prove(pw)?;
        Ok(data.verify(proof.clone())?)
    }

    #[test]
    fn test_calculate_id() -> frontend::Result<()> {
        // Case with no public public statements
        let params = Params {
            max_public_statements: 0,
            num_public_statements_id: 8,
            ..Default::default()
        };

        helper_calculate_id(&params, &[]).unwrap();

        // Case with number of statements for the id equal to number of public statements
        let params = Params {
            max_public_statements: 2,
            num_public_statements_id: 2,
            ..Default::default()
        };

        let statements = [
            Statement::equal(AnchoredKey::from((SELF, "foo")), Value::from(42)),
            Statement::equal(
                AnchoredKey::from((SELF, "bar")),
                AnchoredKey::from((SELF, "baz")),
            ),
        ]
        .into_iter()
        .chain(iter::repeat(Statement::None))
        .take(params.max_public_statements)
        .collect_vec();

        helper_calculate_id(&params, &statements).unwrap();

        // Case with more  statements for the id than the number of public statements
        let params = Params {
            max_public_statements: 4,
            num_public_statements_id: 6,
            ..Default::default()
        };

        let pod_id = PodId(hash_str("pod_id"));
        let statements = [
            Statement::equal(AnchoredKey::from((SELF, "foo")), Value::from(42)),
            Statement::equal(
                AnchoredKey::from((SELF, "bar")),
                AnchoredKey::from((SELF, "baz")),
            ),
            Statement::lt(
                AnchoredKey::from((pod_id, "one")),
                AnchoredKey::from((pod_id, "two")),
            ),
        ]
        .into_iter()
        .chain(iter::repeat(Statement::None))
        .take(params.max_public_statements)
        .collect_vec();

        helper_calculate_id(&params, &statements).unwrap();

        Ok(())
    }
}
