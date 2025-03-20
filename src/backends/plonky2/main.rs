use crate::backends::plonky2::basetypes::{Hash, Value, D, EMPTY_HASH, EMPTY_VALUE, F, VALUE_SIZE};
use crate::backends::plonky2::common::{
    CircuitBuilderPod, OperationTarget, StatementTarget, ValueTarget,
};
use crate::backends::plonky2::primitives::merkletree::MerkleProofExistenceCircuit;
use crate::backends::plonky2::primitives::merkletree::{MerkleProof, MerkleTree};
use crate::middleware::{
    hash_str, AnchoredKey, NativeOperation, NativePredicate, Operation, Params, PodType, Predicate,
    Statement, StatementArg, ToFields, KEY_TYPE, SELF, STATEMENT_ARG_F_LEN,
};
use anyhow::Result;
use itertools::Itertools;
use plonky2::{
    field::types::Field,
    hash::{
        hash_types::{HashOut, HashOutTarget},
        poseidon::PoseidonHash,
    },
    iop::{
        target::{BoolTarget, Target},
        witness::{PartialWitness, WitnessWrite},
    },
    plonk::circuit_builder::CircuitBuilder,
};
use std::collections::HashMap;

/// MerkleTree Max Depth
const MD: usize = 32;

//
// SignedPod verification
//

struct SignedPodVerifyGate {
    params: Params,
}

impl SignedPodVerifyGate {
    fn eval(&self, builder: &mut CircuitBuilder<F, D>) -> Result<SignedPodVerifyTarget> {
        // 2. Verify id
        let id = builder.add_virtual_hash();
        let mut mt_proofs = Vec::new();
        for _ in 0..self.params.max_signed_pod_values {
            let mt_proof = MerkleProofExistenceCircuit::<MD>::add_targets(builder)?;
            builder.connect_hashes(id, mt_proof.root);
            mt_proofs.push(mt_proof);
        }

        // 1. Verify type
        let type_mt_proof = &mt_proofs[0];
        let key_type = builder.constant_value(hash_str(KEY_TYPE).into());
        builder.connect_values(type_mt_proof.key, key_type);
        let value_type = builder.constant_value(Value::from(PodType::MockSigned));
        builder.connect_values(type_mt_proof.value, value_type);

        // 3. TODO: Verify signature

        Ok(SignedPodVerifyTarget {
            params: self.params.clone(),
            id,
            mt_proofs,
        })
    }
}

struct SignedPodVerifyTarget {
    params: Params,
    id: HashOutTarget,
    // The KEY_TYPE entry must be the first one
    // The KEY_SIGNER entry must be the second one
    mt_proofs: Vec<MerkleProofExistenceCircuit<MD>>,
}

struct SignedPodVerifyInput {
    kvs: HashMap<Value, Value>,
}

impl SignedPodVerifyTarget {
    fn kvs(&self) -> Vec<(ValueTarget, ValueTarget)> {
        let mut kvs = Vec::new();
        for mt_proof in &self.mt_proofs {
            kvs.push((mt_proof.key, mt_proof.value));
        }
        // TODO: when the slot is unused, do we force the kv to be (EMPTY, EMPTY), and then from
        // it get a ValueOf((id, EMPTY), EMPTY)?  Or should we keep some boolean flags for unused
        // slots and translate them to Statement::None instead?
        kvs
    }

    fn pub_statements(&self) -> Vec<StatementTarget> {
        // TODO: Here we need to use the self.id in the ValueOf statements
        todo!()
    }

    fn set_targets(&self, pw: &mut PartialWitness<F>, input: &SignedPodVerifyInput) -> Result<()> {
        assert!(input.kvs.len() <= self.params.max_signed_pod_values);
        let tree = MerkleTree::new(MD, &input.kvs)?;
        for (i, (k, v)) in input.kvs.iter().sorted_by_key(|kv| kv.0).enumerate() {
            let (_, proof) = tree.prove(&k)?;
            self.mt_proofs[i].set_targets(pw, tree.root(), proof, *k, *v)?;
        }
        // Padding
        for i in input.kvs.len()..self.params.max_signed_pod_values {
            // TODO: We need to disable the proofs for the unused slots.  We could add a flag
            // "enable" to the MerkleTree proof circuit that skips the verification when false.
            // self.mt_proofs[i].set_targets(pw, false, EMPTY_HASH, proof, *k, *v)?;
        }
        Ok(())
    }
}

//
// MainPod verification
//

struct OperationVerifyGate {
    params: Params,
}

impl OperationVerifyGate {
    fn eval(
        &self,
        builder: &mut CircuitBuilder<F, D>,
        st: &StatementTarget,
        op: &OperationTarget,
        prev_statements: &[StatementTarget],
    ) -> Result<OperationVerifyTarget> {
        // Verify that the operation `op` correctly generates the statement `st`.  The operation
        // can reference any of the `prev_statements`.
        // The verification may require aux data which needs to be stored in the
        // `OperationVerifyTarget` so that we can set during witness generation.

        // TODO: Figure out the right encoding of op.code
        let op_none = builder.constant(F::from_canonical_u64(NativeOperation::None as u64));
        let is_none = builder.is_equal(op.code[0], op_none);
        let op_new_entry =
            builder.constant(F::from_canonical_u64(NativeOperation::NewEntry as u64));
        let is_new_entry = builder.is_equal(op.code[0], op_new_entry);
        let op_copy_statement =
            builder.constant(F::from_canonical_u64(NativeOperation::CopyStatement as u64));
        let is_copy_statement = builder.is_equal(op.code[0], op_copy_statement);
        let op_eq_from_entries = builder.constant(F::from_canonical_u64(
            NativeOperation::EqualFromEntries as u64,
        ));
        let is_eq_from_entries = builder.is_equal(op.code[0], op_eq_from_entries);
        let op_gt_from_entries =
            builder.constant(F::from_canonical_u64(NativeOperation::GtFromEntries as u64));
        let is_gt_from_entries = builder.is_equal(op.code[0], op_gt_from_entries);
        let op_lt_from_entries =
            builder.constant(F::from_canonical_u64(NativeOperation::LtFromEntries as u64));
        let is_lt_from_entries = builder.is_equal(op.code[0], op_lt_from_entries);
        let op_contains_from_entries = builder.constant(F::from_canonical_u64(
            NativeOperation::ContainsFromEntries as u64,
        ));
        let is_contains_from_entries = builder.is_equal(op.code[0], op_contains_from_entries);

        let ok = builder._true();
        let none_ok = self.eval_none(builder, st, op);
        let ok = builder.select_bool(is_none, none_ok, ok);
        let new_entry_ok = self.eval_new_entry(builder, st, op);
        let ok = builder.select_bool(is_new_entry, new_entry_ok, ok);

        let _true = builder._true();
        builder.connect(ok.target, _true.target);

        todo!()
    }

    fn eval_none(
        &self,
        builder: &mut CircuitBuilder<F, D>,
        st: &StatementTarget,
        _op: &OperationTarget,
    ) -> BoolTarget {
        let expected_statement_flattened =
            builder.constants(&Statement::None.to_fields(&self.params));
        builder.is_equal_slice(&st.to_flattened(), &expected_statement_flattened)
    }

    fn eval_new_entry(
        &self,
        builder: &mut CircuitBuilder<F, D>,
        st: &StatementTarget,
        _op: &OperationTarget,
    ) -> BoolTarget {
        let value_of_st = &Statement::ValueOf(AnchoredKey(SELF, EMPTY_HASH), EMPTY_VALUE);
        let expected_code =
            builder.constants(&Predicate::Native(NativePredicate::ValueOf).to_fields(&self.params));
        let code_ok = builder.is_equal_slice(&st.code, &expected_code);
        let expected_arg_prefix = builder.constants(
            &StatementArg::Key(AnchoredKey(SELF, EMPTY_HASH)).to_fields(&self.params)[..VALUE_SIZE],
        );
        let arg_prefix_ok = builder.is_equal_slice(&st.args[0][..VALUE_SIZE], &expected_arg_prefix);
        builder.and(code_ok, arg_prefix_ok)
    }
}

struct OperationVerifyTarget {
    // TODO
}

struct OperationVerifyInputs {
    // TODO
}

impl OperationVerifyTarget {
    fn set_targets(&self, pw: &mut PartialWitness<F>, input: &OperationVerifyInputs) -> Result<()> {
        todo!()
    }
}

struct MainPodVerifyGate {
    params: Params,
}

impl MainPodVerifyGate {
    fn eval(&self, builder: &mut CircuitBuilder<F, D>) -> Result<MainPodVerifyTarget> {
        let params = &self.params;
        // 1. Verify all input signed pods
        let mut signed_pods = Vec::new();
        for _ in 0..params.max_input_signed_pods {
            let signed_pod = SignedPodVerifyGate {
                params: params.clone(),
            }
            .eval(builder)?;
            signed_pods.push(signed_pod);
        }

        // Build the statement array
        let mut statements = Vec::new();
        for signed_pod in &signed_pods {
            statements.extend_from_slice(signed_pod.pub_statements().as_slice());
        }

        // Add the input (private and public) statements and corresponding operations
        let mut operations = Vec::new();
        let input_statements_offset = statements.len();
        for _ in 0..params.max_statements {
            statements.push(builder.add_virtual_statement(params));
            operations.push(builder.add_virtual_operation(params));
        }

        let input_statements = &statements[input_statements_offset..];
        let pub_statements = &input_statements[statements.len() - params.max_public_statements..];

        // 2. Calculate the Pod Id from the public statements
        let pub_statements_flattened = pub_statements
            .iter()
            .map(|s| s.code.iter().chain(s.args.iter().flatten()))
            .flatten()
            .cloned()
            .collect();
        let id = builder.hash_n_to_hash_no_pad::<PoseidonHash>(pub_statements_flattened);

        // 3. TODO check that all `input_statements` of type `ValueOf` with origin=SELF have unique
        //    keys (no duplicates)

        // 4. Verify type
        let type_statement = &pub_statements[0];
        // TODO: Store this hash in a global static with lazy init so that we don't have to
        // compute it every time.
        let key_type = hash_str(KEY_TYPE);
        let expected_type_statement_flattened = builder.constants(
            &Statement::ValueOf(AnchoredKey(SELF, key_type), Value::from(PodType::MockMain))
                .to_fields(params),
        );
        builder.connect_slice(
            &type_statement.to_flattened(),
            &expected_type_statement_flattened,
        );

        // 5. Verify input statements
        let mut op_verifications = Vec::new();
        for (i, (st, op)) in input_statements.iter().zip(operations.iter()).enumerate() {
            let prev_statements = &statements[..input_statements_offset + i - 1];
            let op_verification = OperationVerifyGate {
                params: params.clone(),
            }
            .eval(builder, st, op, prev_statements)?;
            op_verifications.push(op_verification);
        }

        Ok(MainPodVerifyTarget {
            params: params.clone(),
            id,
            signed_pods,
            statements: input_statements.to_vec(),
            operations,
            op_verifications,
        })
    }
}

struct MainPodVerifyTarget {
    params: Params,
    id: HashOutTarget,
    signed_pods: Vec<SignedPodVerifyTarget>,
    // The KEY_TYPE statement must be the first public one
    statements: Vec<StatementTarget>,
    operations: Vec<OperationTarget>,
    op_verifications: Vec<OperationVerifyTarget>,
}

struct MainPodVerifyInput {
    signed_pods: Vec<SignedPodVerifyInput>,
}

impl MainPodVerifyTarget {
    fn set_targets(&self, pw: &mut PartialWitness<F>, input: &MainPodVerifyInput) -> Result<()> {
        assert!(input.signed_pods.len() <= self.params.max_input_signed_pods);
        for (i, signed_pod) in input.signed_pods.iter().enumerate() {
            self.signed_pods[i].set_targets(pw, signed_pod)?;
        }
        // Padding
        for i in input.signed_pods.len()..self.params.max_input_signed_pods {
            // TODO: We need to disable the verification for the unused slots.
            // self.signed_pods[i].set_targets(pw, signed_pod)?;
        }
        // TODO: set_targets for:
        // - statements
        // - operations
        // - op_verifications
        Ok(())
    }
}

struct MainPodVerifyCircuit {
    params: Params,
}

impl MainPodVerifyCircuit {
    fn eval(&self, builder: &mut CircuitBuilder<F, D>) -> Result<MainPodVerifyTarget> {
        let main_pod = MainPodVerifyGate {
            params: self.params.clone(),
        }
        .eval(builder)?;
        builder.register_public_inputs(&main_pod.id.elements);
        Ok(main_pod)
    }
}
