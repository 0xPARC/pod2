use crate::backends::plonky2::basetypes::{Hash, Value, D, EMPTY_HASH, EMPTY_VALUE, F, VALUE_SIZE};
use crate::backends::plonky2::common::{
    CircuitBuilderPod, OperationTarget, StatementTarget, ValueTarget,
};
use crate::backends::plonky2::mock_main::Operation;
use crate::backends::plonky2::primitives::merkletree::{MerkleProof, MerkleTree};
use crate::backends::plonky2::primitives::merkletree::{
    MerkleProofExistenceGate, MerkleProofExistenceTarget,
};
use crate::middleware::{
    hash_str, AnchoredKey, NativeOperation, NativePredicate, Params, PodType, Predicate, Statement,
    StatementArg, ToFields, KEY_TYPE, SELF, STATEMENT_ARG_F_LEN,
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
use std::iter;

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
            let mt_proof = MerkleProofExistenceGate {
                max_depth: self.params.max_depth_mt_gate,
            }
            .eval(builder)?;
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
    mt_proofs: Vec<MerkleProofExistenceTarget>,
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
        let tree = MerkleTree::new(self.params.max_depth_mt_gate, &input.kvs)?;

        // First handle the type entry, then the rest of the entries, and finally pad with
        // repetitions of the type entry (which always exists)
        let mut kvs = input.kvs.clone();
        let key_type = Value::from(hash_str(KEY_TYPE));
        let value_type = kvs.remove(&key_type).expect("KEY_TYPE");

        for (i, (k, v)) in iter::once((key_type, value_type))
            .chain(kvs.into_iter().sorted_by_key(|kv| kv.0))
            .chain(iter::repeat((key_type, value_type)))
            .take(self.params.max_signed_pod_values)
            .enumerate()
        {
            let (_, proof) = tree.prove(&k)?;
            self.mt_proofs[i].set_targets(pw, tree.root(), proof, k, v)?;
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
        let _true = builder._true();
        let _false = builder._false();
        let one = builder.constant(F::ONE);

        // Verify that the operation `op` correctly generates the statement `st`.  The operation
        // can reference any of the `prev_statements`.
        // The verification may require aux data which needs to be stored in the
        // `OperationVerifyTarget` so that we can set during witness generation.

        // For now only support native operations
        builder.connect(op.op_type[0], one);
        let native_op = op.op_type[1];

        let mut op_flags = Vec::new();
        let op_none = builder.constant(F::from_canonical_u64(NativeOperation::None as u64));
        let is_none = builder.is_equal(native_op, op_none);
        op_flags.push(is_none);
        let op_new_entry =
            builder.constant(F::from_canonical_u64(NativeOperation::NewEntry as u64));
        let is_new_entry = builder.is_equal(native_op, op_new_entry);
        op_flags.push(is_new_entry);
        let op_copy_statement =
            builder.constant(F::from_canonical_u64(NativeOperation::CopyStatement as u64));
        let is_copy_statement = builder.is_equal(native_op, op_copy_statement);
        op_flags.push(is_copy_statement);
        let op_eq_from_entries = builder.constant(F::from_canonical_u64(
            NativeOperation::EqualFromEntries as u64,
        ));
        let is_eq_from_entries = builder.is_equal(native_op, op_eq_from_entries);
        op_flags.push(is_eq_from_entries);
        let op_lt_from_entries =
            builder.constant(F::from_canonical_u64(NativeOperation::LtFromEntries as u64));
        let is_lt_from_entries = builder.is_equal(native_op, op_lt_from_entries);
        op_flags.push(is_lt_from_entries);
        let op_not_contains_from_entries = builder.constant(F::from_canonical_u64(
            NativeOperation::NotContainsFromEntries as u64,
        ));
        let is_not_contains_from_entries =
            builder.is_equal(native_op, op_not_contains_from_entries);
        op_flags.push(is_not_contains_from_entries);

        // One supported operation must be used.  We sum all operation flags and expect the result
        // to be 1.  Since the flags are boolean and at most one of them is true the sum is
        // equivalent to the OR.
        let or_op_flags = op_flags
            .iter()
            .map(|b| b.target)
            .fold(_false.target, |acc, x| builder.add(acc, x));
        builder.connect(or_op_flags, _true.target);

        let ok = builder._true();
        let none_ok = self.eval_none(builder, st, op);
        let ok = builder.select_bool(is_none, none_ok, ok);
        let new_entry_ok = self.eval_new_entry(builder, st, op);
        let ok = builder.select_bool(is_new_entry, new_entry_ok, ok);

        builder.connect(ok.target, _true.target);

        Ok(OperationVerifyTarget {})
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
        let expected_predicate =
            builder.constants(&Predicate::Native(NativePredicate::ValueOf).to_fields(&self.params));
        let predicate_ok = builder.is_equal_slice(&st.predicate, &expected_predicate);
        let expected_arg_prefix = builder.constants(
            &StatementArg::Key(AnchoredKey(SELF, EMPTY_HASH)).to_fields(&self.params)[..VALUE_SIZE],
        );
        let arg_prefix_ok = builder.is_equal_slice(&st.args[0][..VALUE_SIZE], &expected_arg_prefix);
        builder.and(predicate_ok, arg_prefix_ok)
    }
}

struct OperationVerifyTarget {
    // TODO
}

struct OperationVerifyInput {
    // TODO
}

impl OperationVerifyTarget {
    fn set_targets(&self, pw: &mut PartialWitness<F>, input: &OperationVerifyInput) -> Result<()> {
        // TODO
        Ok(())
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
            .map(|s| s.predicate.iter().chain(s.args.iter().flatten()))
            .flatten()
            .cloned()
            .collect();
        let id = builder.hash_n_to_hash_no_pad::<PoseidonHash>(pub_statements_flattened);

        // 3. TODO check that all `input_statements` of type `ValueOf` with origin=SELF have unique keys (no duplicates).  Maybe we can do this via the NewEntry operation (check that the key doesn't exist in a previous statement with ID=SELF)

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

pub struct MainPodVerifyCircuit {
    pub params: Params,
}

impl MainPodVerifyCircuit {
    pub fn eval(&self, builder: &mut CircuitBuilder<F, D>) -> Result<MainPodVerifyTarget> {
        let main_pod = MainPodVerifyGate {
            params: self.params.clone(),
        }
        .eval(builder)?;
        builder.register_public_inputs(&main_pod.id.elements);
        Ok(main_pod)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::backends::plonky2::basetypes::C;
    use crate::backends::plonky2::mock_main;
    use crate::middleware::OperationType;
    use plonky2::plonk::{circuit_builder::CircuitBuilder, circuit_data::CircuitConfig};

    #[test]
    fn test_signed_pod_verify() -> Result<()> {
        let params = Params::default();

        let config = CircuitConfig::standard_recursion_config();
        let mut builder = CircuitBuilder::<F, D>::new(config);

        let signed_pod_verify = SignedPodVerifyGate { params }.eval(&mut builder)?;

        let mut pw = PartialWitness::<F>::new();
        let kvs = [
            (
                Value::from(hash_str(KEY_TYPE)),
                Value::from(PodType::MockSigned),
            ),
            (Value::from(hash_str("foo")), Value::from(42)),
        ]
        .into();
        let input = SignedPodVerifyInput { kvs };
        signed_pod_verify.set_targets(&mut pw, &input)?;

        // generate & verify proof
        let data = builder.build::<C>();
        let proof = data.prove(pw)?;
        data.verify(proof)?;

        Ok(())
    }

    fn operation_verify(
        st: mock_main::Statement,
        op: mock_main::Operation,
        prev_statements: Vec<mock_main::Statement>,
    ) -> Result<()> {
        let params = Params::default();

        let config = CircuitConfig::standard_recursion_config();
        let mut builder = CircuitBuilder::<F, D>::new(config);

        let st_target = builder.add_virtual_statement(&params);
        let op_target = builder.add_virtual_operation(&params);
        let prev_statements_target: Vec<_> = (0..prev_statements.len())
            .map(|_| builder.add_virtual_statement(&params))
            .collect();

        let operation_verify = OperationVerifyGate {
            params: params.clone(),
        }
        .eval(
            &mut builder,
            &st_target,
            &op_target,
            &prev_statements_target,
        )?;

        let mut pw = PartialWitness::<F>::new();
        st_target.set_targets(&mut pw, &params, &st)?;
        op_target.set_targets(&mut pw, &params, &op)?;
        for (prev_st_target, prev_st) in prev_statements_target.iter().zip(prev_statements.iter()) {
            prev_st_target.set_targets(&mut pw, &params, prev_st)?;
        }
        let input = OperationVerifyInput {};
        operation_verify.set_targets(&mut pw, &input)?;

        // generate & verify proof
        let data = builder.build::<C>();
        let proof = data.prove(pw)?;
        data.verify(proof)?;

        Ok(())
    }

    #[test]
    fn test_operation_verify() -> Result<()> {
        // None
        let st: mock_main::Statement = Statement::None.into();
        let op = mock_main::Operation(OperationType::Native(NativeOperation::None), vec![]);
        let prev_statements = vec![Statement::None.into()];
        operation_verify(st, op, prev_statements)?;

        Ok(())
    }
}
