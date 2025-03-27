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

use crate::backends::plonky2::basetypes::{Hash, Value, D, EMPTY_HASH, EMPTY_VALUE, F, VALUE_SIZE};
use crate::backends::plonky2::circuits::common::{
    CircuitBuilderPod, OperationTarget, StatementTarget, ValueTarget,
};
use crate::backends::plonky2::primitives::merkletree::MerkleTree;
use crate::backends::plonky2::primitives::merkletree::{
    MerkleProofExistenceGadget, MerkleProofExistenceTarget,
};
use crate::middleware::{
    hash_str, AnchoredKey, NativeOperation, NativePredicate, Params, PodType, Statement,
    StatementArg, ToFields, KEY_TYPE, SELF,
};

use super::common::Flattenable;

//
// SignedPod verification
//

struct SignedPodVerifyGadget {
    params: Params,
}

impl SignedPodVerifyGadget {
    fn eval(&self, builder: &mut CircuitBuilder<F, D>) -> Result<SignedPodVerifyTarget> {
        // 2. Verify id
        let id = builder.add_virtual_hash();
        let mut mt_proofs = Vec::new();
        for _ in 0..self.params.max_signed_pod_values {
            let mt_proof = MerkleProofExistenceGadget {
                max_depth: self.params.max_depth_mt_gadget,
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
        let tree = MerkleTree::new(self.params.max_depth_mt_gadget, &input.kvs)?;

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

struct OperationVerifyGadget {
    params: Params,
}

impl OperationVerifyGadget {
    fn eval(
        &self,
        builder: &mut CircuitBuilder<F, D>,
        st: &StatementTarget,
        op: &OperationTarget,
        prev_statements: &[StatementTarget],
    ) -> Result<OperationVerifyTarget> {
        let _true = builder._true();
        let _false = builder._false();

        // Verify that the operation `op` correctly generates the statement `st`.  The operation
        // can reference any of the `prev_statements`.
        // TODO: Clean this up.
        let resolved_op_args = if prev_statements.len() == 0 {
            vec![]
        } else {
            op.args
                .iter()
                .flatten()
                .map(|&i| builder.vec_ref(prev_statements, i))
                .collect::<Vec<_>>()
        };

        // The verification may require aux data which needs to be stored in the
        // `OperationVerifyTarget` so that we can set during witness generation.

        // For now only support native operations
        // Op checks to carry out. Each 'eval_X' should be thought of
        // as 'eval' restricted to the op of type X, where the
        // returned target is `false` if the input targets lie outside
        // of the domain.
        let op_checks = vec![
            vec![
                self.eval_none(builder, st, op),
                self.eval_new_entry(builder, st, op, prev_statements),
            ],
            // Skip these if there are no resolved op args
            if resolved_op_args.len() == 0 {
                vec![]
            } else {
                vec![
                    self.eval_copy(builder, st, op, &resolved_op_args)?,
                    self.eval_eq_from_entries(builder, st, op, &resolved_op_args),
                    self.eval_lt_from_entries(builder, st, op, &resolved_op_args),
                ]
            },
        ]
        .concat();

        let ok = builder.any(op_checks);

        builder.connect(ok.target, _true.target);

        Ok(OperationVerifyTarget {})
    }

    fn eval_eq_from_entries(
        &self,
        builder: &mut CircuitBuilder<F, D>,
        st: &StatementTarget,
        op: &OperationTarget,
        resolved_op_args: &[StatementTarget],
    ) -> BoolTarget {
        let op_code_ok = op.has_native_type(builder, NativeOperation::EqualFromEntries);

        // Expect 2 op args of type `ValueOf`.
        let op_arg_type_checks = resolved_op_args
            .iter()
            .take(2)
            .map(|op_arg| op_arg.has_native_type(builder, &self.params, NativePredicate::ValueOf))
            .collect::<Vec<_>>();
        let op_arg_types_ok = builder.all(op_arg_type_checks);

        // The values embedded in the op args must match, the last
        // `STATEMENT_ARG_F_LEN - VALUE_SIZE` slots of each being 0.
        let arg1_value = resolved_op_args[0].args[1];
        let arg2_value = resolved_op_args[1].args[1];
        let op_arg_range_checks = [
            builder.statement_arg_is_value(&arg1_value),
            builder.statement_arg_is_value(&arg2_value),
        ];
        let op_arg_range_ok = builder.all(op_arg_range_checks);
        let op_args_eq =
            builder.is_equal_slice(&arg1_value[..VALUE_SIZE], &arg2_value[..VALUE_SIZE]);

        let arg1_key = resolved_op_args[0].args[0];
        let arg2_key = resolved_op_args[1].args[0];
        let expected_statement = StatementTarget::new_native(
            builder,
            &self.params,
            NativePredicate::Equal,
            &[arg1_key, arg2_key],
        );
        let st_ok = builder.is_equal_flattenable(st, &expected_statement);

        builder.all([
            op_code_ok,
            op_arg_types_ok,
            op_arg_range_ok,
            op_args_eq,
            st_ok,
        ])
    }

    fn eval_lt_from_entries(
        &self,
        builder: &mut CircuitBuilder<F, D>,
        st: &StatementTarget,
        op: &OperationTarget,
        resolved_op_args: &[StatementTarget],
    ) -> BoolTarget {
        let op_code_ok = op.has_native_type(builder, NativeOperation::LtFromEntries);

        // Expect 2 op args of type `ValueOf`.
        let op_arg_type_checks = resolved_op_args
            .iter()
            .take(2)
            .map(|op_arg| op_arg.has_native_type(builder, &self.params, NativePredicate::ValueOf))
            .collect::<Vec<_>>();
        let op_arg_types_ok = builder.all(op_arg_type_checks);

        // The values embedded in the op args must satisfy `<`, the
        // last `STATEMENT_ARG_F_LEN - VALUE_SIZE` slots of each being
        // 0.
        let arg1_value = resolved_op_args[0].args[1];
        let arg2_value = resolved_op_args[1].args[1];
        let op_arg_range_checks = [&arg1_value, &arg2_value]
            .into_iter()
            .map(|x| builder.statement_arg_is_value(x))
            .collect::<Vec<_>>();
        let op_arg_range_ok = builder.all(op_arg_range_checks);
        builder.assert_less_if(
            op_code_ok,
            ValueTarget::from_slice(&arg1_value[..VALUE_SIZE]),
            ValueTarget::from_slice(&arg2_value[..VALUE_SIZE]),
        );

        let arg1_key = resolved_op_args[0].args[0];
        let arg2_key = resolved_op_args[1].args[0];
        let expected_statement = StatementTarget::new_native(
            builder,
            &self.params,
            NativePredicate::Lt,
            &[arg1_key, arg2_key],
        );
        let st_ok = builder.is_equal_flattenable(st, &expected_statement);

        builder.all([op_code_ok, op_arg_types_ok, op_arg_range_ok, st_ok])
    }

    fn eval_none(
        &self,
        builder: &mut CircuitBuilder<F, D>,
        st: &StatementTarget,
        op: &OperationTarget,
    ) -> BoolTarget {
        let op_code_ok = op.has_native_type(builder, NativeOperation::None);

        let expected_statement =
            StatementTarget::new_native(builder, &self.params, NativePredicate::None, &[]);
        let st_ok = builder.is_equal_flattenable(st, &expected_statement);

        builder.all([op_code_ok, st_ok])
    }

    fn eval_new_entry(
        &self,
        builder: &mut CircuitBuilder<F, D>,
        st: &StatementTarget,
        op: &OperationTarget,
        prev_statements: &[StatementTarget],
    ) -> BoolTarget {
        let op_code_ok = op.has_native_type(builder, NativeOperation::NewEntry);

        let st_code_ok = st.has_native_type(builder, &self.params, NativePredicate::ValueOf);

        let expected_arg_prefix = builder.constants(
            &StatementArg::Key(AnchoredKey(SELF, EMPTY_HASH)).to_fields(&self.params)[..VALUE_SIZE],
        );
        let arg_prefix_ok = builder.is_equal_slice(&st.args[0][..VALUE_SIZE], &expected_arg_prefix);

        let dupe_check = {
            let individual_checks = prev_statements
                .into_iter()
                .map(|ps| {
                    let same_predicate = builder.is_equal_slice(&st.predicate, &ps.predicate);
                    let same_anchored_key = builder.is_equal_slice(&st.args[0], &ps.args[0]);
                    builder.and(same_predicate, same_anchored_key)
                })
                .collect::<Vec<_>>();
            builder.any(individual_checks)
        };

        let no_dupes_ok = builder.not(dupe_check);

        builder.all([op_code_ok, st_code_ok, arg_prefix_ok, no_dupes_ok])
    }

    fn eval_copy(
        &self,
        builder: &mut CircuitBuilder<F, D>,
        st: &StatementTarget,
        op: &OperationTarget,
        resolved_op_args: &[StatementTarget],
    ) -> Result<BoolTarget> {
        let op_code_ok = op.has_native_type(builder, NativeOperation::CopyStatement);

        let expected_statement = &resolved_op_args[0];
        let st_ok = builder.is_equal_flattenable(st, expected_statement);

        Ok(builder.all([op_code_ok, st_ok]))
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

struct MainPodVerifyGadget {
    params: Params,
}

impl MainPodVerifyGadget {
    fn eval(&self, builder: &mut CircuitBuilder<F, D>) -> Result<MainPodVerifyTarget> {
        let params = &self.params;
        // 1. Verify all input signed pods
        let mut signed_pods = Vec::new();
        for _ in 0..params.max_input_signed_pods {
            let signed_pod = SignedPodVerifyGadget {
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
        let expected_type_statement = StatementTarget::from_flattened(
            &builder.constants(
                &Statement::ValueOf(AnchoredKey(SELF, key_type), Value::from(PodType::MockMain))
                    .to_fields(params),
            ),
        );
        builder.connect_flattenable(type_statement, &expected_type_statement);

        // 5. Verify input statements
        let mut op_verifications = Vec::new();
        for (i, (st, op)) in input_statements.iter().zip(operations.iter()).enumerate() {
            let prev_statements = &statements[..input_statements_offset + i - 1];
            let op_verification = OperationVerifyGadget {
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
        let main_pod = MainPodVerifyGadget {
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
    use crate::backends::plonky2::mock::mainpod;
    use crate::backends::plonky2::{
        basetypes::C,
        mock::mainpod::{OperationArg, OperationAux},
    };
    use crate::middleware::{OperationType, PodId};
    use plonky2::plonk::{circuit_builder::CircuitBuilder, circuit_data::CircuitConfig};

    #[test]
    fn test_signed_pod_verify() -> Result<()> {
        let params = Params::default();

        let config = CircuitConfig::standard_recursion_config();
        let mut builder = CircuitBuilder::<F, D>::new(config);

        let signed_pod_verify = SignedPodVerifyGadget { params }.eval(&mut builder)?;

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
        st: mainpod::Statement,
        op: mainpod::Operation,
        prev_statements: Vec<mainpod::Statement>,
    ) -> Result<()> {
        let params = Params::default();

        let config = CircuitConfig::standard_recursion_config();
        let mut builder = CircuitBuilder::<F, D>::new(config);

        let st_target = builder.add_virtual_statement(&params);
        let op_target = builder.add_virtual_operation(&params);
        let prev_statements_target: Vec<_> = (0..prev_statements.len())
            .map(|_| builder.add_virtual_statement(&params))
            .collect();

        let operation_verify = OperationVerifyGadget {
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
        let st: mainpod::Statement = Statement::None.into();
        let op = mainpod::Operation(
            OperationType::Native(NativeOperation::None),
            vec![],
            OperationAux::None,
        );
        let prev_statements = vec![Statement::None.into()];
        operation_verify(st.clone(), op, prev_statements.clone())?;

        // NewEntry
        let st1: mainpod::Statement =
            Statement::ValueOf(AnchoredKey(SELF, "hello".into()), 55.into()).into();
        let op = mainpod::Operation(
            OperationType::Native(NativeOperation::NewEntry),
            vec![],
            OperationAux::None,
        );
        operation_verify(st1.clone(), op, vec![])?;

        // Copy
        let op = mainpod::Operation(
            OperationType::Native(NativeOperation::CopyStatement),
            vec![OperationArg::Index(0)],
            OperationAux::None,
        );
        operation_verify(st, op, prev_statements)?;

        // Eq
        let st2: mainpod::Statement = Statement::ValueOf(
            AnchoredKey(PodId(Value::from(75).into()), "hello".into()),
            55.into(),
        )
        .into();
        let st: mainpod::Statement = Statement::Equal(
            AnchoredKey(SELF, "hello".into()),
            AnchoredKey(PodId(Value::from(75).into()), "hello".into()),
        )
        .into();
        let op = mainpod::Operation(
            OperationType::Native(NativeOperation::EqualFromEntries),
            vec![OperationArg::Index(0), OperationArg::Index(1)],
            OperationAux::None,
        );
        let prev_statements = vec![st1.clone(), st2];
        operation_verify(st, op, prev_statements)?;

        // Lt
        let st2: mainpod::Statement = Statement::ValueOf(
            AnchoredKey(PodId(Value::from(88).into()), "hello".into()),
            56.into(),
        )
        .into();
        let st: mainpod::Statement = Statement::Lt(
            AnchoredKey(SELF, "hello".into()),
            AnchoredKey(PodId(Value::from(88).into()), "hello".into()),
        )
        .into();
        let op = mainpod::Operation(
            OperationType::Native(NativeOperation::LtFromEntries),
            vec![OperationArg::Index(0), OperationArg::Index(1)],
            OperationAux::None,
        );
        let prev_statements = vec![st1.clone(), st2];
        operation_verify(st, op, prev_statements)?;

        Ok(())
    }
}
