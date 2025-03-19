use crate::backends::plonky2::basetypes::{Hash, Value, D, EMPTY_HASH, EMPTY_VALUE, F, VALUE_SIZE};
use crate::backends::plonky2::common::{
    CircuitBuilderPod, OperationTarget, StatementTarget, ValueTarget,
};
use crate::backends::plonky2::mock_signed::MockSignedPod;
use crate::backends::plonky2::primitives::merkletree::MerkleProofExistenceCircuit;
use crate::backends::plonky2::primitives::merkletree::{MerkleProof, MerkleTree};
use crate::middleware::{
    hash_str, Operation, Params, PodType, Statement, KEY_TYPE, STATEMENT_ARG_F_LEN,
};
use anyhow::Result;
use itertools::Itertools;
use plonky2::field::extension::Extendable;
use plonky2::hash::hash_types::RichField;
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

const MD: usize = 32;

//
// SignedPod verification
//

struct SignedPodVerifyGate {
    params: Params,
}

impl SignedPodVerifyGate {
    fn eval(&self, builder: &mut CircuitBuilder<F, D>) -> Result<SignedPodVerifyTarget> {
        // Verify id
        let id = builder.add_virtual_hash();
        let mut mt_proofs = Vec::new();
        for _ in 0..self.params.max_signed_pod_values {
            let mt_proof = MerkleProofExistenceCircuit::<MD>::add_targets(builder)?;
            builder.connect_hashes(id, mt_proof.root);
            mt_proofs.push(mt_proof);
        }

        // Verify type
        let type_mt_proof = &mt_proofs[0];
        let key_type = builder.constant_value(hash_str(KEY_TYPE).into());
        builder.connect_values(type_mt_proof.key, key_type);
        let value_type = builder.constant_value(Value::from(PodType::MockSigned));
        builder.connect_values(type_mt_proof.value, value_type);

        // TODO: Verify signature

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
    // The KEY_TYPE proof must be the first one
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
        todo!()
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
        // Verify all input signed pods
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

        // Verify input statements
        let mut op_verifications = Vec::new();
        for (i, (st, op)) in input_statements.iter().zip(operations.iter()).enumerate() {
            let prev_statements = &statements[..input_statements_offset + i - 1];
            let op_verification = OperationVerifyGate {
                params: params.clone(),
            }
            .eval(builder, st, op, prev_statements)?;
            op_verifications.push(op_verification);
        }

        // Calculate the Pod Id from the public statements
        let pub_statements = &input_statements[statements.len() - params.max_public_statements..];
        let pub_statements_flat = pub_statements
            .iter()
            .map(|s| s.code.iter().chain(s.args.iter().flatten()))
            .flatten()
            .cloned()
            .collect();
        let id = builder.hash_n_to_hash_no_pad::<PoseidonHash>(pub_statements_flat);

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
