use std::{any::Any, iter, sync::Arc};

use base64::{prelude::BASE64_STANDARD, Engine};
use itertools::Itertools;
use plonky2::{
    gates::noop::NoopGate,
    hash::poseidon::PoseidonHash,
    iop::witness::PartialWitness,
    plonk::{
        circuit_builder::CircuitBuilder,
        circuit_data::{CircuitConfig, CircuitData, CommonCircuitData, ProverCircuitData},
        config::Hasher,
        proof::{Proof, ProofWithPublicInputs},
    },
    util::serialization::{Buffer, Read},
};

use crate::{
    backends::plonky2::{
        basetypes::{C, D},
        circuits::{
            common::{Flattenable, StatementTarget},
            mainpod::{
                CalculateIdGadget, CustomPredicateVerification, MainPodVerifyCircuit,
                MainPodVerifyInput, MainPodVerifyTarget, NUM_PUBLIC_INPUTS, PI_OFFSET_ID,
            },
        },
        error::{Error, Result},
        mainpod,
        mainpod::{calculate_id, MainPodProof},
        primitives::merkletree::MerkleClaimAndProof,
        recursion::{self, RecursiveCircuit},
        signedpod::SignedPod,
    },
    middleware::{
        self, resolve_wildcard_values, AnchoredKey, CustomPredicateBatch, DynError, Hash,
        MainPodInputs, NativeOperation, NonePod, OperationType, Params, Pod, PodId, PodProver,
        PodType, Statement, StatementArg, ToFields, Value, EMPTY_HASH, F, HASH_SIZE, KEY_TYPE,
        SELF,
    },
};

struct EmptyPodVerifyCircuit {
    params: Params,
}

fn type_statement() -> Statement {
    Statement::ValueOf(
        AnchoredKey::from((SELF, KEY_TYPE)),
        Value::from(PodType::Empty),
    )
}

impl EmptyPodVerifyCircuit {
    fn eval(&self, builder: &mut CircuitBuilder<F, D>) -> Result<EmptyPodVerifyTarget> {
        let type_statement = StatementTarget::from_flattened(
            &self.params,
            &builder.constants(&type_statement().to_fields(&self.params)),
        );
        let id = CalculateIdGadget {
            params: self.params.clone(),
        }
        .eval(builder, &[type_statement]);
        let vds_root = builder.add_virtual_hash();
        builder.register_public_inputs(&id.elements);
        builder.register_public_inputs(&vds_root.elements);
        Ok(EmptyPodVerifyTarget {})
    }
}

pub struct EmptyPodVerifyTarget {}

#[derive(Clone, Debug)]
pub struct EmptyPod {
    params: Params,
    id: PodId,
    proof: MainPodProof,
}

// TODO: Cache this (this comes from the recursive circuit instantiated with the MainPod circuit)
fn get_circuit_data(params: &Params) -> Result<CircuitData<F, C, D>> {
    let circuit_data = RecursiveCircuit::<MainPodVerifyTarget>::circuit_data(
        params.max_input_main_pods,
        NUM_PUBLIC_INPUTS,
        params,
    )?;
    Ok(circuit_data)
}

/// Pad the circuit to match a given `CommonCircuitData`.
fn pad_circuit(builder: &mut CircuitBuilder<F, D>, common_data: &CommonCircuitData<F, D>) {
    assert_eq!(common_data.config, builder.config);
    assert_eq!(common_data.num_public_inputs, builder.num_public_inputs());
    // TODO: We need to figure this out once we enable zero-knowledge
    assert!(
        !common_data.config.zero_knowledge,
        "Degree calculation can be off if zero-knowledge is on."
    );

    let degree = common_data.degree();
    let num_noop_gate = degree - builder.num_gates();
    for _ in 0..num_noop_gate {
        builder.add_gate(NoopGate, vec![]);
    }
    for gate in &common_data.gates {
        builder.add_gate_to_gate_set(gate.clone());
    }
}

// TODO: Cache this
fn build(params: &Params) -> Result<CircuitData<F, C, D>> {
    let config = CircuitConfig::standard_recursion_config();
    let mut builder = CircuitBuilder::<F, D>::new(config);
    let _ = EmptyPodVerifyCircuit {
        params: params.clone(),
    }
    .eval(&mut builder)?;
    let circuit_data = get_circuit_data(params)?;
    pad_circuit(&mut builder, &circuit_data.common);

    let data = builder.build::<C>();
    assert_eq!(data.common, circuit_data.common);
    Ok(data)
}

impl EmptyPod {
    fn _prove(&mut self, params: &Params) -> Result<EmptyPod> {
        let data = build(params)?;

        let pw = PartialWitness::<F>::new();
        let proof = data.prove(pw)?;
        let id = &proof.public_inputs[PI_OFFSET_ID..PI_OFFSET_ID + HASH_SIZE];
        let id = PodId(Hash([id[0], id[1], id[2], id[3]]));
        Ok(EmptyPod {
            params: params.clone(),
            id,
            proof: proof.proof,
        })
    }
    fn new(&mut self, params: &Params) -> Result<Box<dyn Pod>, Box<DynError>> {
        Ok(self._prove(params).map(Box::new)?)
    }
    fn _verify(&self) -> Result<()> {
        let statements = self
            .pub_statements()
            .into_iter()
            .map(|st| mainpod::Statement::from(st))
            .collect_vec();
        let id = PodId(calculate_id(&statements, &self.params));
        if id != self.id {
            return Err(Error::id_not_equal(self.id, id));
        }

        let public_inputs = id
            .to_fields(&self.params)
            .iter()
            .chain(EMPTY_HASH.0.iter()) // slot for the unused vds root
            .cloned()
            .collect_vec();

        let data = build(&self.params)?;
        data.verify(ProofWithPublicInputs {
            proof: self.proof.clone(),
            public_inputs,
        })
        .map_err(|e| Error::custom(format!("EmptyPod proof verification failure: {:?}", e)))
    }
}

impl Pod for EmptyPod {
    fn verify(&self) -> Result<(), Box<DynError>> {
        Ok(self._verify()?)
    }

    fn id(&self) -> PodId {
        self.id
    }

    fn pub_statements(&self) -> Vec<middleware::Statement> {
        vec![type_statement()]
    }

    fn serialized_proof(&self) -> String {
        let mut buffer = Vec::new();
        use plonky2::util::serialization::Write;
        buffer.write_proof(&self.proof).unwrap();
        BASE64_STANDARD.encode(buffer)
    }
}
