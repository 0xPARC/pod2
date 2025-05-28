use std::{
    collections::HashMap,
    sync::{MappedRwLockReadGuard, RwLock},
};

use base64::{prelude::BASE64_STANDARD, Engine};
use itertools::Itertools;
use plonky2::{
    hash::hash_types::HashOutTarget,
    iop::witness::{PartialWitness, WitnessWrite},
    plonk::{
        circuit_builder::CircuitBuilder,
        circuit_data::{self, CircuitConfig},
        proof::ProofWithPublicInputs,
    },
};

use crate::{
    backends::plonky2::{
        basetypes::{Proof, C, D},
        circuits::{
            common::{Flattenable, StatementTarget},
            mainpod::{CalculateIdGadget, PI_OFFSET_ID},
        },
        error::{Error, Result},
        mainpod::{self, calculate_id},
        recursion::pad_circuit,
        LazyLock, DEFAULT_PARAMS, STANDARD_REC_MAIN_POD_CIRCUIT_DATA,
    },
    middleware::{
        self, AnchoredKey, DynError, Hash, Params, Pod, PodId, PodType, RecursivePod, Statement,
        ToFields, Value, VerifierOnlyCircuitData, EMPTY_HASH, F, HASH_SIZE, KEY_TYPE, SELF,
    },
    timed,
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
        Ok(EmptyPodVerifyTarget { vds_root })
    }
}

pub struct EmptyPodVerifyTarget {
    vds_root: HashOutTarget,
}

impl EmptyPodVerifyTarget {
    pub fn set_targets(&self, pw: &mut PartialWitness<F>, vds_root: Hash) -> Result<()> {
        Ok(pw.set_target_arr(&self.vds_root.elements, &vds_root.0)?)
    }
}

#[derive(Clone, Debug)]
pub struct EmptyPod {
    params: Params,
    id: PodId,
    vds_root: Hash,
    proof: Proof,
}

// /// Pad the circuit to match a given `CommonCircuitData`.
// fn pad_circuit(builder: &mut CircuitBuilder<F, D>, common_data: &CommonCircuitData<F, D>) {
//     assert_eq!(common_data.config, builder.config);
//     assert_eq!(common_data.num_public_inputs, builder.num_public_inputs());
//     // TODO: We need to figure this out once we enable zero-knowledge
//     assert!(
//         !common_data.config.zero_knowledge,
//         "Degree calculation can be off if zero-knowledge is on."
//     );
//
//     let degree = common_data.degree();
//     // Need to account for public input hashing, a `PublicInputGate` and 32 `ConstantGate`.
//     // NOTE: the builder doesn't have any public method to see how many constants have been
//     // registered, so we can't know exactly how many `ConstantGates` will be required.  We hope
//     // that no more than 64 constants are used :pray:.  Maybe we should make a PR to plonky2 to
//     // expose this?
//     let num_noop_gate =
//         degree - builder.num_gates() - common_data.num_public_inputs.div_ceil(8) - 33;
//     for _ in 0..num_noop_gate {
//         builder.add_gate(NoopGate, vec![]);
//     }
//     for gate in &common_data.gates {
//         builder.add_gate_to_gate_set(gate.clone());
//     }
// }

use pretty_assertions::assert_eq;

type CircuitData = circuit_data::CircuitData<F, C, D>;

static STANDARD_EMPTY_POD_DATA: LazyLock<(EmptyPodVerifyTarget, CircuitData)> =
    LazyLock::new(|| build().expect("successful build"));

fn build() -> Result<(EmptyPodVerifyTarget, CircuitData)> {
    let params = &*DEFAULT_PARAMS;
    let config = CircuitConfig::standard_recursion_config();
    let mut builder = CircuitBuilder::<F, D>::new(config);
    let empty_pod_verify_target = EmptyPodVerifyCircuit {
        params: params.clone(),
    }
    .eval(&mut builder)?;
    let circuit_data = &*STANDARD_REC_MAIN_POD_CIRCUIT_DATA;
    pad_circuit(&mut builder, &circuit_data.common);
    // println!("DBG builder.num_gates={}", builder.num_gates());

    let data = timed!("EmptyPod build", builder.build::<C>());
    // println!(
    //     "DBG circuit_data.common.degree={}",
    //     circuit_data.common.degree()
    // );
    // println!("DBG         data.common.degree={}", data.common.degree());
    assert_eq!(circuit_data.common, data.common);
    Ok((empty_pod_verify_target, data))
}

// fn build(params: &Params) -> MappedRwLockReadGuard<(EmptyPodVerifyTarget, CircuitData)> {
//     get_or_set_map_cache("EmptyPod build", &EMPTY_POD_DATA, params, |params| {
//         _build(params).expect("successful build")
//     })
// }

impl EmptyPod {
    // TODO: Cache this by (params, vds_root)
    pub fn _prove(params: &Params, vds_root: Hash) -> Result<EmptyPod> {
        let (empty_pod_verify_target, data) = &*STANDARD_EMPTY_POD_DATA;

        let mut pw = PartialWitness::<F>::new();
        empty_pod_verify_target.set_targets(&mut pw, vds_root)?;
        let proof = timed!("EmptyPod prove", data.prove(pw)?);
        let id = &proof.public_inputs[PI_OFFSET_ID..PI_OFFSET_ID + HASH_SIZE];
        let id = PodId(Hash([id[0], id[1], id[2], id[3]]));
        // println!("DBG Empty Pod id={}, vds_root={}", id, vds_root);
        Ok(EmptyPod {
            params: params.clone(),
            id,
            vds_root,
            proof: proof.proof,
        })
    }
    pub fn new(params: &Params, vds_root: Hash) -> Result<Box<dyn RecursivePod>> {
        Ok(Self::_prove(params, vds_root).map(Box::new)?)
    }
    fn _verify(&self) -> Result<()> {
        let statements = self
            .pub_self_statements()
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

        let (_, data) = &*STANDARD_EMPTY_POD_DATA;
        data.verify(ProofWithPublicInputs {
            proof: self.proof.clone(),
            public_inputs,
        })
        .map_err(|e| Error::custom(format!("EmptyPod proof verification failure: {:?}", e)))
    }
}

impl Pod for EmptyPod {
    fn params(&self) -> &Params {
        &self.params
    }
    fn verify(&self) -> Result<(), Box<DynError>> {
        Ok(self._verify()?)
    }

    fn id(&self) -> PodId {
        self.id
    }

    fn pub_self_statements(&self) -> Vec<middleware::Statement> {
        vec![type_statement()]
    }

    fn serialized_proof(&self) -> String {
        let mut buffer = Vec::new();
        use plonky2::util::serialization::Write;
        buffer.write_proof(&self.proof).unwrap();
        BASE64_STANDARD.encode(buffer)
    }
}

impl RecursivePod for EmptyPod {
    fn verifier_data(&self) -> VerifierOnlyCircuitData {
        let (_, data) = &*STANDARD_EMPTY_POD_DATA;
        data.verifier_only.clone()
    }
    fn proof(&self) -> Proof {
        self.proof.clone()
    }
    fn vds_root(&self) -> Hash {
        self.vds_root
    }
}

#[cfg(test)]
pub mod tests {
    use super::*;

    #[test]
    fn test_empty_pod() {
        let params = Params::default();

        let empty_pod = EmptyPod::new(&params, EMPTY_HASH).unwrap();
        empty_pod.verify().unwrap();
    }
}
