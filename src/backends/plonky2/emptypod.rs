use std::{
    collections::HashMap,
    sync::{LazyLock, Mutex},
};

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
use serde::{Deserialize, Serialize};

use crate::{
    backends::plonky2::{
        basetypes::{Proof, C, D},
        circuits::{
            common::{Flattenable, StatementTarget},
            mainpod::{calculate_id_circuit, PI_OFFSET_ID},
        },
        deserialize_proof,
        error::{Error, Result},
        mainpod::{self, calculate_id},
        recursion::pad_circuit,
        serialize_proof, DEFAULT_PARAMS, STANDARD_REC_MAIN_POD_CIRCUIT_DATA,
    },
    middleware::{
        self, AnchoredKey, Hash, Params, Pod, PodId, PodType, RecursivePod, Statement, ToFields,
        VDSet, Value, VerifierOnlyCircuitData, F, HASH_SIZE, KEY_TYPE, SELF,
    },
    timed,
};

struct EmptyPodVerifyCircuit {
    params: Params,
}

fn type_statement() -> Statement {
    Statement::equal(
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
        let id = calculate_id_circuit(&self.params, builder, &[type_statement]);
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

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct EmptyPod {
    params: Params,
    id: PodId,
    vd_set: VDSet,
    proof: Proof,
}

type CircuitData = circuit_data::CircuitData<F, C, D>;

pub static STANDARD_EMPTY_POD_DATA: LazyLock<(EmptyPodVerifyTarget, CircuitData)> =
    LazyLock::new(|| build().expect("successful build"));

fn build() -> Result<(EmptyPodVerifyTarget, CircuitData)> {
    let params = &*DEFAULT_PARAMS;

    #[cfg(not(feature = "zk"))]
    let config = CircuitConfig::standard_recursion_config();
    #[cfg(feature = "zk")]
    let config = CircuitConfig::standard_recursion_zk_config();

    let mut builder = CircuitBuilder::<F, D>::new(config);
    let empty_pod_verify_target = EmptyPodVerifyCircuit {
        params: params.clone(),
    }
    .eval(&mut builder)?;
    let circuit_data = &*STANDARD_REC_MAIN_POD_CIRCUIT_DATA;
    pad_circuit(&mut builder, &circuit_data.common);

    let data = timed!("EmptyPod build", builder.build::<C>());
    assert_eq!(circuit_data.common, data.common);
    Ok((empty_pod_verify_target, data))
}

static EMPTY_POD_CACHE: LazyLock<Mutex<HashMap<Hash, EmptyPod>>> =
    LazyLock::new(|| Mutex::new(HashMap::new()));

impl EmptyPod {
    pub fn new(params: &Params, vd_set: VDSet) -> Result<EmptyPod> {
        let (empty_pod_verify_target, data) = &*STANDARD_EMPTY_POD_DATA;

        let mut pw = PartialWitness::<F>::new();
        empty_pod_verify_target.set_targets(&mut pw, vd_set.root())?;
        let proof = timed!("EmptyPod prove", data.prove(pw)?);
        let id = &proof.public_inputs[PI_OFFSET_ID..PI_OFFSET_ID + HASH_SIZE];
        let id = PodId(Hash([id[0], id[1], id[2], id[3]]));
        Ok(EmptyPod {
            params: params.clone(),
            id,
            vd_set,
            proof: proof.proof,
        })
    }
    pub fn new_boxed(params: &Params, vd_set: VDSet) -> Box<dyn RecursivePod> {
        let default_params = &*DEFAULT_PARAMS;
        assert_eq!(default_params.id_params(), params.id_params());

        let empty_pod = EMPTY_POD_CACHE
            .lock()
            .unwrap()
            .entry(vd_set.root())
            .or_insert_with(|| Self::new(params, vd_set).expect("prove EmptyPod"))
            .clone();
        Box::new(empty_pod)
    }
}

#[derive(Serialize, Deserialize)]
struct Data {
    proof: String,
}

impl Pod for EmptyPod {
    fn params(&self) -> &Params {
        &self.params
    }
    fn verify(&self) -> Result<()> {
        let statements = self
            .pub_self_statements()
            .into_iter()
            .map(mainpod::Statement::from)
            .collect_vec();
        let id = PodId(calculate_id(&statements, &self.params));
        if id != self.id {
            return Err(Error::id_not_equal(self.id, id));
        }

        let public_inputs = id
            .to_fields(&self.params)
            .iter()
            .chain(self.vd_set.root().0.iter())
            .cloned()
            .collect_vec();

        let (_, data) = &*STANDARD_EMPTY_POD_DATA;
        data.verify(ProofWithPublicInputs {
            proof: self.proof.clone(),
            public_inputs,
        })
        .map_err(|e| Error::plonky2_proof_fail("EmptyPod", e))
    }

    fn id(&self) -> PodId {
        self.id
    }
    fn pod_type(&self) -> (usize, &'static str) {
        (PodType::Empty as usize, "Empty")
    }

    fn pub_self_statements(&self) -> Vec<middleware::Statement> {
        vec![type_statement()]
    }

    fn serialize_data(&self) -> serde_json::Value {
        serde_json::to_value(Data {
            proof: serialize_proof(&self.proof),
        })
        .expect("serialization to json")
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
    fn vd_set(&self) -> &VDSet {
        &self.vd_set
    }
    fn deserialize_data(
        params: Params,
        data: serde_json::Value,
        vd_set: VDSet,
        id: PodId,
    ) -> Result<Box<dyn RecursivePod>> {
        let data: Data = serde_json::from_value(data)?;
        let circuit_data = &*STANDARD_REC_MAIN_POD_CIRCUIT_DATA;
        let proof = deserialize_proof(&circuit_data.common, &data.proof)?;
        Ok(Box::new(Self {
            params,
            id,
            vd_set,
            proof,
        }))
    }
}

#[cfg(test)]
pub mod tests {
    use super::*;

    #[test]
    fn test_empty_pod() {
        let params = Params::default();

        let empty_pod = EmptyPod::new_boxed(&params, VDSet::new(8, &[]).unwrap());
        empty_pod.verify().unwrap();
    }
}
