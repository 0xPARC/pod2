use std::{collections::HashMap, sync::Mutex};

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
            mainpod::{CalculateIdGadget, PI_OFFSET_ID},
        },
        deserialize_proof,
        error::{Error, Result},
        mainpod::{self, calculate_id},
        recursion::pad_circuit,
        serialize_proof, LazyLock, DEFAULT_PARAMS, STANDARD_REC_MAIN_POD_CIRCUIT_DATA,
    },
    middleware::{
        self, AnchoredKey, DynError, Hash, Params, Pod, PodId, PodType, RecursivePod, Statement,
        ToFields, Value, VerifierOnlyCircuitData, F, HASH_SIZE, KEY_TYPE, SELF,
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

type CircuitData = circuit_data::CircuitData<F, C, D>;

pub static STANDARD_EMPTY_POD_DATA: LazyLock<(EmptyPodVerifyTarget, CircuitData)> =
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

    let data = timed!("EmptyPod build", builder.build::<C>());
    assert_eq!(circuit_data.common, data.common);
    Ok((empty_pod_verify_target, data))
}

static EMPTY_POD_CACHE: LazyLock<Mutex<HashMap<Hash, EmptyPod>>> =
    LazyLock::new(|| Mutex::new(HashMap::new()));

impl EmptyPod {
    pub fn _prove(params: &Params, vds_root: Hash) -> Result<EmptyPod> {
        let (empty_pod_verify_target, data) = &*STANDARD_EMPTY_POD_DATA;

        let mut pw = PartialWitness::<F>::new();
        empty_pod_verify_target.set_targets(&mut pw, vds_root)?;
        let proof = timed!("EmptyPod prove", data.prove(pw)?);
        let id = &proof.public_inputs[PI_OFFSET_ID..PI_OFFSET_ID + HASH_SIZE];
        let id = PodId(Hash([id[0], id[1], id[2], id[3]]));
        Ok(EmptyPod {
            params: params.clone(),
            id,
            vds_root,
            proof: proof.proof,
        })
    }
    pub fn new_boxed(params: &Params, vds_root: Hash) -> Box<dyn RecursivePod> {
        let default_params = &*DEFAULT_PARAMS;
        assert_eq!(default_params.id_params(), params.id_params());

        let empty_pod = EMPTY_POD_CACHE
            .lock()
            .unwrap()
            .entry(vds_root)
            .or_insert_with(|| Self::_prove(params, vds_root).expect("prove EmptyPod"))
            .clone();
        Box::new(empty_pod)
    }
    fn _verify(&self) -> Result<()> {
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
            .chain(self.vds_root.0.iter())
            .cloned()
            .collect_vec();

        let (_, data) = &*STANDARD_EMPTY_POD_DATA;
        data.verify(ProofWithPublicInputs {
            proof: self.proof.clone(),
            public_inputs,
        })
        .map_err(|e| Error::custom(format!("EmptyPod proof verification failure: {:?}", e)))
    }

    pub(crate) fn deserialize(
        params: Params,
        id: PodId,
        vds_root: Hash,
        data: serde_json::Value,
    ) -> Result<Box<dyn RecursivePod>> {
        let data: Data = serde_json::from_value(data)?;
        let circuit_data = &*STANDARD_REC_MAIN_POD_CIRCUIT_DATA;
        let proof = deserialize_proof(&circuit_data.common, &data.proof)?;
        Ok(Box::new(Self {
            params,
            id,
            vds_root,
            proof,
        }))
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
    fn verify(&self) -> Result<(), Box<DynError>> {
        Ok(self._verify()?)
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
    fn vds_root(&self) -> Hash {
        self.vds_root
    }
}

#[cfg(test)]
pub mod tests {
    use super::*;
    use crate::middleware::EMPTY_HASH;

    #[test]
    fn test_empty_pod() {
        let params = Params::default();

        let empty_pod = EmptyPod::new_boxed(&params, EMPTY_HASH);
        empty_pod.verify().unwrap();
    }
}
