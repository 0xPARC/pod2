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
        cache_get_standard_rec_main_pod_common_circuit_data,
        circuits::{
            common::{Flattenable, StatementTarget},
            mainpod::{calculate_id_circuit, PI_OFFSET_ID},
        },
        deserialize_proof, deserialize_verifier_only,
        error::{Error, Result},
        hash_common_data,
        mainpod::{self, calculate_id},
        recursion::pad_circuit,
        serialization::{
            CircuitDataSerializer, VerifierCircuitDataSerializer, VerifierOnlyCircuitDataSerializer,
        },
        serialize_proof, serialize_verifier_only,
    },
    cache::{self, CacheEntry},
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

#[derive(Clone, Serialize, Deserialize)]
pub struct EmptyPodVerifyTarget {
    vds_root: HashOutTarget,
}

impl EmptyPodVerifyTarget {
    pub fn set_targets(&self, pw: &mut PartialWitness<F>, vds_root: Hash) -> Result<()> {
        Ok(pw.set_target_arr(&self.vds_root.elements, &vds_root.0)?)
    }
}

#[derive(Clone, Debug, Eq, PartialEq, Serialize, Deserialize)]
pub struct EmptyPod {
    params: Params,
    id: PodId,
    verifier_only: VerifierOnlyCircuitDataSerializer,
    common_hash: String,
    vd_set: VDSet,
    proof: Proof,
}

type CircuitData = circuit_data::CircuitData<F, C, D>;

pub fn cache_get_standard_empty_pod_circuit_data(
) -> CacheEntry<(EmptyPodVerifyTarget, CircuitDataSerializer)> {
    cache::get("standard_empty_pod_circuit_data", &(), |_| {
        let (target, circuit_data) = build().expect("successful build");
        (target, CircuitDataSerializer(circuit_data))
    })
    .expect("cache ok")
}

pub fn cache_get_standard_empty_pod_verifier_circuit_data(
) -> CacheEntry<VerifierCircuitDataSerializer> {
    cache::get("standard_empty_pod_verifier_circuit_data", &(), |_| {
        let (_, standard_empty_pod_circuit_data) = &*cache_get_standard_empty_pod_circuit_data();
        VerifierCircuitDataSerializer(standard_empty_pod_circuit_data.verifier_data().clone())
    })
    .expect("cache ok")
}

fn build() -> Result<(EmptyPodVerifyTarget, CircuitData)> {
    let params = Params::default();

    #[cfg(not(feature = "zk"))]
    let config = CircuitConfig::standard_recursion_config();
    #[cfg(feature = "zk")]
    let config = CircuitConfig::standard_recursion_zk_config();

    let mut builder = CircuitBuilder::<F, D>::new(config);
    let empty_pod_verify_target = EmptyPodVerifyCircuit {
        params: params.clone(),
    }
    .eval(&mut builder)?;
    let common_circuit_data = &*cache_get_standard_rec_main_pod_common_circuit_data();
    pad_circuit(&mut builder, common_circuit_data);

    let data = timed!("EmptyPod build", builder.build::<C>());
    assert_eq!(common_circuit_data.0, data.common);
    Ok((empty_pod_verify_target, data))
}

impl EmptyPod {
    fn new(params: &Params, vd_set: VDSet) -> Result<EmptyPod> {
        let (empty_pod_verify_target, data) = &*cache_get_standard_empty_pod_circuit_data();

        let mut pw = PartialWitness::<F>::new();
        empty_pod_verify_target.set_targets(&mut pw, vd_set.root())?;
        let proof = timed!("EmptyPod prove", data.prove(pw)?);
        let id = &proof.public_inputs[PI_OFFSET_ID..PI_OFFSET_ID + HASH_SIZE];
        let id = PodId(Hash([id[0], id[1], id[2], id[3]]));
        let common_hash = hash_common_data(&data.common).expect("hash ok");
        Ok(EmptyPod {
            params: params.clone(),
            verifier_only: VerifierOnlyCircuitDataSerializer(data.verifier_only.clone()),
            common_hash,
            id,
            vd_set,
            proof: proof.proof,
        })
    }
    pub fn new_boxed(params: &Params, vd_set: VDSet) -> Box<dyn RecursivePod> {
        let default_params = Params::default();
        assert_eq!(default_params.id_params(), params.id_params());

        let empty_pod = cache::get(
            "empty_pod",
            &(default_params, vd_set),
            |(params, vd_set)| Self::new(params, vd_set.clone()).expect("prove EmptyPod"),
        )
        .expect("cache ok");
        Box::new(empty_pod.clone())
    }
}

#[derive(Serialize, Deserialize)]
struct Data {
    proof: String,
    verifier_only: String,
    common_hash: String,
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

        let standard_empty_pod_verifier_data = cache_get_standard_empty_pod_verifier_circuit_data();
        standard_empty_pod_verifier_data
            .verify(ProofWithPublicInputs {
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
            verifier_only: serialize_verifier_only(&self.verifier_only),
            common_hash: self.common_hash.clone(),
        })
        .expect("serialization to json")
    }
}

impl RecursivePod for EmptyPod {
    fn verifier_data(&self) -> VerifierOnlyCircuitData {
        self.verifier_only.0.clone()
    }
    fn common_hash(&self) -> String {
        self.common_hash.clone()
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
        let common_circuit_data = cache_get_standard_rec_main_pod_common_circuit_data();
        let proof = deserialize_proof(&common_circuit_data, &data.proof)?;
        let verifier_only = deserialize_verifier_only(&data.verifier_only)?;
        Ok(Box::new(Self {
            params,
            id,
            verifier_only: VerifierOnlyCircuitDataSerializer(verifier_only),
            common_hash: data.common_hash,
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
