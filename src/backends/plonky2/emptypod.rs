use itertools::Itertools;
use plonky2::{
    hash::hash_types::HashOutTarget,
    iop::witness::{PartialWitness, WitnessWrite},
    plonk::{
        circuit_data::{self, CircuitConfig},
        proof::ProofWithPublicInputs,
    },
};
use serde::{Deserialize, Serialize};

use crate::{
    backends::plonky2::{
        basetypes::{CircuitBuilder, Proof, C, D},
        cache_get_standard_rec_main_pod_common_circuit_data,
        circuits::{
            common::{Flattenable, StatementTarget},
            mainpod::{calculate_statements_hash_circuit, PI_OFFSET_STATEMENTS_HASH},
        },
        deserialize_proof, deserialize_verifier_only,
        error::{Error, Result},
        hash_common_data,
        mainpod::{self, calculate_statements_hash},
        recursion::pad_circuit,
        serialization::{
            CircuitDataSerializer, VerifierCircuitDataSerializer, VerifierOnlyCircuitDataSerializer,
        },
        serialize_proof, serialize_verifier_only,
    },
    cache::{self, CacheEntry},
    middleware::{
        self, Hash, IntroPredicateRef, Params, Pod, PodType, Statement, ToFields, VDSet,
        VerifierOnlyCircuitData, EMPTY_HASH, F, HASH_SIZE,
    },
    timed,
};

fn empty_statement() -> Statement {
    Statement::Intro(
        IntroPredicateRef {
            name: "empty".to_string(),
            args_len: 0,
            verifier_data_hash: EMPTY_HASH,
        },
        vec![],
    )
}

#[derive(Clone, Serialize, Deserialize)]
pub struct EmptyPodVerifyTarget {
    vds_root: HashOutTarget,
}

impl EmptyPodVerifyTarget {
    pub fn new_virtual(builder: &mut CircuitBuilder) -> Self {
        Self {
            vds_root: builder.add_virtual_hash(),
        }
    }
    pub fn set_targets(&self, pw: &mut PartialWitness<F>, vds_root: Hash) -> Result<()> {
        Ok(pw.set_target_arr(&self.vds_root.elements, &vds_root.0)?)
    }
}

fn verify_empty_pod_circuit(
    params: &Params,
    builder: &mut CircuitBuilder,
    empty_pod: &EmptyPodVerifyTarget,
) {
    let empty_statement = StatementTarget::from_flattened(
        params,
        &builder.constants(&empty_statement().to_fields(params)),
    );
    let sts_hash = calculate_statements_hash_circuit(params, builder, &[empty_statement]);
    builder.register_public_inputs(&sts_hash.elements);
    builder.register_public_inputs(&empty_pod.vds_root.elements);
}

#[derive(Clone, Debug, Eq, PartialEq, Serialize, Deserialize)]
pub struct EmptyPod {
    params: Params,
    sts_hash: Hash,
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

    let mut builder = CircuitBuilder::new(config);
    let empty_pod = EmptyPodVerifyTarget::new_virtual(&mut builder);
    verify_empty_pod_circuit(&params, &mut builder, &empty_pod);
    let common_circuit_data = &*cache_get_standard_rec_main_pod_common_circuit_data();
    pad_circuit(&mut builder, common_circuit_data);

    let data = timed!("EmptyPod build", builder.build::<C>());
    assert_eq!(common_circuit_data.0, data.common);
    Ok((empty_pod, data))
}

impl EmptyPod {
    fn new(params: &Params, vd_set: VDSet) -> Result<EmptyPod> {
        let (empty_pod_verify_target, data) = &*cache_get_standard_empty_pod_circuit_data();

        let mut pw = PartialWitness::<F>::new();
        empty_pod_verify_target.set_targets(&mut pw, vd_set.root())?;
        let proof = timed!("EmptyPod prove", data.prove(pw)?);
        let sts_hash = {
            let v = &proof.public_inputs
                [PI_OFFSET_STATEMENTS_HASH..PI_OFFSET_STATEMENTS_HASH + HASH_SIZE];
            Hash([v[0], v[1], v[2], v[3]])
        };
        let common_hash = hash_common_data(&data.common).expect("hash ok");
        Ok(EmptyPod {
            params: params.clone(),
            verifier_only: VerifierOnlyCircuitDataSerializer(data.verifier_only.clone()),
            common_hash,
            sts_hash,
            vd_set,
            proof: proof.proof,
        })
    }
    pub fn new_boxed(params: &Params, vd_set: VDSet) -> Box<dyn Pod> {
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
        let sts_hash = calculate_statements_hash(&statements, &self.params);
        if sts_hash != self.sts_hash {
            return Err(Error::statements_hash_not_equal(self.sts_hash, sts_hash));
        }

        let public_inputs = sts_hash
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

    fn statements_hash(&self) -> Hash {
        self.sts_hash
    }
    fn pod_type(&self) -> (usize, &'static str) {
        (PodType::Empty as usize, "Empty")
    }

    fn pub_self_statements(&self) -> Vec<middleware::Statement> {
        vec![empty_statement()]
    }

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

    fn serialize_data(&self) -> serde_json::Value {
        serde_json::to_value(Data {
            proof: serialize_proof(&self.proof),
            verifier_only: serialize_verifier_only(&self.verifier_only),
            common_hash: self.common_hash.clone(),
        })
        .expect("serialization to json")
    }
    fn deserialize_data(
        params: Params,
        data: serde_json::Value,
        vd_set: VDSet,
        sts_hash: Hash,
    ) -> Result<Self> {
        let data: Data = serde_json::from_value(data)?;
        let common_circuit_data = cache_get_standard_rec_main_pod_common_circuit_data();
        let proof = deserialize_proof(&common_circuit_data, &data.proof)?;
        let verifier_only = deserialize_verifier_only(&data.verifier_only)?;
        Ok(Self {
            params,
            sts_hash,
            verifier_only: VerifierOnlyCircuitDataSerializer(verifier_only),
            common_hash: data.common_hash,
            vd_set,
            proof,
        })
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
