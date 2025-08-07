pub mod basetypes;
pub mod circuits;
pub mod emptypod;
mod error;
pub mod mainpod;
pub mod mock;
pub mod primitives;
pub mod recursion;
pub mod serialization;
pub mod signedpod;

use std::iter;

use base64::{prelude::BASE64_STANDARD, Engine};
pub use error::*;
use plonky2::{
    field::{
        extension::quadratic::QuadraticExtension,
        types::{Field, Field64},
    },
    hash::hash_types::HashOut,
    plonk::vars::EvaluationVars,
    util::serialization::{Buffer, Read},
};
use rand::prelude::*;
use rand_chacha::ChaCha20Rng;
use serde::{ser, Deserialize, Serialize};
use sha2::{Digest, Sha256};

use crate::{
    backends::plonky2::{
        basetypes::{CommonCircuitData, Proof, VerifierOnlyCircuitData, F},
        circuits::mainpod::{MainPodVerifyTarget, NUM_PUBLIC_INPUTS},
        recursion::RecursiveCircuit,
        serialization::{CommonCircuitDataSerializer, Pod2GateSerializer},
    },
    cache::{self, CacheEntry},
    middleware::Params,
    timed,
};

pub fn cache_get_standard_rec_main_pod_common_circuit_data(
) -> CacheEntry<CommonCircuitDataSerializer> {
    let params = Params::default();
    cache::get(
        "standard_rec_main_pod_common_circuit_data",
        &params,
        |params| {
            let circuit_data = timed!(
                "recursive MainPod circuit_data",
                RecursiveCircuit::<MainPodVerifyTarget>::target_and_circuit_data(
                    params.max_input_recursive_pods,
                    NUM_PUBLIC_INPUTS,
                    params
                )
                .expect("calculate circuit_data")
            );
            CommonCircuitDataSerializer(circuit_data.1.common)
        },
    )
    .expect("cache ok")
}

pub fn serialize_bytes(bytes: &[u8]) -> String {
    BASE64_STANDARD.encode(bytes)
}

pub fn deserialize_bytes(data: &str) -> Result<Vec<u8>> {
    BASE64_STANDARD.decode(data).map_err(|e| {
        Error::custom(format!(
            "Failed to decode data from base64: {}. Value: {}",
            e, data
        ))
    })
}

pub fn deserialize_proof(common: &CommonCircuitData, proof: &str) -> Result<Proof> {
    let decoded = deserialize_bytes(proof)?;
    let mut buf = Buffer::new(&decoded);
    let proof = buf.read_proof(common).map_err(|e| {
        Error::custom(format!(
            "Failed to read proof from buffer: {}. Value: {}",
            e, proof
        ))
    })?;

    Ok(proof)
}

pub fn serialize_verifier_only(verifier_only: &VerifierOnlyCircuitData) -> String {
    let bytes = verifier_only.to_bytes().expect("write to Vec");
    serialize_bytes(&bytes)
}

pub fn deserialize_verifier_only(verifier_only: &str) -> Result<VerifierOnlyCircuitData> {
    let decoded = deserialize_bytes(verifier_only)?;
    let verifier_only = VerifierOnlyCircuitData::from_bytes(&decoded).map_err(|e| {
        Error::custom(format!(
            "Failed to read VerifierOnlyCircuitData from buffer: {}. Value: {}",
            e, verifier_only
        ))
    })?;

    Ok(verifier_only)
}

pub fn serialize_proof(proof: &Proof) -> String {
    let mut buffer = Vec::new();
    use plonky2::util::serialization::Write;
    buffer.write_proof(proof).unwrap();
    serialize_bytes(&buffer)
}

fn rand_vec(rng: &mut impl RngCore, len: usize) -> Vec<F> {
    iter::repeat_with(|| rng.next_u64())
        .filter(|v| *v < F::ORDER)
        .map(F::from_canonical_u64)
        .take(len)
        .collect()
}

fn base(r: F, xs: &[F]) -> F {
    let mut res = F::ZERO;
    for x in xs.iter().rev() {
        res *= r;
        res += *x;
    }
    res
}

fn gate_fingerprints(common: &CommonCircuitData) -> Vec<(String, F)> {
    type Ext = QuadraticExtension<F>;
    let config = &common.config;
    let mut rng = ChaCha20Rng::seed_from_u64(42);
    let r = rand_vec(&mut rng, 1)[0];
    let local_constants: Vec<Ext> = rand_vec(&mut rng, config.num_constants)
        .into_iter()
        .map(Ext::from)
        .collect();
    let local_wires: Vec<Ext> = rand_vec(&mut rng, config.num_wires)
        .into_iter()
        .map(Ext::from)
        .collect();
    let public_inputs_hash = HashOut::from_vec(rand_vec(&mut rng, 4));
    let vars = EvaluationVars {
        local_constants: &local_constants,
        local_wires: &local_wires,
        public_inputs_hash: &public_inputs_hash,
    };
    let mut fingerprints = Vec::new();
    for gate in &common.gates {
        let eval: Vec<F> = gate
            .0
            .eval_unfiltered(vars)
            .into_iter()
            .map(|e| e.0[0])
            .collect();
        fingerprints.push((gate.0.id(), base(r, &eval)));
    }
    fingerprints
}

pub fn hash_common_data(common: &CommonCircuitData) -> serde_json::Result<String> {
    #[derive(Serialize, Deserialize)]
    pub struct CommonFingerprintData {
        common: String,
        gate_fingerprints: Vec<(String, F)>,
    }

    let gate_serializer = Pod2GateSerializer {};
    let bytes = common
        .to_bytes(&gate_serializer)
        .map_err(ser::Error::custom)?;
    let gate_fingerprints = gate_fingerprints(common);
    let data = CommonFingerprintData {
        common: serialize_bytes(&bytes),
        gate_fingerprints,
    };

    let json = serde_json::to_string(&data)?;
    let json_hash = Sha256::digest(&json);
    let json_hash_str_long = format!("{:x}", json_hash);
    let json_hash_str = json_hash_str_long[..32].to_string();
    Ok(json_hash_str)
}
