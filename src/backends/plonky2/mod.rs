pub mod basetypes;
pub mod circuits;
pub mod emptypod;
mod error;
pub mod mainpod;
pub mod mock;
pub mod primitives;
pub mod recursion;
pub mod signedpod;

use std::sync::LazyLock;

use base64::{prelude::BASE64_STANDARD, Engine};
pub use error::*;
use plonky2::util::serialization::{Buffer, Read};

use crate::{
    backends::plonky2::{
        basetypes::{CircuitData, CommonCircuitData, Proof},
        circuits::mainpod::{MainPodVerifyTarget, NUM_PUBLIC_INPUTS},
        recursion::RecursiveCircuit,
    },
    middleware::Params,
    timed,
};

pub static DEFAULT_PARAMS: LazyLock<Params> = LazyLock::new(Params::default);

pub static STANDARD_REC_MAIN_POD_CIRCUIT_DATA: LazyLock<CircuitData> = LazyLock::new(|| {
    let params = &*DEFAULT_PARAMS;
    timed!(
        "recursive MainPod circuit_data",
        RecursiveCircuit::<MainPodVerifyTarget>::target_and_circuit_data(
            params.max_input_recursive_pods,
            NUM_PUBLIC_INPUTS,
            params
        )
        .expect("calculate circuit_data")
        .1
    )
});

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

pub fn serialize_proof(proof: &Proof) -> String {
    let mut buffer = Vec::new();
    use plonky2::util::serialization::Write;
    buffer.write_proof(proof).unwrap();
    serialize_bytes(&buffer)
}
