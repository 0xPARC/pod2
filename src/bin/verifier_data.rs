use std::iter;

use anyhow::anyhow;
use plonky2::{
    field::{
        extension::quadratic::QuadraticExtension,
        types::{Field, Field64},
    },
    hash::hash_types::HashOut,
    plonk::vars::EvaluationVars,
};
use pod2::{
    backends::plonky2::{
        basetypes::F, mainpod::cache_get_rec_main_pod_verifier_circuit_data,
        recursion::circuit::hash_verifier_data, serialization::Pod2GateSerializer, serialize_bytes,
    },
    middleware::{CommonCircuitData, Hash, Params},
};
use rand::prelude::*;
use rand_chacha::ChaCha20Rng;
use serde::{ser, Deserialize, Serialize};
use sha2::{Digest, Sha256};

type Ext = QuadraticExtension<F>;

fn rand_vec(rng: &mut impl RngCore, len: usize) -> Vec<F> {
    iter::repeat_with(|| rng.next_u64())
        .filter(|v| *v < F::ORDER)
        .map(|v| F::from_canonical_u64(v))
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
    let config = &common.config;
    let mut rng = ChaCha20Rng::seed_from_u64(42);
    let r = rand_vec(&mut rng, 1)[0];
    let local_constants: Vec<Ext> = rand_vec(&mut rng, config.num_constants)
        .into_iter()
        .map(|v| Ext::from(v))
        .collect();
    let local_wires: Vec<Ext> = rand_vec(&mut rng, config.num_wires)
        .into_iter()
        .map(|v| Ext::from(v))
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
            .eval_unfiltered(vars.clone())
            .into_iter()
            .map(|e| e.0[0])
            .collect();
        fingerprints.push((gate.0.id(), base(r, &eval)));
    }
    fingerprints
}

#[derive(Serialize)]
struct Data {
    vd_only_hash: Hash,
    vd_only: String,
    common: String,
    gate_fingerprints: Vec<(String, F)>,
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
    let gate_fingerprints = gate_fingerprints(&common);
    let data = CommonFingerprintData {
        common: serialize_bytes(&bytes),
        gate_fingerprints,
    };

    let json = serde_json::to_string(&data)?;
    let json_hash = Sha256::digest(&json);
    let json_hash_str_long = format!("{:x}", json_hash);
    let json_hash_str = format!("{}", &json_hash_str_long[..32]);
    Ok(json_hash_str)
}

fn main() -> anyhow::Result<()> {
    let params = Params::default();
    let vd = &*cache_get_rec_main_pod_verifier_circuit_data(&params);
    let gate_serializer = Pod2GateSerializer {};
    let json = serde_json::to_string_pretty(&Data {
        vd_only_hash: Hash(hash_verifier_data(&vd.verifier_only).elements),
        vd_only: serialize_bytes(
            &vd.verifier_only
                .to_bytes()
                .map_err(|err| anyhow!("{}", err))?,
        ),
        common: serialize_bytes(
            &vd.common
                .to_bytes(&gate_serializer)
                .map_err(|err| anyhow!("{}", err))?,
        ),
        gate_fingerprints: gate_fingerprints(&vd.common),
    })?;
    println!("{}", json);
    Ok(())
}
