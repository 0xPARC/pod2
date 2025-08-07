use std::env;

use anyhow::anyhow;
use pod2::{
    backends::plonky2::{
        hash_common_data, mainpod::cache_get_rec_main_pod_verifier_circuit_data,
        recursion::circuit::hash_verifier_data,
    },
    middleware::{Hash, Params},
};
use serde::Serialize;
use sha2::{Digest, Sha256};

#[derive(Serialize)]
struct Info {
    params_hash: String,
    verifier_hash: Hash,
    common_hash: String,
}

fn main() -> anyhow::Result<()> {
    let args: Vec<String> = env::args().collect();

    let params = Params::default();
    match args.get(1).map(|s| s.as_str()) {
        Some("params") => {
            let params_json = serde_json::to_string_pretty(&params)?;
            println!("{params_json}");
        }
        Some("circuit-info") => {
            let params_json = serde_json::to_string(&params)?;
            let params_json_hash = Sha256::digest(&params_json);
            let params_json_hash_str_long = format!("{params_json_hash:x}");
            let params_json_hash_str = params_json_hash_str_long[..32].to_string();

            let vd = &*cache_get_rec_main_pod_verifier_circuit_data(&params);
            let info = Info {
                params_hash: params_json_hash_str,
                verifier_hash: Hash(hash_verifier_data(&vd.verifier_only).elements),
                common_hash: hash_common_data(&vd.common)?,
            };
            let json = serde_json::to_string_pretty(&info)?;
            println!("{json}");
        }
        _ => {
            return Err(anyhow!(
                "Invalid arguments.  Usage: {} params/circuit-info",
                args[0]
            ));
        }
    }
    Ok(())
}
