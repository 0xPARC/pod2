use std::{collections::HashMap, sync::Arc};

use crate::{
    frontend::{PodRequest, Result},
    lang::{load_module, parse_request, Module},
    middleware::{CustomPredicateBatch, Params},
};

/// Instantiates an ETHDos batch
pub fn eth_dos_batch(params: &Params) -> Result<Arc<CustomPredicateBatch>> {
    let input = r#"
        eth_friend(src, dst, private: attestation) = AND(
            SignedBy(attestation, src)
            Contains(attestation, "attestation", dst)
        )

        eth_dos_base(src, dst, distance) = AND(
            Equal(src, dst)
            Equal(distance, 0)
        )

        eth_dos_ind(src, dst, distance, private: shorter_distance, intermed) = AND(
            eth_dos(src, intermed, shorter_distance)
            SumOf(distance, shorter_distance, 1)
            eth_friend(intermed, dst)
        )

        eth_dos(src, dst, distance) = OR(
            eth_dos_base(src, dst, distance)
            eth_dos_ind(src, dst, distance)
        )
        "#;
    let module = load_module(input, "eth_dos", params, &[]).expect("lang parse");
    let batch = module.batch.clone();
    println!("a.0. {}", batch.predicates()[0]);
    println!("a.1. {}", batch.predicates()[1]);
    println!("a.2. {}", batch.predicates()[2]);
    println!("a.3. {}", batch.predicates()[3]);
    Ok(batch)
}

pub fn eth_dos_request() -> Result<PodRequest> {
    use hex::ToHex;

    let batch = eth_dos_batch(&Params::default())?;
    let eth_dos_module = Arc::new(Module::new(batch, HashMap::new()));
    let module_hash = eth_dos_module.id().encode_hex::<String>();

    let input = format!(
        r#"
        use module 0x{} as eth_dos
        REQUEST(
            eth_dos::eth_dos(src, dst, distance)
        )
        "#,
        module_hash
    );
    Ok(parse_request(
        &input,
        &Params::default(),
        &[eth_dos_module],
    )?)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_eth_friend_batch() {
        let params = Params::default();
        eth_dos_batch(&params).unwrap();
    }
}
