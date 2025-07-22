use std::sync::Arc;

use crate::{
    frontend::Result,
    lang::parse,
    middleware::{CustomPredicateBatch, Params, PodType, Value, KEY_SIGNER, KEY_TYPE},
};

macro_rules! render {
    ($tmpl: expr, $($arg:tt)*) => {{
        format!(
            $tmpl,
            KEY_TYPE = Value::from(KEY_TYPE),
            KEY_SIGNER = Value::from(KEY_SIGNER),
            $($arg)*
        )
    }};
}

/// Instantiates an ETHDos batch
pub fn eth_dos_batch(params: &Params) -> Result<Arc<CustomPredicateBatch>> {
    let input = render!(
        r#"
        eth_friend(src, dst, private: attestation_pod) = AND(
            Equal(?attestation_pod[{KEY_TYPE}], {pod_type})
            Equal(?attestation_pod[{KEY_SIGNER}], ?src)
            Equal(?attestation_pod["attestation"], ?dst)
        )

        eth_dos_base(src, dst, distance) = AND(
            Equal(?src, ?dst)
            Equal(?distance, 0)
        )

        eth_dos_ind(src, dst, distance, private: shorter_distance, intermed) = AND(
            eth_dos(?src, ?intermed, ?shorter_distance)
            SumOf(?distance, ?shorter_distance, 1)
            eth_friend(?intermed, ?dst)
        )

        eth_dos(src, dst, distance) = OR(
            eth_dos_base(?src, ?dst, ?distance)
            eth_dos_ind(?src, ?dst, ?distance)
        )
        "#,
        pod_type = Value::from(PodType::Signed),
    );
    let batch = parse(&input, params, &[]).expect("lang parse").custom_batch;
    println!("a.0. {}", batch.predicates[0]);
    println!("a.1. {}", batch.predicates[1]);
    println!("a.2. {}", batch.predicates[2]);
    println!("a.3. {}", batch.predicates[3]);
    Ok(batch)
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
