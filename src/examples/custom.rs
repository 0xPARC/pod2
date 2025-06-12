use std::{collections::HashMap, sync::Arc};

use tinytemplate::TinyTemplate;

use crate::{
    frontend::Result,
    lang::parse,
    middleware::{CustomPredicateBatch, Params, PodType, Value, KEY_SIGNER, KEY_TYPE},
};

fn render(tmpl: &str, consts: HashMap<&str, Value>) -> String {
    let mut tt = TinyTemplate::new();
    tt.set_default_formatter(&tinytemplate::format_unescaped);
    tt.add_template("tmpl", tmpl).expect("template parse");

    let mut context: HashMap<_, Value> = [
        ("KEY_TYPE", Value::from(KEY_TYPE)),
        ("KEY_SIGNER", Value::from(KEY_SIGNER)),
    ]
    .into_iter()
    .collect();

    for (name, value) in consts.into_iter() {
        context.insert(name, value);
    }
    let context: HashMap<_, String> = context
        .into_iter()
        .map(|(k, v)| (k, format!("{}", v)))
        .collect();
    tt.render("tmpl", &context).expect("template render")
}

/// Instantiates an ETHDos batch
pub fn eth_dos_batch(params: &Params, mock: bool) -> Result<Arc<CustomPredicateBatch>> {
    let pod_type = Value::from(if mock {
        PodType::MockSigned
    } else {
        PodType::Signed
    });
    let consts = [("pod_type", pod_type)].into_iter().collect();
    let input = render(
        r#"
        eth_friend(src, dst, private: attestation_pod) = AND(
            Equal(?attestation_pod[{KEY_TYPE}], {pod_type})
            Equal(?attestation_pod[{KEY_SIGNER}], ?src)
            Equal(?attestation_pod["attestation"], ?dst)
        )

        eth_dos_distance_base(src, dst, distance) = AND(
            Equal(?src, ?dst)
            Equal(?distance, 0)
        )

        eth_dos_distance_ind(src, dst, distance, private: shorter_distance, intermed) = AND(
            eth_dos_distance(?src, ?dst, ?distance)
            SumOf(?distance, ?shorter_distance, 1)
            eth_friend(?intermed, ?dst)
        )

        eth_dos_distance(src, dst, distance) = OR(
            eth_dos_distance_base(?src, ?dst, ?distance)
            eth_dos_distance_ind(?src, ?dst, ?distance)
        )
        "#,
        consts,
    );
    let batch = parse(&input, params).expect("lang parse").custom_batch;
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
        eth_dos_batch(&params, true).unwrap();
    }
}
