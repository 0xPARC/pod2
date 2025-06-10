use std::sync::Arc;

use StatementTmplBuilder as STB;

use crate::{
    frontend::{key, literal, CustomPredicateBatchBuilder, Result, StatementTmplBuilder},
    middleware::{
        CustomPredicateBatch, CustomPredicateRef, NativePredicate as NP, Params, PodType,
        Predicate, KEY_SIGNER, KEY_TYPE,
    },
};

/// Instantiates an ETH friend batch
pub fn eth_friend_batch(params: &Params, mock: bool) -> Result<Arc<CustomPredicateBatch>> {
    let pod_type = if mock {
        PodType::MockSigned
    } else {
        PodType::Signed
    };
    let mut builder = CustomPredicateBatchBuilder::new(params.clone(), "eth_friend".into());
    let _eth_friend = builder.predicate_and(
        "eth_friend",
        // arguments:
        &["src_key", "dst_key"],
        // private arguments:
        &["attestation_pod"],
        // statement templates:
        &[
            // there is an attestation pod that's a SignedPod
            STB::new(NP::Equal)
                .arg(("attestation_pod", key(KEY_TYPE)))
                .arg(literal(pod_type)),
            // the attestation pod is signed by (src_or, src_key)
            STB::new(NP::Equal)
                .arg(("attestation_pod", key(KEY_SIGNER)))
                .arg(("SELF", "src_key")),
            // that same attestation pod has an "attestation"
            STB::new(NP::Equal)
                .arg(("attestation_pod", key("attestation")))
                .arg(("SELF", "dst_key")),
        ],
    )?;

    println!("a.0. {}", builder.predicates.last().unwrap());
    Ok(builder.finish())
}

/// Instantiates an ETHDoS batch
pub fn eth_dos_batch(params: &Params, mock: bool) -> Result<Arc<CustomPredicateBatch>> {
    let eth_friend = Predicate::Custom(CustomPredicateRef::new(eth_friend_batch(params, mock)?, 0));
    let mut builder =
        CustomPredicateBatchBuilder::new(params.clone(), "eth_dos_distance_base".into());

    // eth_dos_distance_base(src_or, src_key, dst_or, dst_key, distance_or, distance_key) = and<
    //   eq(src_or, src_key, dst_or, dst_key),
    //   ValueOf(distance_or, distance_key, 0)
    // >
    let eth_dos_distance_base = builder.predicate_and(
        "eth_dos_distance_base",
        &[
            // arguments:
            "src_key",
            "dst_key",
            "distance_key",
        ],
        &[  // private arguments:
            ],
        &[
            // statement templates:
            STB::new(NP::Equal)
                .arg(("SELF", "src_key"))
                .arg(("SELF", "dst_key")),
            STB::new(NP::Equal)
                .arg(("SELF", "distance_key"))
                .arg(literal(0)),
        ],
    )?;
    println!("b.0. {}", builder.predicates.last().unwrap());

    let eth_dos_distance = Predicate::BatchSelf(2);

    let eth_dos_distance_ind = builder.predicate_and(
        "eth_dos_distance_ind",
        &[
            // arguments:
            "src_key",
            "dst_key",
            "distance_key",
        ],
        &[
            // private arguments:
            "one_key",
            "shorter_distance_key",
            "intermed_key",
        ],
        &[
            // statement templates:
            STB::new(eth_dos_distance)
                .arg("src_key")
                .arg("intermed_key")
                .arg("shorter_distance_key"),
            // distance == shorter_distance + 1
            STB::new(NP::Equal).arg(("SELF", "one_key")).arg(literal(1)),
            STB::new(NP::SumOf)
                .arg(("SELF", "distance_key"))
                .arg(("SELF", "shorter_distance_key"))
                .arg(("SELF", "one_key")),
            // intermed is a friend of dst
            STB::new(eth_friend).arg("intermed_key").arg("dst_key"),
        ],
    )?;

    println!("b.1. {}", builder.predicates.last().unwrap());

    let _eth_dos_distance = builder.predicate_or(
        "eth_dos_distance",
        &["src_key", "dst_key", "distance_key"],
        &[],
        &[
            STB::new(eth_dos_distance_base)
                .arg("src_key")
                .arg("dst_key")
                .arg("distance_key"),
            STB::new(eth_dos_distance_ind)
                .arg("src_key")
                .arg("dst_key")
                .arg("distance_key"),
        ],
    )?;

    println!("b.2. {}", builder.predicates.last().unwrap());

    Ok(builder.finish())
}
