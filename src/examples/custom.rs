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
        &["id", "src_key", "dst_key"],
        // private arguments:
        &["attestation_pod"],
        // statement templates:
        &[
            // there is an attestation pod that's a SignedPod
            STB::new(NP::ValueOf)
                .arg(("attestation_pod", key(KEY_TYPE)))
                .arg(literal(pod_type)),
            // the attestation pod is signed by (src_or, src_key)
            STB::new(NP::Equal)
                .arg(("attestation_pod", key(KEY_SIGNER)))
                .arg(("id", "src_key")),
            // that same attestation pod has an "attestation"
            STB::new(NP::Equal)
                .arg(("attestation_pod", key("attestation")))
                .arg(("id", "dst_key")),
        ],
    )?;

    println!("a.0. eth_friend = {}", builder.predicates.last().unwrap());
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
            "id",
            "src_key",
            "dst_key",
            "distance_key",
        ],
        &[  // private arguments:
            ],
        &[
            // statement templates:
            STB::new(NP::Equal)
                .arg(("id", "src_key"))
                .arg(("id", "dst_key")),
            STB::new(NP::ValueOf)
                .arg(("id", "distance_key"))
                .arg(literal(0)),
        ],
    )?;
    println!(
        "b.0. eth_dos_distance_base = {}",
        builder.predicates.last().unwrap()
    );

    let eth_dos_distance = Predicate::BatchSelf(2);

    let eth_dos_distance_ind = builder.predicate_and(
        "eth_dos_distance_ind",
        &[
            // arguments:
            "id1",
            "id2",
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
            // FIXME: This is actually broken, if this statement was proved in another pod, then
            // the keys can have different values in SELF...  Can be fixed with
            // https://github.com/0xPARC/pod2/issues/229
            STB::new(eth_dos_distance)
                .arg("id1")
                .arg("src_key")
                .arg("intermed_key")
                .arg("shorter_distance_key"),
            // distance == shorter_distance + 1
            STB::new(NP::ValueOf)
                .arg(("id2", "one_key"))
                .arg(literal(1)),
            STB::new(NP::SumOf)
                .arg(("id2", "distance_key"))
                .arg(("id2", "shorter_distance_key"))
                .arg(("id2", "one_key")),
            // intermed is a friend of dst
            STB::new(eth_friend)
                .arg("id2")
                .arg("intermed_key")
                .arg("dst_key"),
            STB::new(NP::Equal)
                .arg(("id1", "src_key"))
                .arg(("id2", "src_key")),
            STB::new(NP::Equal)
                .arg(("id1", "intermed_key"))
                .arg(("id2", "intermed_key")),
            STB::new(NP::Equal)
                .arg(("id1", "shorter_distance_key"))
                .arg(("id2", "shorter_distance_key")),
        ],
    )?;

    println!(
        "b.1. eth_dos_distance_ind = {}",
        builder.predicates.last().unwrap()
    );

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

    println!(
        "b.2. eth_dos_distance = {}",
        builder.predicates.last().unwrap()
    );

    Ok(builder.finish())
}
