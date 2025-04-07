use std::sync::Arc;

use anyhow::Result;

use crate::{
    frontend::{
        literal, CustomPredicateBatch, CustomPredicateBatchBuilder, CustomPredicateRef,
        NativePredicate, Predicate, StatementTmplBuilder, Value,
    },
    middleware::{self, Params, PodType, KEY_SIGNER, KEY_TYPE},
};

use NativePredicate as NP;
use StatementTmplBuilder as STB;

/// Instantiates an ETH friend batch
pub fn eth_friend_batch(params: &Params) -> Result<Arc<CustomPredicateBatch>> {
    let mut builder = CustomPredicateBatchBuilder::new("eth_friend".into());
    let _eth_friend = builder.predicate_and(
        params,
        // arguments:
        &["src_ori", "src_key", "dst_ori", "dst_key"],
        // private arguments:
        &["attestation_pod"],
        // statement templates:
        &[
            // there is an attestation pod that's a SignedPod
            STB::new(NP::ValueOf)
                .arg(("attestation_pod", literal(KEY_TYPE)))
                .arg(middleware::Value::from(PodType::MockSigned)), // TODO
            // the attestation pod is signed by (src_or, src_key)
            STB::new(NP::Equal)
                .arg(("attestation_pod", literal(KEY_SIGNER)))
                .arg(("src_ori", "src_key")),
            // that same attestation pod has an "attestation"
            STB::new(NP::Equal)
                .arg(("attestation_pod", literal("attestation")))
                .arg(("dst_ori", "dst_key")),
        ],
        "eth_friend",
    )?;

    println!("a.0. eth_friend = {}", builder.predicates.last().unwrap());
    Ok(builder.finish())
}

/// Instantiates an ETHDoS batch
pub fn eth_dos_batch(params: &Params) -> Result<Arc<CustomPredicateBatch>> {
    let eth_friend = Predicate::Custom(CustomPredicateRef::new(eth_friend_batch(params)?, 0));
    let mut builder = CustomPredicateBatchBuilder::new("eth_dos_distance_base".into());

    // eth_dos_distance_base(src_or, src_key, dst_or, dst_key, distance_or, distance_key) = and<
    //   eq(src_or, src_key, dst_or, dst_key),
    //   ValueOf(distance_or, distance_key, 0)
    // >
    let eth_dos_distance_base = builder.predicate_and(
        params,
        &[
            // arguments:
            "src_ori",
            "src_key",
            "dst_ori",
            "dst_key",
            "distance_ori",
            "distance_key",
        ],
        &[  // private arguments:
            ],
        &[
            // statement templates:
            STB::new(NP::Equal)
                .arg(("src_ori", "src_key"))
                .arg(("dst_ori", "dst_key")),
            STB::new(NP::ValueOf)
                .arg(("distance_ori", "distance_key"))
                .arg(0),
        ],
        "eth_dos_distance_base",
    )?;
    println!(
        "b.0. eth_dos_distance_base = {}",
        builder.predicates.last().unwrap()
    );

    let eth_dos_distance = Predicate::BatchSelf(2);

    let eth_dos_distance_ind = builder.predicate_and(
        params,
        &[
            // arguments:
            "src_ori",
            "src_key",
            "dst_ori",
            "dst_key",
            "distance_ori",
            "distance_key",
        ],
        &[
            // private arguments:
            "one_ori",
            "one_key",
            "shorter_distance_ori",
            "shorter_distance_key",
            "intermed_ori",
            "intermed_key",
        ],
        &[
            // statement templates:
            STB::new(eth_dos_distance)
                .arg(("src_ori", "src_key"))
                .arg(("intermed_ori", "intermed_key"))
                .arg(("shorter_distance_ori", "shorter_distance_key")),
            // distance == shorter_distance + 1
            STB::new(NP::ValueOf).arg(("one_ori", "one_key")).arg(1),
            STB::new(NP::SumOf)
                .arg(("distance_ori", "distance_key"))
                .arg(("shorter_distance_ori", "shorter_distance_key"))
                .arg(("one_ori", "one_key")),
            // intermed is a friend of dst
            STB::new(eth_friend)
                .arg(("intermed_ori", "intermed_key"))
                .arg(("dst_ori", "dst_key")),
        ],
        "eth_dos_distance_ind",
    )?;

    println!(
        "b.1. eth_dos_distance_ind = {}",
        builder.predicates.last().unwrap()
    );

    let _eth_dos_distance = builder.predicate_or(
        params,
        &[
            "src_ori",
            "src_key",
            "dst_ori",
            "dst_key",
            "distance_ori",
            "distance_key",
        ],
        &[],
        &[
            STB::new(eth_dos_distance_base)
                .arg(("src_ori", "src_key"))
                .arg(("dst_ori", "dst_key"))
                .arg(("distance_ori", "distance_key")),
            STB::new(eth_dos_distance_ind)
                .arg(("src_ori", "src_key"))
                .arg(("dst_ori", "dst_key"))
                .arg(("distance_ori", "distance_key")),
        ],
        "eth_dos_distance",
    )?;

    println!(
        "b.2. eth_dos_distance = {}",
        builder.predicates.last().unwrap()
    );

    Ok(builder.finish())
}
