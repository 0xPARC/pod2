//! Simple example of building a signed pod and verifying it
//!
//! Run: `cargo run --release --example signed_pod`
use std::collections::HashSet;

use pod2::{
    backends::plonky2::{primitives::ec::schnorr::SecretKey, signedpod::Signer},
    frontend::SignedPodBuilder,
    middleware::{containers::Set, Params, Value},
};

fn main() -> Result<(), Box<dyn std::error::Error>> {
    let params = Params::default();

    // Create a schnorr key pair to sign the pod
    let sk = SecretKey::new_rand();
    let pk = sk.public_key();
    println!("Public key: {:?}\n", pk);

    let mut signer = Signer(sk);

    // Build the signed pod
    let mut builder = SignedPodBuilder::new(&params);
    // The values can be String, i64, bool, Array, Set, Dictionary, ...
    builder.insert("name", "Alice");
    builder.insert("lucky_number", 42);
    builder.insert("human", true);
    let friends_set: HashSet<Value> = ["Bob", "Charlie", "Dave"]
        .into_iter()
        .map(Value::from)
        .collect();
    builder.insert(
        "friends",
        Set::new(params.max_merkle_proofs_containers, friends_set)?,
    );

    // Sign the pod and verify it
    let pod = builder.sign(&mut signer)?;
    pod.verify()?;

    println!("{}", pod);

    Ok(())
}
