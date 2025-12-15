#![allow(clippy::uninlined_format_args)] // TODO: Remove this in another PR
//! Simple example of building a signed dict and verifying it
//!
//! Run: `cargo run --release --example signed_dict`
use std::collections::HashSet;

use pod2::{
    backends::plonky2::{primitives::ec::schnorr::SecretKey, signer::Signer},
    frontend::SignedDictBuilder,
    middleware::{containers::Set, Params, Value},
};

fn main() -> Result<(), Box<dyn std::error::Error>> {
    let params = Params::default();

    // Create a schnorr key pair to sign the dict
    let sk = SecretKey::new_rand();
    let pk = sk.public_key();
    println!("Public key: {}\n", pk);

    let signer = Signer(sk);

    // Build the signed dict
    let mut builder = SignedDictBuilder::new(&params);
    // The values can be String, i64, bool, Array, Set, Dictionary, ...
    builder.insert("name", "Alice");
    builder.insert("lucky_number", 42);
    builder.insert("human", true);
    let friends_set: HashSet<Value> = ["Bob", "Charlie", "Dave"]
        .into_iter()
        .map(Value::from)
        .collect();
    builder.insert("friends", Set::new(friends_set));

    // Sign the dict and verify it
    let signed_dict = builder.sign(&signer)?;
    signed_dict.verify()?;

    println!("{}", signed_dict);

    Ok(())
}
