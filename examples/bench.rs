#![allow(clippy::uninlined_format_args)] // TODO: Remove this in another PR
//! Run: `cargo run --release --example bench`
use pod2::{
    backends::plonky2::{basetypes::DEFAULT_VD_SET, mainpod::Prover},
    frontend::MainPodBuilder,
    middleware::Params,
};

fn main() -> Result<(), Box<dyn std::error::Error>> {
    env_logger::init();

    let params = Params::default();

    let vd_set = &*DEFAULT_VD_SET;
    let prover = &Prover {};

    let mut builder = MainPodBuilder::new(&params, vd_set);
    let pod = builder.prove(prover).unwrap();
    assert!(pod.pod.verify().is_ok());

    Ok(())
}
