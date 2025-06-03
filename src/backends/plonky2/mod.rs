pub mod basetypes;
pub mod circuits;
pub mod emptypod;
mod error;
pub mod mainpod;
pub mod mock;
pub mod primitives;
pub mod recursion;
pub mod signedpod;

use std::sync::LazyLock;

pub use error::*;

use crate::{
    backends::plonky2::{
        basetypes::CircuitData,
        circuits::mainpod::{MainPodVerifyTarget, NUM_PUBLIC_INPUTS},
        recursion::RecursiveCircuit,
    },
    middleware::Params,
    timed,
};

pub static DEFAULT_PARAMS: LazyLock<Params> = LazyLock::new(Params::default);

pub static STANDARD_REC_MAIN_POD_CIRCUIT_DATA: LazyLock<CircuitData> = LazyLock::new(|| {
    let params = &*DEFAULT_PARAMS;
    timed!(
        "recursive MainPod circuit_data",
        RecursiveCircuit::<MainPodVerifyTarget>::target_and_circuit_data(
            params.max_input_recursive_pods,
            NUM_PUBLIC_INPUTS,
            params
        )
        .expect("calculate circuit_data")
        .1
    )
});
