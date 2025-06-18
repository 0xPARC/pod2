use std::sync::Arc;

use crate::{
    middleware::Pod,
    solver::{
        db::FactDB,
        engine::{semi_naive::SemiNaiveEngine, ProofRequest},
        error::SolverError,
        planner::Planner,
        proof::Proof,
        semantics::PodSemantics,
    },
};

pub mod db;
pub mod engine;
pub mod error;
pub mod ir;
pub mod planner;
pub mod proof;
pub mod semantics;

pub fn solve(request: &ProofRequest, pods: &[Box<dyn Pod>]) -> Result<Option<Proof>, SolverError> {
    let db = Arc::new(FactDB::build(pods.to_vec()).unwrap());
    let semantics = PodSemantics::new(db);

    let planner = Planner::new();
    let plan = planner.create_plan(request).unwrap();

    let engine = SemiNaiveEngine::new();

    engine.execute(&plan, &semantics)
}

#[cfg(test)]
mod tests {
    use hex::ToHex;

    use super::*;
    use crate::{
        backends::plonky2::mock::signedpod::MockSigner,
        examples::{attest_eth_friend, custom::eth_dos_batch},
        lang::parse,
        middleware::{hash_str, Params},
    };

    #[test]
    fn test_ethdos() {
        let _ = env_logger::builder().is_test(true).try_init();
        let params = Params {
            max_input_pods_public_statements: 8,
            max_statements: 24,
            max_public_statements: 8,
            ..Default::default()
        };

        let mut alice = MockSigner { pk: "Alice".into() };
        let mut bob = MockSigner { pk: "Bob".into() };
        let charlie = MockSigner {
            pk: "Charlie".into(),
        };
        let _david = MockSigner { pk: "David".into() };

        let alice_attestation = attest_eth_friend(&params, &mut alice, bob.public_key());
        let bob_attestation = attest_eth_friend(&params, &mut bob, charlie.public_key());
        let batch = eth_dos_batch(&params, true).unwrap();

        let req1 = format!(
            r#"
      use _, _, _, eth_dos from 0x{}
      
      REQUEST(
          eth_dos(0x{}, 0x{}, ?Distance)
      )
      "#,
            batch.id().encode_hex::<String>(),
            hash_str(&alice.pk).encode_hex::<String>(),
            hash_str(&charlie.pk).encode_hex::<String>()
        );

        let request = parse(&req1, &params, &[batch.clone()])
            .unwrap()
            .request_templates;

        let result = solve(&request, &[alice_attestation.pod, bob_attestation.pod]).unwrap();

        println!("Proof tree: {}", result.unwrap());
    }
}
