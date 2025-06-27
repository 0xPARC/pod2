use std::sync::Arc;

use crate::{
    frontend::Operation,
    middleware::{Params, PodId, StatementTmpl},
    solver::{
        db::{FactDB, IndexablePod},
        engine::semi_naive::SemiNaiveEngine,
        error::SolverError,
        metrics::{
            CounterMetrics, DebugMetrics, MetricsLevel, MetricsReport, MetricsSink, NoOpMetrics,
        },
        planner::{Planner, QueryPlan},
        proof::Proof,
        semantics::materializer::Materializer,
    },
};

pub mod db;
pub mod debug;
pub mod engine;
pub mod error;
pub mod explainer;
pub mod ir;
pub mod metrics;
pub mod planner;
pub mod proof;
pub mod semantics;
pub mod vis;

/// The main entry point for the solver.
///
/// Takes a proof request, a set of pods containing asserted facts, and runtime
/// parameters, and attempts to find a valid proof. It can be configured to
/// different levels of metrics during execution.
pub fn solve(
    request: &[StatementTmpl],
    pods: &[IndexablePod],
    params: &Params,
    metrics_level: MetricsLevel,
) -> Result<(Proof, MetricsReport), SolverError> {
    // Common setup logic that is independent of the metrics level.
    let db = Arc::new(FactDB::build(pods).unwrap());
    let materializer = Materializer::new(db.clone(), params);
    let planner = Planner::new();
    let plan = planner.create_plan(request).unwrap();

    // Dispatch to the appropriate generic implementation based on the desired
    // metrics level. This allows the compiler to monomorphize the engine's
    // execution path and eliminate the overhead of metrics collection when it
    // is not needed.
    match metrics_level {
        MetricsLevel::None => {
            let (proof, _) = run_solve(plan, materializer, NoOpMetrics)?;
            Ok((proof, MetricsReport::None))
        }
        MetricsLevel::Counters => {
            let (proof, metrics) = run_solve(plan, materializer, CounterMetrics::default())?;
            Ok((proof, MetricsReport::Counters(metrics)))
        }
        MetricsLevel::Debug => {
            let (proof, metrics) = run_solve(plan, materializer, DebugMetrics::default())?;
            Ok((proof, MetricsReport::Debug(metrics)))
        }
    }
}

/// The private, generic worker function for the solver.
///
/// This function is monomorphized by the compiler for each concrete `MetricsSink`
/// type, allowing for zero-cost static dispatch of metrics collection.
fn run_solve<M: MetricsSink>(
    plan: QueryPlan,
    materializer: Materializer,
    metrics: M,
) -> Result<(Proof, M), SolverError> {
    let mut engine = SemiNaiveEngine::new(metrics);

    let (all_facts, provenance) = engine.execute(&plan, &materializer)?;
    let proof = engine.reconstruct_proof(&all_facts, &provenance, &materializer)?;

    Ok((proof, engine.into_metrics()))
}

#[cfg(test)]
mod tests {
    use hex::ToHex;

    use super::*;
    use crate::{
        backends::plonky2::mock::{mainpod::MockProver, signedpod::MockSigner},
        examples::{
            attest_eth_friend, custom::eth_dos_batch, zu_kyc_sign_pod_builders, MOCK_VD_SET,
        },
        frontend::MainPodBuilder,
        lang::parse,
        middleware::Params,
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
          eth_dos({}, {}, ?Distance)
      )
      "#,
            batch.id().encode_hex::<String>(),
            alice.public_key(),
            bob.public_key()
        );

        let request = parse(&req1, &params, &[batch.clone()])
            .unwrap()
            .request_templates;

        let (result, metrics) = solve(
            &request,
            &[
                IndexablePod::signed_pod(&alice_attestation),
                IndexablePod::signed_pod(&bob_attestation),
            ],
            &params,
            MetricsLevel::Counters,
        )
        .unwrap();

        println!("Result: {:?}", result);
        println!("Metrics: {:?}", metrics);
        //println!("Proof tree: {}", result);
    }

    #[test]
    fn test_zukyc() {
        let _ = env_logger::builder().is_test(true).try_init();
        let params = Params::default();

        let const_18y = 1169909388;
        let const_1y = 1706367566;

        let (gov_id, pay_stub, sanction_list) = zu_kyc_sign_pod_builders(&params);
        let mut signer = MockSigner {
            pk: "ZooGov".into(),
        };
        let gov_id = gov_id.sign(&mut signer).unwrap();

        let mut signer = MockSigner {
            pk: "ZooDeel".into(),
        };
        let pay_stub = pay_stub.sign(&mut signer).unwrap();

        let mut signer = MockSigner {
            pk: "ZooOFAC".into(),
        };
        let sanction_list = sanction_list.sign(&mut signer).unwrap();

        let zukyc_request = format!(
            r#"
        REQUEST(
            NotContains(?sanctions["sanctionList"], ?gov["idNumber"])
            Lt(?gov["dateOfBirth"], {})
            Equal(?pay["startDate"], {})
            Equal(?gov["socialSecurityNumber"], ?pay["socialSecurityNumber"])
        )
        "#,
            const_18y, const_1y
        );

        let request = parse(&zukyc_request, &params, &[])
            .unwrap()
            .request_templates;

        let pods = [
            IndexablePod::signed_pod(&gov_id),
            IndexablePod::signed_pod(&pay_stub),
            IndexablePod::signed_pod(&sanction_list),
        ];

        let (result, _) = solve(&request, &pods, &params, MetricsLevel::Counters).unwrap();

        let prover = MockProver {};
        let mut builder = MainPodBuilder::new(&params, &MOCK_VD_SET);

        let (pod_ids, ops) = result.to_inputs();

        for (op, public) in ops {
            if public {
                builder.pub_op(op).unwrap();
            } else {
                builder.priv_op(op).unwrap();
            }
        }

        for pod_id in pod_ids {
            let pod = pods.iter().find(|p| p.id() == pod_id).unwrap();
            if let IndexablePod::SignedPod(pod) = pod {
                builder.add_signed_pod(pod);
            } else {
                panic!("Expected signed pod, got {:?}", pod);
            }
        }

        let kyc = builder.prove(&prover, &params).unwrap();

        println!("{}", kyc);
    }
}
