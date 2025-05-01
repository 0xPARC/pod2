use crate::{
    backends::plonky2::mock::signedpod::MockSigner,
    frontend::{Result, SignedPod, SignedPodBuilder},
    middleware::{Params, Pod, PodId, Statement, Value},
    prover::indexing::ProverIndexes,
};

/// Creates a simple SignedPod for testing purposes using a mock signer.
///
/// # Arguments
///
/// * `params` - Middleware parameters.
/// * `kvs` - A slice of key-value pairs to insert into the pod. Keys are strings, values are `middleware::Value`.
/// * `signer_pk` - The public key string for the mock signer.
///
/// # Returns
///
/// A `Result` containing the created `frontend::SignedPod` or a frontend `Error`.
pub fn create_test_signed_pod(
    params: &Params,
    kvs: &[(&str, Value)],
    signer_pk: &str,
) -> Result<SignedPod> {
    let mut builder = SignedPodBuilder::new(params);
    for (key_str, value) in kvs {
        builder.insert(*key_str, value.clone());
    }

    let mut signer = MockSigner {
        pk: signer_pk.into(),
    };
    builder.sign(&mut signer) // Convert backend error to frontend::Error if necessary,
                              // assuming builder.sign returns a compatible Result type or we use .map_err
}

/// Creates a populated `ProverIndexes` instance from a list of test Pods.
///
/// # Arguments
///
/// * `params` - Middleware parameters.
/// * `pods` - A slice of references to trait objects (`&dyn Pod`) representing the test pods.
///
/// # Returns
///
/// A `ProverIndexes` instance populated with the public statements from the input pods.
pub fn setup_prover_indexes(params: Params, pods: &[&dyn Pod]) -> ProverIndexes {
    let all_facts: Vec<(PodId, Statement)> = pods
        .iter()
        .flat_map(|pod| {
            let pod_id = pod.id();
            pod.pub_statements()
                .into_iter()
                .map(move |stmt| (pod_id, stmt))
        })
        .collect();

    ProverIndexes::build(params, &all_facts)
}
// Other test utilities will go here...
