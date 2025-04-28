use std::sync::Arc;

use crate::{
    frontend::{MainPod, SignedPod},
    middleware::{self, CustomPredicateBatch},
    prover::{error::ProverError, types::TranslationOutput},
};

/// Stage 1: Translation
///
/// Input:
///   - Frontend `SignedPod`s
///   - Frontend `MainPod`s
///   - `CustomPredicateBatch` definitions
///
/// Output:
///   - `TranslationOutput` containing:
///     - `custom_definitions`: A map from canonical custom predicate IDs (Vec<F>) to their definitions.
///     - `initial_facts`: A vector of all public statements from input PODs, paired with their origin `PodId`.
pub fn translate(
    signed_pods: &[SignedPod],
    main_pods: &[MainPod],
    custom_batches: &[Arc<CustomPredicateBatch>],
) -> Result<TranslationOutput, ProverError> {
    // TODO: Implement custom predicate parsing
    // TODO: Implement fact collection from pods
    unimplemented!("Translation stage not implemented yet");
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{
        backends::plonky2::mock::{mainpod::MockProver, signedpod::MockSigner},
        middleware::Params,
    };

    #[test]
    fn test_translation_basic() {
        let params = Params::default();
        let mut signer = MockSigner {
            pk: "test_signer".to_string(),
        };

        // Create dummy inputs
        let signed_pod_builder = crate::frontend::SignedPodBuilder::new(&params);
        // Add some values if needed
        let signed_pod = signed_pod_builder.sign(&mut signer).unwrap();

        let main_pod_builder = crate::frontend::MainPodBuilder::new(&params);
        // Add ops/statements if needed
        let main_pod = main_pod_builder.prove(&mut MockProver {}, &params).unwrap();

        let custom_batches = vec![]; // Add dummy custom batches if needed

        let result = translate(&[signed_pod], &[main_pod], &custom_batches);

        // Basic check: Ensure it doesn't panic (as it's unimplemented)
        assert!(result.is_err());
        if let Err(ProverError::Generic(msg)) = result {
            assert!(msg.contains("not implemented"));
        } else {
            panic!("Expected unimplemented error");
        }

        // TODO: Add more specific tests once implemented
        // assert!(result.is_ok());
        // let output = result.unwrap();
        // assert_eq!(output.custom_definitions.len(), 0);
        // assert!(!output.initial_facts.is_empty());
    }
}
