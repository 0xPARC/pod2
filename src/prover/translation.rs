use std::{collections::HashMap, sync::Arc};

use crate::{
    frontend::{MainPod, SignedPod},
    middleware::{CustomPredicateBatch, CustomPredicateRef, Params, Predicate, ToFields},
    prover::{
        error::ProverError,
        types::{CustomDefinitions, InitialFacts, TranslationOutput},
    },
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
    params: &Params,
    signed_pods: &[SignedPod],
    main_pods: &[MainPod],
    custom_batches: &[Arc<CustomPredicateBatch>],
) -> Result<TranslationOutput, ProverError> {
    let mut custom_definitions: CustomDefinitions = HashMap::new();

    for batch in custom_batches {
        for (index, predicate_def) in batch.predicates.iter().enumerate() {
            // Create the Predicate::Custom variant representing this definition
            let predicate_ref = CustomPredicateRef {
                batch: batch.clone(),
                index,
            };
            let predicate = Predicate::Custom(predicate_ref);

            // Calculate the canonical ID
            let canonical_id = predicate.to_fields(params);

            // Store the definition and the Arc to the batch, keyed by its ID
            custom_definitions.insert(canonical_id, (predicate_def.clone(), batch.clone()));
        }
    }

    let mut initial_facts: InitialFacts = Vec::new();

    // Collect facts from SignedPods
    for signed_pod in signed_pods {
        let pod_id = signed_pod.id();
        for key in signed_pod.kvs().keys() {
            initial_facts.push((pod_id, signed_pod.get_statement(key.clone()).unwrap()));
        }
    }

    // Collect facts from MainPods
    for main_pod in main_pods {
        let pod_id = main_pod.id();
        for statement in main_pod.public_statements.iter() {
            if !statement.is_none() {
                initial_facts.push((pod_id, statement.clone()));
            }
        }
    }

    Ok(TranslationOutput {
        custom_definitions,
        initial_facts,
    })
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{
        backends::plonky2::mock::{mainpod::MockProver, signedpod::MockSigner},
        frontend::{MainPodBuilder, SignedPodBuilder},
        middleware::{Key, PodType, Statement, Value, KEY_SIGNER, KEY_TYPE},
    };

    #[test]
    fn test_translation_basic() {
        let params = Params::default();
        let signer_pk = "test_signer".to_string();
        let mut signer = MockSigner {
            pk: signer_pk.clone(),
        };

        // Create dummy inputs
        let mut signed_pod_builder = SignedPodBuilder::new(&params);
        signed_pod_builder.insert("data", Value::from(123));
        let signed_pod = signed_pod_builder.sign(&mut signer).unwrap();
        let signed_pod_id = signed_pod.id();

        let mut main_pod_builder = MainPodBuilder::new(&params);
        // Add a public statement to the main pod for testing
        let lit_stmt = main_pod_builder.pub_literal(Value::from(456)).unwrap();
        let main_pod = main_pod_builder.prove(&mut MockProver {}, &params).unwrap();
        let main_pod_id = main_pod.id();

        let custom_batches = vec![]; // No custom batches for this test

        let result = translate(
            &params,
            &[signed_pod.clone()],
            &[main_pod.clone()],
            &custom_batches,
        );

        assert!(result.is_ok());
        let output = result.unwrap();

        // Check custom definitions
        assert!(output.custom_definitions.is_empty());

        // Check initial facts
        // Expecting: _signer, _type, data from signed pod
        // Expecting: _type, and the public literal from main pod
        assert_eq!(output.initial_facts.len(), 3 + 2);

        // Check some specific facts
        let signer_key = Key::from(KEY_SIGNER);
        let type_key = Key::from(KEY_TYPE);
        let data_key = Key::from("data");
        let const_key = lit_stmt.args()[0].key().unwrap().key; // Key generated for the literal

        let has_signed_signer = output.initial_facts.iter().any(|(id, stmt)| {
            *id == signed_pod_id
                && matches!(stmt, Statement::ValueOf(ak, _v) if ak.key == signer_key)
        });
        let has_signed_type = output.initial_facts.iter().any(|(id, stmt)| {
             *id == signed_pod_id && matches!(stmt, Statement::ValueOf(ak, v) if ak.key == type_key && v == &Value::from(PodType::MockSigned))
        });
        let has_signed_data = output.initial_facts.iter().any(|(id, stmt)| {
             *id == signed_pod_id && matches!(stmt, Statement::ValueOf(ak, v) if ak.key == data_key && v == &Value::from(123))
        });
        let has_main_type = output.initial_facts.iter().any(|(id, stmt)| {
             *id == main_pod_id && matches!(stmt, Statement::ValueOf(ak, v) if ak.key == type_key && v == &Value::from(PodType::MockMain))
        });
        let has_main_literal = output.initial_facts.iter().any(|(id, stmt)| {
             *id == main_pod_id && matches!(stmt, Statement::ValueOf(ak, v) if ak.key == const_key && v == &Value::from(456))
        });

        assert!(has_signed_signer, "Missing signed pod signer fact");
        assert!(has_signed_type, "Missing signed pod type fact");
        assert!(has_signed_data, "Missing signed pod data fact");
        assert!(has_main_type, "Missing main pod type fact");
        assert!(has_main_literal, "Missing main pod literal fact");
    }

    // TODO: Add test with custom predicates
}
