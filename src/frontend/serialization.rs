use std::collections::HashMap;

use schemars::JsonSchema;
use serde::{Deserialize, Serialize};

use crate::{
    backends::plonky2::mock::{mainpod::MockMainPod, signedpod::MockSignedPod},
    frontend::{Error, MainPod, SignedPod, Statement},
    middleware::{containers::Dictionary, Key, PodId, Value},
};

#[derive(Serialize, Deserialize, JsonSchema)]
#[serde(rename_all = "camelCase")]
#[schemars(title = "SignedPod")]
pub struct SignedPodHelper {
    entries: HashMap<Key, Value>,
    proof: String,
    pod_class: String,
    pod_type: String,
}

impl TryFrom<SignedPodHelper> for SignedPod {
    type Error = Error;

    fn try_from(helper: SignedPodHelper) -> Result<SignedPod, Self::Error> {
        if helper.pod_class != "Signed" {
            return Err(Error::custom("pod_class is not Signed"));
        }
        if helper.pod_type != "Mock" {
            return Err(Error::custom("pod_type is not Mock"));
        }

        let dict = Dictionary::new(helper.entries.clone())?.clone();
        let pod = MockSignedPod::new(PodId(dict.commitment()), helper.proof, dict.kvs().clone());

        Ok(SignedPod {
            pod: Box::new(pod),
            kvs: helper.entries,
        })
    }
}

impl From<SignedPod> for SignedPodHelper {
    fn from(pod: SignedPod) -> Self {
        SignedPodHelper {
            entries: pod.kvs,
            proof: pod.pod.serialized_proof(),
            pod_class: "Signed".to_string(),
            pod_type: "Mock".to_string(),
        }
    }
}

#[derive(Serialize, Deserialize, JsonSchema)]
#[schemars(title = "MainPod")]
#[serde(rename_all = "camelCase")]
pub struct MainPodHelper {
    public_statements: Vec<Statement>,
    proof: String,
    pod_class: String,
    pod_type: String,
}

impl TryFrom<MainPodHelper> for MainPod {
    type Error = Error; // or you can create a custom error type

    fn try_from(helper: MainPodHelper) -> Result<Self, Self::Error> {
        if helper.pod_class != "Main" {
            return Err(Error::custom("pod_class is not Main"));
        }
        if helper.pod_type != "Mock" {
            return Err(Error::custom("pod_type is not Mock"));
        }

        let pod = MockMainPod::deserialize(helper.proof)
            .map_err(|e| Error::custom(format!("Failed to deserialize proof: {}", e)))?;

        Ok(MainPod {
            pod: Box::new(pod),
            public_statements: helper.public_statements,
        })
    }
}

impl From<MainPod> for MainPodHelper {
    fn from(pod: MainPod) -> Self {
        MainPodHelper {
            public_statements: pod.public_statements,
            proof: pod.pod.serialized_proof(),
            pod_class: "Main".to_string(),
            pod_type: "Mock".to_string(),
        }
    }
}

#[cfg(test)]
mod tests {
    use std::collections::HashSet;

    // Pretty assertions give nicer diffs between expected and actual values
    use pretty_assertions::assert_eq;
    use schemars::schema_for;

    use super::*;
    use crate::{
        backends::plonky2::mock::{mainpod::MockProver, signedpod::MockSigner},
        examples::{
            eth_dos_pod_builder, eth_friend_signed_pod_builder, zu_kyc_pod_builder,
            zu_kyc_sign_pod_builders,
        },
        frontend::{Result, SignedPodBuilder},
        middleware::{
            self,
            containers::{Array, Set},
            Params, TypedValue,
        },
    };

    #[test]
    fn test_value_serialization() {
        // Pairs of values and their expected serialized representations
        let values = vec![
            (TypedValue::String("hello".to_string()), "\"hello\""),
            (TypedValue::Int(42), "{\"Int\":\"42\"}"),
            (TypedValue::Bool(true), "true"),
            (
                TypedValue::Array(Array::new(vec!["foo".into(), false.into()]).unwrap()),
                "[\"foo\",false]",
            ),
            (
                TypedValue::Dictionary(
                    Dictionary::new(HashMap::from([
                        // The set of valid keys is equal to the set of valid JSON keys
                        ("foo".into(), 123.into()),
                        // Empty strings are valid JSON keys
                        (("".into()), "baz".into()),
                        // Keys can contain whitespace
                        (("    hi".into()), false.into()),
                        // Keys can contain special characters
                        (("!@£$%^&&*()".into()), "".into()),
                        // Keys can contain _very_ special characters
                        (("\0".into()), "".into()),
                        // Keys can contain emojis
                        (("🥳".into()), "party time!".into()),
                    ]))
                    .unwrap(),
                ),
                "{\"Dictionary\":{\"\":\"baz\",\"\\u0000\":\"\",\"    hi\":false,\"!@£$%^&&*()\":\"\",\"foo\":{\"Int\":\"123\"},\"🥳\":\"party time!\"}}",
            ),
            (
                TypedValue::Set(Set::new(HashSet::from(["foo".into(), "bar".into()])).unwrap()),
                "{\"Set\":[\"bar\",\"foo\"]}",
            ),
        ];

        for (value, expected) in values {
            let serialized = serde_json::to_string(&value).unwrap();
            assert_eq!(serialized, expected);
            let deserialized: TypedValue = serde_json::from_str(&serialized).unwrap();
            assert_eq!(
                value, deserialized,
                "value {:#?} should equal deserialized {:#?}",
                value, deserialized
            );
            let expected_deserialized: TypedValue = serde_json::from_str(expected).unwrap();
            assert_eq!(value, expected_deserialized);
        }
    }

    fn build_signed_pod() -> Result<SignedPod> {
        let mut signer = MockSigner { pk: "test".into() };
        let mut builder = SignedPodBuilder::new(&Params::default());
        builder.insert("name", "test");
        builder.insert("age", 30);
        builder.insert("very_large_int", 1152921504606846976);
        builder.insert(
            "a_dict_containing_one_key",
            Dictionary::new(HashMap::from([
                ("foo".into(), 123.into()),
                (
                    "an_array_containing_three_ints".into(),
                    Array::new(vec![1.into(), 2.into(), 3.into()])
                        .unwrap()
                        .into(),
                ),
                (
                    "a_set_containing_two_strings".into(),
                    Set::new(HashSet::from([
                        Array::new(vec!["foo".into(), "bar".into()]).unwrap().into(),
                        "baz".into(),
                    ]))
                    .unwrap()
                    .into(),
                ),
            ]))
            .unwrap(),
        );

        let pod = builder.sign(&mut signer).unwrap();
        Ok(pod)
    }

    #[test]
    fn test_signed_pod_serialization() {
        let pod = build_signed_pod().unwrap();

        let serialized = serde_json::to_string_pretty(&pod).unwrap();
        println!("serialized: {}", serialized);
        let deserialized: SignedPod = serde_json::from_str(&serialized).unwrap();

        assert_eq!(pod.kvs, deserialized.kvs);
        assert_eq!(pod.verify().is_ok(), deserialized.verify().is_ok());
        assert_eq!(pod.id(), deserialized.id())
    }

    fn build_zukyc_pod() -> Result<MainPod> {
        let params = middleware::Params::default();

        let (gov_id_builder, pay_stub_builder, sanction_list_builder) =
            zu_kyc_sign_pod_builders(&params);
        let mut signer = MockSigner {
            pk: "ZooGov".into(),
        };
        let gov_id_pod = gov_id_builder.sign(&mut signer).unwrap();
        let mut signer = MockSigner {
            pk: "ZooDeel".into(),
        };
        let pay_stub_pod = pay_stub_builder.sign(&mut signer).unwrap();
        let mut signer = MockSigner {
            pk: "ZooOFAC".into(),
        };
        let sanction_list_pod = sanction_list_builder.sign(&mut signer).unwrap();
        let kyc_builder =
            zu_kyc_pod_builder(&params, &gov_id_pod, &pay_stub_pod, &sanction_list_pod).unwrap();

        let mut prover = MockProver {};
        let kyc_pod = kyc_builder.prove(&mut prover, &params).unwrap();
        Ok(kyc_pod)
    }

    #[test]
    fn test_main_pod_serialization() -> Result<()> {
        let kyc_pod = build_zukyc_pod()?;
        let serialized = serde_json::to_string_pretty(&kyc_pod).unwrap();
        println!("serialized: {}", serialized);
        let deserialized: MainPod = serde_json::from_str(&serialized).unwrap();

        assert_eq!(kyc_pod.public_statements, deserialized.public_statements);
        assert_eq!(kyc_pod.pod.id(), deserialized.pod.id());
        assert_eq!(kyc_pod.pod.verify()?, deserialized.pod.verify()?);

        Ok(())
    }

    fn build_ethdos_pod() -> Result<MainPod> {
        let params = Params {
            max_input_signed_pods: 3,
            max_input_main_pods: 3,
            max_statements: 31,
            max_signed_pod_values: 8,
            max_public_statements: 10,
            max_statement_args: 6,
            max_operation_args: 5,
            max_custom_predicate_arity: 5,
            max_custom_batch_size: 5,
            max_custom_predicate_wildcards: 12,
            ..Default::default()
        };

        let mut alice = MockSigner { pk: "Alice".into() };
        let bob = MockSigner { pk: "Bob".into() };
        let mut charlie = MockSigner {
            pk: "Charlie".into(),
        };

        // Alice attests that she is ETH friends with Charlie and Charlie
        // attests that he is ETH friends with Bob.
        let alice_attestation =
            eth_friend_signed_pod_builder(&params, charlie.pubkey().into()).sign(&mut alice)?;
        let charlie_attestation =
            eth_friend_signed_pod_builder(&params, bob.pubkey().into()).sign(&mut charlie)?;

        let mut prover = MockProver {};
        let alice_bob_ethdos = eth_dos_pod_builder(
            &params,
            &alice_attestation,
            &charlie_attestation,
            &bob.pubkey().into(),
        )?
        .prove(&mut prover, &params)?;

        Ok(alice_bob_ethdos)
    }

    #[test]
    // This tests that we can generate JSON Schemas for the MainPod and
    // SignedPod types, and that we can validate real Signed and Main Pods
    // against the schemas.
    fn test_schema() {
        let mainpod_schema = schema_for!(MainPodHelper);
        let signedpod_schema = schema_for!(SignedPodHelper);

        let kyc_pod = build_zukyc_pod().unwrap();
        let signed_pod = build_signed_pod().unwrap();
        let ethdos_pod = build_ethdos_pod().unwrap();
        let mainpod_schema_value = serde_json::to_value(&mainpod_schema).unwrap();
        let signedpod_schema_value = serde_json::to_value(&signedpod_schema).unwrap();

        let kyc_pod_value = serde_json::to_value(&kyc_pod).unwrap();
        let mainpod_valid = jsonschema::validate(&mainpod_schema_value, &kyc_pod_value);
        assert!(mainpod_valid.is_ok(), "{:#?}", mainpod_valid);

        let signed_pod_value = serde_json::to_value(&signed_pod).unwrap();
        let signedpod_valid = jsonschema::validate(&signedpod_schema_value, &signed_pod_value);
        assert!(signedpod_valid.is_ok(), "{:#?}", signedpod_valid);

        let ethdos_pod_value = serde_json::to_value(&ethdos_pod).unwrap();
        let ethdos_pod_valid = jsonschema::validate(&mainpod_schema_value, &ethdos_pod_value);
        assert!(ethdos_pod_valid.is_ok(), "{:#?}", ethdos_pod_valid);
    }
}
