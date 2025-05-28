use std::{any::Any, collections::HashMap};

use schemars::JsonSchema;
use serde::{Deserialize, Serialize};

use super::Error;
use crate::{
    backends::plonky2::{
        mainpod::{pad_statement, MainPod as Plonky2MainPod, Statement as BackendStatement},
        mock::{mainpod::MockMainPod, signedpod::MockSignedPod},
        signedpod::SignedPod as Plonky2SignedPod,
    },
    frontend::{MainPod, SignedPod},
    middleware::{
        self, containers::Dictionary, serialization::ordered_map, AnchoredKey, Hash, Key, Params,
        PodId, Statement, StatementArg, Value, EMPTY_HASH, SELF,
    },
};

#[derive(Serialize, Deserialize, JsonSchema)]
pub enum SignedPodType {
    Signed,
    MockSigned,
}

#[derive(Serialize, Deserialize, JsonSchema)]
#[serde(rename_all = "camelCase")]
#[schemars(rename = "SignedPod")]
pub struct SerializedSignedPod {
    id: PodId,
    #[serde(serialize_with = "ordered_map")]
    entries: HashMap<Key, Value>,
    proof: String,
    pod_type: SignedPodType,
}

#[derive(Serialize, Deserialize, JsonSchema)]
pub enum MainPodType {
    Main,
    MockMain,
}

#[derive(Serialize, Deserialize, JsonSchema)]
#[serde(rename_all = "camelCase")]
#[schemars(rename = "MainPod")]
pub struct SerializedMainPod {
    id: PodId,
    vds_root: Hash,
    public_statements: Vec<Statement>,
    proof: String,
    params: Params,
    pod_type: MainPodType,
}

impl From<SignedPod> for SerializedSignedPod {
    fn from(pod: SignedPod) -> Self {
        SerializedSignedPod {
            id: pod.id(),
            entries: pod.kvs,
            proof: pod.pod.serialized_proof(),
            pod_type: if (&*pod.pod as &dyn Any)
                .downcast_ref::<Plonky2SignedPod>()
                .is_some()
            {
                SignedPodType::Signed
            } else if (&*pod.pod as &dyn Any)
                .downcast_ref::<MockSignedPod>()
                .is_some()
            {
                SignedPodType::MockSigned
            } else {
                unreachable!()
            },
        }
    }
}

impl From<SerializedSignedPod> for SignedPod {
    fn from(serialized: SerializedSignedPod) -> Self {
        match serialized.pod_type {
            SignedPodType::Signed => SignedPod {
                pod: Box::new(Plonky2SignedPod {
                    id: serialized.id,
                    signature: Plonky2SignedPod::decode_signature(&serialized.proof).unwrap(),
                    dict: Dictionary::new(serialized.entries.clone()).unwrap(),
                }),
                kvs: serialized.entries,
            },
            SignedPodType::MockSigned => SignedPod {
                pod: Box::new(MockSignedPod::new(
                    serialized.id,
                    serde_json::from_str(&serialized.proof).unwrap(),
                    serialized.entries.clone(),
                )),
                kvs: serialized.entries,
            },
        }
    }
}

impl From<MainPod> for SerializedMainPod {
    fn from(pod: MainPod) -> Self {
        let (pod_type, vds_root) =
            if let Some(pod) = (&*pod.pod as &dyn Any).downcast_ref::<Plonky2MainPod>() {
                (MainPodType::Main, pod.vds_root())
            } else if (&*pod.pod as &dyn Any)
                .downcast_ref::<MockMainPod>()
                .is_some()
            {
                (MainPodType::MockMain, EMPTY_HASH)
            } else {
                unreachable!()
            };
        SerializedMainPod {
            id: pod.id(),
            vds_root,
            proof: pod.pod.serialized_proof(),
            params: pod.params.clone(),
            pod_type,
            public_statements: pod.public_statements.clone(),
        }
    }
}

impl TryFrom<SerializedMainPod> for MainPod {
    type Error = Error;

    fn try_from(serialized: SerializedMainPod) -> Result<Self, Self::Error> {
        match serialized.pod_type {
            MainPodType::Main => Ok(MainPod {
                pod: Box::new(Plonky2MainPod::new(
                    Plonky2MainPod::decode_proof(&serialized.proof, &serialized.params).map_err(
                        |e| {
                            Error::custom(format!(
                                "Failed to deserialize MainPod proof: {}. Value: {}",
                                e, serialized.proof
                            ))
                        },
                    )?,
                    middleware_statements_to_backend(
                        serialized.public_statements.clone(),
                        &serialized.params,
                        serialized.id,
                    ),
                    serialized.id,
                    serialized.vds_root,
                    serialized.params.clone(),
                )),
                public_statements: serialized.public_statements,
                params: serialized.params,
            }),
            MainPodType::MockMain => Ok(MainPod {
                pod: Box::new(
                    MockMainPod::deserialize(serialized.proof.clone()).map_err(|e| {
                        Error::custom(format!(
                            "Failed to deserialize MockMainPod: {}. Value: {}",
                            e, serialized.proof
                        ))
                    })?,
                ),
                public_statements: serialized.public_statements,
                params: serialized.params,
            }),
        }
    }
}

// To deserialize a backend MainPod, we need to convert the middleware
// statements to backend statements, and padding the list with None statements.
fn middleware_statements_to_backend(
    mid_statements: Vec<Statement>,
    params: &Params,
    id: PodId,
) -> Vec<BackendStatement> {
    let mut statements = Vec::new();
    for i in 0..(params.max_public_statements) {
        let mut st: BackendStatement = mid_statements
            .get(i)
            .unwrap_or(&middleware::Statement::None)
            .clone()
            .into();

        st = BackendStatement(
            st.0.clone(),
            st.1.iter()
                .map(|sa| match &sa {
                    StatementArg::Key(AnchoredKey { pod_id, key }) if *pod_id == id => {
                        StatementArg::Key(AnchoredKey::new(SELF, key.clone()))
                    }
                    _ => sa.clone(),
                })
                .collect(),
        );
        pad_statement(params, &mut st);
        statements.push(st);
    }

    statements
}

#[cfg(test)]
mod tests {
    use std::collections::{HashMap, HashSet};

    use pretty_assertions::assert_eq;
    use schemars::schema_for;

    use super::*;
    use crate::{
        backends::plonky2::{
            mainpod::Prover,
            mock::{mainpod::MockProver, signedpod::MockSigner},
            primitives::signature::SecretKey,
            signedpod::Signer,
        },
        examples::{
            eth_dos_pod_builder, eth_friend_signed_pod_builder, zu_kyc_pod_builder,
            zu_kyc_sign_pod_builders,
        },
        frontend::{Result, SignedPodBuilder},
        middleware::{
            self,
            containers::{Array, Set},
            Params, RawValue, TypedValue,
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

    fn signed_pod_builder() -> SignedPodBuilder {
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
        builder
    }

    #[test]
    fn test_signed_pod_serialization() {
        let builder = signed_pod_builder();
        let mut signer = Signer(SecretKey(RawValue::from(1)));
        let pod = builder.sign(&mut signer).unwrap();

        let serialized = serde_json::to_string_pretty(&pod).unwrap();
        println!("serialized: {}", serialized);
        let deserialized: SignedPod = serde_json::from_str(&serialized).unwrap();
        println!(
            "deserialized: {}",
            serde_json::to_string_pretty(&deserialized).unwrap()
        );
        assert_eq!(pod.kvs, deserialized.kvs);
        assert_eq!(pod.verify().is_ok(), deserialized.verify().is_ok());
        assert_eq!(pod.id(), deserialized.id())
    }

    #[test]
    fn test_mock_signed_pod_serialization() {
        let builder = signed_pod_builder();
        let mut signer = MockSigner { pk: "test".into() };
        let pod = builder.sign(&mut signer).unwrap();

        let serialized = serde_json::to_string_pretty(&pod).unwrap();
        println!("serialized: {}", serialized);
        let deserialized: SignedPod = serde_json::from_str(&serialized).unwrap();
        println!(
            "deserialized: {}",
            serde_json::to_string_pretty(&deserialized).unwrap()
        );
        assert_eq!(pod.kvs, deserialized.kvs);
        assert_eq!(pod.verify().is_ok(), deserialized.verify().is_ok());
        assert_eq!(pod.id(), deserialized.id())
    }

    fn build_mock_zukyc_pod() -> Result<MainPod> {
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

    fn build_plonky2_zukyc_pod() -> Result<MainPod> {
        let params = middleware::Params {
            // Currently the circuit uses random access that only supports vectors of length 64.
            // With max_input_main_pods=3 we need random access to a vector of length 73.
            max_input_recursive_pods: 1,
            ..Default::default()
        };

        let (gov_id_builder, pay_stub_builder, sanction_list_builder) =
            zu_kyc_sign_pod_builders(&params);
        let mut signer = Signer(SecretKey(RawValue::from(1)));
        let gov_id_pod = gov_id_builder.sign(&mut signer)?;
        let mut signer = Signer(SecretKey(RawValue::from(2)));
        let pay_stub_pod = pay_stub_builder.sign(&mut signer)?;
        let mut signer = Signer(SecretKey(RawValue::from(3)));
        let sanction_list_pod = sanction_list_builder.sign(&mut signer)?;
        let kyc_builder =
            zu_kyc_pod_builder(&params, &gov_id_pod, &pay_stub_pod, &sanction_list_pod)?;

        let mut prover = Prover {};
        let kyc_pod = kyc_builder.prove(&mut prover, &params)?;

        Ok(kyc_pod)
    }

    #[test]
    fn test_mock_main_pod_serialization() -> Result<()> {
        let kyc_pod = build_mock_zukyc_pod()?;
        let serialized = serde_json::to_string_pretty(&kyc_pod).unwrap();
        println!("serialized: {}", serialized);
        let deserialized: MainPod = serde_json::from_str(&serialized).unwrap();

        assert_eq!(kyc_pod.public_statements, deserialized.public_statements);
        assert_eq!(kyc_pod.pod.id(), deserialized.pod.id());
        assert_eq!(kyc_pod.pod.verify()?, deserialized.pod.verify()?);

        Ok(())
    }

    #[test]
    fn test_plonky2_main_pod_serialization() -> Result<()> {
        let kyc_pod = build_plonky2_zukyc_pod()?;
        let serialized = serde_json::to_string_pretty(&kyc_pod).unwrap();
        let deserialized: MainPod = serde_json::from_str(&serialized).unwrap();

        assert_eq!(kyc_pod.public_statements, deserialized.public_statements);
        assert_eq!(kyc_pod.pod.id(), deserialized.pod.id());
        assert_eq!(kyc_pod.pod.verify()?, deserialized.pod.verify()?);

        Ok(())
    }

    fn build_ethdos_pod() -> Result<MainPod> {
        let params = Params {
            max_input_signed_pods: 3,
            max_input_recursive_pods: 3,
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
            eth_friend_signed_pod_builder(&params, charlie.public_key().into()).sign(&mut alice)?;
        let charlie_attestation =
            eth_friend_signed_pod_builder(&params, bob.public_key().into()).sign(&mut charlie)?;

        let mut prover = MockProver {};
        let alice_bob_ethdos = eth_dos_pod_builder(
            &params,
            true,
            &alice_attestation,
            &charlie_attestation,
            bob.public_key().into(),
        )?
        .prove(&mut prover, &params)?;

        Ok(alice_bob_ethdos)
    }

    #[test]
    // This tests that we can generate JSON Schemas for the MainPod and
    // SignedPod types, and that we can validate Signed and Main Pods
    // against the schemas. Since both Mock and Plonky2 PODs have the same
    // public interface, we can assume that the schema works for both.
    fn test_schema() {
        let mainpod_schema = schema_for!(SerializedMainPod);
        let signedpod_schema = schema_for!(SerializedSignedPod);

        let kyc_pod = build_mock_zukyc_pod().unwrap();
        let signed_pod = signed_pod_builder()
            .sign(&mut MockSigner { pk: "test".into() })
            .unwrap();
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
