use std::{any::Any, collections::BTreeMap, fmt};

use schemars::JsonSchema;
use serde::{
    de::{self, MapAccess, Visitor},
    ser::SerializeStruct,
    Deserialize, Serialize,
};

use crate::{
    backends::plonky2::{
        mainpod::{MainPod as Plonky2MainPod, MainPodProof, Statement as BackendStatement},
        mock::{mainpod::MockMainPod, signedpod::MockSignedPod},
        signedpod::SignedPod as Plonky2SignedPod,
    },
    frontend::{MainPod, SignedPod},
    middleware::{
        containers::Dictionary, AnchoredKey, Params, Pod, PodId, PodType, Statement, StatementArg,
        Value, SELF,
    },
};

impl Serialize for SignedPod {
    fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
    where
        S: serde::Serializer,
    {
        let mut state = serializer.serialize_struct("SignedPod", 4)?;
        //  state.serialize_field("pod", &self.pod)?;
        // Force sorting by keys using a BTreeMap
        let kvs_btree: BTreeMap<String, Value> = self
            .kvs
            .clone()
            .into_iter()
            .map(|(k, v)| (k.name().to_string(), v))
            .collect();
        state.serialize_field("entries", &kvs_btree)?;
        state.serialize_field("id", &self.id())?;

        if let Ok(pod) = (self.pod.clone() as Box<dyn Any>).downcast::<MockSignedPod>() {
            state.serialize_field("podType", &PodType::MockSigned)?;
            state.serialize_field("proof", &pod.signature())?;
        } else if let Ok(pod) = (self.pod.clone() as Box<dyn Any>).downcast::<Plonky2SignedPod>() {
            state.serialize_field("podType", &PodType::Signed)?;
            state.serialize_field("proof", &pod.signature)?;
        }

        state.end()
    }
}

impl<'de> Deserialize<'de> for SignedPod {
    fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
    where
        D: serde::Deserializer<'de>,
    {
        enum Field {
            Entries,
            Id,
            Proof,
            PodType,
        }

        impl<'de> Deserialize<'de> for Field {
            fn deserialize<D>(deserializer: D) -> Result<Field, D::Error>
            where
                D: serde::Deserializer<'de>,
            {
                struct FieldVisitor;

                impl Visitor<'_> for FieldVisitor {
                    type Value = Field;

                    fn expecting(&self, formatter: &mut fmt::Formatter) -> fmt::Result {
                        formatter.write_str("`entries`, `id`, `proof`, or `podType`")
                    }

                    fn visit_str<E>(self, value: &str) -> Result<Field, E>
                    where
                        E: de::Error,
                    {
                        match value {
                            "entries" => Ok(Field::Entries),
                            "id" => Ok(Field::Id),
                            "proof" => Ok(Field::Proof),
                            "podType" => Ok(Field::PodType),
                            _ => Err(de::Error::unknown_field(value, FIELDS)),
                        }
                    }
                }
                deserializer.deserialize_identifier(FieldVisitor)
            }
        }

        struct SignedPodVisitor;

        impl<'de> Visitor<'de> for SignedPodVisitor {
            type Value = SignedPod;

            fn expecting(&self, formatter: &mut fmt::Formatter) -> fmt::Result {
                formatter.write_str("struct SignedPod")
            }

            fn visit_map<V>(self, mut map: V) -> Result<SignedPod, V::Error>
            where
                V: MapAccess<'de>,
            {
                let mut entries: Option<Dictionary> = None;
                let mut id: Option<PodId> = None;
                let mut proof_value: Option<serde_json::Value> = None;
                let mut pod_type: Option<PodType> = None;

                while let Some(key) = map.next_key()? {
                    match key {
                        Field::Entries => {
                            if entries.is_some() {
                                return Err(de::Error::duplicate_field("entries"));
                            }
                            entries = Some(map.next_value()?);
                        }
                        Field::Id => {
                            if id.is_some() {
                                return Err(de::Error::duplicate_field("id"));
                            }
                            id = Some(map.next_value()?);
                        }
                        Field::Proof => {
                            if proof_value.is_some() {
                                return Err(de::Error::duplicate_field("proof"));
                            }
                            proof_value = Some(map.next_value()?);
                        }
                        Field::PodType => {
                            if pod_type.is_some() {
                                return Err(de::Error::duplicate_field("podType"));
                            }
                            pod_type = Some(map.next_value()?);
                        }
                    }
                }

                let entries = entries.ok_or_else(|| de::Error::missing_field("entries"))?;
                let _id = id.ok_or_else(|| de::Error::missing_field("id"))?;
                let proof_value = proof_value.ok_or_else(|| de::Error::missing_field("proof"))?;
                let pod_type = pod_type.ok_or_else(|| de::Error::missing_field("podType"))?;

                let kvs = entries.kvs().clone();
                let pod: Box<dyn Pod> = match pod_type {
                    PodType::MockSigned => {
                        let proof_string: String = serde_json::from_value(proof_value.clone())
                            .map_err(|e| {
                                de::Error::custom(format!(
                                    "Proof for MockSigned is not a string: {}. Value: {}",
                                    e, proof_value
                                ))
                            })?;
                        Box::new(MockSignedPod::new(
                            PodId(entries.commitment()),
                            proof_string,
                            kvs.clone(),
                        ))
                    }
                    PodType::Signed => {
                        let signature_obj: crate::backends::plonky2::primitives::signature::Signature =
                            serde_json::from_value(proof_value.clone()).map_err(|e| {
                                de::Error::custom(format!(
                                    "Proof for Signed is not a Plonky2 Signature object: {}. Value: {}",
                                    e, proof_value
                                ))
                            })?;
                        Box::new(Plonky2SignedPod {
                            id: PodId(entries.commitment()), // Use derived ID
                            signature: signature_obj,
                            dict: entries,
                        })
                    }
                    _ => {
                        return Err(de::Error::custom(format!(
                            "Unsupported pod_type for SignedPod: {:?}",
                            pod_type
                        )))
                    }
                };

                Ok(SignedPod { pod, kvs })
            }
        }

        const FIELDS: &[&str] = &["entries", "id", "proof", "podType"];
        deserializer.deserialize_struct("SignedPod", FIELDS, SignedPodVisitor)
    }
}

impl Serialize for MainPod {
    fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
    where
        S: serde::Serializer,
    {
        let mut state = serializer.serialize_struct("MainPod", 5)?;
        state.serialize_field("id", &self.pod.id())?;
        state.serialize_field("public_statements", &self.public_statements)?;

        if let Ok(pod) = (self.pod.clone() as Box<dyn Any>).downcast::<MockMainPod>() {
            state.serialize_field("params", &pod.params())?;
            state.serialize_field("podType", &PodType::MockMain)?;
            state.serialize_field("proof", &pod.serialized_proof())?;
        } else if let Ok(pod) = (self.pod.clone() as Box<dyn Any>).downcast::<Plonky2MainPod>() {
            state.serialize_field("params", &pod.params())?;
            state.serialize_field("podType", &PodType::Main)?;
            state.serialize_field("proof", &pod.proof())?;
        }

        state.end()
    }
}

impl<'de> Deserialize<'de> for MainPod {
    fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
    where
        D: serde::Deserializer<'de>,
    {
        enum Field {
            Id,
            PublicStatements,
            PodType,
            Proof,
            Params,
        }

        impl<'de> Deserialize<'de> for Field {
            fn deserialize<D>(deserializer: D) -> Result<Field, D::Error>
            where
                D: serde::Deserializer<'de>,
            {
                struct FieldVisitor;

                impl Visitor<'_> for FieldVisitor {
                    type Value = Field;

                    fn expecting(&self, formatter: &mut fmt::Formatter) -> fmt::Result {
                        formatter
                            .write_str("`id`, `public_statements`, `podType`, `proof`, or `params`")
                    }

                    fn visit_str<E>(self, value: &str) -> Result<Field, E>
                    where
                        E: de::Error,
                    {
                        match value {
                            "id" => Ok(Field::Id),
                            "public_statements" => Ok(Field::PublicStatements),
                            "podType" => Ok(Field::PodType),
                            "proof" => Ok(Field::Proof),
                            "params" => Ok(Field::Params),
                            _ => Err(de::Error::unknown_field(value, FIELDS)),
                        }
                    }
                }
                deserializer.deserialize_identifier(FieldVisitor)
            }
        }

        struct MainPodVisitor;

        impl<'de> Visitor<'de> for MainPodVisitor {
            type Value = MainPod;

            fn expecting(&self, formatter: &mut fmt::Formatter) -> fmt::Result {
                formatter.write_str("struct MainPod")
            }

            fn visit_map<V>(self, mut map: V) -> Result<MainPod, V::Error>
            where
                V: MapAccess<'de>,
            {
                let mut id: Option<PodId> = None;
                let mut public_statements: Option<Vec<Statement>> = None;
                let mut pod_type: Option<PodType> = None;
                let mut proof_value: Option<serde_json::Value> = None;
                let mut params: Option<Params> = None;

                while let Some(key) = map.next_key()? {
                    match key {
                        Field::Id => {
                            if id.is_some() {
                                return Err(de::Error::duplicate_field("id"));
                            }
                            id = Some(map.next_value()?);
                        }
                        Field::PublicStatements => {
                            if public_statements.is_some() {
                                return Err(de::Error::duplicate_field("public_statements"));
                            }
                            public_statements = Some(map.next_value()?);
                        }
                        Field::PodType => {
                            if pod_type.is_some() {
                                return Err(de::Error::duplicate_field("podType"));
                            }
                            pod_type = Some(map.next_value()?);
                        }
                        Field::Proof => {
                            if proof_value.is_some() {
                                return Err(de::Error::duplicate_field("proof"));
                            }
                            proof_value = Some(map.next_value()?);
                        }
                        Field::Params => {
                            if params.is_some() {
                                return Err(de::Error::duplicate_field("params"));
                            }
                            params = Some(map.next_value()?);
                        }
                    }
                }

                let id = id.ok_or_else(|| de::Error::missing_field("id"))?;
                let public_statements = public_statements
                    .ok_or_else(|| de::Error::missing_field("public_statements"))?;
                let pod_type = pod_type.ok_or_else(|| de::Error::missing_field("podType"))?;
                let proof_value = proof_value.ok_or_else(|| de::Error::missing_field("proof"))?;
                let params = params.ok_or_else(|| de::Error::missing_field("params"))?;

                let pod: Box<dyn Pod> = match pod_type {
                    PodType::MockMain => {
                        let proof_string: String = serde_json::from_value(proof_value.clone())
                            .map_err(|e| {
                                de::Error::custom(format!(
                                    "Proof for MockMainPod is not a string: {}. Value: {}",
                                    e, proof_value
                                ))
                            })?;
                        Box::new(MockMainPod::deserialize(proof_string).map_err(|e| {
                            de::Error::custom(format!("Failed to deserialize MockMainPod: {}", e))
                        })?)
                    }
                    PodType::Main => {
                        let actual_proof: MainPodProof =
                            serde_json::from_value(proof_value.clone()).map_err(|e| {
                                de::Error::custom(format!(
                                    "Proof for Plonky2MainPod is not a valid Plonky2Proof structure: {}. Value: {}",
                                    e, proof_value
                                ))
                            })?;
                        Box::new(Plonky2MainPod::new(
                            actual_proof,
                            public_statements
                                .clone()
                                .into_iter()
                                .map(|s| {
                                    // We need to turn the middleware::Statement into a backend statement
                                    let bs: BackendStatement = s.into();
                                    BackendStatement(
                                        bs.0.clone(),
                                        bs.1.iter()
                                            .map(|sa| match &sa {
                                                // Reverse the normalization step by restoring the SELF PodId in places
                                                // where the current Pod's ID has been used in an anchored key.
                                                StatementArg::Key(AnchoredKey { pod_id, key })
                                                    if *pod_id == id =>
                                                {
                                                    println!(
                                                        "Replacing {:?} with {:?}",
                                                        pod_id, SELF
                                                    );
                                                    StatementArg::Key(AnchoredKey::new(
                                                        SELF,
                                                        key.clone(),
                                                    ))
                                                }
                                                _ => sa.clone(),
                                            })
                                            .collect(),
                                    )
                                })
                                .collect(),
                            id,
                            params,
                        ))
                    }
                    _ => {
                        return Err(de::Error::custom(format!(
                            "Unsupported pod_type for MainPod: {:?}",
                            pod_type
                        )))
                    }
                };

                Ok(MainPod {
                    pod,
                    public_statements,
                })
            }
        }

        const FIELDS: &[&str] = &["id", "public_statements", "podType", "proof", "params"];
        deserializer.deserialize_struct("MainPod", FIELDS, MainPodVisitor)
    }
}

// #[derive(Serialize, Deserialize, JsonSchema)]
// #[schemars(title = "MainPod")]
// #[serde(rename_all = "camelCase")]
// pub struct MainPodHelper {
//     public_statements: Vec<Statement>,
//     proof: String,
//     pod_class: String,
//     pod_type: String,
// }

// impl TryFrom<MainPodHelper> for MainPod {
//     type Error = Error; // or you can create a custom error type

//     fn try_from(helper: MainPodHelper) -> Result<Self, Self::Error> {
//         if helper.pod_class != "Main" {
//             return Err(Error::custom("pod_class is not Main"));
//         }
//         if helper.pod_type != "Mock" {
//             return Err(Error::custom("pod_type is not Mock"));
//         }

//         let pod = MockMainPod::deserialize(helper.proof)
//             .map_err(|e| Error::custom(format!("Failed to deserialize proof: {}", e)))?;

//         Ok(MainPod {
//             pod: Box::new(pod),
//             public_statements: helper.public_statements,
//         })
//     }
// }

// impl From<MainPod> for MainPodHelper {
//     fn from(pod: MainPod) -> Self {
//         MainPodHelper {
//             public_statements: pod.public_statements,
//             proof: pod.pod.serialized_proof(),
//             pod_class: "Main".to_string(),
//             pod_type: "Mock".to_string(),
//         }
//     }
// }

#[cfg(test)]
mod tests {
    use std::collections::{HashMap, HashSet};

    // Pretty assertions give nicer diffs between expected and actual values
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
            max_input_main_pods: 1,
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
        println!("id: {}", kyc_pod.pod.id());
        let serialized = serde_json::to_string_pretty(&kyc_pod).unwrap();
        // println!("serialized: {}", serialized);
        let deserialized: MainPod = serde_json::from_str(&serialized).unwrap();
        println!("deserialized id: {}", deserialized.pod.id());

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

    // #[test]
    // // This tests that we can generate JSON Schemas for the MainPod and
    // // SignedPod types, and that we can validate real Signed and Main Pods
    // // against the schemas.
    // fn test_schema() {
    //     let mainpod_schema = schema_for!(MainPodHelper);
    //     let signedpod_schema = schema_for!(SignedPodHelper);

    //     let kyc_pod = build_zukyc_pod().unwrap();
    //     let signed_pod = build_signed_pod().unwrap();
    //     let ethdos_pod = build_ethdos_pod().unwrap();
    //     let mainpod_schema_value = serde_json::to_value(&mainpod_schema).unwrap();
    //     let signedpod_schema_value = serde_json::to_value(&signedpod_schema).unwrap();

    //     let kyc_pod_value = serde_json::to_value(&kyc_pod).unwrap();
    //     let mainpod_valid = jsonschema::validate(&mainpod_schema_value, &kyc_pod_value);
    //     assert!(mainpod_valid.is_ok(), "{:#?}", mainpod_valid);

    //     let signed_pod_value = serde_json::to_value(&signed_pod).unwrap();
    //     let signedpod_valid = jsonschema::validate(&signedpod_schema_value, &signed_pod_value);
    //     assert!(signedpod_valid.is_ok(), "{:#?}", signedpod_valid);

    //     let ethdos_pod_value = serde_json::to_value(&ethdos_pod).unwrap();
    //     let ethdos_pod_valid = jsonschema::validate(&mainpod_schema_value, &ethdos_pod_value);
    //     assert!(ethdos_pod_valid.is_ok(), "{:#?}", ethdos_pod_valid);
    // }
}
