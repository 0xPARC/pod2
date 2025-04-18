use std::collections::HashMap;

use schemars::{JsonSchema, Schema};
use serde::{Deserialize, Serialize};

use crate::{
    backends::plonky2::mock::{mainpod::MockMainPod, signedpod::MockSignedPod},
    frontend::{MainPod, SignedPod, Statement},
    middleware::{containers::Dictionary, Key, PodId, Value},
};

#[derive(Serialize, Deserialize /*JsonSchema*/)]
//#[schemars(title = "SignedPod")]
pub struct SignedPodHelper {
    entries: HashMap<Key, Value>,
    proof: String,
    pod_class: String,
    pod_type: String,
}

impl TryFrom<SignedPodHelper> for SignedPod {
    type Error = anyhow::Error;

    fn try_from(helper: SignedPodHelper) -> Result<SignedPod, Self::Error> {
        if helper.pod_class != "Signed" {
            return Err(anyhow::anyhow!("pod_class is not Signed"));
        }
        if helper.pod_type != "Mock" {
            return Err(anyhow::anyhow!("pod_type is not Mock"));
        }

        let dict = Dictionary::new(helper.entries.clone())?.clone();
        let pod =
            MockSignedPod::deserialize(PodId(dict.commitment()), helper.proof, dict.kvs().clone());

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

#[derive(Serialize, Deserialize /*JsonSchema*/)]
//#[schemars(title = "MainPod")]
pub struct MainPodHelper {
    public_statements: Vec<Statement>,
    proof: String,
    pod_class: String,
    pod_type: String,
}

impl TryFrom<MainPodHelper> for MainPod {
    type Error = anyhow::Error; // or you can create a custom error type

    fn try_from(helper: MainPodHelper) -> Result<Self, Self::Error> {
        if helper.pod_class != "Main" {
            return Err(anyhow::anyhow!("pod_class is not Main"));
        }
        if helper.pod_type != "Mock" {
            return Err(anyhow::anyhow!("pod_type is not Mock"));
        }

        let pod = MockMainPod::deserialize(helper.proof)
            .map_err(|e| anyhow::anyhow!("Failed to deserialize proof: {}", e))?;

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

pub fn transform_value_schema(schema: &mut Schema) {
    let obj = schema.as_object_mut().unwrap();

    // Get the oneOf array which contains our variant schemas
    if let Some(one_of_container) = obj.get_mut("oneOf") {
        if let Some(variants) = one_of_container.as_array_mut() {
            // Add String variant (untagged)
            variants.push(serde_json::json!({
                "type": "string"
            }));

            // Add Boolean variant (untagged)
            variants.push(serde_json::json!({
                "type": "boolean"
            }));

            // Add Array variant (untagged)
            variants.push(serde_json::json!({
                "type": "array",
                "items": {
                    "$ref": "#/definitions/Value"
                }
            }));
        }
    }
}

#[cfg(test)]
mod tests {
    use std::collections::HashSet;

    use anyhow::Result;
    // Pretty assertions give nicer diffs between expected and actual values
    use pretty_assertions::assert_eq;
    use schemars::generate::SchemaSettings;

    use super::*;
    use crate::{
        backends::plonky2::mock::{mainpod::MockProver, signedpod::MockSigner},
        examples::{zu_kyc_pod_builder, zu_kyc_sign_pod_builders},
        frontend::SignedPodBuilder,
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
                        ("foo".into(), 123.into()),
                        (("bar".into()), "baz".into()),
                    ]))
                    .unwrap(),
                ),
                "{\"Dictionary\":{\"bar\":\"baz\",\"foo\":{\"Int\":\"123\"}}}",
            ),
            (
                TypedValue::Set(Set::new(HashSet::from(["foo".into(), "bar".into()])).unwrap()),
                "{\"Set\":[\"foo\",\"bar\"]}",
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
            let expected_deserialized: TypedValue = serde_json::from_str(&expected).unwrap();
            assert_eq!(value, expected_deserialized);
        }
    }
    #[test]
    fn test_signed_pod_serialization() {
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

        let serialized = serde_json::to_string(&pod).unwrap();
        println!("serialized: {}", serialized);
        let deserialized: SignedPod = serde_json::from_str(&serialized).unwrap();

        assert_eq!(pod.kvs, deserialized.kvs);
        assert_eq!(pod.verify().is_ok(), deserialized.verify().is_ok());
        assert_eq!(pod.id(), deserialized.id())
    }

    #[test]
    fn test_main_pod_serialization() -> Result<()> {
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

        let serialized = serde_json::to_string(&kyc_pod).unwrap();
        println!("serialized: {}", serialized);
        let deserialized: MainPod = serde_json::from_str(&serialized).unwrap();

        assert_eq!(kyc_pod.public_statements, deserialized.public_statements);
        assert_eq!(kyc_pod.pod.id(), deserialized.pod.id());
        assert_eq!(kyc_pod.pod.verify()?, deserialized.pod.verify()?);

        Ok(())
    }
    /*
    #[test]
    fn test_schema() {
        let generator = SchemaSettings::draft07().into_generator();
        let mainpod_schema = generator.clone().into_root_schema_for::<MainPodHelper>();
        let signedpod_schema = generator.into_root_schema_for::<SignedPodHelper>();

        println!("{}", serde_json::to_string_pretty(&mainpod_schema).unwrap());
        println!(
            "{}",
            serde_json::to_string_pretty(&signedpod_schema).unwrap()
        );
    }*/
}
