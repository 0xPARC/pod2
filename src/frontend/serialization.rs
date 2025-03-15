use std::collections::HashMap;

use base64::prelude::*;
use schemars::JsonSchema;
use serde::{Deserialize, Serialize};

use crate::backends::plonky2::mock_main::MockMainPod;
use crate::backends::plonky2::mock_signed::MockSignedPod;
use crate::frontend::containers::Dictionary;
use crate::frontend::Statement;
use crate::frontend::StatementSerdeHelper;
use crate::middleware::{PodId, F};
use crate::middleware::{HASH_SIZE, VALUE_SIZE};
use plonky2::field::types::Field;

use super::Value;
use super::{MainPod, SignedPod};

#[derive(Serialize, Deserialize, JsonSchema)]
pub struct SignedPodHelper {
    entries: HashMap<String, Value>,
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

        let dict = Dictionary::new(helper.entries.clone())
            .middleware_dict()
            .clone();
        let pod = MockSignedPod::new(PodId(dict.commitment()), helper.proof, dict);

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
pub struct MainPodHelper {
    #[schemars(with = "Vec<StatementSerdeHelper>")]
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

        let proof = String::from_utf8(BASE64_STANDARD.decode(&helper.proof)?)
            .map_err(|e| anyhow::anyhow!("Invalid base64 encoding: {}", e))?;

        let pod: MockMainPod = serde_json::from_str(&proof)
            .map_err(|e| anyhow::anyhow!("Failed to parse proof: {}", e))?;

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

pub fn serialize_i64<S>(value: &i64, serializer: S) -> Result<S::Ok, S::Error>
where
    S: serde::Serializer,
{
    serializer.serialize_str(&value.to_string())
}

pub fn deserialize_i64<'de, D>(deserializer: D) -> Result<i64, D::Error>
where
    D: serde::Deserializer<'de>,
{
    String::deserialize(deserializer)?
        .parse()
        .map_err(serde::de::Error::custom)
}

fn serialize_field_tuple<S, const N: usize>(
    value: &[F; N],
    serializer: S,
) -> Result<S::Ok, S::Error>
where
    S: serde::Serializer,
{
    serializer.serialize_str(&format!(
        "{:016x}{:016x}{:016x}{:016x}",
        value[0].0, value[1].0, value[2].0, value[3].0
    ))
}

fn deserialize_field_tuple<'de, D, const N: usize>(deserializer: D) -> Result<[F; N], D::Error>
where
    D: serde::Deserializer<'de>,
{
    let hex_str = String::deserialize(deserializer)?;

    if !hex_str.chars().count() == 64 || !hex_str.chars().all(|c| c.is_ascii_hexdigit()) {
        return Err(serde::de::Error::custom(
            "Invalid hex string format - expected 64 hexadecimal characters",
        ));
    }

    let mut v = [F::ZERO; N];
    for i in 0..N {
        let start = i * 16;
        let end = start + 16;
        let hex_part = &hex_str[start..end];
        v[i] = F::from_canonical_u64(
            u64::from_str_radix(hex_part, 16).map_err(serde::de::Error::custom)?,
        );
    }
    Ok(v)
}

pub fn serialize_hash_tuple<S>(value: &[F; HASH_SIZE], serializer: S) -> Result<S::Ok, S::Error>
where
    S: serde::Serializer,
{
    serialize_field_tuple::<S, HASH_SIZE>(value, serializer)
}

pub fn deserialize_hash_tuple<'de, D>(deserializer: D) -> Result<[F; HASH_SIZE], D::Error>
where
    D: serde::Deserializer<'de>,
{
    deserialize_field_tuple::<D, HASH_SIZE>(deserializer)
}

pub fn serialize_value_tuple<S>(value: &[F; VALUE_SIZE], serializer: S) -> Result<S::Ok, S::Error>
where
    S: serde::Serializer,
{
    serialize_field_tuple::<S, VALUE_SIZE>(value, serializer)
}

pub fn deserialize_value_tuple<'de, D>(deserializer: D) -> Result<[F; VALUE_SIZE], D::Error>
where
    D: serde::Deserializer<'de>,
{
    deserialize_field_tuple::<D, VALUE_SIZE>(deserializer)
}

#[cfg(test)]
mod tests {
    use crate::{
        backends::plonky2::{mock_main::MockProver, mock_signed::MockSigner},
        examples::{zu_kyc_pod_builder, zu_kyc_sign_pod_builders},
        frontend::{
            containers::{Array, Dictionary, Set},
            SignedPodBuilder,
        },
        middleware::{self, Params},
    };

    use super::*;

    #[test]
    fn test_value_serialization() {
        let values = vec![
            Value::String("hello".to_string()),
            Value::Int(42),
            Value::Bool(true),
        ];

        for value in values {
            let serialized = serde_json::to_string(&value).unwrap();
            let deserialized: Value = serde_json::from_str(&serialized).unwrap();
            assert_eq!(value, deserialized);
        }
    }

    #[test]
    fn test_serialized_signed_pod() {
        let mut entries = HashMap::new();
        entries.insert("name".to_string(), Value::String("test".to_string()));
        entries.insert("age".to_string(), Value::Int(30));

        let mut signer = MockSigner { pk: "test".into() };
        let mut builder = SignedPodBuilder::new(&Params::default());
        builder.insert("name", "test");
        builder.insert("age", 30);
        builder.insert("very_large_int", 1152921504606846976);
        builder.insert(
            "a_dict_containing_one_key",
            Value::Dictionary(Dictionary::new(HashMap::from([
                ("foo".to_string(), Value::Int(123)),
                (
                    "an_array_containing_three_ints".to_string(),
                    Value::Array(Array::new(vec![
                        Value::Int(1),
                        Value::Int(2),
                        Value::Int(3),
                    ])),
                ),
                (
                    "a_set_containing_two_strings".to_string(),
                    Value::Set(Set::new(vec![
                        Value::Array(Array::new(vec![
                            Value::String("foo".to_string()),
                            Value::String("bar".to_string()),
                        ])),
                        Value::String("baz".to_string()),
                    ])),
                ),
            ]))),
        );

        let pod = builder.sign(&mut signer).unwrap();

        let serialized = serde_json::to_string(&pod).unwrap();
        println!("serialized: {}", serialized);
        let deserialized: SignedPod = serde_json::from_str(&serialized).unwrap();

        assert_eq!(pod.kvs, deserialized.kvs);
        assert_eq!(pod.origin(), deserialized.origin());
        assert_eq!(pod.verify(), deserialized.verify());
        assert_eq!(pod.id(), deserialized.id())
    }

    #[test]
    fn test_main_pod_serialization() {
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
        assert_eq!(kyc_pod.pod.verify(), deserialized.pod.verify());
    }

    #[test]
    fn test_gen_schema() {
        let schema = schemars::schema_for!(SignedPodHelper);
        let schema = serde_json::to_string_pretty(&schema).unwrap();
        println!("schema: {}", schema);

        let schema = schemars::schema_for!(MainPodHelper);
        let schema = serde_json::to_string_pretty(&schema).unwrap();
        println!("schema: {}", schema);
    }
}
