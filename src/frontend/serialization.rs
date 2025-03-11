use std::collections::HashMap;

use serde::ser::{SerializeStruct, Serializer};
use serde::{Deserialize, Serialize};

use crate::backends::plonky2::mock_signed::MockSignedPod;
use crate::frontend::containers::{Array, Dictionary, Set};
use crate::middleware::{self, PodId, F};
use plonky2::field::types::Field;

use super::SignedPod;
use super::Value;

impl Serialize for SignedPod {
    fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
    where
        S: Serializer,
    {
        let mut state = serializer.serialize_struct("SignedPod", 3)?;
        state.serialize_field(
            "entries",
            &self
                .kvs
                .iter()
                .map(|(k, v)| (k.clone(), v))
                .collect::<HashMap<String, &Value>>(),
        )?;

        let signer = match self.kvs.get("_signer").unwrap() {
            Value::Raw(s) => s,
            _ => panic!("_signer must be a raw value"),
        };
        let signature = self.pod.serialized_proof();

        state.serialize_field("proof", &signature)?;
        state.serialize_field("pod_type", "signed")?;
        state.end()
    }
}

impl<'de> Deserialize<'de> for SignedPod {
    fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
    where
        D: serde::Deserializer<'de>,
    {
        #[derive(Deserialize)]
        struct SignedPodHelper {
            entries: HashMap<String, Value>,
            proof: String,
        }

        let helper = SignedPodHelper::deserialize(deserializer)?;
        let kvs = helper.entries;
        let dict = Dictionary::new(kvs.clone()).middleware_dict().clone();
        let pod = MockSignedPod::new(PodId(dict.commitment()), helper.proof, dict);
        Ok(SignedPod {
            pod: Box::new(pod),
            kvs: kvs,
        })
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

pub fn serialize_raw<S>(value: &middleware::Value, serializer: S) -> Result<S::Ok, S::Error>
where
    S: serde::Serializer,
{
    serializer.serialize_str(&format!(
        "{:016x}{:016x}{:016x}{:016x}",
        value.0[0].0, value.0[1].0, value.0[2].0, value.0[3].0
    ))
}

pub fn deserialize_raw<'de, D>(deserializer: D) -> Result<middleware::Value, D::Error>
where
    D: serde::Deserializer<'de>,
{
    let hex_str = String::deserialize(deserializer)?;
    let mut v = [F::ZERO; 4];
    for i in 0..4 {
        let start = i * 16;
        let end = start + 16;
        let hex_part = &hex_str[start..end];
        v[i] = F::from_canonical_u64(
            u64::from_str_radix(hex_part, 16).map_err(serde::de::Error::custom)?,
        );
    }
    Ok(middleware::Value(v))
}

#[cfg(test)]
mod tests {
    use crate::{
        backends::plonky2::mock_signed::MockSigner,
        frontend::{containers::Dictionary, SignedPodBuilder},
        middleware::Params,
    };

    use super::*;
    use serde_json::json;

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
    fn test_serialized_pod() {
        let mut entries = HashMap::new();
        entries.insert("name".to_string(), Value::String("test".to_string()));
        entries.insert("age".to_string(), Value::Int(30));

        let mut signer = MockSigner { pk: "test".into() };
        let mut builder = SignedPodBuilder::new(&Params::default());
        builder.insert("name", "test");
        builder.insert("age", 30);
        builder.insert(
            "map",
            Value::Dictionary(Dictionary::new(HashMap::from([
                ("foo".to_string(), Value::Int(123)),
                (
                    "array".to_string(),
                    Value::Array(Array::new(vec![
                        Value::Int(1),
                        Value::Int(2),
                        Value::Int(3),
                    ])),
                ),
                (
                    "set".to_string(),
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
}
