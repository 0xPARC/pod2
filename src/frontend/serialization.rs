use std::collections::HashMap;
use std::ops::Deref;

use serde::ser::{SerializeStruct, Serializer};
use serde::{Deserialize, Serialize};

use crate::backends::plonky2::mock_signed::MockSignedPod;
use crate::frontend::containers::{Array, Dictionary, Set};
use crate::middleware::{hash_str, PodId, F};
// This is something of an abstraction leak.
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
        let signature = format!("{}_signed_by_{}", self.id(), signer);

        state.serialize_field("signature", &signature)?;
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
            signature: String,
        }

        let helper = SignedPodHelper::deserialize(deserializer)?;
        let kvs = helper.entries;
        let dict = Dictionary::new(kvs.clone()).middleware_dict().clone();
        let pod = MockSignedPod::new(PodId(dict.commitment()), helper.signature, dict);
        Ok(SignedPod {
            pod: Box::new(pod),
            kvs: kvs,
        })
    }
}

impl Serialize for Value {
    fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
    where
        S: Serializer,
    {
        // Create a struct with 2 fields: type and value
        let mut state = serializer.serialize_struct("Value", 2)?;

        match self {
            Value::String(s) => {
                state.serialize_field("type", "string")?;
                state.serialize_field("value", s)?;
            }
            Value::Int(i) => {
                state.serialize_field("type", "int")?;
                state.serialize_field("value", i)?;
            }
            Value::Bool(b) => {
                state.serialize_field("type", "bool")?;
                state.serialize_field("value", b)?;
            }
            Value::Dictionary(d) => {
                state.serialize_field("type", "dictionary")?;
                state.serialize_field("value", &d.values())?;
            }
            Value::Set(s) => {
                state.serialize_field("type", "set")?;
                state.serialize_field("value", &s.values())?;
            }
            Value::Array(a) => {
                state.serialize_field("type", "array")?;
                state.serialize_field("value", &a.values())?;
            }
            Value::Raw(v) => {
                state.serialize_field("type", "raw")?;
                state.serialize_field("value", &format!("{:016x}{:016x}{:016x}{:016x}", v.0[0].0, v.0[1].0, v.0[2].0, v.0[3].0))?;
            }
        }
        state.end()
    }
}

impl<'de> Deserialize<'de> for Value {
    fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
    where
        D: serde::Deserializer<'de>,
    {
        #[derive(Deserialize)]
        struct ValueHelper {
            #[serde(rename = "type")]
            type_: String,
            value: serde_json::Value,
        }

        let helper = ValueHelper::deserialize(deserializer)?;
        match helper.type_.as_str() {
            "string" => Ok(Value::String(helper.value.as_str().unwrap().to_string())),
            "int" => Ok(Value::Int(helper.value.as_i64().unwrap())),
            "bool" => Ok(Value::Bool(helper.value.as_bool().unwrap())),
            "raw" => {
                let hex_str = helper.value.as_str().unwrap();
                let mut v = [F::ZERO; 4];
                for i in 0..4 {
                    let start = i * 16;
                    let end = start + 16;
                    let hex_part = &hex_str[start..end];
                    v[i] = F::from_canonical_u64(u64::from_str_radix(hex_part, 16).unwrap());
                }
                Ok(Value::Raw(crate::middleware::Value(v)))
            },
            "dictionary" => {
                let obj = helper.value.as_object().unwrap();
                let mut map = HashMap::new();
                for (k, v) in obj {
                    // Recursively deserialize each value using the same Value deserialization
                    let value: Value = serde_json::from_value(v.clone()).unwrap();
                    map.insert(k.clone(), value);
                }
                Ok(Value::Dictionary(Dictionary::new(map)))
            }
            "set" => {
                let obj = helper.value.as_object().unwrap();
                let mut set = Vec::new();
                for (k, v) in obj {
                    let value: Value = serde_json::from_value(v.clone()).unwrap();
                    set.push(value);
                }
                Ok(Value::Set(Set::new(set)))
            }
            "array" => {
                let obj = helper.value.as_object().unwrap();
                let mut array = Vec::new();
                for (k, v) in obj {
                    let value: Value = serde_json::from_value(v.clone()).unwrap();
                    array.push(value);
                }
                Ok(Value::Array(Array::new(array)))
            }
            _ => Err(serde::de::Error::custom("unsupported value type")),
        }
    }
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
            Value::Dictionary(Dictionary::new(HashMap::from([(
                "foo".to_string(),
                Value::Int(123),
            )]))),
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
