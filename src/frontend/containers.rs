use std::collections::HashMap;

use anyhow::Result;
use schemars::JsonSchema;
use serde::{Deserialize, Serialize};

use super::Value;
use crate::frontend::serialization::ordered_map;
use crate::middleware::{
    containers::{
        Array as MiddlewareArray, Dictionary as MiddlewareDictionary, Set as MiddlewareSet,
    },
    hash_str, Value as MiddlewareValue,
};

#[derive(Clone, Debug, PartialEq, Eq, Serialize, JsonSchema)]
#[serde(transparent)]
pub struct Set(Vec<Value>, #[serde(skip)] MiddlewareSet);

impl Set {
    pub fn new(values: Vec<Value>) -> Result<Self> {
        let set = MiddlewareSet::new(&values.iter().map(|v| MiddlewareValue::from(v)).collect())?;
        Ok(Self(values, set))
    }

    pub fn middleware_set(&self) -> &MiddlewareSet {
        &self.1
    }

    pub fn values(&self) -> &Vec<Value> {
        &self.0
    }
}

impl<'de> Deserialize<'de> for Set {
    fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
    where
        D: serde::Deserializer<'de>,
    {
        let values: Vec<Value> = Vec::deserialize(deserializer)?;
        Set::new(values).map_err(serde::de::Error::custom)
    }
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, JsonSchema)]
#[serde(transparent)]
pub struct Dictionary(
    #[serde(serialize_with = "ordered_map")] HashMap<String, Value>,
    #[serde(skip)] MiddlewareDictionary,
);

impl Dictionary {
    pub fn new(values: HashMap<String, Value>) -> Result<Self> {
        let dict = MiddlewareDictionary::new(
            &values
                .iter()
                .map(|(k, v)| (hash_str(k), MiddlewareValue::from(v)))
                .collect::<HashMap<_, _>>(),
        )?;
        Ok(Self(values, dict))
    }

    pub fn middleware_dict(&self) -> &MiddlewareDictionary {
        &self.1
    }

    pub fn values(&self) -> &HashMap<String, Value> {
        &self.0
    }
}

impl<'de> Deserialize<'de> for Dictionary {
    fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
    where
        D: serde::Deserializer<'de>,
    {
        let values: HashMap<String, Value> = HashMap::deserialize(deserializer)?;
        Dictionary::new(values).map_err(serde::de::Error::custom)
    }
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, JsonSchema)]
#[serde(transparent)]
pub struct Array(Vec<Value>, #[serde(skip)] MiddlewareArray);

impl Array {
    pub fn new(values: Vec<Value>) -> Result<Self> {
        let array =
            MiddlewareArray::new(&values.iter().map(|v| MiddlewareValue::from(v)).collect())?;
        Ok(Self(values, array))
    }

    pub fn middleware_array(&self) -> &MiddlewareArray {
        &self.1
    }

    pub fn values(&self) -> &Vec<Value> {
        &self.0
    }
}

impl<'de> Deserialize<'de> for Array {
    fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
    where
        D: serde::Deserializer<'de>,
    {
        let values: Vec<Value> = Vec::deserialize(deserializer)?;
        Array::new(values).map_err(serde::de::Error::custom)
    }
}
