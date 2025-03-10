use std::collections::HashMap;

use super::Value;
use crate::middleware::{
    containers::{
        Array as MiddlewareArray, Dictionary as MiddlewareDictionary, Set as MiddlewareSet,
    },
    hash_str, Value as MiddlewareValue,
};

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Set(Vec<Value>, MiddlewareSet);

impl Set {
  pub fn new(values: Vec<Value>) -> Self {
    let set = MiddlewareSet::new(&values.iter().map(|v| MiddlewareValue::from(v)).collect()).unwrap();
    Self(values, set)
  }

  pub fn middleware_set(&self) -> &MiddlewareSet {
    &self.1
  }

  pub fn values(&self) -> &Vec<Value> {
    &self.0
  }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Dictionary(HashMap<String, Value>, MiddlewareDictionary);

impl Dictionary {
    pub fn new(values: HashMap<String, Value>) -> Self {
        let dict = MiddlewareDictionary::new(
            &values
                .iter()
                .map(|(k, v)| (hash_str(k), MiddlewareValue::from(v)))
                .collect::<HashMap<_, _>>(),
        )
        .unwrap();
        Self(values, dict)
    }

    pub fn middleware_dict(&self) -> &MiddlewareDictionary {
        &self.1
    }

    pub fn values(&self) -> &HashMap<String, Value> {
        &self.0
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Array(Vec<Value>, MiddlewareArray);

impl Array {
    pub fn new(values: Vec<Value>) -> Self {
        let array =
            MiddlewareArray::new(&values.iter().map(|v| MiddlewareValue::from(v)).collect())
                .unwrap();
        Self(values, array)
    }

    pub fn middleware_array(&self) -> &MiddlewareArray {
        &self.1
    }

    pub fn values(&self) -> &Vec<Value> {
        &self.0
    }
}
