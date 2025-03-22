use anyhow::{anyhow, Result};
use schemars::JsonSchema;
use serde::{Deserialize, Serialize};
use std::fmt;

use super::{AnchoredKey, SignedPod, Value};
//use crate::middleware::{self, NativePredicate, Predicate};
use crate::middleware::{self, CustomPredicateRef};

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash, Serialize, Deserialize, JsonSchema)]
pub enum NativePredicate {
    None = 0,
    ValueOf = 1,
    Equal = 2,
    NotEqual = 3,
    Gt = 4,
    Lt = 5,
    SumOf = 8,
    ProductOf = 9,
    MaxOf = 10,
    DictContains = 11,
    DictNotContains = 12,
    SetContains = 13,
    SetNotContains = 14,
    ArrayContains = 15, // there is no ArrayNotContains
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize, JsonSchema)]
pub enum Predicate {
    Native(NativePredicate),
    BatchSelf(usize),
    Custom(CustomPredicateRef),
}

impl From<NativePredicate> for Predicate {
    fn from(v: NativePredicate) -> Self {
        Self::Native(v)
    }
}
