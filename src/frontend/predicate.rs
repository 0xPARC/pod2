use anyhow::{anyhow, Result};
use schemars::JsonSchema;
use serde::{Deserialize, Serialize};
use std::fmt;

use super::{AnchoredKey, SignedPod, Value};
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

impl From<NativePredicate> for middleware::NativePredicate {
    fn from(np: NativePredicate) -> Self {
        use middleware::NativePredicate as MidNP;
        use NativePredicate::*;
        match np {
            None => MidNP::None,
            ValueOf => MidNP::ValueOf,
            Equal => MidNP::Equal,
            NotEqual => MidNP::NotEqual,
            Gt => MidNP::Gt,
            Lt => MidNP::Lt,
            SumOf => MidNP::SumOf,
            ProductOf => MidNP::ProductOf,
            MaxOf => MidNP::MaxOf,
            DictContains => MidNP::Contains,
            DictNotContains => MidNP::NotContains,
            SetContains => MidNP::Contains,
            SetNotContains => MidNP::NotContains,
            ArrayContains => MidNP::Contains,
        }
    }
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
