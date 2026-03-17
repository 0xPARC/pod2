use std::{
    collections::{BTreeMap, HashMap, HashSet},
    fmt::Debug,
    sync::{Arc, RwLock},
};

use anyhow::bail;
use dyn_clone::DynClone;
use schemars::JsonSchema;
use serde::{de, ser, Deserialize, Deserializer, Serialize};

use super::serialization::{ordered_map, ordered_set};
#[cfg(feature = "backend_plonky2")]
use crate::backends::plonky2::primitives::merkletree::{
    self, MerkleProof, MerkleTree, MerkleTreeStateTransitionProof, TreeError,
};
use crate::middleware::{
    hash_str, Error, Hash, Key, RawValue, Result, TypedValue, Value, EMPTY_HASH, EMPTY_VALUE,
};

pub mod mem;

// Trait for database that stores values.  Must be cheap to clone.
pub trait DB: Debug + DynClone + Sync + Send + merkletree::db::DB {
    fn load_value(&self, raw: RawValue) -> anyhow::Result<Option<Value>>;
    // If the DB is persistent, for containers only the root needs to be stored because the
    // Container type makes sure the underlying merkle tree is stored in the DB independently, so
    // that it can be recovered back just with the root and the DB.
    // If the value is RawValue and a previous non-RawValue exists, no store overwrite it.
    // should be done. If the value is non-RawValue and a previous RawValue exists, store
    // should overwrite it.
    fn store_value(&mut self, value: Value) -> anyhow::Result<()>;
    fn is_persistent(&self) -> bool;
    fn clone_box(&self) -> Box<dyn DB>;
}
dyn_clone::clone_trait_object!(DB);
