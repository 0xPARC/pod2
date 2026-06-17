use std::{
    collections::HashMap,
    fmt::Debug,
    sync::{Arc, RwLock},
};

use dyn_clone::DynClone;

#[cfg(feature = "backend_plonky2")]
use crate::backends::plonky2::primitives::merkletree::{self};
use crate::middleware::{ContainerKind, Hash, RawValue, Value};

pub mod mem;
#[cfg(feature = "db_rocksdb")]
pub mod rocks;

pub trait Read {
    fn load_value(&self, raw: RawValue) -> anyhow::Result<Option<Value>>;
    fn load_kind(&self, root: Hash) -> anyhow::Result<Option<ContainerKind>>;
}

pub trait TX: Read + merkletree::db::TX {
    // If the value is RawValue and a previous non-RawValue exists, no store will overwrite it.
    // If the value is non-RawValue and a previous RawValue exists, store should overwrite it,
    // merging the kind field in case of a Container (unless the DB is persistent).
    fn store_value(&mut self, value: Value) -> anyhow::Result<()>;
    fn update_kind(&mut self, root: Hash, kind: ContainerKind) -> anyhow::Result<()>;
    fn is_persistent(&self) -> bool;
    fn commit(self: Box<Self>) -> anyhow::Result<()>;
}

// pub trait TX: merkletree::db::DB {}

// Trait for database that stores values.  Must be cheap to clone.
pub trait DB: Debug + DynClone + Sync + Send + Read + merkletree::db::DB {
    // If the DB is persistent, for containers only the root needs to be stored because the
    // Container type makes sure the underlying merkle tree is stored in the DB independently, so
    // that it can be recovered back just with the root and the DB.
    fn is_persistent(&self) -> bool;
    fn clone_box(&self) -> Box<dyn DB>;
    fn tx<'a>(&'a self) -> Box<dyn TX + 'a>;
}
dyn_clone::clone_trait_object!(DB);
