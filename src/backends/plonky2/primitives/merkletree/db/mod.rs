#![allow(dead_code)]
//! Module that implements the key-value DB used at the MerkleTree module.

use std::{
    collections::HashMap,
    fmt::Debug,
    sync::{Arc, Mutex},
};

use anyhow::{anyhow, bail, Result};
use dyn_clone::DynClone;

use crate::{
    backends::plonky2::primitives::merkletree::{Leaf, Node},
    middleware::{RawValue, EMPTY_VALUE},
};

pub mod rocks;

pub trait DB: Debug + DynClone + Sync + Send {
    fn load_node(&self, hash: RawValue) -> Result<Node>;
    fn store_node(&mut self, node: Node) -> Result<()>;
}
dyn_clone::clone_trait_object!(DB);

/// MemDB implements the DB trait in a in-memory HashMap.
#[derive(Clone, Debug, Default)]
pub(crate) struct MemDB {
    inner: Arc<Mutex<HashMap<RawValue, Node>>>,
}

impl MemDB {
    pub fn new() -> Self {
        Self::default()
    }
}

impl DB for MemDB {
    fn load_node(&self, hash: RawValue) -> Result<Node> {
        let db = self
            .inner
            .lock()
            .map_err(|e| anyhow!("failed to acquire memdb lock for read: {}", e))?;

        if let Some(node) = db.get(&hash) {
            return Ok(node.clone());
        }

        if hash == RawValue::default() {
            return Ok(Node::Leaf(Leaf::new(hash, EMPTY_VALUE)));
        }

        bail!("MemDB error: node not found: {}", hash);
    }

    fn store_node(&mut self, node: Node) -> Result<()> {
        let mut db = self
            .inner
            .lock()
            .map_err(|e| anyhow!("failed to acquire memdb lock for write: {}", e))?;
        db.insert(node.hash().into(), node);
        Ok(())
    }
}

// NOTE: this can be replaced by `.to_bytes` & `from_bytes` optimized methods at `Node`
fn encode_node(node: &Node) -> Result<Vec<u8>> {
    serde_json::to_vec(node).map_err(|e| anyhow!("failed to serialize node: {e}"))
}
fn decode_node(bytes: &[u8]) -> Result<Node> {
    serde_json::from_slice(bytes).map_err(|e| anyhow!("failed to deserialize node: {e}"))
}

#[cfg(test)]
pub mod tests {

    use super::*;

    #[test]
    fn test_db() -> Result<()> {
        let mut db = MemDB::new();
        test_db_opt(&mut db)?;

        let path = "/tmp/rocksdb";
        let mut db = rocks::RocksDB::open(path)?;
        test_db_opt(&mut db)?;

        Ok(())
    }

    fn test_db_opt(db: &mut dyn DB) -> Result<()> {
        let node = Leaf::new(1.into(), 1.into());
        db.store_node(Node::Leaf(node.clone()))?;

        let obtained_node = db.load_node(node.hash.into())?;
        let leaf = match obtained_node {
            Node::Leaf(l) => l,
            _ => panic!("expected a leaf"),
        };
        assert_eq!(leaf.hash, node.hash);

        Ok(())
    }
}
