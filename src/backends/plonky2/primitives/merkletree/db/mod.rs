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
    fn begin_txn<'a>(&'a self, write: bool) -> Result<Box<dyn Txn + 'a>>;
}
dyn_clone::clone_trait_object!(DB);

/// Txn implements an atomic transaction for the DB.
/// `Drop` is used to discard the db's transactions when not used.
pub trait Txn: Debug + Send {
    fn load_node(&self, hash: RawValue) -> Result<Node>;
    fn store_node(&mut self, node: Node) -> Result<()>;
    fn commit(&mut self) -> Result<()>;
}

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
    fn begin_txn<'a>(&'a self, write: bool) -> Result<Box<dyn Txn + 'a>> {
        Ok(Box::new(MemTxn {
            db: Arc::clone(&self.inner),
            write,
        }))
    }
}

// WIP: for now the MemTxn is fake and directly writes to the MemDB.
#[derive(Debug)]
struct MemTxn {
    db: Arc<Mutex<HashMap<RawValue, Node>>>,
    write: bool,
}

impl Txn for MemTxn {
    fn load_node(&self, hash: RawValue) -> Result<Node> {
        let db = self
            .db
            .lock()
            .map_err(|e| anyhow!("failed to acquire memdb lock for read: {}", e))?;

        if let Some(node) = db.get(&hash) {
            return Ok(node.clone());
        }

        if hash == RawValue::default() {
            return Ok(Node::Leaf(Leaf::new(hash, EMPTY_VALUE)));
        }

        bail!("MemTxn error: node not found: {}", hash);
    }

    fn store_node(&mut self, node: Node) -> Result<()> {
        if !self.write {
            bail!("MemTxn error: cannot write in read-only transaction");
        }

        let mut db = self
            .db
            .lock()
            .map_err(|e| anyhow!("failed to acquire memdb lock for write: {}", e))?;
        db.insert(node.hash().into(), node);
        Ok(())
    }

    fn commit(&mut self) -> Result<()> {
        Ok(())
    }
}

// NOTE: this will be replaced by `.to_bytes` & `from_bytes` optimized methods at `Node`
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
        let db = Box::new(MemDB::new());
        test_db_opt(db)?;

        let path = "/tmp/rocksdb";
        let db = Box::new(rocks::RocksDB::open(path)?);
        test_db_opt(db)?;

        Ok(())
    }

    fn test_db_opt(db: Box<dyn DB>) -> Result<()> {
        let mut txn = db.begin_txn(true)?;
        let node = Leaf::new(1.into(), 1.into());
        txn.store_node(Node::Leaf(node.clone()))?;

        txn.commit()?;

        let txn = db.begin_txn(false)?;
        let obtained_node = txn.load_node(node.hash.into())?;
        let leaf = match obtained_node {
            Node::Leaf(l) => l,
            _ => panic!("expected a leaf"),
        };
        assert_eq!(leaf.hash, node.hash);

        // next transaction will be dropped when the test function ends
        let _txn = db.begin_txn(false)?;

        Ok(())
    }
}
