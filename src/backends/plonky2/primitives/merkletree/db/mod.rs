//! Module that implements the key-value DB used at the MerkleTree module.

use std::{
    collections::HashMap,
    fmt::Debug,
    sync::{Arc, Mutex},
};

use anyhow::{anyhow, Result};
use dyn_clone::DynClone;

use crate::{
    backends::plonky2::primitives::merkletree::{Intermediate, Node},
    middleware::{Hash, EMPTY_HASH},
};

#[cfg(feature = "db_rocksdb")]
pub mod rocks;

pub trait Read {
    /// Must always return the empty intermediate node when hash is EMPTY_HASH
    fn load_node(&self, hash: Hash) -> Result<Option<Node>>;
}

pub trait TX: Read {
    fn store_node(&mut self, node: Node) -> Result<()>;
    fn commit(self: Box<Self>) -> Result<()>;
}

pub trait DB: Debug + DynClone + Sync + Send + Read {
    fn tx<'a>(&'a self) -> Box<dyn TX + 'a>;
}
dyn_clone::clone_trait_object!(DB);

/// MemDB implements the DB trait in a in-memory HashMap.
#[derive(Clone, Debug, Default)]
pub(crate) struct MemDB {
    inner: Arc<Mutex<HashMap<Hash, Node>>>,
}

impl MemDB {
    pub fn new() -> Self {
        Self::default()
    }
}

impl Read for MemDB {
    fn load_node(&self, hash: Hash) -> Result<Option<Node>> {
        let db = self
            .inner
            .lock()
            .map_err(|e| anyhow!("failed to acquire memdb lock for read: {}", e))?;

        if hash == EMPTY_HASH {
            return Ok(Some(Node::Intermediate(Intermediate::new(
                EMPTY_HASH, EMPTY_HASH,
            ))));
        }
        Ok(db.get(&hash).cloned())
    }
}

impl DB for MemDB {
    fn tx<'a>(&'a self) -> Box<dyn TX + 'a> {
        todo!()
    }
    // fn store_node(&mut self, node: Node) -> Result<()> {
    //     let mut db = self
    //         .inner
    //         .lock()
    //         .map_err(|e| anyhow!("failed to acquire memdb lock for write: {}", e))?;
    //     db.insert(node.hash(), node);
    //     Ok(())
    // }
}

#[cfg(test)]
pub mod tests {

    use super::{super::Leaf, *};

    #[test]
    fn test_db() -> Result<()> {
        let mut db = MemDB::new();
        test_db_opt(&mut db)?;

        #[cfg(feature = "db_rocksdb")]
        {
            let path = "/tmp/rocksdb";
            let mut db = rocks::RocksDB::open(path)?;
            test_db_opt(&mut db)?;
        }

        Ok(())
    }

    fn test_db_opt(db: &mut dyn DB) -> Result<()> {
        let node = Leaf::new(1.into(), 1.into());
        let mut tx = db.tx();
        tx.store_node(Node::Leaf(node.clone()))?;
        tx.commit().unwrap();

        let obtained_node = db.load_node(node.hash)?.unwrap();
        let leaf = match obtained_node {
            Node::Leaf(l) => l,
            _ => panic!("expected a leaf"),
        };
        assert_eq!(leaf.hash, node.hash);

        Ok(())
    }
}
