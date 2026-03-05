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

pub trait DB: Debug + DynClone + Sync + Send {
    fn begin_txn(&self, write: bool) -> Result<Box<dyn Txn>>;
}
dyn_clone::clone_trait_object!(DB);

pub trait Txn: Debug + Sync + Send {
    fn load_node(&self, hash: RawValue) -> Result<Node>;
    fn store_node(&mut self, hash: RawValue, node: Node) -> Result<()>;
    fn commit(self: Box<Self>) -> Result<()>;
    // TODO-NOTE: it may be the case that in some databases we're required to
    // 'discard' the txn in case that we're not committing it.
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
    fn begin_txn(&self, write: bool) -> Result<Box<dyn Txn>> {
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

    fn store_node(&mut self, hash: RawValue, node: Node) -> Result<()> {
        if !self.write {
            bail!("MemTxn error: cannot write in read-only transaction");
        }

        let mut db = self
            .db
            .lock()
            .map_err(|e| anyhow!("failed to acquire memdb lock for write: {}", e))?;
        db.insert(hash, node);
        Ok(())
    }

    fn commit(self: Box<Self>) -> Result<()> {
        Ok(())
    }
}
