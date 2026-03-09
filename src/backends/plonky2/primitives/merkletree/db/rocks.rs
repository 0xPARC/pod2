use std::{fmt, path::Path, sync::Arc};

use anyhow::{anyhow, Result};
use rocksdb::{Options, TransactionDB, TransactionDBOptions};

use super::DB;
use crate::{
    backends::plonky2::primitives::merkletree::{Leaf, Node},
    middleware::{RawValue, EMPTY_VALUE},
};

#[derive(Clone)]
pub struct RocksDB(Arc<TransactionDB>);

impl RocksDB {
    pub fn open(path: impl AsRef<Path>) -> Result<Self> {
        let mut options = Options::default();
        options.create_if_missing(true);
        let txn_options = TransactionDBOptions::default();
        let inner =
            TransactionDB::open(&options, &txn_options, path).map_err(|e| anyhow!("{e}"))?;
        Ok(Self(Arc::new(inner)))
    }
}

impl fmt::Debug for RocksDB {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        writeln!(f, "RocksDB")
    }
}

impl DB for RocksDB {
    fn load_node(&self, hash: RawValue) -> Result<Node> {
        if hash == EMPTY_VALUE {
            return Ok(Node::Leaf(Leaf::new(hash, EMPTY_VALUE)));
        }

        let maybe_node_bytes = self
            .0
            .get(hash.to_bytes())
            .map_err(|e| anyhow!("rocksdb transaction get failed: {e}"))?;

        match maybe_node_bytes {
            Some(bytes) => super::decode_node(&bytes),
            None => Err(anyhow!("rocksdb: node not found")),
        }
    }

    fn store_node(&mut self, node: Node) -> Result<()> {
        self.0
            .put(
                RawValue::from(node.hash()).to_bytes(),
                super::encode_node(&node)?,
            )
            .map_err(|e| anyhow!("rocksdb transaction put failed: {e}"))
    }
}
