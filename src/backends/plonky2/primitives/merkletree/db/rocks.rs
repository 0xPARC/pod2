use std::{fmt, path::Path, sync::Arc};

use anyhow::{anyhow, Result};
use rocksdb::{Options, TransactionDB, TransactionDBOptions};

use crate::{
    backends::plonky2::primitives::merkletree::{self, db},
    middleware::{Hash, RawValue, EMPTY_HASH},
};

#[derive(Clone)]
pub struct RocksDB(Arc<TransactionDB>);

#[allow(dead_code)]
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

impl db::DB for RocksDB {
    fn load_node(&self, hash: Hash) -> Result<Option<merkletree::Node>> {
        if hash == EMPTY_HASH {
            return Ok(Some(merkletree::Node::Intermediate(
                merkletree::Intermediate::new(EMPTY_HASH, EMPTY_HASH),
            )));
        }

        match self
            .0
            .get(RawValue::from(hash).to_bytes())
            .map_err(|e| anyhow!("rocksdb: get failed: {e}"))?
        {
            None => Ok(None),
            Some(bytes) => Ok(Some(merkletree::Node::decode(bytes.as_ref())?)),
        }
    }

    fn store_node(&mut self, node: merkletree::Node) -> Result<()> {
        self.0
            .put(RawValue::from(node.hash()).to_bytes(), node.encode()?)
            .map_err(|e| anyhow!("rocksdb transaction put failed: {e}"))
    }
}
