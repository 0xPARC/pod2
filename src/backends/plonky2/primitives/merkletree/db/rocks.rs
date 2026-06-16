use std::{fmt, path::Path, sync::Arc};

use anyhow::{anyhow, Result};
use rocksdb::{Options, Transaction, TransactionDB, TransactionDBOptions};

use crate::{
    backends::plonky2::primitives::merkletree::{self, db},
    middleware::{Hash, RawValue, EMPTY_HASH},
};

#[derive(Clone)]
pub struct RocksDB(pub(crate) Arc<TransactionDB>);

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
        writeln!(f, "RocksDB(path: {:?})", self.0.path())
    }
}

pub(crate) fn load_node_db(db: &TransactionDB, hash: Hash) -> Result<Option<merkletree::Node>> {
    if hash == EMPTY_HASH {
        return Ok(Some(merkletree::Node::Intermediate(
            merkletree::Intermediate::new(EMPTY_HASH, EMPTY_HASH),
        )));
    }

    match db
        .get(RawValue::from(hash).to_bytes())
        .map_err(|e| anyhow!("rocksdb: get failed: {e}"))?
    {
        None => Ok(None),
        Some(bytes) => Ok(Some(merkletree::Node::decode(bytes.as_ref())?)),
    }
}

impl db::Read for RocksDB {
    fn load_node(&self, hash: Hash) -> Result<Option<merkletree::Node>> {
        load_node_db(&self.db, hash)
    }
}

impl db::DB for RocksDB {
    fn tx<'a>(&'a self) -> Box<dyn db::TX + 'a> {
        Box::new(RocksTx(self.0.transaction()))
    }
}

pub(crate) struct RocksTx<'a>(pub(crate) Transaction<'a, TransactionDB>);

pub(crate) fn load_node_tx<'a>(
    tx: &Transaction<'a, TransactionDB>,
    hash: Hash,
) -> Result<Option<merkletree::Node>> {
    if hash == EMPTY_HASH {
        return Ok(Some(merkletree::Node::Intermediate(
            merkletree::Intermediate::new(EMPTY_HASH, EMPTY_HASH),
        )));
    }

    match tx
        .get(RawValue::from(hash).to_bytes())
        .map_err(|e| anyhow!("rocksdb: get failed: {e}"))?
    {
        None => Ok(None),
        Some(bytes) => Ok(Some(merkletree::Node::decode(bytes.as_ref())?)),
    }
}

impl<'a> db::Read for RocksTx<'a> {
    fn load_node(&self, hash: Hash) -> Result<Option<merkletree::Node>> {
        load_node_tx(&self.0, hash)
    }
}

pub(crate) fn store_node_tx(
    tx: &Transaction<'a, TransactionDB>,
    node: merkletree::Node,
) -> Result<()> {
    tx.put(RawValue::from(node.hash()).to_bytes(), node.encode()?)
        .map_err(|e| anyhow!("rocksdb transaction put failed: {e}"))
}

impl<'a> db::TX for RocksTx<'a> {
    fn store_node(&mut self, node: merkletree::Node) -> Result<()> {
        store_node_tx(&self.tx, node)
    }
    fn commit(self: Box<Self>) -> Result<()> {
        self.0
            .commit()
            .map_err(|e| anyhow!("rocksdb commit error: {e}"))
    }
}
