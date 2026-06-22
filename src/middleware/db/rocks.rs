use std::{fmt, path::Path, sync::Arc};

use anyhow::{anyhow, Result};
use rocksdb::{DBAccess, Options, ReadOptions, Transaction, TransactionDB, TransactionDBOptions};

use super::*;
use crate::middleware::EMPTY_HASH;

fn node_key(hash: Hash) -> Vec<u8> {
    let mut k = Vec::with_capacity(2 + 4);
    k.extend_from_slice(b"n/");
    k.extend_from_slice(&RawValue::from(hash).to_bytes());
    k
}

fn value_key(raw: RawValue) -> Vec<u8> {
    let mut k = Vec::with_capacity(2 + 4);
    k.extend_from_slice(b"v/");
    k.extend_from_slice(&raw.to_bytes());
    k
}

fn kind_key(root: Hash) -> Vec<u8> {
    let mut k = Vec::with_capacity(2 + 4);
    k.extend_from_slice(b"k/");
    k.extend_from_slice(&RawValue(root.0).to_bytes());
    k
}

#[derive(Clone)]
pub struct RocksDB(Arc<TransactionDB>);

impl fmt::Debug for RocksDB {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        writeln!(f, "RocksDB(path: {:?})", self.0.path())
    }
}

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

fn load_node_db(db: &impl DBAccess, hash: Hash) -> Result<Option<merkletree::Node>> {
    if hash == EMPTY_HASH {
        return Ok(Some(merkletree::Node::Intermediate(
            merkletree::Intermediate::new(EMPTY_HASH, EMPTY_HASH),
        )));
    }

    let node_key = node_key(hash);
    match db
        .get_opt(&node_key, &ReadOptions::default())
        .map_err(|e| anyhow!("rocksdb: get failed: {e}"))?
    {
        None => Ok(None),
        Some(bytes) => Ok(Some(merkletree::Node::decode(bytes.as_ref())?)),
    }
}

fn store_node_tx<'a>(tx: &Transaction<'a, TransactionDB>, node: merkletree::Node) -> Result<()> {
    let node_key = node_key(node.hash());
    tx.put(&node_key, node.encode()?)
        .map_err(|e| anyhow!("rocksdb transaction put failed: {e}"))
}

impl merkletree::db::Read for RocksDB {
    fn load_node(&self, hash: Hash) -> Result<Option<merkletree::Node>> {
        load_node_db(&*self.0, hash)
    }
}

impl merkletree::db::DB for RocksDB {
    fn tx<'a>(&'a self) -> Box<dyn merkletree::db::TX + 'a> {
        DB::tx(self)
    }
}

pub(crate) struct RocksTx<'a> {
    tx: rocksdb::Transaction<'a, rocksdb::TransactionDB>,
    db: RocksDB,
}

impl<'a> merkletree::db::Read for RocksTx<'a> {
    fn load_node(&self, hash: Hash) -> anyhow::Result<Option<merkletree::Node>> {
        load_node_db(&self.tx, hash)
    }
}

impl<'a> merkletree::db::TX for RocksTx<'a> {
    fn store_node(&mut self, node: merkletree::Node) -> anyhow::Result<()> {
        store_node_tx(&self.tx, node)
    }
    fn commit(self: Box<Self>) -> anyhow::Result<()> {
        panic!("use middleware::db::TX::commit")
    }
}

impl<'a> Read for RocksTx<'a> {
    fn load_value(&self, raw: RawValue) -> anyhow::Result<Option<Value>> {
        match self.tx.get(value_key(raw))? {
            None => Ok(None),
            Some(bytes) => Ok(Some({
                if bytes.is_empty() {
                    Value::from(raw)
                } else {
                    Value::from_bytes(bytes.as_ref(), self.db.clone_box())?
                }
            })),
        }
    }
    fn load_kind(&self, root: Hash) -> anyhow::Result<Option<ContainerKind>> {
        if root == EMPTY_HASH {
            return Ok(Some(
                *ContainerKind::default()
                    .set_dictionary()
                    .set_set()
                    .set_array(),
            ));
        }
        self.tx
            .get_for_update(kind_key(root), true)
            .map(|opt| {
                opt.map(|bytes| match bytes.len() {
                    1 => Ok(ContainerKind(bytes[0])),
                    l => Err(anyhow!("db: invalid kind len: {}", l)),
                })
            })?
            .transpose()
    }
}

impl<'a> TX for RocksTx<'a> {
    fn store_value(&mut self, value: Value) -> anyhow::Result<()> {
        let value_key = value_key(value.raw());
        if let Some(_old_value_bytes) = self.tx.get(&value_key)? {
            // Never overwrite an old value with a RawValue.
            if value.is_raw() {
                return Ok(());
            }
            // No need to update container kind bitmask because in persistent store we don't store
            // containers as Value, their content is stored as merkle nodes via the MerkleTree
        };
        let value_bytes = if value.is_raw() {
            // For RawValue we store an empty vector because it's a duplicate of the key.
            // This way we can easily check for RawValue without decoding.
            vec![]
        } else {
            Value::to_bytes(&value)
        };
        Ok(self.tx.put(value_key, value_bytes)?)
    }
    fn update_kind(&mut self, root: Hash, kind: ContainerKind) -> anyhow::Result<()> {
        let kind = match self.load_kind(root).expect("ok") {
            Some(old_kind) => ContainerKind(old_kind.0 | kind.0),
            None => kind,
        };
        let kind_key = kind_key(root);
        Ok(self.tx.put(&kind_key, [kind.0])?)
    }
    fn is_persistent(&self) -> bool {
        true
    }
    fn commit(self: Box<Self>) -> anyhow::Result<()> {
        Ok(self.tx.commit()?)
    }
}

impl Read for RocksDB {
    fn load_value(&self, raw: RawValue) -> anyhow::Result<Option<Value>> {
        match self.0.get(value_key(raw))? {
            None => Ok(None),
            Some(bytes) => Ok(Some({
                if bytes.is_empty() {
                    Value::from(raw)
                } else {
                    Value::from_bytes(bytes.as_ref(), self.clone_box())?
                }
            })),
        }
    }
    fn load_kind(&self, root: Hash) -> anyhow::Result<Option<ContainerKind>> {
        if root == EMPTY_HASH {
            return Ok(Some(
                *ContainerKind::default()
                    .set_dictionary()
                    .set_set()
                    .set_array(),
            ));
        }
        Ok(self.0.get(kind_key(root)).map(|opt| {
            opt.map(|bytes| {
                assert_eq!(1, bytes.len());
                ContainerKind(bytes[0])
            })
        })?)
    }
}

impl DB for RocksDB {
    fn tx<'a>(&'a self) -> Box<dyn TX + 'a> {
        Box::new(RocksTx {
            tx: self.0.transaction(),
            db: self.clone(),
        })
    }
    fn is_persistent(&self) -> bool {
        true
    }
    fn clone_box(&self) -> Box<dyn DB> {
        Box::new(self.clone())
    }
}
