use std::{fmt, path::Path, sync::Arc};

use anyhow::{anyhow, Result};
use rocksdb::{Options, TransactionDB, TransactionDBOptions};

use super::*;

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

#[derive(Clone)]
pub struct RocksDB {
    db: Arc<TransactionDB>,
}

impl fmt::Debug for RocksDB {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        writeln!(f, "RocksDB(path: {:?})", self.db.path())
    }
}

impl RocksDB {
    pub fn open(path: impl AsRef<Path>) -> Result<Self> {
        let mut options = Options::default();
        options.create_if_missing(true);
        let txn_options = TransactionDBOptions::default();
        let inner =
            TransactionDB::open(&options, &txn_options, path).map_err(|e| anyhow!("{e}"))?;
        Ok(Self {
            db: Arc::new(inner),
        })
    }
}

impl merkletree::db::Read for RocksDB {
    fn load_node(&self, hash: Hash) -> Result<Option<merkletree::Node>> {
        if hash == EMPTY_HASH {
            return Ok(Some(merkletree::Node::Intermediate(
                merkletree::Intermediate::new(EMPTY_HASH, EMPTY_HASH),
            )));
        }

        match self.db.get(node_key(hash))? {
            None => Ok(None),
            Some(bytes) => Ok(Some(merkletree::Node::decode(bytes.as_ref())?)),
        }
    }
}

impl merkletree::db::DB for RocksDB {
    fn tx<'a>(&'a self) -> Box<dyn merkletree::db::TX + 'a> {
        todo!()
    }

    // fn store_node(&mut self, node: merkletree::Node) -> Result<()> {
    //     self.db
    //         .put(node_key(node.hash()), node.encode()?)
    //         .map_err(|e| anyhow!("rocksdb transaction put failed: {e}"))
    // }
}

pub struct RocksTx<'a> {
    tx: rocksdb::Transaction<'a, rocksdb::TransactionDB>,
}

impl<'a> fmt::Debug for RocksTx<'a> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        writeln!(f, "RocksTx")
    }
}

// impl<'a> merkletree::db::DB for RocksTx<'a> {
//     fn load_node(&self, hash: Hash) -> Result<Option<merkletree::Node>> {
//         if hash == EMPTY_HASH {
//             return Ok(Some(merkletree::Node::Intermediate(
//                 merkletree::Intermediate::new(EMPTY_HASH, EMPTY_HASH),
//             )));
//         }
//
//         match self.tx.get(node_key(hash))? {
//             None => Ok(None),
//             Some(bytes) => Ok(Some(merkletree::Node::decode(bytes.as_ref())?)),
//         }
//     }
//
//     fn store_node(&mut self, node: merkletree::Node) -> Result<()> {
//         self.tx
//             .put(node_key(node.hash()), node.encode()?)
//             .map_err(|e| anyhow!("rocksdb transaction put failed: {e}"))
//     }
// }

impl Read for RocksDB {
    fn load_value(&self, raw: RawValue) -> anyhow::Result<Option<Value>> {
        match self.db.get(value_key(raw))? {
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
    fn load_kind(&self, root: Hash) -> anyhow::Result<ContainerKind> {
        todo!()
    }
}

impl DB for RocksDB {
    fn tx<'a>(&'a self) -> Box<dyn TX + 'a> {
        todo!()
    }
    // fn store_value(&mut self, value: Value) -> anyhow::Result<()> {
    //     let value_key = value_key(value.raw());
    //     let tx = self.db.transaction();
    //     if let Some(_old_value_bytes) = tx.get_for_update(&value_key, true)? {
    //         // Never overwrite an old value with a RawValue.
    //         if value.is_raw() {
    //             return Ok(());
    //         }
    //         // No need to update container kind bitmask because in persistent store we don't store
    //         // containers as Value, their content is stored as merkle nodes via the MerkleTree
    //     }
    //     let value_bytes = if value.is_raw() {
    //         // For RawValue we store an empty vector because it's a duplicate of the key.
    //         // This way we can easily check for RawValue without decoding.
    //         vec![]
    //     } else {
    //         Value::to_bytes(&value)
    //     };
    //     tx.put(value_key, value_bytes)?;
    //     Ok(tx.commit()?)
    // }
    fn is_persistent(&self) -> bool {
        true
    }
    fn clone_box(&self) -> Box<dyn DB> {
        Box::new(self.clone())
    }
    // fn tx<'a>(&'a self) -> Box<dyn TX + 'a> {
    //     Box::new(self.db.transaction())
    // }
}
