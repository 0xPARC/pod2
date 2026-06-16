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

fn kind_key(root: Hash) -> Vec<u8> {
    let mut k = Vec::with_capacity(2 + 4);
    k.extend_from_slice(b"k/");
    k.extend_from_slice(&root.to_bytes());
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

impl merkletree::db::Read for RocksDB {
    fn load_node(&self, hash: Hash) -> Result<Option<merkletree::Node>> {
        merkletree::db::rocks::load_node_db(&self.0, hash)
    }
}

impl merkletree::db::DB for RocksDB {
    fn tx<'a>(&'a self) -> Box<dyn merkletree::db::TX + 'a> {
        DB::tx(self)
    }

    // fn store_node(&mut self, node: merkletree::Node) -> Result<()> {
    //     self.db
    //         .put(node_key(node.hash()), node.encode()?)
    //         .map_err(|e| anyhow!("rocksdb transaction put failed: {e}"))
    // }
}

pub(crate) struct RocksTx<'a> {
    tx: rocksdb::Transaction<'a, rocksdb::TransactionDB>,
    db: RocksDB,
}

impl<'a> merkletree::db::Read for RocksTx<'a> {
    fn load_node(&self, hash: Hash) -> anyhow::Result<Option<merkletree::Node>> {
        merkletree::db::rocks::load_node_tx(&self.tx, hash)
    }
}

impl<'a> merkletree::db::TX for RocksTx<'a> {
    fn store_node(&mut self, node: merkletree::Node) -> anyhow::Result<()> {
        merkletree::db::rocks::store_node_tx(&self.tx, node)
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
        Ok(self.tx.get(kind_key(root)).map(|opt| {
            opt.map(|bytes| {
                assert_eq!(1, bytes.len());
                ContainerKind(bytes[0])
            })
        })?)
    }
}

impl<'a> TX for RocksTx<'a> {
    fn store_value(&mut self, mut value: Value) -> anyhow::Result<()> {
        let value_raw = value.raw();
        if let Some(old_value) = self.load_value(value_raw)? {
            // Never overwrite an old value with a RawValue.
            if value.is_raw() {
                return Ok(());
            }
            // If a container was previously stored, update the kind bitmask
            if let (TypedValue::Container(old_c), TypedValue::Container(ref mut c)) =
                (&old_value.typed, &mut value.typed)
            {
                c.kind.0 |= old_c.kind.0;
            }
        };
        self.tmp.values.insert(value_raw, value);
        Ok(())
    }
    fn update_kind(&mut self, root: Hash, kind: ContainerKind) -> anyhow::Result<()> {
        let kind = match self.load_kind(root).expect("ok") {
            Some(old_kind) => ContainerKind(old_kind.0 | kind.0),
            None => kind,
        };
        self.tmp.kinds.insert(root, kind);
        Ok(())
    }
    fn is_persistent(&self) -> bool {
        true
    }
    fn commit(mut self: Box<Self>) -> anyhow::Result<()> {
        self.tx.commit()
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
    fn load_kind(&self, root: Hash) -> anyhow::Result<Option<ContainerKind>> {
        todo!()
    }
}

impl DB for RocksDB {
    fn tx<'a>(&'a self) -> Box<dyn TX + 'a> {
        Box::new(RocksTx {
            tx: self.tx.transaction(),
            db: self.db.clone(),
        })
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
