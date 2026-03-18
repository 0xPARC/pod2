use std::{fmt, path::Path, sync::Arc};

use anyhow::{anyhow, Result};
use rocksdb::{Options, TransactionDB, TransactionDBOptions};

use super::*;
use crate::middleware::{
    containers::{Array, Dictionary, Set},
    Predicate, PublicKey, SecretKey,
};

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

impl merkletree::db::DB for RocksDB {
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

    fn store_node(&mut self, node: merkletree::Node) -> Result<()> {
        self.db
            .put(node_key(node.hash()), node.encode()?)
            .map_err(|e| anyhow!("rocksdb transaction put failed: {e}"))
    }
}

#[derive(Serialize, Deserialize)]
enum ValueAux {
    Raw(RawValue),
    Int(i64),
    PublicKey(PublicKey),
    SecretKey(SecretKey),
    Predicate(Predicate),
    Set(Hash),
    Dictionary(Hash),
    Array(Hash),
    String(String),
}

impl From<Value> for ValueAux {
    fn from(v: Value) -> Self {
        match v.typed {
            TypedValue::Int(v) => ValueAux::Int(v),
            TypedValue::Raw(v) => ValueAux::Raw(v),
            TypedValue::PublicKey(v) => ValueAux::PublicKey(v),
            TypedValue::SecretKey(v) => ValueAux::SecretKey(v),
            TypedValue::Predicate(v) => ValueAux::Predicate(v),
            TypedValue::Set(v) => ValueAux::Set(v.commitment()),
            TypedValue::Dictionary(v) => ValueAux::Dictionary(v.commitment()),
            TypedValue::Array(v) => ValueAux::Array(v.commitment()),
            TypedValue::String(v) => ValueAux::String(v),
        }
    }
}

impl ValueAux {
    fn into_value(self, db: &RocksDB) -> Result<Value> {
        Ok(match self {
            ValueAux::Int(v) => Value::from(v),
            ValueAux::Raw(v) => Value::from(v),
            ValueAux::PublicKey(v) => Value::from(v),
            ValueAux::SecretKey(v) => Value::from(v),
            ValueAux::Predicate(v) => Value::from(v),
            ValueAux::Set(v) => Value::from(Set::from_db(v, Box::new(db.clone()))?),
            ValueAux::Dictionary(v) => Value::from(Dictionary::from_db(v, Box::new(db.clone()))?),
            ValueAux::Array(v) => Value::from(Array::from_db(v, Box::new(db.clone()))?),
            ValueAux::String(v) => Value::from(v),
        })
    }
}

// NOTE: serialization is using json.  Using a byte-native serialization would improve performance
// and storage usage.
impl DB for RocksDB {
    fn load_value(&self, raw: RawValue) -> anyhow::Result<Option<Value>> {
        match self.db.get(value_key(raw))? {
            None => Ok(None),
            Some(bytes) => {
                let value_aux: ValueAux = serde_json::from_slice(bytes.as_ref())?;
                Ok(Some(value_aux.into_value(self)?))
            }
        }
    }
    fn store_value(&mut self, value: Value) -> anyhow::Result<()> {
        let value_key = value_key(value.raw());
        let tx = self.db.transaction();
        if let Some(old_value_bytes) = tx.get_for_update(&value_key, true)? {
            // NOTE: If we could peek instead of doing a full decode this would improve performance
            let old_value: ValueAux = serde_json::from_slice(&old_value_bytes)?;
            // If we had a non-raw value stored never overwrite it with a raw value
            if !matches!(old_value, ValueAux::Raw(_)) && value.is_raw() {
                return Ok(());
            }
        }
        let value_bytes = serde_json::to_vec(&ValueAux::from(value))?;
        tx.put(value_key, value_bytes)?;
        Ok(tx.commit()?)
    }
    fn is_persistent(&self) -> bool {
        true
    }
    fn clone_box(&self) -> Box<dyn DB> {
        Box::new(self.clone())
    }
}
