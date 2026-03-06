use std::{fmt, mem::ManuallyDrop, path::Path, sync::Arc};

use anyhow::{anyhow, bail, Result};
use rocksdb::{Options, Transaction, TransactionDB, TransactionDBOptions};

use super::{Txn, DB};
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
    fn begin_txn<'a>(&'a self, write: bool) -> Result<Box<dyn Txn + 'a>> {
        // let txn = self.0.transaction();
        let txn = ManuallyDrop::new(self.0.transaction_opt(
            &rocksdb::WriteOptions::default(),
            &rocksdb::TransactionOptions::default(),
        ));
        Ok(Box::new(RocksTxn::<'a> {
            txn,
            write,
            committed: false,
        }))
    }
}

struct RocksTxn<'a> {
    txn: ManuallyDrop<Transaction<'a, TransactionDB>>,
    write: bool,
    committed: bool,
}

impl fmt::Debug for RocksTxn<'_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        writeln!(f, "RocksTxn")
    }
}

impl Txn for RocksTxn<'_> {
    fn load_node(&self, hash: RawValue) -> Result<Node> {
        if hash == EMPTY_VALUE {
            return Ok(Node::Leaf(Leaf::new(hash, EMPTY_VALUE)));
        }

        match self.txn.get(hash.to_bytes())? {
            Some(bytes) => super::decode_node(&bytes),
            None => Err(anyhow!("rocksdb: node not found")),
        }
    }

    fn store_node(&mut self, node: Node) -> Result<()> {
        if !self.write {
            bail!("RocksTxn error: cannot write in read-only transaction");
        }
        self.txn
            .put(
                RawValue::from(node.hash()).to_bytes(),
                super::encode_node(&node)?,
            )
            .map_err(|e| anyhow!("rocksdb transaction put failed: {e}"))?;
        Ok(())
    }

    fn commit(&mut self) -> Result<()> {
        if !self.write {
            self.committed = true;
            return Ok(());
        }
        unsafe {
            let txn = ManuallyDrop::take(&mut self.txn);
            txn.commit()
                .map_err(|e| anyhow!("rocksdb transaction commit failed: {e}"))?;
            self.committed = true;
            Ok(())
        }
    }
}
impl<'a> Drop for RocksTxn<'a> {
    fn drop(&mut self) {
        if !self.committed {
            self.txn.rollback().unwrap() // TODO unwrap
        }
    }
}
