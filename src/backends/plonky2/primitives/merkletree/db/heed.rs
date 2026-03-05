use std::{fmt, path::Path, sync::Arc};

use anyhow::{anyhow, bail, Result};
use heed::{types::*, AnyTls, Database, Env, EnvOpenOptions, RoTxn, RwTxn, WithTls};

use super::{Txn, DB};
use crate::{
    backends::plonky2::primitives::merkletree::{Leaf, Node},
    middleware::{RawValue, EMPTY_VALUE},
};

#[derive(Clone)]
pub struct HeedDB {
    env: Env<AnyTls>,
    db: Database<Str, U32<heed::byteorder::NativeEndian>>,
}

impl HeedDB {
    pub fn open(path: impl AsRef<Path>) -> Result<Self> {
        let env = unsafe { EnvOpenOptions::new().open(path)? };

        let mut wtxn = env.write_txn()?;
        let db: Database<Str, U32<heed::byteorder::NativeEndian>> =
            env.create_database(&mut wtxn, None)?;

        Ok(Self { env, db })
    }
}

impl fmt::Debug for HeedDB {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        writeln!(f, "HeedDB")
    }
}

impl DB for HeedDB {
    fn begin_txn(&self, write: bool) -> Result<Box<dyn Txn>> {
        let txn = if write {
            HeedTxn {
                write: true,
                rw: Some(self.env.write_txn()?),
                ro: None,
            }
        } else {
            HeedTxn {
                write: false,
                rw: None,
                ro: Some(self.env.read_txn()?),
            }
        };
        Ok(Box::new(txn))
    }
}

struct HeedTxn<'a> {
    // ideally we would have a single parameter, but heed does not have a
    // unified txn interface
    write: bool,
    rw: Option<RwTxn<'a>>,
    ro: Option<RoTxn<'a>>,
}

impl fmt::Debug for HeedTxn<'_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        writeln!(f, "HeedTxn")
    }
}

impl<'a> Txn for HeedTxn<'a> {
    fn load_node(&self, hash: RawValue) -> Result<Node> {
        if hash == EMPTY_VALUE {
            return Ok(Node::Leaf(Leaf::new(hash, EMPTY_VALUE)));
        }

        todo!()
    }

    fn store_node(&mut self, hash: RawValue, node: Node) -> Result<()> {
        if !self.write {
            bail!("HeelTxn: cannot write in read-only transaction");
        }
        todo!()
    }

    fn commit(self: Box<Self>) -> Result<()> {
        if !self.write {
            return Ok(());
        }
        todo!()
    }
}
impl<'a> Drop for HeedTxn<'a> {
    fn drop(&mut self) {
        if self.write {
            self.rw.unwrap().abort()
        }
    }
}
