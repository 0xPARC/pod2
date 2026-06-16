use std::sync::RwLockWriteGuard;

use super::*;
use crate::middleware::TypedValue;

#[derive(Default, Debug)]
struct Store {
    values: HashMap<RawValue, Value>,
    kinds: HashMap<Hash, ContainerKind>,
}

/// MemDB implements the DB trait in a in-memory HashMap.
#[derive(Clone, Debug, Default)]
pub struct MemDB {
    mt_db: merkletree::db::MemDB,
    db: Arc<RwLock<Store>>,
}

impl MemDB {
    pub fn new() -> Self {
        Self::default()
    }
}

impl merkletree::db::Read for MemDB {
    fn load_node(&self, hash: Hash) -> anyhow::Result<Option<merkletree::Node>> {
        self.mt_db.load_node(hash)
    }
}

impl merkletree::db::DB for MemDB {
    fn tx<'a>(&'a self) -> Box<dyn merkletree::db::TX + 'a> {
        DB::tx(self)
    }
}

impl Read for MemDB {
    fn load_value(&self, raw: RawValue) -> anyhow::Result<Option<Value>> {
        let store = self.db.read().expect("lock not poisoned");

        Ok(store.values.get(&raw).cloned())
    }
    fn load_kind(&self, root: Hash) -> anyhow::Result<Option<ContainerKind>> {
        let store = self.db.read().expect("lock not poisoned");
        Ok(store.kinds.get(&root).cloned())
    }
}

impl DB for MemDB {
    fn tx<'a>(&'a self) -> Box<dyn TX + 'a> {
        Box::new(MemTx {
            mt_tx: merkletree::db::DB::tx(&self.mt_db),
            db: self.db.write().expect("not poisoned"),
            tmp: Store::default(),
        })
    }
    fn is_persistent(&self) -> bool {
        false
    }
    fn clone_box(&self) -> Box<dyn DB> {
        Box::new(self.clone())
    }
}

pub(crate) struct MemTx<'a> {
    mt_tx: Box<dyn merkletree::db::TX + 'a>,
    db: RwLockWriteGuard<'a, Store>,
    tmp: Store,
}

impl<'a> merkletree::db::Read for MemTx<'a> {
    fn load_node(&self, hash: Hash) -> anyhow::Result<Option<merkletree::Node>> {
        self.mt_tx.load_node(hash)
    }
}

impl<'a> merkletree::db::TX for MemTx<'a> {
    fn store_node(&mut self, node: merkletree::Node) -> anyhow::Result<()> {
        self.mt_tx.store_node(node)
    }
    fn commit(self: Box<Self>) -> anyhow::Result<()> {
        panic!("use middleware::db::TX::commit")
    }
}

impl<'a> Read for MemTx<'a> {
    fn load_value(&self, raw: RawValue) -> anyhow::Result<Option<Value>> {
        Ok(self
            .tmp
            .values
            .get(&raw)
            .or_else(|| self.db.values.get(&raw))
            .cloned())
    }
    fn load_kind(&self, root: Hash) -> anyhow::Result<Option<ContainerKind>> {
        Ok(self
            .tmp
            .kinds
            .get(&root)
            .or_else(|| self.db.kinds.get(&root))
            .cloned())
    }
}

impl<'a> TX for MemTx<'a> {
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
        false
    }
    fn commit(mut self: Box<Self>) -> anyhow::Result<()> {
        self.mt_tx.commit()?;
        for (k, v) in self.tmp.values {
            self.db.values.insert(k, v);
        }
        for (k, v) in self.tmp.kinds {
            self.db.kinds.insert(k, v);
        }
        Ok(())
    }
}
