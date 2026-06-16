use super::*;

/// MemDB implements the DB trait in a in-memory HashMap.
#[derive(Clone, Debug, Default)]
pub struct MemDB {
    nodes: Arc<RwLock<HashMap<Hash, merkletree::Node>>>,
    values: Arc<RwLock<HashMap<RawValue, Value>>>,
}

impl MemDB {
    pub fn new() -> Self {
        Self::default()
    }
}

impl merkletree::db::Read for MemDB {
    fn load_node(&self, hash: Hash) -> anyhow::Result<Option<merkletree::Node>> {
        let nodes = self.nodes.read().expect("lock not poisoned");

        if hash == EMPTY_HASH {
            return Ok(Some(merkletree::Node::Intermediate(
                merkletree::Intermediate::new(EMPTY_HASH, EMPTY_HASH),
            )));
        }

        Ok(nodes.get(&hash).cloned())
    }
}

impl merkletree::db::DB for MemDB {
    fn tx<'a>(&'a self) -> Box<dyn merkletree::db::TX + 'a> {
        todo!()
    }

    // fn store_node(&mut self, node: merkletree::Node) -> anyhow::Result<()> {
    //     let mut nodes = self.nodes.write().expect("lock not poisoned");
    //     nodes.insert(node.hash(), node);
    //     Ok(())
    // }
}

impl Read for MemDB {
    fn load_value(&self, raw: RawValue) -> anyhow::Result<Option<Value>> {
        let values = self.values.read().expect("lock not poisoned");

        Ok(values.get(&raw).cloned())
    }
    fn load_kind(&self, root: Hash) -> anyhow::Result<ContainerKind> {
        todo!()
    }
}

impl DB for MemDB {
    fn tx<'a>(&'a self) -> Box<dyn TX + 'a> {
        todo!()
    }
    // fn store_value(&mut self, mut value: Value) -> anyhow::Result<()> {
    //     let mut values = self.values.write().expect("lock not poisoned");
    //     let value_raw = value.raw();
    //     if let Some(old_value) = values.get(&value_raw) {
    //         // Never overwrite an old value with a RawValue.
    //         if value.is_raw() {
    //             return Ok(());
    //         }
    //         // If a container was previously stored, update the kind bitmask
    //         if let (TypedValue::Container(old_c), TypedValue::Container(ref mut c)) =
    //             (&old_value.typed, &mut value.typed)
    //         {
    //             c.kind.0 |= old_c.kind.0;
    //         }
    //     };
    //     values.insert(value_raw, value);
    //     Ok(())
    // }
    fn is_persistent(&self) -> bool {
        false
    }
    fn clone_box(&self) -> Box<dyn DB> {
        Box::new(self.clone())
    }
}
