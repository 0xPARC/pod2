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

impl merkletree::db::DB for MemDB {
    fn load_node(&self, hash: Hash) -> anyhow::Result<Option<merkletree::Node>> {
        let nodes = self.nodes.read().expect("lock not poisoned");

        if hash == EMPTY_HASH {
            return Ok(Some(merkletree::Node::Intermediate(
                merkletree::Intermediate::new(EMPTY_HASH, EMPTY_HASH),
            )));
        }

        Ok(nodes.get(&hash).cloned())
    }

    fn store_node(&mut self, node: merkletree::Node) -> anyhow::Result<()> {
        let mut nodes = self.nodes.write().expect("lock not poisoned");
        nodes.insert(node.hash(), node);
        Ok(())
    }
}

impl DB for MemDB {
    fn load_value(&self, raw: RawValue) -> anyhow::Result<Option<Value>> {
        let values = self.values.read().expect("lock not poisoned");

        Ok(values.get(&raw).cloned())
    }
    fn store_value(&mut self, value: Value) -> anyhow::Result<()> {
        let mut values = self.values.write().expect("lock not poisoned");
        let value_raw = value.raw();
        if let Some(old_value) = values.get(&value_raw) {
            // If we had a non-raw value stored never overwrite it with a raw value
            if !old_value.is_raw() && value.is_raw() {
                return Ok(());
            }
        }
        values.insert(value_raw, value);
        Ok(())
    }
    fn is_persistent(&self) -> bool {
        false
    }
    fn clone_box(&self) -> Box<dyn DB> {
        Box::new(self.clone())
    }
}
