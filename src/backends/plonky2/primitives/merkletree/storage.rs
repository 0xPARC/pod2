use std::{
    collections::HashMap,
    fs::{create_dir_all, rename, File},
    io::{Read, Write},
    path::{Path, PathBuf},
    sync::{Arc, RwLock},
};

use serde::{Deserialize, Serialize};

use super::{error::TreeResult, TreeError};
use crate::middleware::{Hash, RawValue};

/// Storage backend abstraction for persisted Merkle nodes and root hash.
///
/// The Merkle algorithm remains identical regardless of the backend. Backends
/// only control where the node graph and root are persisted.
pub trait MerkleStorage:
    Send + Sync + std::fmt::Debug + std::panic::RefUnwindSafe + std::panic::UnwindSafe
{
    fn load_root(&self) -> TreeResult<Option<Hash>>;
    fn save_root(&self, root: Hash) -> TreeResult<()>;
    fn load_node(&self, hash: Hash) -> TreeResult<Option<StoredNode>>;
    fn save_node(&self, hash: Hash, node: &StoredNode) -> TreeResult<()>;
}

#[derive(Clone, Debug, Serialize, Deserialize)]
pub enum StoredNode {
    Leaf { key: RawValue, value: RawValue },
    Intermediate { left: Hash, right: Hash },
}

/// In-memory storage backend.
#[derive(Debug, Default)]
pub struct InMemoryMerkleStorage {
    root: RwLock<Option<Hash>>,
    nodes: RwLock<HashMap<Hash, StoredNode>>,
}

impl InMemoryMerkleStorage {
    pub fn new() -> Self {
        Self::default()
    }
}

impl MerkleStorage for InMemoryMerkleStorage {
    fn load_root(&self) -> TreeResult<Option<Hash>> {
        Ok(*self
            .root
            .read()
            .map_err(|e| TreeError::from(anyhow::anyhow!("rwlock poisoned: {e}")))?)
    }

    fn save_root(&self, root: Hash) -> TreeResult<()> {
        *self
            .root
            .write()
            .map_err(|e| TreeError::from(anyhow::anyhow!("rwlock poisoned: {e}")))? = Some(root);
        Ok(())
    }

    fn load_node(&self, hash: Hash) -> TreeResult<Option<StoredNode>> {
        Ok(self
            .nodes
            .read()
            .map_err(|e| TreeError::from(anyhow::anyhow!("rwlock poisoned: {e}")))?
            .get(&hash)
            .cloned())
    }

    fn save_node(&self, hash: Hash, node: &StoredNode) -> TreeResult<()> {
        self.nodes
            .write()
            .map_err(|e| TreeError::from(anyhow::anyhow!("rwlock poisoned: {e}")))?
            .insert(hash, node.clone());
        Ok(())
    }
}

/// Disk-backed storage backend.
///
/// Stores Merkle root and node index as JSON files.
#[derive(Debug, Clone)]
pub struct DiskMerkleStorage {
    path: PathBuf,
}

impl DiskMerkleStorage {
    pub fn new(path: impl AsRef<Path>) -> Self {
        Self {
            path: path.as_ref().to_path_buf(),
        }
    }

    fn root_path(&self) -> PathBuf {
        self.path.with_extension("root.json")
    }

    fn nodes_dir(&self) -> PathBuf {
        self.path.with_extension("nodes")
    }

    fn hash_key(hash: Hash) -> String {
        format!(
            "{:016x}{:016x}{:016x}{:016x}",
            hash.0[0].0, hash.0[1].0, hash.0[2].0, hash.0[3].0
        )
    }

    fn node_path(&self, hash: Hash) -> PathBuf {
        self.nodes_dir()
            .join(format!("{}.json", Self::hash_key(hash)))
    }
}

impl MerkleStorage for DiskMerkleStorage {
    fn load_root(&self) -> TreeResult<Option<Hash>> {
        let path = self.root_path();
        if !path.exists() {
            return Ok(None);
        }
        let mut file = File::open(path).map_err(anyhow::Error::from)?;
        let mut buf = Vec::new();
        file.read_to_end(&mut buf).map_err(anyhow::Error::from)?;
        let root = serde_json::from_slice(&buf).map_err(anyhow::Error::from)?;
        Ok(Some(root))
    }

    fn save_root(&self, root: Hash) -> TreeResult<()> {
        let path = self.root_path();
        if let Some(parent) = path.parent() {
            create_dir_all(parent).map_err(anyhow::Error::from)?;
        }
        let bytes = serde_json::to_vec(&root).map_err(anyhow::Error::from)?;
        let tmp_path = path.with_extension("tmp");
        {
            let mut file = File::create(&tmp_path).map_err(anyhow::Error::from)?;
            file.write_all(&bytes).map_err(anyhow::Error::from)?;
        }
        rename(tmp_path, path).map_err(anyhow::Error::from)?;
        Ok(())
    }

    fn load_node(&self, hash: Hash) -> TreeResult<Option<StoredNode>> {
        let path = self.node_path(hash);
        if !path.exists() {
            return Ok(None);
        }
        let mut file = File::open(path).map_err(anyhow::Error::from)?;
        let mut buf = Vec::new();
        file.read_to_end(&mut buf).map_err(anyhow::Error::from)?;
        let node = serde_json::from_slice(&buf).map_err(anyhow::Error::from)?;
        Ok(Some(node))
    }

    fn save_node(&self, hash: Hash, node: &StoredNode) -> TreeResult<()> {
        let dir = self.nodes_dir();
        create_dir_all(&dir).map_err(anyhow::Error::from)?;
        let path = self.node_path(hash);
        let bytes = serde_json::to_vec(node).map_err(anyhow::Error::from)?;
        let tmp_path = path.with_extension("tmp");
        {
            let mut file = File::create(&tmp_path).map_err(anyhow::Error::from)?;
            file.write_all(&bytes).map_err(anyhow::Error::from)?;
        }
        rename(tmp_path, path).map_err(anyhow::Error::from)?;
        Ok(())
    }
}

pub fn in_memory_storage() -> Arc<dyn MerkleStorage> {
    Arc::new(InMemoryMerkleStorage::new())
}
