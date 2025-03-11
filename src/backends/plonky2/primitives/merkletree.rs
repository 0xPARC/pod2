//! Module that implements the MerkleTree specified at
//! https://0xparc.github.io/pod2/merkletree.html .
use anyhow::{anyhow, Result};
use plonky2::field::goldilocks_field::GoldilocksField;
use plonky2::hash::poseidon::PoseidonHash;
use plonky2::plonk::config::Hasher;
use std::collections::HashMap;
use std::fmt;
use std::iter::IntoIterator;

use crate::backends::plonky2::basetypes::{Hash, Value, F, NULL};

/// Implements the MerkleTree specified at
/// https://0xparc.github.io/pod2/merkletree.html
#[derive(Clone, Debug)]
pub struct MerkleTree {
    max_depth: usize,
    root: Node,
}

impl MerkleTree {
    /// builds a new `MerkleTree` where the leaves contain the given key-values
    pub fn new(max_depth: usize, kvs: &HashMap<Value, Value>) -> Result<Self> {
        let mut root = Node::Intermediate(Intermediate::empty());

        for (k, v) in kvs.iter() {
            let leaf = Leaf::new(max_depth, *k, *v)?;
            root.add_leaf(0, max_depth, leaf)?;
        }

        let _ = root.compute_hash();
        Ok(Self { max_depth, root })
    }

    /// returns the root of the tree
    pub fn root(&self) -> Hash {
        self.root.hash()
    }

    /// returns the max_depth parameter from the tree
    pub fn max_depth(&self) -> usize {
        self.max_depth
    }

    /// returns the value at the given key
    pub fn get(&self, key: &Value) -> Result<Value> {
        let path = keypath(self.max_depth, *key)?;
        let key_resolution = self.root.down(0, self.max_depth, path, None)?;
        match key_resolution {
            Some((k, v)) if &k == key => Ok(v),
            _ => Err(anyhow!("key not found")),
        }
    }

    /// returns a boolean indicating whether the key exists in the tree
    pub fn contains(&self, key: &Value) -> Result<bool> {
        let path = keypath(self.max_depth, *key)?;
        match self.root.down(0, self.max_depth, path, None) {
            Ok(Some((k, _))) => {
                if &k == key {
                    Ok(true)
                } else {
                    Ok(false)
                }
            }
            _ => Ok(false),
        }
    }

    /// returns a proof of existence, which proves that the given key exists in
    /// the tree. It returns the `value` of the leaf at the given `key`, and the
    /// `MerkleProof`.
    pub fn prove(&self, key: &Value) -> Result<(Value, MerkleProof)> {
        let path = keypath(self.max_depth, *key)?;

        let mut siblings: Vec<Hash> = Vec::new();

        match self
            .root
            .down(0, self.max_depth, path, Some(&mut siblings))?
        {
            Some((k, v)) if &k == key => Ok((
                v,
                MerkleProof {
                    existence: true,
                    siblings,
                    other_leaf: None,
                },
            )),
            _ => Err(anyhow!("key not found")),
        }
    }

    /// returns a proof of non-existence, which proves that the given
    /// `key` does not exist in the tree. The return value specifies
    /// the key-value pair in the leaf reached as a result of
    /// resolving `key` as well as a `MerkleProof`.
    pub fn prove_nonexistence(&self, key: &Value) -> Result<MerkleProof> {
        let path = keypath(self.max_depth, *key)?;

        let mut siblings: Vec<Hash> = Vec::new();

        // note: non-existence of a key can be in 2 cases:
        match self
            .root
            .down(0, self.max_depth, path, Some(&mut siblings))?
        {
            // case i) the expected leaf does not exist
            None => Ok(MerkleProof {
                existence: false,
                siblings,
                other_leaf: None,
            }),
            // case ii) the expected leaf does exist in the tree, but it has a different `key`
            Some((k, v)) if &k != key => Ok(MerkleProof {
                existence: false,
                siblings,
                other_leaf: Some((k, v)),
            }),
            _ => Err(anyhow!("key found")),
        }
        // both cases prove that the given key don't exist in the tree. ∎
    }

    /// verifies an inclusion proof for the given `key` and `value`
    pub fn verify(
        max_depth: usize,
        root: Hash,
        proof: &MerkleProof,
        key: &Value,
        value: &Value,
    ) -> Result<()> {
        let h = proof.compute_root_from_leaf(max_depth, key, Some(*value))?;

        if h != root {
            Err(anyhow!("proof of inclusion does not verify"))
        } else {
            Ok(())
        }
    }

    /// verifies a non-inclusion proof for the given `key`, that is, the given
    /// `key` does not exist in the tree
    pub fn verify_nonexistence(
        max_depth: usize,
        root: Hash,
        proof: &MerkleProof,
        key: &Value,
    ) -> Result<()> {
        match proof.other_leaf {
            Some((k, _v)) if &k == key => Err(anyhow!("Invalid non-existence proof.")),
            _ => {
                let k = proof.other_leaf.map(|(k, _)| k).unwrap_or(*key);
                let v: Option<Value> = proof.other_leaf.map(|(_, v)| v);
                let h = proof.compute_root_from_leaf(max_depth, &k, v)?;

                if h != root {
                    Err(anyhow!("proof of exclusion does not verify"))
                } else {
                    Ok(())
                }
            }
        }
    }

    /// returns an iterator over the leaves of the tree
    pub fn iter(&self) -> Iter {
        Iter {
            state: vec![&self.root],
        }
    }
}

/// Hash function for key-value pairs. Different branch pair hashes to
/// mitigate fake proofs.
pub fn kv_hash(key: &Value, value: Option<Value>) -> Hash {
    value
        .map(|v| {
            Hash(
                PoseidonHash::hash_no_pad(
                    &[key.0.to_vec(), v.0.to_vec(), vec![GoldilocksField(1)]].concat(),
                )
                .elements,
            )
        })
        .unwrap_or(Hash([GoldilocksField(0); 4]))
}

impl<'a> IntoIterator for &'a MerkleTree {
    type Item = (&'a Value, &'a Value);
    type IntoIter = Iter<'a>;

    fn into_iter(self) -> Self::IntoIter {
        self.iter()
    }
}

impl fmt::Display for MerkleTree {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        writeln!(
            f,
            "\nPaste in GraphViz (https://dreampuf.github.io/GraphvizOnline/):\n-----"
        )?;
        writeln!(f, "digraph hierarchy {{")?;
        writeln!(f, "node [fontname=Monospace,fontsize=10,shape=box]")?;
        write!(f, "{}", self.root)?;
        writeln!(f, "\n}}\n-----")
    }
}

#[derive(Clone, Debug)]
pub struct MerkleProof {
    // note: currently we don't use the `_existence` field, we would use if we merge the methods
    // `verify` and `verify_nonexistence` into a single one
    #[allow(unused)]
    existence: bool,
    siblings: Vec<Hash>,
    // other_leaf is used for non-existence proofs
    other_leaf: Option<(Value, Value)>,
}

impl fmt::Display for MerkleProof {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        for (i, s) in self.siblings.iter().enumerate() {
            if i > 0 {
                write!(f, ", ")?;
            }
            write!(f, "{}", s)?;
        }
        Ok(())
    }
}

impl MerkleProof {
    /// Computes the root of the Merkle tree suggested by a Merkle proof given a
    /// key & value. If a value is not provided, the terminal node is assumed to
    /// be empty.
    fn compute_root_from_leaf(
        &self,
        max_depth: usize,
        key: &Value,
        value: Option<Value>,
    ) -> Result<Hash> {
        if self.siblings.len() >= max_depth {
            return Err(anyhow!("max depth reached"));
        }

        let path = keypath(max_depth, *key)?;
        let mut h = kv_hash(key, value);
        for (i, sibling) in self.siblings.iter().enumerate().rev() {
            let input: Vec<F> = if path[i] {
                [sibling.0, h.0].concat()
            } else {
                [h.0, sibling.0].concat()
            };
            h = Hash(PoseidonHash::hash_no_pad(&input).elements);
        }
        Ok(h)
    }
}

#[derive(Clone, Debug)]
enum Node {
    None,
    Leaf(Leaf),
    Intermediate(Intermediate),
}

impl fmt::Display for Node {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Intermediate(n) => {
                writeln!(
                    f,
                    "\"{}\" -> {{ \"{}\" \"{}\" }}",
                    n.hash(),
                    n.left.hash(),
                    n.right.hash()
                )?;
                write!(f, "{}", n.left)?;
                write!(f, "{}", n.right)
            }
            Self::Leaf(l) => {
                writeln!(f, "\"{}\" [style=filled]", l.hash())?;
                writeln!(f, "\"k:{}\\nv:{}\" [style=dashed]", l.key, l.value)?;
                writeln!(
                    f,
                    "\"{}\" -> {{ \"k:{}\\nv:{}\" }}",
                    l.hash(),
                    l.key,
                    l.value,
                )
            }
            Self::None => Ok(()),
        }
    }
}

impl Node {
    fn is_empty(&self) -> bool {
        match self {
            Self::None => true,
            Self::Leaf(_l) => false,
            Self::Intermediate(_n) => false,
        }
    }
    fn compute_hash(&mut self) -> Hash {
        match self {
            Self::None => NULL,
            Self::Leaf(l) => l.compute_hash(),
            Self::Intermediate(n) => n.compute_hash(),
        }
    }
    fn hash(&self) -> Hash {
        match self {
            Self::None => NULL,
            Self::Leaf(l) => l.hash(),
            Self::Intermediate(n) => n.hash(),
        }
    }

    /// Goes down from the current node until it encounters a terminal node,
    /// viz. a leaf or empty node, or until it reaches the maximum depth. The
    /// `siblings` parameter is used to store the siblings while going down to
    /// the leaf, if the given parameter is set to `None`, then no siblings are
    /// stored. In this way, the same method `down` can be used by MerkleTree
    /// methods `get`, `contains`, `prove` and `prove_nonexistence`.
    ///
    /// Be aware that this method will return the found leaf at the given path,
    /// which may contain a different key and value than the expected one.
    fn down(
        &self,
        lvl: usize,
        max_depth: usize,
        path: Vec<bool>,
        mut siblings: Option<&mut Vec<Hash>>,
    ) -> Result<Option<(Value, Value)>> {
        if lvl >= max_depth {
            return Err(anyhow!("max depth reached"));
        }

        match self {
            Self::Intermediate(n) => {
                if path[lvl] {
                    if let Some(s) = siblings.as_mut() {
                        s.push(n.left.hash());
                    }
                    n.right.down(lvl + 1, max_depth, path, siblings)
                } else {
                    if let Some(s) = siblings.as_mut() {
                        s.push(n.right.hash());
                    }
                    n.left.down(lvl + 1, max_depth, path, siblings)
                }
            }
            Self::Leaf(Leaf {
                key,
                value,
                path: _p,
                hash: _h,
            }) => Ok(Some((*key, *value))),
            _ => Ok(None),
        }
    }

    // adds the leaf at the tree from the current node (self), without computing any hash
    fn add_leaf(&mut self, lvl: usize, max_depth: usize, leaf: Leaf) -> Result<()> {
        if lvl >= max_depth {
            return Err(anyhow!("max depth reached"));
        }

        match self {
            Self::Intermediate(n) => {
                if leaf.path[lvl] {
                    if n.right.is_empty() {
                        // empty sub-node, add the leaf here
                        n.right = Box::new(Node::Leaf(leaf));
                        return Ok(());
                    }
                    n.right.add_leaf(lvl + 1, max_depth, leaf)?;
                } else {
                    if n.left.is_empty() {
                        // empty sub-node, add the leaf here
                        n.left = Box::new(Node::Leaf(leaf));
                        return Ok(());
                    }
                    n.left.add_leaf(lvl + 1, max_depth, leaf)?;
                }
            }
            Self::Leaf(l) => {
                // in this case, it means that we found a leaf in the new-leaf
                // path, thus we need to push both leaves (old-leaf and
                // new-leaf) down the path till their paths diverge.

                // first check that keys of both leaves are different
                // (l=old-leaf, leaf=new-leaf)
                if l.key == leaf.key {
                    // Note: current approach returns an error when trying to
                    // add to a leaf where the key already exists. We could also
                    // ignore it if needed.
                    return Err(anyhow!("key already exists"));
                }
                let old_leaf = l.clone();
                // set self as an intermediate node
                *self = Node::Intermediate(Intermediate::empty());
                return self.down_till_divergence(lvl, max_depth, old_leaf, leaf);
            }
            Self::None => {
                return Err(anyhow!("reached empty node, should not have entered"));
            }
        }
        Ok(())
    }

    /// goes down through a 'virtual' path till finding a divergence. This
    /// method is used for when adding a new leaf another already existing leaf
    /// is found, so that both leaves (new and old) are pushed down the path
    /// till their keys diverge.
    fn down_till_divergence(
        &mut self,
        lvl: usize,
        max_depth: usize,
        old_leaf: Leaf,
        new_leaf: Leaf,
    ) -> Result<()> {
        if lvl >= max_depth {
            return Err(anyhow!("max depth reached"));
        }

        if let Node::Intermediate(ref mut n) = self {
            if old_leaf.path[lvl] != new_leaf.path[lvl] {
                // reached divergence in next level, set the leaves as children
                // at the current node
                if new_leaf.path[lvl] {
                    n.left = Box::new(Node::Leaf(old_leaf));
                    n.right = Box::new(Node::Leaf(new_leaf));
                } else {
                    n.left = Box::new(Node::Leaf(new_leaf));
                    n.right = Box::new(Node::Leaf(old_leaf));
                }
                return Ok(());
            }

            // no divergence yet, continue going down
            if new_leaf.path[lvl] {
                n.right = Box::new(Node::Intermediate(Intermediate::empty()));
                return n
                    .right
                    .down_till_divergence(lvl + 1, max_depth, old_leaf, new_leaf);
            } else {
                n.left = Box::new(Node::Intermediate(Intermediate::empty()));
                return n
                    .left
                    .down_till_divergence(lvl + 1, max_depth, old_leaf, new_leaf);
            }
        }
        Ok(())
    }
}

#[derive(Clone, Debug)]
struct Intermediate {
    hash: Option<Hash>,
    left: Box<Node>,
    right: Box<Node>,
}
impl Intermediate {
    fn empty() -> Self {
        Self {
            hash: None,
            left: Box::new(Node::None),
            right: Box::new(Node::None),
        }
    }
    fn compute_hash(&mut self) -> Hash {
        if self.left.clone().is_empty() && self.right.clone().is_empty() {
            self.hash = Some(NULL);
            return NULL;
        }
        let l_hash = self.left.compute_hash();
        let r_hash = self.right.compute_hash();
        let input: Vec<F> = [l_hash.0, r_hash.0].concat();
        let h = Hash(PoseidonHash::hash_no_pad(&input).elements);
        self.hash = Some(h);
        h
    }
    fn hash(&self) -> Hash {
        self.hash.unwrap()
    }
}

#[derive(Clone, Debug)]
struct Leaf {
    hash: Option<Hash>,
    path: Vec<bool>,
    key: Value,
    value: Value,
}
impl Leaf {
    fn new(max_depth: usize, key: Value, value: Value) -> Result<Self> {
        Ok(Self {
            hash: None,
            path: keypath(max_depth, key)?,
            key,
            value,
        })
    }
    fn compute_hash(&mut self) -> Hash {
        let h = kv_hash(&self.key, Some(self.value));
        self.hash = Some(h);
        h
    }
    fn hash(&self) -> Hash {
        self.hash.unwrap()
    }
}

// NOTE 1: think if maybe the length of the returned vector can be <256
// (8*bytes.len()), so that we can do fewer iterations. For example, if the
// tree.max_depth is set to 20, we just need 20 iterations of the loop, not 256.
// NOTE 2: which approach do we take with keys that are longer than the
// max-depth? ie, what happens when two keys share the same path for more bits
// than the max_depth?
/// returns the path of the given key
fn keypath(max_depth: usize, k: Value) -> Result<Vec<bool>> {
    let bytes = k.to_bytes();
    if max_depth > 8 * bytes.len() {
        // note that our current keys are of Value type, which are 4 Goldilocks
        // field elements, ie ~256 bits, therefore the max_depth can not be
        // bigger than 256.
        return Err(anyhow!(
            "key to short (key length: {}) for the max_depth: {}",
            8 * bytes.len(),
            max_depth
        ));
    }
    Ok((0..max_depth)
        .map(|n| bytes[n / 8] & (1 << (n % 8)) != 0)
        .collect())
}

pub struct Iter<'a> {
    state: Vec<&'a Node>,
}

impl<'a> Iterator for Iter<'a> {
    type Item = (&'a Value, &'a Value);

    fn next(&mut self) -> Option<Self::Item> {
        let node = self.state.pop();
        match node {
            Some(Node::None) => self.next(),
            Some(Node::Leaf(Leaf {
                hash: _,
                path: _,
                key,
                value,
            })) => Some((key, value)),
            Some(Node::Intermediate(Intermediate {
                hash: _,
                left,
                right,
            })) => {
                self.state.push(right);
                self.state.push(left);
                self.next()
            }
            _ => None,
        }
    }
}

#[cfg(test)]
pub mod tests {
    use itertools::Itertools;
    use std::cmp::Ordering;

    use super::*;

    #[test]
    fn test_merkletree() -> Result<()> {
        let mut kvs = HashMap::new();
        for i in 0..8 {
            if i == 1 {
                continue;
            }
            kvs.insert(Value::from(i), Value::from(1000 + i));
        }
        let key = Value::from(13);
        let value = Value::from(1013);
        kvs.insert(key, value);

        let tree = MerkleTree::new(32, &kvs)?;
        // when printing the tree, it should print the same tree as in
        // https://0xparc.github.io/pod2/merkletree.html#example-2
        println!("{}", tree);

        // Inclusion checks
        let (v, proof) = tree.prove(&Value::from(13))?;
        assert_eq!(v, Value::from(1013));
        println!("{}", proof);

        MerkleTree::verify(32, tree.root(), &proof, &key, &value)?;

        // Exclusion checks
        let key = Value::from(12);
        let proof = tree.prove_nonexistence(&key)?;
        assert_eq!(
            proof.other_leaf.unwrap(),
            (Value::from(4), Value::from(1004))
        );
        println!("{}", proof);

        MerkleTree::verify_nonexistence(32, tree.root(), &proof, &key)?;

        let key = Value::from(1);
        let proof = tree.prove_nonexistence(&Value::from(1))?;
        assert_eq!(proof.other_leaf, None);
        println!("{}", proof);

        MerkleTree::verify_nonexistence(32, tree.root(), &proof, &key)?;

        // Check iterator
        let collected_kvs: Vec<_> = tree.into_iter().collect::<Vec<_>>();

        // Expected key ordering
        let cmp = |max_depth: usize| {
            move |k1, k2| {
                let path1 = keypath(max_depth, k1).unwrap();
                let path2 = keypath(max_depth, k2).unwrap();

                let first_unequal_bits = std::iter::zip(path1, path2).find(|(b1, b2)| b1 != b2);

                match first_unequal_bits {
                    Some((b1, b2)) => {
                        if !b1 & b2 {
                            Ordering::Less
                        } else {
                            Ordering::Greater
                        }
                    }
                    _ => Ordering::Equal,
                }
            }
        };

        let sorted_kvs = kvs
            .iter()
            .sorted_by(|(k1, _), (k2, _)| cmp(32)(**k1, **k2))
            .collect::<Vec<_>>();

        assert_eq!(collected_kvs, sorted_kvs);

        Ok(())
    }
}
