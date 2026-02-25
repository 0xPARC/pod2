use anyhow::Result;

use crate::middleware::{Hash, RawValue, EMPTY_HASH, EMPTY_VALUE, F};

struct Intermediate {
    hash: Hash,
    left_hash: Hash,
    right_hash: Hash,
}

impl Intermediate {
    fn compute_hash(left_hash: Hash, right_hash: Hash) -> Hash {
        let input: Vec<F> = [left_hash.0.to_vec(), right_hash.0.to_vec()].concat();
        hash_with_flag(F::TWO, &input)
    }
    fn new(left_hash: Hash, right_hash: Hash) -> Self {
        let hash = Self::compute_hash(left_hash, right_hash);
        Self {
            hash,
            left_hash,
            right_hash,
        }
    }
}

struct Leaf {
    hash: Hash,
    path: Vec<bool>,
    key: RawValue,
    value: RawValue,
}

enum Node {
    None,
    Leaf(Leaf),
    Intermediate(Intermediate),
}

trait Database {
    fn load_node(hash: Hash) -> Result<Node>;
}
