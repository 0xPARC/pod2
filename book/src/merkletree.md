# MerkleTree

In the POD2 backend, a MerkleTree is used to store an unordered set of key-value pairs.  The frontend compound types `Array`, `Set`, and `Dictionary` are all represented as `MerkleTree`s on the backend.

From the high level, we can think of a `MerkleTree` as a 'hashmap' storage, that allows us to generate proofs of inclusion and non-inclusion of the key-values stored into it, as well as proofs of correct insertion, update and deletion.

A `MerkleTree` is represented in-circuit as its Merkle root; in the Plonky2 backend, this root is a tuple of four field elements.  This makes a `MerkleTree` the same size in-circuit as the atomic types `Int` and `String`.  (In general, regardless of the proof system used on the backend, all three types are represented in-circuit by the same number of field elements; this number is determined by the security requirement of the hash function.)

The encoding of the `MerkleTree` is a recursive process:
- Encode all keys and values in the `MerkleTree`.
- Put all keys and values into a sparse Merkle tree.
- The `MerkleTree` is encoded in-circuit as the root of this sparse Merkle tree.

This document explains the construction of the sparse Merkle tree.

## The branching rule

A sparse Merkle tree is implemented as a binary tree.  The insertion path of any key is given by a deterministic rule: given ```key``` and a nonnegative integer ```depth```, the rule determines that ```key``` belongs to either the ```left``` or ```right``` branch at depth ```depth```.

The precise rule is as follows.  The key is a backend value, which is a 4-tuple of field elements
```
key = (k_0, k_1, k_2, k_3).
```
Write the field elements in binary (in little-endian order):
```
k_0 = b_0 b_1 ... b_63
k_1 = b_64 b_65 ... b_127
....
```

At the root, ```key``` goes to the left subtree if ```b_0 = 0```, otherwise the right subtree.  At depth 1, ```key``` goes to the left subtree if ```b_1 = 0```, otherwise the right subtree, and similarly for higher depth.

The key bits are used directly, without hashing.  Dictionary keys are already hashes (of the key strings) and set keys are hashes for any non-integer value, so their paths are pseudo-random.  Array keys are small integers, so arrays fill the tree densely from the left.

## The tree structure

A Merkle tree with no entry at all is represented by the empty hash
```root = (0, 0, 0, 0)```.

A Merkle tree with a single entry ```(key, value)``` is called a "leaf".  It is represented by the hash value
```root = hash(1, (key, value))```, where `1` is a flag indicating that it is a leaf, and it's used as the initial state of the hash (Poseidon) permutation.

A Merkle tree ```tree``` with more than one entry is required to have two subtrees, ```left``` and ```right```.  It is then represented by the hash value
```root = hash(2, (left_root, right_root))```, where `2` is a flag indicating that it is an intermediate node, and it's used as the initial state of the hash (Poseidon) permutation.

The flags are used as the initial state of the Poseidon permutation so that they don't account for extra inputs in the Poseidon gadget, needing only 1 gate for each node/leaf hash.

(The role of the constants 1 and 2 is to prevent collisions between leaves and non-leaf Merkle roots.  If the constants were omitted, a large Merkle tree could be dishonestly interpreted as a leaf, leading to security vulnerabilities.)

## Example 1

Suppose we want to build a Merkle tree from the following key-value pairs, where the keys are integers:
```
{
    4: "even",
    5: "odd",
    6: "even"
}
```

The keys are integers, so they are represented in-circuit by themselves.  In little-endian order, the first three bits of the keys are:
```
4 = 001...
5 = 101...
6 = 011...
```

The resulting tree looks like:
```
                        root
                         /\
                        /  \
                       /    \
                      /      \
                   L_root   R_root = hash(1, (5, "odd"))
                     /\
                    /  \
                   /    \
                  /      \
               LL_root  LR_root = hash(1, (6, "even"))
                 ||
         hash(1, (4, "even"))
```

The intermediate roots are computed as hashes of their subroots:
```
L_root = hash(2, (LL_root, LR_root))
root = hash(2, (L_root, R_root)).
```

The full set of key-value pairs is then represented in the backend as `root` (four field elements in the Plonky2 backend).

### Example 2
So for example, imagine we have 8 key-pairs, where the keys are just an enumeration from 0 to 7, then the tree leaves positions would look like:
![](img/merkletree-example-1-a.png)

Now let's replace the leaf `key=1` by a leaf with `key=13`.  Since `5` and `13` share their first three bits, their respective leaf paths will be the same until they diverge in the 4-th bit:

![](img/merkletree-example-1-b.png)


### Example 3

Suppose we have 4 key-values, where the first four bits of the keys are `0000`, `0100`, `1010` and `1011`. The tree would look like:
![](img/merkletree-example-2-a.png)

To iterate this example, suppose we have the following `Dictionary`:
```js
{
	idNumber: "424242",
	dateOfBirth: 1169909384,
	userPk: 9876543210, // target user of this dictionary
	_signerPk: 1234567890, // signer of the dictionary
}
```

Suppose that the binary representation of the hash of the key `userPk` is `1011...`. This uniquely defines the leaf position that contains the public key of the authenticated user. Similarly for the other key-values:

![](img/merkletree-example-2-b.png)


## Proofs of inclusion and non-inclusion
Merkle proofs contain the siblings along the path from the leaf to the root, where the leaf position is determined by the key binary representation.

Since leaf positions are deterministic based on the key, the same approach is used for non-inclusion proofs, where it can be proven that a key is not in the tree, and furthermore, that a value is not in the tree (although the key exists):
1. Proving that the key does not exist in the tree is achieved by generating the merkle-proof for the specific key, and showing that the (virtual) leaf is empty - this is, showing that going down the path of the non-existing key, there is a leaf with a different key, meaning that the non-existing key has not been inserted in the tree.
2. Proving that a value is not in the tree (although the key exists) is achieved by generating the merkle-proof for the specific key, and showing that the leaf exists but it has a different value than the one being proved.

For the current use cases, we don't need to prove that the key exists but the value is different on that leaf, so we only use the option 1.

There are 2 cases to have into account when dealing with non-inclusion proofs:
- case i) the expected leaf does not exist.
- case ii) the expected leaf does exist in the tree, but it has a different `key`.

In case ii) the proof includes the key-value pair of the other leaf found on the path.

## State transition proofs

A state transition proof shows that a tree with root `new_root` is obtained from a tree with root `old_root` by one operation on the entry `(key, value)`:
- **insert**: `key` does not exist under `old_root` (non-inclusion proof), and `(key, value)` exists under `new_root`.
- **update**: `key` exists under `old_root` with some value, and under `new_root` it maps to `value` instead.
- **delete**: `(key, value)` exists under `old_root`, and `key` does not exist under `new_root`.

In all cases the circuit checks that the rest of the tree is unchanged.  These proofs back the `ContainerInsert`, `ContainerUpdate` and `ContainerDelete` [statements](./statements.md).

## Proof depth

Out of circuit the tree can have up to 256 levels (one per key bit).  In-circuit, Merkle proofs are verified with a fixed maximum depth.  The MainPOD supports two sizes of Merkle proof gadgets: *small* proofs (8 levels by default) and *medium* proofs (32 levels by default), with the number of each configured by the circuit parameters.

## Interface

```rust
impl MerkleTree {
    /// builds a new `MerkleTree` where the leaves contain the given key-values
    fn new(kvs: &HashMap<RawValue, RawValue>) -> Self;

    /// returns the root of the tree
    fn root(&self) -> Hash;

    /// returns the value at the given key
    fn get(&self, key: &RawValue) -> Result<Option<RawValue>>;

    /// returns a boolean indicating whether the key exists in the tree
    fn contains(&self, key: &RawValue) -> Result<bool>;

    /// inserts / updates / deletes an entry, returning a proof of the state transition
    fn insert(&mut self, key: &RawValue, value: &RawValue) -> Result<MerkleTreeStateTransitionProof>;
    fn update(&mut self, key: &RawValue, value: &RawValue) -> Result<MerkleTreeStateTransitionProof>;
    fn delete(&mut self, key: &RawValue) -> Result<MerkleTreeStateTransitionProof>;

    /// returns a proof of existence, which proves that the given key exists in
    /// the tree. It returns the `value` of the leaf at the given `key`, and the
    /// `MerkleProof`.
    fn prove(&self, key: &RawValue) -> Result<(RawValue, MerkleProof)>;

    /// returns a proof of non-existence, which proves that the given
    /// `key` does not exist in the tree.
    fn prove_nonexistence(&self, key: &RawValue) -> Result<MerkleProof>;

    /// returns an iterator over the leaves of the tree
    fn iter(&self) -> Iter;
}

/// verifies an inclusion proof for the given `key` and `value`
fn verify(root: Hash, proof: &MerkleProof, key: &RawValue, value: &RawValue) -> Result<()>;

/// verifies a non-inclusion proof for the given `key`, that is, the given
/// `key` does not exist in the tree
fn verify_nonexistence(root: Hash, proof: &MerkleProof, key: &RawValue) -> Result<()>;

/// verifies a state transition proof (insert, update or delete)
fn verify_state_transition(proof: &MerkleTreeStateTransitionProof) -> Result<()>;
```

## Resources
- [https://docs.iden3.io/publications/pdfs/Merkle-Tree.pdf](https://docs.iden3.io/publications/pdfs/Merkle-Tree.pdf)
- [https://eprint.iacr.org/2018/955](https://eprint.iacr.org/2018/955)
