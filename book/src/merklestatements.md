# Copied from statements.md

```
Branches(parent: AnchoredKey::MerkleTree, left: AnchoredKey::MerkleTree, right: AnchoredKey::MerkleTree)

Leaf(node: AnchoredKey::MerkleTree, key: AnchoredKey, value: AnchoredKey)

IsNullTree(node: AnchoredKey::MerkleTree)

GoesLeft(key: AnchoredKey, depth: Value::Integer)

GoesRight(key: AnchoredKey, depth: Value::Integer)

Contains(root: AnchoredKey::MerkleTree, key: AnchoredKey, value: AnchoredKey)

MerkleSubtree(root: AnchoredKey::MerkleTree, node: AnchoredKey::MerkleTree)

MerkleCorrectPath(root: AnchoredKey::MerkleTree, node: AnchoredKey::MerkleTree, key: AnchoredKey, depth: Value::Integer)

Contains(root: AnchoredKey::MerkleTree, key: AnchoredKey, value: AnchoredKey)

NotContains(root: AnchoredKey::MerkleTree, key: AnchoredKey)

ContainsHashedKey(root: AnchoredKey::DictOrSet, key: AnchoredKey)

NotContainsHashedKey(root: AnchoredKey::DictOrSet, key: AnchoredKey)

ContainsValue(root: AnchoredKey::Array, value: AnchoredKey)
```

# Statements involving compound types and Merkle trees

The front end has three compound types
- `Dictionary`
- `Array`
- `Set`

all of which are represented as `MerkleTree` on the back end.

The frontend compound types and their implementation as Merkle trees is explained under [POD value types](./values.md#dictionary-array-set).  The backend structure of a MerkleTree is explained on [the Merkle tree page](./merkletree.md).

The POD2 interface provides statements for working with Merkle trees and compond types at all layers of the stack:
- Primitive statements for Merkle trees
- General derived statements for Merkle trees
- Specialized `ContainsKey`, `NotContainsKey`, and `ContainsValue` statements for the three front-end types.

## Primitive statements for Merkle trees

```
Branches(parent: AnchoredKey::MerkleTree, left: AnchoredKey::MerkleTree, right: AnchoredKey::MerkleTree)

Leaf(node: AnchoredKey::MerkleTree, key: AnchoredKey, value: AnchoredKey)

IsNullTree(node: AnchoredKey::MerkleTree)

GoesLeft(key: AnchoredKey, depth: Value::Integer)

GoesRight(key: AnchoredKey, depth: Value::Integer)
```

These four statements expose the inner workings of a Merkle tree. Their implementations depend on the implementation details of POD2's sparse Merkle trees. In-circuit, verifying these statements requires low-level computation: either a hash or a binary decomposition.

Every Merkle root either:
- is a special type of Merkle tree called a "null tree", which has no elements,
- is a special type of Merkle tree called a "leaf", which just has a single element, or
- has two branches, left and right -- each of which is itself a Merkle tree.  Such a tree is called a "non-leaf" Merkle tree.

### `Branches`

```
Branches(parent, left, right)
```
means that ```parent``` is a non-leaf Merkle node, and ```left``` and ```right``` are its branches.  

A `Branches` statement is proved by computing a hash, as specified on [the Merkle tree page](./merkletree.md).

### `Leaf`

```
Leaf(node, key, value)
```
means that ```node``` is a leaf Merkle node, whose single item is the key-value pair ```(key, value)```.  

A `Leaf` statement is proved by computing a hash, as specified on [the Merkle tree page](./merkletree.md).

### `IsNullTree`

```
IsNullTree(node)
```
means that ```node``` is a null Merkle tree.

An `IsNullTree` statement is proved by comparing the value of `node` to `hash(0)`.

### `GoesLeft` and `GoesRight`

```
GoesLeft(key, depth)
```
means that if ```key``` is contained in a sparse Merkle tree, then at depth ```depth```, it must be in the left branch.

```GoesRight``` is similar.

A `GoesLeft` or `GoesRight` statement is proved by computing a binary decomposition of `key` and extracting the bit at index `depth`, as specified on [the Merkle tree page](./merkletree.md).

## General derived statements for Merkle trees

```
MerkleSubtree(root: AnchoredKey::MerkleTree, node: AnchoredKey::MerkleTree)

MerkleCorrectPath(root: AnchoredKey::MerkleTree, node: AnchoredKey::MerkleTree, key: AnchoredKey, depth: Value::Integer)

Contains(root: AnchoredKey::MerkleTree, key: AnchoredKey, value: AnchoredKey)

NotContains(root: AnchoredKey::MerkleTree, key: AnchoredKey)
```

### `MerkleSubtree`

```
MerkleSubtree(root, node)
```
means that there is a valid Merkle path of length `depth` from `root` to `node`.

A `MerkleSubtree` statement is proved as follows:
```
MerkleSubtree(root, root)
```
is automatically true.

Otherwise, `MerkleSubtree(root, node)` can be deduced from either
```
MerkleSubtree(root, parent)
Branches(parent, node, other)
```
or
```
MerkleSubtree(root, parent)
Branches(parent, other, node).
```

### `MerkleCorrectPath`

```
MerkleCorrectPath(root, node, key, depth)
```
means that there is a valid Merkle path of length `depth` from `root` to `node`, and if `key` appears as a key in the Merkle tree with root `root`, then `key` must be in the subtree under `node`.

A `MerkleCorrectPath` statement is proved as follows:
```
MerkleCorrectPath(root, root, key, 0)
```
is automatically true.

Otherwise, `MerkleCorrectPath(root, node, key, depth)` can be deduced from either:
```
MerkleCorrectPath(root, parent, key, depth-1)
Branches(parent, node, other)
GoesLeft(key, depth-1)
```
or
```
MerkleCorrectPath(root, parent, key, depth-1)
Branches(parent, other, node)
GoesRight(key, depth-1).
```

### `Contains`

```
Contains(root, key, value)
```
means that the key-value pair ```(key, value)``` is contained in the Merkle tree with Merkle root ```root```.

A `Contains` statement can be deduced from the following two statements.
```
MerkleSubtree(root, node)
Leaf(node, key, value)
```

### `NotContains`

```
NotContains(root, key)
```
means that the key ```key``` is not contained in the sparse Merkle tree with Merkle root ```root```.

The statement `NotContains(root, key)` can be deduced from either
```
MerkleCorrectPath(root, node, key, depth)
Leaf(node, otherkey, value)
NotEqual(otherkey, key)
```
or
```
MerkleCorrectPath(root, node, key, depth)
IsNullTree(node).
```

## Specialized statements for front-end compound types

```
ContainsHashedKey(root: AnchoredKey::DictOrSet, key: AnchoredKey)

NotContainsHashedKey(root: AnchoredKey::DictOrSet, key: AnchoredKey)

ContainsValue(root: AnchoredKey::Array, value: AnchoredKey)
```

When a dictionary or set is converted to a Merkle tree, its key is hashed -- see the [POD2 values page](./values.md#dictionary-array-set).

```ContainsHashedKey(root, key)``` is deduced from
```
Contains(root, keyhash, value)
keyhash = hash(key).
```

```NotContainsHashedKey(root, key)``` is deduced from 
```
NotContains(root, keyhash)
keyhash = hash(key)
```

```ContainsValue(root, value)``` is deduced from
```
Contains(root, idx, value).
```
