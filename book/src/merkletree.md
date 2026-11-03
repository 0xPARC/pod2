# MerkleTree

A `MerkleTree` is a sparse binary Merkle tree that stores a set of key-value
pairs with unique keys, and is committed to by its root hash.

## Notation

- A `key`, a `value` and a hash are each 4 Goldilocks field elements.
- `EMPTY = (0, 0, 0, 0)`.
- `H(flag, x)`: Poseidon permutation whose 12-element state is initialized to
  `flag` in every position, then the first 8 positions are overwritten with the
  8 elements of `x`, permuted once, and the first 4 elements are returned.

## Key path

The path of a key is its little-endian bit decomposition, using the canonical
(less than the field modulus) 64-bit representation of each element:

```
path[i] = bit (i mod 64) of key[i / 64]
```

`path[i] = 0` means "go left" at depth `i`, and `1` means "go right".  Distinct
keys have distinct paths, so the tree has depth at most 256.

Paths are taken from the raw keys, not from their hashes, so the shape of the
tree is controlled by the choice of keys.  This allows filling a shallow tree
completely, e.g. with the sequential keys `0..2^d` for a tree of depth `d`.
The flip side is that keys sharing a long path prefix produce a deep tree, so
whoever chooses the keys can push entries past a circuit's `max_depth`.  Keys
should be either chosen deliberately (e.g. sequential) or uniformly
distributed (e.g. hashes).

## Tree

The root of a set of entries `S`, all sharing the first `d` bits of their
paths, is defined recursively:

```
root(S, d) =
    EMPTY                              if S is empty
    leaf_hash(key, value)              if S = {(key, value)}
    node_hash(root(L, d+1), root(R, d+1))  otherwise
```

where `L` (resp. `R`) are the entries of `S` with `path[d] = 0` (resp. `1`),
and

```
leaf_hash(key, value)  = H(1, key ‖ value)
node_hash(left, right) = H(2, left ‖ right)
```

The root of the tree is `root(S, 0)`.  The flags `1` and `2` separate leaves
from intermediate nodes, so that one can't be passed off as the other.

## Example

Take the entries `{0: v0, 2: v2, 5: v5}`.  The first path bits are
`0 → 000`, `2 → 010` and `5 → 101`:

```
            root
           /    \
          n      leaf(5)
         / \
   leaf(0)  leaf(2)

n    = node_hash(leaf_hash(0, v0), leaf_hash(2, v2))
root = node_hash(n, leaf_hash(5, v5))
```

## Proofs

A Merkle proof for a key is the list of sibling hashes `siblings[0..n]` along
the key's path, where `siblings[i]` is the root of the subtree next to the
path at depth `i + 1`, and `n` is the depth where the path ends at a leaf or an
empty subtree.  It proves either that `(key, value)` is in the tree, or that
`key` is not, by showing that its path ends at an empty subtree or at a leaf
with a different key.

## Verification of a proof of existence

Input: `root`, `key`, `value` and `siblings[0..n]`.  The same check is implemented natively (`merkletree::verify`) and
in-circuit (`verify_merkle_proof_existence_circuit`).

```
h = leaf_hash(key, value)
for i = n-1 down to 0:
    if path[i] == 0:
        h = node_hash(h, siblings[i])
    else:
        h = node_hash(siblings[i], h)
accept iff h == root
```

### Circuit specifics

The circuit is built for a fixed `max_depth` (at most 256) and only uses the
first `max_depth` bits of the path.
`siblings` is padded with `EMPTY` up to `max_depth`, and `n` is taken as one
plus the index of the last non-empty sibling (`0` if all are empty).  This
loses nothing: in a valid proof the last sibling is never `EMPTY`, otherwise
the leaf would have been collapsed one level higher.
