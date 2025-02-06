# Encoding dictionaries as Merkle trees

In the backend, every value of any of the three types
- `Integer`
- `String`
- `Dictionary`
is represented by a sequence of field elements of the same length, which is the output length of the cryptographic hash function.  (In the case of the Plonky2 backend with 100 bits of security, all of these types are represented as 4 field elements.)

The encoding of `Integer` and `String` types is explained in [Values](./values.md) -- in brief, a integer is encoded in limbs of suitable size, while a string is encoded by hashing.

The encoding of the `Dictionary` is a recursive process:
- Encode all keys and values in the `Dictionary`.
- Put all keys and values into a sparse Merkle tree.
- The `Dictionary` is encoded as the root of this sparse Merkle tree.

This document explains the construction of the sparse Merkle tree.

## The branching rule

A sparse Merkle tree is implemented as a binary tree.  The insertion path of any key is given by a deterministic rule: given ```key``` and a nonnegative integer ```depth```, the rule determines that ```key``` belongs to either the ```left``` or ```right``` branch at depth ```depth```.

The precise rule is as follows.  In-circuit, compute a Poseidon hash of ```key``` to obtain a 4-tuple of field elements 
```
Poseidon(key) = (k_0, k_1, k_2, k_3).
```
Write the field elements in binary (in little-endian order):
```
k_0 = b_0 b_1 ... b_63
k_1 = b_64 b_65 ... b_127
....
```

At the root, ```key``` goes to the left subtree if ```b_0 = 0```, otherwise the right subtree.  At depth 1, ```key``` goes to the left subtree if ```b_1 = 0```, otherwise the right subtree, and similarly for higher depth.

## The tree structure

A Merkle tree with no entry at all is represented by the hash value
```root = hash(0).```
(With the Plonky2 backend, the hash function ```hash``` will output a 4-tuple of field elements.)

A Merkle tree with a single entry ```(key, value)``` is called a "leaf".  It is represented by the hash value
```root = hash((key, value, 1)).```

A Merkle tree ```tree``` with more than one entry is required to have two subtrees, ```left``` and ```right```.  It is then represented by the hash value
```root = hash((left_root, right_root, 2)).```

(The role of the constants 1 and 2 is to prevent collisions between leaves and non-leaf Merkle roots.  If the constants were omitted, a large Merkle tree could be dishonestly interpreted as a leaf, leading to security vulnerabilities.)

## Example

Suppose we want to build a Merkle tree from the following `Dictionary` with three key-value pairs:
```
{
    4: "even",
    5: "odd",
    6: "even"
}
```

The keys are integers, so the are represented in-circuit by themselves.  Let's suppose that in little-endian order, the first three bits of the hashes of the keys are:
```
hash(4) = 000...
hash(5) = 010...
hash(6) = 001...
```

The resulting tree looks like:
```
                root
              /      \
           L_root   R_root = hash(0)
          /      \
      LL_root   LR_root = hash((4, "even", 1))
      /    \
          LLR_root = hash((5, "odd", 1))
LLL_root = hash((6, "even", 1)).
```

The intermediate roots are computed as hashes of their subroots:
```
LL_root = hash((LLL_root, LLR_root, 2))
L_root = hash((LL_root, LR_root, 2))
root = hash((L_root, R_root, 2)).
```

The full `Dictionary` is then represented in the backend as `root` (four field elements in the Plonky2 backend).
