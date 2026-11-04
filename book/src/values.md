# POD value types
From the frontend perspective, POD values may be one of the following types: atomic types
- `Int`
- `Bool`
- `String`
- `PublicKey`
- `SecretKey`
- `Predicate`
- `Untyped`

and three compound types
- `Dictionary`
- `Array`
- `Set`.

From the backend perspective, however, these types will all be encoded as a fixed number of field elements, the number being chosen so as to accommodate the `Int` type as well as hashes to represent the `String` and compound types with the appropriate level of security.

In the case of the Plonky2 backend with 100 bits of security, all of these types are represented as 4 field elements, the output of the Poseidon hash function used there being

$$\texttt{HashOut<GoldilocksField>}\simeq\texttt{[GoldilocksField; 4]}.$$

The exact encodings are described in [Backend types](./backendtypes.md).

## `Int`
In the frontend, this type is none other than `i64`. In the backend, it will be appropriately embedded into the codomain of the canonical hash function.

## `Bool`
In the frontend, this is a simple bool.  In the backend, it will have the same encoding as an `Int` `0` (for `false`) or `1` (for `true`).

## `String`
In the frontend, this type corresponds to the usual `String`. In the backend, the string will be mapped to a sequence of field elements and hashed with the hash function employed there, thus being represented by its hash.

## `PublicKey` and `SecretKey`
A public key (a point of the elliptic curve) and a secret key (a scalar) of the
[signature scheme](./signature.md).  In the backend, each is represented by the
hash of its field element representation.

## `Predicate`
A [predicate](./statements.md) used as a value.  In the backend, it is
represented by the hash of the predicate.  This allows custom predicates to take
other predicates as arguments.

## `Untyped`
An untyped raw value, which exposes a [backend `Value`](./backendtypes.md) on the frontend.

With the plonky2 backend, an `Untyped` value is a tuple of 4 elements of the Goldilocks field.

## Dictionary, array, set

The array, set and dictionary types are similar types. While all of them use [a merkletree](./merkletree.md) under the hood, each of them uses it in a specific way:
- **dictionary**: the keys are strings, which are hashed to be used as the leaf key; the leaf value is the backend value of the original value.
    - `leaf.key=hash(original_key)`
    - `leaf.value=original_value`
- **array**: the elements are placed at the value field of each leaf, and the key field is just the array index (integer)
    - `leaf.key=i`
    - `leaf.value=original_value`
- **set**: both the key and the value are set to the value.
    - `leaf.key=original_value`
    - `leaf.value=original_value`

In the three types, the merkletree under the hood allows to prove inclusion & non-inclusion of the particular entry of the {dictionary/array/set} element.

Since the backend only sees the Merkle root, a container may be interpreted as
more than one type.  For example, `Dictionary{"a": "a"}` and `Set{"a"}` have the
same root, and so do `Array[0]` and `Set{0}`.  All empty containers share the
same root.

A concrete implementation of dictionary, array, set can be found at [pod2/src/middleware/containers.rs](https://github.com/0xPARC/pod2/blob/main/src/middleware/containers.rs).
