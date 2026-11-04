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

From the backend perspective, however, these types are all encoded as a fixed number of field elements (4 in the Plonky2 backend); the encodings are described in [Backend types](./backendtypes.md).

## `Int`
A signed 64-bit integer (`i64`).

## `Bool`
A boolean.  It has the same encoding as an `Int` `0` (for `false`) or `1` (for `true`).

## `String`
A UTF-8 string.  Strings can only be compared for equality.

## `PublicKey` and `SecretKey`
A public key (a point of the elliptic curve) and a secret key (a scalar) of the
[signature scheme](./signature.md).

## `Predicate`
A [predicate](./statements.md) used as a value.  This allows custom predicates
to take other predicates as arguments.

## `Untyped`
An untyped raw value, which exposes a [backend `Value`](./backendtypes.md) on the frontend.

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
