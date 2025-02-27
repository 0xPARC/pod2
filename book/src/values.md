# POD value types
From the frontend perspective, POD values may be one of the following[^type] types: two atomic types
- `Integer`
- `Bool`
- `String`
- `Raw`

and three compound types
- `Dictionary`
- `Array`
- `Set`.

From the backend perspective, however, these types will all be encoded as a fixed number of field elements, the number being chosen so as to accommodate the `Integer` type as well as hashes to represent the `String` and compound types with the appropriate level of security.

In the case of the Plonky2 backend with 100 bits of security, all of these types are represented as 4 field elements, the output of the Poseidon hash function used there being

$$\texttt{HashOut<GoldilocksField>}\simeq\texttt{[GoldilocksField; 4]}.$$


## `Integer`
In the frontend, this type is none other than `u64`[^i64]. In the backend, it will be appropriately embedded into the codomain of the canonical hash function.

In the case of the Plonky2 backend, this is done by decomposing such an integer $x$ as
$$x = x_0 + x_1 \cdot 2^{32}$$
with $0 \leq x_0, x_1 < 2^{32}$ and representing it as
$$\texttt{map}\ \iota\ [x_0, x_1, 0, 0],$$
where $\iota:\mathbb{N}\cup\{0\}\rightarrow\texttt{GoldilocksField}$ is the canonical projection.

## `Bool`
In the frontend, this is a simple bool.  In the backend, it will have the same encoding as an `Integer` `0` (for `false`) or `1` (for `true`).

## `String`
In the frontend, this type corresponds to the usual `String`. In the backend, the string will be mapped to a sequence of field elements and hashed with the hash function employed there, thus being represented by its hash.

In the case of the Plonky2 backend, the string is converted to a sequence of bytes with the byte `0x01` appended as  padding, then the bytes are split into 7-byte chunks starting from the left, these chunks then being interpreted as integers in little-endian form, each of which is naturally an element of `GoldilocksField`, whence the resulting sequence may be hashed via the Poseidon hash function. Symbolically, given a string $s$, its hash is defined by

$$\texttt{poseidon}(\texttt{map}\ (\iota\circ\jmath_\texttt{le-bytes->int})\ \texttt{chunks}_7(\jmath_\texttt{string->bytes}(s)\ \texttt{++}\ [\texttt{0x01}])),$$

where `poseidon` is the Poseidon instance used by Plonky2, $\iota$ is as above, $\texttt{chunks}_{n}:[\texttt{u8}]\rightarrow [[\texttt{u8}]]$ is defined such that[^aux]

$$\texttt{chunks}_n(v) = \textup{if}\ v = [\ ]\ \textup{then}\ [\ ]\ \textup{else}\ [\texttt{take}_n v]\ \texttt{++}\ \texttt{chunks}_n(\texttt{drop}_n v),$$

the mapping $\jmath_\texttt{le-bytes->int}: [u8] \rightarrow{N}\cup\{0\}$ is given by

$$[b_0,\dots,b_{N-1}]\mapsto \sum_{i=0}^{N-1} b_i \cdot 2^{8i},$$

and $\jmath_\texttt{string->bytes}$ is the canonical mapping of a string to its UTF-8 representation.

## `Raw`
"Raw" is short for "raw value".  A `Raw` exposes a backend value on the frontend.

With the plonky2 backend, a `Raw` is a tuple of 4 elements of the Goldilocks field.

## Dictionary, array, set

The array, set and dictionary types are similar types. While all of them use [a merkletree](./merkletree.md) under the hood, each of them uses it in a specific way:
- **dictionary**: the user original keys and values are hashed to be used in the leaf.
    - `leaf.key=hash(original_key)`
    - `leaf.value=hash(original_value)`
- **array**: the elements are placed at the value field of each leaf, and the key field is just the array index (integer)
    - `leaf.key=i` 
    - `leaf.value=original_value` 
- **set**: the value field of the leaf is unused, and the key contains the hash of the element
    -  `leaf.key=hash(original_value)`
    - `leaf.value=0`

In the three types, the merkletree under the hood allows to prove inclusion & non-inclusion of the particular entry of the {dictionary/array/set} element.

A concrete implementation of dictionary, array, set can be found at [pod2/src/middleware/containers.rs](https://github.com/0xPARC/pod2/blob/main/src/middleware/containers.rs).

<br><br>

---


[^type]: <font color="red">TODO</font> In POD 1, there is the `cryptographic` type, which has the same type of the output of the hash function employed there. It is useful for representing arbitrary hashes. Do we want to expand our type list to include a similar type, which would correspond to the `HashOut` type in the case of Plonky2? This would not have a uniform representation in the frontend if we continue to be backend agnostic unless we fix the number of bits to e.g. 256, in which case we would actually need one more field element in the case of Plonky2.
[^i64]: <font color="red">TODO</font> Replace this with `i64` once operational details have been worked out.
[^aux]: Definitions of `drop` and `take` may be found [here](https://hackage.haskell.org/package/haskell98-2.0.0.3/docs/Prelude.html#v:drop) and [here](https://hackage.haskell.org/package/haskell98-2.0.0.3/docs/Prelude.html#v:take).
                      
