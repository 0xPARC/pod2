# Backend types

On the backend, there is only a single type: `Value`.

A `Value` is simply a tuple of field elements.  With the plonky2 backend, a `Value` is a tuple of 4 field elements.  In general, the backend will expose a constant `VALUE_SIZE`, and a `Value` will be a tuple of `VALUE_SIZE` field elements.

## Integers and booleans

The backend encoding stores integers in such a way that arithmetic operations (addition, multiplication, comparison) are inexpensive to verify in-circuit.

In the case of the Plonky2 backend, an integer $x$ is decomposed as
$$x = x_0 + x_1 \cdot 2^{32}$$
with $0 \leq x_0, x_1 < 2^{32}$ and represented as
$$\texttt{map}\ \iota\ [x_0, x_1, 0, 0],$$
where $\iota:\mathbb{N}\cup\{0\}\rightarrow\texttt{GoldilocksField}$ is the canonical projection.

On the backend, a boolean is stored as an integer, either 0 or 1; so logical operations on booleans are also inexpensive.

## Strings

The backend encoding stores strings as hashes, using a hash function that might not be zk-friendly.  For this reason, string operations (substrings, accessing individual characters) are hard to verify in-circuit.  The POD2 system does not provide methods for manipulating strings.

In other words: As POD2 sees it, two strings are either equal or not equal.  There are no other relationships between strings.

In the case of the Plonky2 backend, a string is converted to a sequence of bytes with the byte `0x01` appended as  padding, then the bytes are split into 7-byte chunks starting from the left, these chunks then being interpreted as integers in little-endian form, each of which is naturally an element of `GoldilocksField`, whence the resulting sequence may be hashed via the Poseidon hash function. Symbolically, given a string $s$, its hash is defined by

$$\texttt{poseidon}(\texttt{map}\ (\iota\circ\jmath_\texttt{le-bytes->int})\ \texttt{chunks}_7(\jmath_\texttt{string->bytes}(s)\ \texttt{++}\ [\texttt{0x01}])),$$

where `poseidon` is the Poseidon instance used by Plonky2, $\iota$ is as above, $\texttt{chunks}_{n}:[\texttt{u8}]\rightarrow [[\texttt{u8}]]$ is defined such that[^aux]

$$\texttt{chunks}_n(v) = \textup{if}\ v = [\ ]\ \textup{then}\ [\ ]\ \textup{else}\ [\texttt{take}_n v]\ \texttt{++}\ \texttt{chunks}_n(\texttt{drop}_n v),$$

the mapping $\jmath_\texttt{le-bytes->int}: [u8] \rightarrow{N}\cup\{0\}$ is given by

$$[b_0,\dots,b_{N-1}]\mapsto \sum_{i=0}^{N-1} b_i \cdot 2^{8i},$$

and $\jmath_\texttt{string->bytes}$ is the canonical mapping of a string to its UTF-8 representation.

## Compound types

The three front-end compound types (`Dictionary`, `Array`, `Set`) are all represented as Merkle roots on the backend.  The details of the representation are explained on a separate [Merkle tree](./merkletree.md) page.